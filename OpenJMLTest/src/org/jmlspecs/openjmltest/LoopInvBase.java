package org.jmlspecs.openjmltest;

import static org.junit.Assert.fail;

import java.io.File;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.LinkedList;

import org.junit.Rule;
import org.junit.rules.TestName;

public class LoopInvBase extends JmlTestCase {
    protected static final String OutputDirPath = "/Users/koja/UCF/Research/rapidOutput";
    protected static final String LoopExercisesPath = "/Users/koja/git/OpenJML/OpenJMLTest/testfiles/loopExercises/";

    /** options is a comma- or space-separated list of options to be added */
    protected String options;
    protected String solver;

    @Rule
    public TestName testname = new TestName();
    protected int expectedExit = 0;

    @Override
    public void setUp() throws Exception {
        super.setUp();
    }

    @Override
    public void tearDown() throws Exception {
        super.tearDown();
        specs = null;
    }

    public java.util.List<String> setupForFiles(String sourceDirOrFilename, String outDir, String... opts) {
        new File(outDir).mkdirs();
        java.util.List<String> args = new LinkedList<String>();
        args.add("-loopInv");
        args.add("-mName");
        args.add("max");
        args.add("-outputDir");
        args.add(outDir);
        if (!new File(sourceDirOrFilename).isFile())
            args.add("-dir");
        args.add(sourceDirOrFilename);
        if (solver != null)
            args.add("-prover=" + solver);
        addOptionsToArgs(options, args);
        args.addAll(Arrays.asList(opts));
        return args;
    }

    static public void addOptionsToArgs(String options, java.util.List<String> args) {
        if (options != null) {
            if (options.indexOf(',') >= 0) {
                for (String o : options.split(","))
                    if (!o.isEmpty())
                        args.add(o);
            } else {
                for (String o : options.split(" "))
                    if (!o.isEmpty())
                        args.add(o);
            }
        }
    }

    public void loopInvOnFiles(String sourceDirname, String outDir, String... opts) {
        // boolean print = false;
        try {
            java.util.List<String> args = setupForFiles(sourceDirname, outDir, opts);
            String actCompile = outDir + "/actual";
            new File(actCompile).delete();
            PrintWriter pw = new PrintWriter(actCompile);
            int ex = -1;
            try {
                ex = org.jmlspecs.openjml.Main.execute(pw, null, null, args.toArray(new String[args.size()]));
            } finally {
                pw.close();
            }

            String diffs = outputCompare.compareFiles(outDir + "/expected", actCompile);
            int n = 0;
            while (diffs != null) {
                n++;
                String name = outDir + "/expected" + n;
                if (!new File(name).exists())
                    break;
                diffs = outputCompare.compareFiles(name, actCompile);
            }
            if (diffs != null) {
                System.out.println("TEST DIFFERENCES: " + testname.getMethodName());
                System.out.println(diffs);
                fail("Files differ: " + diffs);
            }
            if (expectedExit != -1 && ex != expectedExit)
                fail("Compile ended with exit code " + ex);
            new File(actCompile).delete();

        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            throw e;
        } finally {
            // Should close open objects
        }
    }

}
