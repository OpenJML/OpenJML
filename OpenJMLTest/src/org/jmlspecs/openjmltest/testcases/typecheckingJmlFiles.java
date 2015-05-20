package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.fail;

import java.io.File;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Test;

public class typecheckingJmlFiles extends TCBase {

//    @Override
//    public void setUp() throws Exception {
////        noCollectDiagnostics = true;
////        jmldebug = true;
//        super.setUp();
//    }

    public void helpTCF(String sourceDirname, String outDir, String ... opts) {
        boolean print = false;
        try {
            new File(outDir).mkdirs();
            String actCompile = outDir + "/actual";
            new File(actCompile).delete();
            List<String> args = new LinkedList<String>();
            args.add("-check");
            args.add("-jmltesting");
            if (new File(sourceDirname).isDirectory()) args.add("-dir");
            args.add(sourceDirname);
            if (opts != null) {
                for (String o: opts) args.add(o);
            }
            
            args.addAll(Arrays.asList(opts));
            
            PrintWriter pw = new PrintWriter(actCompile);
            int ex = org.jmlspecs.openjml.Main.execute(pw,null,null,args.toArray(new String[args.size()]));
            pw.close();
            
            String diffs = compareFiles(outDir + "/expected", actCompile);
            int n = 0;
            while (diffs != null) {
                n++;
                String name = outDir + "/expected" + n;
                if (!new File(name).exists()) break;
                diffs = compareFiles(name, actCompile);
            }
            if (diffs != null) {
                System.out.println(diffs);
                fail("Files differ: " + diffs);
            }  
            new File(actCompile).delete();
            if (ex != expectedExit) fail("Compile ended with exit code " + ex);

        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            throw e;
        } finally {
            // Should close open objects
        }
    }


    @Test public void test() {
        helpTCF("test/tcWithJml/TCWithJml.java","test/tcWithJml", "-cp", "test/tcWithJml");
    }
    
}
