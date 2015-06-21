package org.jmlspecs.openjmltest.testcases;

import static org.junit.Assert.fail;

import java.io.File;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjmltest.TCBase;
import org.junit.Ignore;
import org.junit.Test;

public class SFBugs extends TCBase {

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
    	expectedExit = 1;
        helpTCF("test/tcWithJml/TCWithJml.java","test/tcWithJml", "-cp", "test/tcWithJml");
    }
    
    @Test public void sfpatch25() {
    	expectedExit = 0;
        helpTCF("test/sfpatch25/A.java","test/sfpatch25", "-cp", "test/sfpatch25", "-esc");
    }
    
    @Test public void sfbug407() {
    	expectedExit = 0;
        helpTCF("test/sfbug407","test/sfbug407", "-cp", "test/sfbug407", "-esc", "-progress");
    }
    
    @Test public void sfbug398() {
    	expectedExit = 0;
        helpTCF("test/sfbug398","test/sfbug398", "-cp", "test/sfbug398", "-esc", "-progress");
    }
    
    @Test public void sfbug399() {
    	expectedExit = 0;
        helpTCF("test/sfbug399","test/sfbug399", "-cp", "test/sfbug399", "-esc","-progress");
    }
    
    @Ignore // very long running
    @Test public void sfbug404() {
    	expectedExit = 0;
        helpTCF("test/sfbug404","test/sfbug404", "-cp", "test/sfbug404", "-esc","-progress","-logic=AUFNIRA");
    }
    
    @Test public void sfbug408() {
    	expectedExit = 0;
        helpTCF("test/sfbug408","test/sfbug408", "-cp", "test/sfbug408", "-esc","-progress");
    }
    
    @Test public void sfbug409() {
    	expectedExit = 0;
        helpTCF("test/sfbug409","test/sfbug409", "-cp", "test/sfbug409", "-esc","-progress");
    }
    
    @Test public void sfbug410() {
    	expectedExit = 0;
        helpTCF("test/sfbug410","test/sfbug410", "-cp", "test/sfbug410", "-esc","-progress");
    }
    
    @Ignore // Can be very long running
    @Test public void sfbug414() {
    	expectedExit = 0;
        helpTCF("test/sfbug414","test/sfbug414", "-cp", "test/sfbug414", "-esc","-progress","-logic=AUFNIRA","-escMaxWarnings=5","-show","-method=Sqrt.sqrt","-subexpressions");
    }
    
    
}
