package tests;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.net.URI;

import javax.tools.JavaFileObject;

import junit.framework.AssertionFailedError;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Utils;

import tests.JmlTestCase.FilteredDiagnosticCollector;

import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

public abstract class RacBase extends JmlTestCase {

    static String z = java.io.File.pathSeparator;
    static String testspecpath1 = "$A"+z+"$B";
    static String testspecpath;
    int expectedExit = 0;
    int expectedRACExit = 0;
    int expectedErrors = 0;
    boolean jdkrac = false;

    String jdk = System.getProperty("java.home") + "/bin/java";

    String[] defrac = new String[]{jdk, "-classpath","bin;testdata",null};

    String[] rac; // initialized in subclasses
    

    protected void setUp() throws Exception {
        //System.out.println("Using " + jdk);
        testspecpath = testspecpath1;
        collector = new FilteredDiagnosticCollector<JavaFileObject>(true);
        super.setUp();
        options.put("-specs",   testspecpath);
        options.put("-d", "testdata");
        options.put("-rac",   "");
        if (jdkrac) {
            String sy = System.getProperty(Utils.eclipseProjectLocation);
            if (sy == null) {
                fail("The OpenJML project location should be set using -D" + Utils.eclipseProjectLocation + "=...");
            } else if (!new File(sy).exists()) {
                fail("The OpenJML project location set using -D" + Utils.eclipseProjectLocation + " to " + sy + " does not exist");
            } else {
                options.put("-classpath",sy+"/testdata"+z+sy+"/jdkbin"+z+sy+"/bin");
            }
        }
        main.register(context);
        specs = JmlSpecs.instance(context);
        Log.instance(context).multipleErrors = true;
        expectedExit = 0;
        expectedRACExit = 0;
        expectedErrors = 0;
        print = false;
    }
    
    protected void tearDown() throws Exception {
        super.tearDown();
        specs = null;
    }

//    public void helpFailure(String failureMessage, String s, Object ... list) {
//        noExtraPrinting = true;
//        boolean failed = false;
//        try {
//            helpTC(s,list);
//        } catch (AssertionFailedError a) {
//            failed = true;
//            assertEquals("Failure report wrong",failureMessage,a.getMessage());
//        }
//        if (!failed) fail("Test Harness failed to report an error");
//    }

//    public void helpTC(String s, Object ... list) {
//        helpTCX(null,s,list);
//    }
//
//    public void helpTCF(String filename,String s, Object ... list) {
//        helpTCX(filename,s,list);
//    }
    
    public void helpTCX(String classname, String s, Object... list) {
        BufferedReader r = null;
        BufferedReader rerr = null;
        try {
            String filename = classname.replace(".","/")+".java";
            JavaFileObject f = new TestJavaFileObject(filename,s);
            
            Log.instance(context).useSource(f);
            List<JavaFileObject> files = List.of(f);
            //int ex = main.compile(new String[]{"-target","5"}, context, files, null);  // FIXME - don't yet have multiple versions working - perhaps 
            int ex = main.compile(new String[]{}, context, files, null);
            
            if (print || collector.getDiagnostics().size()!=expectedErrors) printErrors();
            assertEquals("Errors seen",expectedErrors,collector.getDiagnostics().size());
            for (int i=0; i<expectedErrors; i++) {
                assertEquals("Error " + i, list[2*i].toString(), collector.getDiagnostics().get(i).toString());
                assertEquals("Error " + i, ((Integer)list[2*i+1]).intValue(), collector.getDiagnostics().get(i).getColumnNumber());
            }
            if (ex != expectedExit) fail("Compile ended with exit code " + ex);
            if (ex != 0) return;
            
            if (rac == null) rac = defrac;
            rac[rac.length-1] = classname;
            Process p = Runtime.getRuntime().exec(rac);
            r = new BufferedReader(new InputStreamReader(p.getInputStream()));
            rerr = new BufferedReader(new InputStreamReader(p.getErrorStream()));
            int i = expectedErrors*2;
            boolean done = false;
            boolean edone = false;
            while (!done || !edone) {
                while (!done && !rerr.ready()) {
                    String ss = r.readLine();
                    if (ss == null) { done = true; break; }
                    if (print || i >= list.length) { System.out.println("OUT: " + ss); }
                    if (!print) if (i < list.length) assertEquals("Output line " + i, list[i], ss);
                    i++;
                }

                while (!edone && !r.ready()) {
                    String ss = rerr.readLine();
                    if (ss == null) { edone = true; break; }
                    if (print || i >= list.length) { System.out.println("ERR: " + ss); }
                    if (!print) if (i < list.length) assertEquals("Output line " + i, list[i], ss);
                    i++;
                }
            }
            if (i> list.length) fail("More output than specified: " + i + " vs. " + list.length + " lines");
            if (i< list.length) fail("Less output than specified: " + i + " vs. " + list.length + " lines");
            if (p.exitValue() != expectedRACExit) fail("Exit code was " + p.exitValue());
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionFailedError e) {
            if (!print && !noExtraPrinting) printErrors();
            throw e;
        } finally {
            if (r != null) 
                try { r.close(); } 
                catch (java.io.IOException e) { 
                    // Give up if there is an exception
                }
            if (rerr != null) 
                try { rerr.close(); } 
                catch (java.io.IOException e) {
                    // Give up if there is an exception
                }
        }
    }

    /** Used to add a pseudo file to the file system. Note that for testing, a 
     * typical filename given here might be #B/A.java, where #B denotes a 
     * mock directory on the specification path
     * @param filename the name of the file, including leading directory components 
     * @param content the String constituting the content of the pseudo-file
     */
    protected void addMockFile(/*@ non_null */ String filename, /*@ non_null */String content) {
        try {
            addMockFile(filename,new TestJavaFileObject(new URI("file:///" + filename),content));
        } catch (Exception e) {
            fail("Exception in creating a URI: " + e);
        }
    }

    /** Used to add a pseudo file to the file system. Note that for testing, a 
     * typical filename given here might be #B/A.java, where #B denotes a 
     * mock directory on the specification path
     * @param filename the name of the file, including leading directory components 
     * @param file the JavaFileObject to be associated with this name
     */
    protected void addMockFile(String filename, JavaFileObject file) {
        specs.addMockFile(filename,file);
    }


}
