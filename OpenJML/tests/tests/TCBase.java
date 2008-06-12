package tests;
import java.net.URI;

import javax.tools.Diagnostic;
import javax.tools.JavaFileObject;

import junit.framework.AssertionFailedError;

import org.jmlspecs.openjml.JmlSpecs;

import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;



public abstract class TCBase extends JmlTestCase {

    static String z = java.io.File.pathSeparator;
    static String testspecpath1 = "$A"+z+"$B";
    static String testspecpath;
    int expectedExit = -1;
    boolean useSystemSpecs = false;

    protected void setUp() throws Exception {
        testspecpath = testspecpath1;
        super.setUp();
        options.put("-specs",   testspecpath);
        options.put("-sourcepath",   testspecpath);
        if (!useSystemSpecs) options.put("-noInternalSpecs","");
        main.register(context);
        JmlEnter.instance(context); // Needed to avoid circular dependencies in tool constructors that only occur in testing
        specs = JmlSpecs.instance(context);
        Log.instance(context).multipleErrors = true;
        expectedExit = -1; // -1 means use default: some message==>1, no messages=>0
                    // this needs to be set manually if all the messages are warnings
        print = false;
    }
    
    protected void tearDown() throws Exception {
        super.tearDown();
        specs = null;
    }

    public void helpFailure(String failureMessage, String s, Object ... list) {
        noExtraPrinting = true;
        boolean failed = false;
        try {
            helpTC(s,list);
        } catch (AssertionFailedError a) {
            failed = true;
            assertEquals("Failure report wrong",failureMessage,a.getMessage());
        }
        if (!failed) fail("Test Harness failed to report an error");
    }

    public void helpTC(String s, Object ... list) {
        helpTCX(null,s,list);
    }

    public void helpTCF(String filename,String s, Object ... list) {
        helpTCX(filename,s,list);
    }

    public void helpTCX(String filename, String s, Object[] list) {
        try {
            JavaFileObject f = new TestJavaFileObject(filename,s);
            if (filename != null) addMockFile("#B/" + filename,f);
            Log.instance(context).useSource(f);
            List<JavaFileObject> files = List.of(f);
            //comp.compile(files,List.<String>nil(),null);
            int ex = main.compile(new String[]{}, context, files, null);
            
            if (print) JmlSpecs.instance(context).printDatabase();
            if (print) printErrors();
            assertEquals("Wrong number of messages seen",list.length,2*d.getDiagnostics().size());
            int i=0;
            int k = 0;
            for (Diagnostic<? extends JavaFileObject> dd: d.getDiagnostics()) {
                if (k >= list.length) break;
                assertEquals("Message " + i + " mismatch",list[k++],dd.toString());
                if (k >= list.length) break;
                assertEquals("Column for message " + i,((Integer)list[k++]).intValue(),dd.getColumnNumber());
                i++;
            }
            if (expectedExit == -1) expectedExit = list.length == 0?0:1;
            assertEquals("Wrong exit code",expectedExit, ex);
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionFailedError e) {
            if (!print && !noExtraPrinting) printErrors();
            throw e;
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

