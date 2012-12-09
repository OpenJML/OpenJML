package tests;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.net.URI;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;


public abstract class EscBase extends JmlTestCase {

    static String z = java.io.File.pathSeparator;
    static String testspecpath1 = "$A"+z+"$B";
    static String testspecpath;
    int expectedExit = 0;
    int expectedErrors = 0;
    boolean noAssociatedDeclaration;
    String[] args;

    @Override
    public void setUp() throws Exception {
        testspecpath = testspecpath1;
        collector = new FilteredDiagnosticCollector<JavaFileObject>(true);
        super.setUp();
        options.put("-specspath",   testspecpath);
        options.put("-command","esc");
        Utils.instance(context).jmlverbose = 4;
        main.setupOptions();
        //main.register(context);
        specs = JmlSpecs.instance(context);
        Log.instance(context).multipleErrors = true;
        expectedExit = 0;
        expectedErrors = 0;
        noAssociatedDeclaration = false;
        print = false;
        args = new String[]{};
    }
    

    protected void setOption(String option) {
        if (option == null) {
            // nothing set
        } else if (option.equals("-boogie")) {
            options.put("-newesc","");
            options.put("-boogie","");
        } else {
            options.put(option,"");
        }
    }

    @Override
    public void tearDown() throws Exception {
        super.tearDown();
        specs = null;
    }

    
    protected void helpTCX(String classname, String s, Object... list) {
        try {
            expectedErrors = list.length/2;
            String filename = classname.replace(".","/")+".java";
            JavaFileObject f = new TestJavaFileObject(filename,s);
            
            Log.instance(context).useSource(f);
            List<JavaFileObject> files = List.of(f);
            int ex = main.compile(args, context, files, null);
            
            if (print) printErrors();
            int j = 0;
            for (int i=0; i<expectedErrors; i++) {
                int col = ((Integer)list[2*i+1]).intValue();
                if (col < 0) {
                    // allowed to be optional
                    if (j >= collector.getDiagnostics().size()) {
                        // OK - just skip
                    } else if (list[2*i].toString().equals(noSource(collector.getDiagnostics().get(j))) &&
                            -col == Math.abs(collector.getDiagnostics().get(j).getColumnNumber())) {
                        j++;
                    } else {
                        // Not equal and the expected error is optional so just skip
                    }
                } else {
                    if (noAssociatedDeclaration && list[2*i].toString().contains("Associated declaration")) {
                        // OK - skip
                    } else if (j >= collector.getDiagnostics().size()) {
                        assertEquals("Errors seen",expectedErrors,collector.getDiagnostics().size());
                    } else {
                        assertEquals("Error " + i, list[2*i].toString(), noSource(collector.getDiagnostics().get(j)));
                        assertEquals("Error " + i, col, collector.getDiagnostics().get(j).getColumnNumber());
                        j++;
                    }
                }
            }
            if (j < collector.getDiagnostics().size()) {
                assertEquals("Errors seen",expectedErrors,collector.getDiagnostics().size());
            }
            if (ex != expectedExit) fail("Compile ended with exit code " + ex);

        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
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
