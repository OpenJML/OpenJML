package org.jmlspecs.openjmltest;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Strings;
import org.junit.Before;
import org.junit.BeforeClass;

import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Options;

/** This is a base class for unit test files that exercise the RAC.
 * It inherits from JmlTestCase the diagnostic collector implementation
 * and the (optional) collection of System.out and System.err.  It 
 * implements as well the mechanisms for running RAC via programmatic
 * calls to openjml and then executing the resulting program.
 * 
 * @author David R. Cok
 *
 */
public abstract class RacBase extends JmlTestCase {
	
	// These are common strings for parts of expected output that can frequently change
    public static final String locA = "(Utils.java:143)";
    public static final String locB = "(Utils.java:94)";
    public static final String locC = "(Utils.java:96)";
    public static final String locD = "(Utils.java:127)";

	public final static String OpenJMLDemoPath = "../../OpenJMLDemo";
	
    protected String testspecpath1 = "$A"+z+"$B";
    protected String testspecpath;
    protected int expectedExit = 0; // Expected result of compiler
    protected int expectedRACExit = 0; // Expected result of RACed program
    protected int expectedNotes; // Number of messages to ignore (e.g. uninteresting compiler warnings)
    protected boolean jdkrac = false; // Set to true to do external system tests of RAC (emulating outside of JUnit)
    protected boolean continueAnyway = false; // If true, attempt to run the program despite compiler warnings or errors
    
    protected String expected_compile = "expected-compile";
    protected String expected_run = "expected-run";

    /** These are the default command-line arguments for running the RACed
     * program.  The first argument is the java executable; the null argument
     * is replaced by the class name of the class containing the main method.     
     * */
    protected String[] defrac = new String[]{jdk, "-ea", "-classpath", "",null};

    /** These are actual command-line arguments, if they are set differently
     * by a subclass.
     */
    protected String[] rac = null; // initialized in subclasses
    
    protected String outdir;

    @BeforeClass
    public static void mktempdirectory() {
    	File f = new File("testcompiles");
    	if (!f.exists()) {
    		f.mkdir();
    	}
    }
    
    /** Derived classes can initialize
     * testspecpath1 - the specspath to use
     * <BR>jdkrac - default is false; if true, adjusts the classpath???
     * <BR>rac - the command-line to run the raced program; default is the contents of defrac
     * <BR>
     * After this call, if desired, modify
     * <BR>print - if true, prints out errors as encountered, for test debugging (and disables failing the JUnit test if the error mismatches)
     * <BR>expectedExit - the expected exit code from running openjml
     * <BR>expectedRacExit - the expected exit code from running the RACed program
     * <BR>expectedErrors - the expected number of errors from openjml (typically and by default 0)
     */
    @Override
    @Before
    public void setUp() throws Exception {
        //System.out.println("Using " + jdk);
        
        // Use the default specs path for tests
        testspecpath = testspecpath1;
        // Define a new collector that filters out the notes
        collector = new FilteredDiagnosticCollector<JavaFileObject>(false,false);
        super.setUp();
        
        // Setup the options
        addOptions("--specs-path", testspecpath);
        //main.addJavaOption("-d", outdir); // This is where the output program goes // FIXME - for some reason this does not work here
        addOptions("--rac","--rac-java-checks","--rac-check-assumptions");
        addOptions("--show-not-implemented");
        addOptions("--no-purity-check"); // System specs have a lot of purity errors, so turn this off for now
        addOptions("--rac-show-source=none");
        expectedExit = 0;
        expectedRACExit = 0;
        expectedNotes = 2; // Two lines to ignore
        print = false;
    }
    
    @Override
    public void tearDown() throws Exception {
        super.tearDown();
    }
    
    public static String macstring = "Exception in thread \"main\" ";

    public String setupOutdir() {
        outdir = System.getenv("OPENJML_ROOT") + "/../OpenJML/OpenJMLTest/testcompiles/" + getMethodName(2);
        var d = new java.io.File(outdir);
        d.mkdirs();
        defrac[3] = outdir;
        if (rac == null) rac = new String[]{jdk, "-ea", "-classpath", outdir, null};
        return outdir;
    }
    
    /** This method does the running of a RAC test for tests that supply with body
     * of a file as a String.
     * No output is
     * expected from running openjml to produce the RACed program;
     * the number of expected diagnostics is set by 'expectedErrors'.
     * @param classname The fully-qualified classname for the test class
     * @param compilationUnitText the compilation unit text which will be put in a mock file
     * @param list any expected diagnostics from openjml, followed by the error messages from the RACed program, line by line
     */
    public void helpTCX(String classname, String compilationUnitText, Object... list) {
    	// Source files are synthetic
    	// Compile destination is destdir
    	// Expected output is containted in the test code (not in a file)
    	String destdir = setupOutdir();
    	new java.io.File(destdir).delete(); // Make sure old builds are deleted
    	new java.io.File(destdir).mkdir();

        String term = "\n|(\r(\n)?)"; // any of the kinds of line terminators
        StreamGobbler out=null,err=null;
        boolean isMac = System.getProperty("os.name").contains("Mac");
        try {
            ListBuffer<JavaFileObject> files = new ListBuffer<JavaFileObject>();
            String filename = classname.replace(".","/")+".java";
            JavaFileObject f = new TestJavaFileObject(filename,compilationUnitText);
            files.append(f);
            for (JavaFileObject ff: mockFiles) {
                if (ff.toString().endsWith(".java")) files.append(ff);
            }

            Log.instance(context).useSource(files.first());

            int ex = main.compile(new String[]{"-d", destdir},files.toList()).exitCode;
            if (print) printDiagnostics();
            int observedMessages = collector.getDiagnostics().size() - expectedNotes;
            if (observedMessages < 0) observedMessages = 0;

            for (int i=0; i<observedMessages; i++) {
                int k = 2*i + 2*expectedNotes;
                if (k >= list.length) {
                    if (!print) printDiagnostics();
                    fail("More diagnostics than expected");
                }
                String expected = list[k].toString();
                String s = noSource(collector.getDiagnostics().get(i));
                assertEquals("Message " + i, expected, s);
                assertEquals("Message " + i, ((Integer)list[k+1]).intValue(), collector.getDiagnostics().get(i).getColumnNumber());
            }
            if (ex != expectedExit) fail("Compile ended with exit code " + ex);
            if (ex != 0 && !continueAnyway) return;
            
            if (rac == null) rac = defrac;
            rac[rac.length-2] = destdir;
            rac[rac.length-1] = classname;
            Process p = Runtime.getRuntime().exec(rac);
            
            out = new StreamGobbler(p.getInputStream());
            err = new StreamGobbler(p.getErrorStream());
            out.start();
            err.start();
            if (timeout(p,10000)) { // 10 second timeout
                fail("Process did not complete within the timeout period");
            }
            
            int i = observedMessages*2;
            if (print) {
                String data = out.input();
                if (data.length() > 0) {
                    String[] lines = data.split(term);
                    for (String line: lines) {
                        System.out.println("OUT: " + line);
                    }
                }
                data = err.input();
                if (data.length() > 0) {
                    String[] lines = data.split(term);
                    for (String line: lines) {
                        System.out.println("ERR: " + line);
                    }
                }
            }
            String data = out.input();
            if (data.length() > 0) {
                String[] lines = data.split(term);
                for (String actual: lines) {
                	//System.out.println("ACT: " + line);
                	if (i < list.length) {
                		String expected = list[i].toString();
                		expected = expected.replace("#DEMO", OpenJMLDemoPath);
                		//System.out.println("EXP: " + expected);
                		if (expected.contains(":") && !actual.matches("^[^:]*:[0-9]+:.*")) 
                			expected = expected.replaceFirst("^[^:]*:[0-9]+: ","");
                		if (!actual.matches(".*:[0-9]+:$")) 
                			expected = expected.replaceFirst(": [^:]*:[0-9]+:$","");
                		//System.out.println("EXP: " + expected);
                        if (!expected.contains("verify: ")) actual = actual.replace("verify: ", "");
                		//System.out.println("EXP: " + expected);
                        assertEquals("Output line " + i, expected, actual);
                	}
                    i++;
                }
            }
            data = err.input();
            if (data.length() > 0) {
                String[] lines = data.split(term);
                for (String actual: lines) {
                	//System.out.println("ERR-ACT: " + actual);
                	if (i < list.length) {
                		String expected = list[i].toString();
                		expected = expected.replace("#DEMO", OpenJMLDemoPath);
                		//System.out.println("ERR-EXP: " + expected);
                        if (actual.startsWith(macstring) && !expected.startsWith(macstring)) actual = actual.substring(macstring.length());
                        else if (!actual.startsWith(macstring) && expected.startsWith(macstring)) expected = expected.substring(macstring.length());
                		//System.out.println("ERR-EXP: " + expected);
//                		if (expected.contains(":") && !actual.matches("^[^:]*:[0-9]+:.*")) 
//                			expected = expected.replaceFirst("^[^:]*:[0-9]+: ","");
//                		if (!actual.matches(".*:[0-9]+:$")) 
//                			expected = expected.replaceFirst(": [^:]*:[0-9]+:",":");
                		//System.out.println("ERR-EXP: " + expected);
                        if (!expected.contains("verify: ")) actual = actual.replace("verify: ", "");
                		//System.out.println("ERR-EXP: " + expected);
                        assertEquals("Output line " + i, expected, actual);
                	}
                    i++;
                }
                if (isMac && i < list.length && list[i].equals(macstring)) i++;
            }

            if (i != list.length && !print) { // if print, then we already printed
                printDiagnostics();
            }
            if (i> list.length) fail("More output than specified: " + i + " vs. " + list.length + " lines");
            if (i< list.length) fail("Less output than specified: " + i + " vs. " + list.length + " lines");
            if (p.exitValue() != expectedRACExit) fail("Exit code was " + p.exitValue());
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            if (!print) printDiagnostics();
            if (!print && !noExtraPrinting) {
                if (out != null) {
                    String[] lines = out.input().split(term);
                    for (String line: lines) {
                        System.out.println("OUT: " + line);
                    }
                }
                if (err != null) {
                    String[] lines = err.input().split(term);
                    for (String line: lines) {
                        System.out.println("ERR: " + line);
                    }
                }
            }
            throw e;
        } finally {
//            if (r != null) 
//                try { r.close(); } 
//                catch (java.io.IOException e) { 
//                    // Give up if there is an exception
//                }
//            if (rerr != null) 
//                try { rerr.close(); } 
//                catch (java.io.IOException e) {
//                    // Give up if there is an exception
//                }
        }
    }
    
    // The following is for tests based on files

    protected boolean runrac = true;
    
    
    /** Call this as a setup routine, followed by RacBase.setUp for file based tests */
    public void setUpForFiles() throws Exception {
//        rac = sysrac;
        jdkrac = true;
        runrac = true;
    }


    /** This method does the running of a RAC test that is based in an external file.  No output is
     * expected from running openjml to produce the RACed program;
     * the number of expected diagnostics is set by 'expectedErrors'.
     * @param dirname The directory containing the test sources, a relative path
     * from the project folder
     * @param mainClassname The fully-qualified classname for the test class (where main is)
     * @param list any expected diagnostics from openjml, followed by the error messages from the RACed program, line by line
     */
    public void helpTCF(String dirname, String outputdir, String mainClassname, String ... opts) {
    	String destDir = setupOutdir();
//    	System.out.println("SOURCEDIR " + dirname);
//    	System.out.println("DESTDIR " + destDir);
//    	System.out.println("OUTDIR " + outputdir);
        boolean print = false;
        StreamGobbler out=null,err=null;
        try {
            String actCompile = outputdir + "/actual-compile";
            String actRun = outputdir + "/actual-run";
            new File(outputdir).mkdirs();
            new File(actCompile).delete();
            new File(actRun).delete();
            List<String> args = new LinkedList<String>();
            //args.add("-no-jml");
            args.add("-d");
            args.add(outdir);
            //args.add("-classpath");
            //args.add(cp);
            args.add("--rac");
            args.add("--no-purity-check");
            args.add("--code-math=java");
            args.add("--spec-math=bigint");
            if (new File(dirname).isDirectory()) args.add("--dir");
            args.add(dirname);
            args.addAll(Arrays.asList(opts));
            
            PrintWriter pw = new PrintWriter(actCompile);
            int ex = org.jmlspecs.openjml.Main.execute(pw,null,null,args.toArray(new String[args.size()]));
            pw.close();
            
            String compdiffs = "";
            if (new File(outputdir + "/" + expected_compile).exists()) {
            	compdiffs = outputCompare.compareFiles(outputdir + "/" + expected_compile, actCompile);
        		if (compdiffs == null) {
        			new File(actCompile).delete();
        		} 
        	} else {
            	for (String file: new File(outputdir).list()) {
            		if (!file.contains("expected-compile")) continue;
            		compdiffs = outputCompare.compareFiles(outputdir + "/" + file, actCompile);
            		if (compdiffs == null) {
            			new File(actCompile).delete();
            			break;
            		}
            	}
            }
            if (compdiffs != null) {
                if (compdiffs.isEmpty()) {
                    compdiffs = ("No expected output file for compiler output");
                    System.out.println(compdiffs);
                } else {
                    System.out.println(compdiffs);
                    //  fail("Files differ: " + compdiffs);
                }
            }
            if (ex != expectedExit) fail("Compile ended with exit code " + ex);

            if (runrac) {
                if (rac == null) rac = defrac;
                rac[rac.length-1] = mainClassname;
                Process p = Runtime.getRuntime().exec(rac);

                out = new StreamGobbler(p.getInputStream());
                err = new StreamGobbler(p.getErrorStream());
                out.start();
                err.start();
                if (timeout(p,10000)) { // 10 second timeout
                    fail("Process did not complete within the timeout period");
                }
                String output = out.input().replaceAll("@[0-9abcdef]+", "@########");
                ex = p.exitValue();
                output = "OUT:" + eol + output + eol + "ERR:" + eol + err.input();
                if (print) System.out.println(output);
                String diffs = "";
                for (String file: new File(outputdir).list()) {
                    if (!file.contains("expected-run")) continue;
                    diffs = outputCompare.compareText(outputdir + "/" + file,output);
                    if (diffs == null) break;
                }
                if (diffs != null) {
                    BufferedWriter b = new BufferedWriter(new FileWriter(actRun));
                    b.write(output);
                    b.close();
                }
                if (ex != expectedRACExit) fail("Execution ended with exit code " + ex + " " + output);
                if (diffs != null) {
                    if (diffs.isEmpty()) {
                        fail("No expected output file for runtime output");
                    } else {
                        //System.out.println("EXP:" + outputdir + "   ACT: " + actRun + "   CUR: " + System.getProperty("user.dir") + "  DEMO: " + OpenJMLDemoPath);
                        System.out.println(diffs);
                        fail("Unexpected output: " + diffs);
                    }
                }
            }
            if (compdiffs != null) fail("Files differ: " + compdiffs);

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
