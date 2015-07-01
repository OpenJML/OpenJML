package org.jmlspecs.openjmltest;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.PrintWriter;
import java.net.URI;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;

import javax.tools.JavaFileObject;

import org.eclipse.jdt.annotation.Nullable;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.esc.MethodProverSMT;
import org.jmlspecs.openjmltest.JmlTestCase.FilteredDiagnosticCollector;
import org.junit.Rule;
import org.junit.rules.TestName;
import org.junit.rules.Timeout;
import org.junit.runners.Parameterized.Parameters;

import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;


public abstract class EscBase extends JmlTestCase {
    
	public static final String OpenJMLDemoPath = "../../OpenJMLDemo";
	
    @Rule public TestName testname = new TestName();
    @Rule public Timeout timeout = new Timeout(1800000); // 30 minutes per test
    
    static public java.util.List<String> solvers = java.util.Arrays.asList(new String[]{ 
            "z3_4_3", 
 //           "cvc4",
            //"yices2",
 //             "yices", 
 //            "simplify" 
            });
        
    static public java.util.List<String> solversWithNull = java.util.Arrays.asList(new String[]{ 
    		null,
            "z3_4_3", 
 //           "cvc4",
            //"yices2",
 //             "yices", 
 //            "simplify" 
            });
        
    static public java.util.List<String[]> minQuants = java.util.Arrays.asList(new String[][]{ 
            new String[]{"-minQuant"}, 
            new String[]{"-no-minQuant"}, 
            });
        
    /** The parameters must be a String[] and a String */
    @Parameters
    static public Collection<String[]> parameters() {
        return minQuantAndSolvers(solvers);
    }
    
    static public Collection<String[]> solversOnly() {
        return makeParameters(solvers);
    }
    
    public static final String[] minQuantOptions = new String[]{"-no-minQuant","-minQuant"};
    
    static public  Collection<String[]> minQuantAndSolvers(java.util.List<String> solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) {
            data.add(new String[]{"-no-minQuant",s});
            data.add(new String[]{"-minQuant",s});
        }
        return data;
    }

    static public  Collection<String[]> optionsAndSolvers(String[] options, java.util.List<String> solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) {
        	for (String opts: options) {
        		data.add(new String[]{opts,s});
        	}
        }
        return data;
    }

    
    static public  Collection<String[]> makeParameters(java.util.List<String> options, java.util.List<String> solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) {
            for (String option: options) {
                data.add(new String[]{option,s});
            }
        }
        return data;
    }

    static public  Collection<String[]> makeParameters(java.util.List<String> solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) data.add(new String[]{null,s});
        return data;
    }

    static public  Collection<String[]> makeParameters(String... solvers) {
        Collection<String[]> data = new ArrayList<String[]>(10);
        for (String s: solvers) data.add(new String[]{null,s});
        return data;
    }
    
    static public void addOptionsToArgs(String options, java.util.List<String> args) {
        if (options != null) {
            if (options.indexOf(',')>= 0) {
            	for (String o: options.split(",")) if (!o.isEmpty()) args.add(o);
            } else {
            	for (String o: options.split(" ")) if (!o.isEmpty()) args.add(o);
            }
        }
    }
    
    public void addOptions(String options) {
        if (options != null) {
            if (options.indexOf(',')>= 0) {
            	main.addOptions(options.split(","));
            } else {
            	main.addOptions(options.split(","));
            }
        }
    }
    
    protected static boolean runLongTests = false;
    

    /** options is a comma- or space-separated list of options to be added */
    protected String options;
    protected String solver;
    protected boolean captureOutput = false;
    
    /** options is a comma- or space-separated list of options to be added */
    public EscBase(String options, String solver) {
        this.options = options;
        this.solver = solver;
    }
    
    public void printDiagnostics() {
        System.out.println("SOLVER: " + solver + " " + options);
        super.printDiagnostics();
    }

    protected static String z = java.io.File.pathSeparator;
    protected static String testspecpath1 = "$A"+z+"$B";
    protected static String testspecpath;
    protected int expectedExit = 0;
    protected int expectedErrors = 0;
    protected boolean noAssociatedDeclaration;
    protected String[] args;
//    protected String openJmlPropertiesDir = "../OpenJML"; 

    @Override
    public void setUp() throws Exception {
        if (captureOutput) collectOutput(true);
        testspecpath = testspecpath1;
        collector = new FilteredDiagnosticCollector<JavaFileObject>(true);
        super.setUp();
        main.addOptions("-specspath",   testspecpath);
        main.addOptions("-command","esc");
        main.addOptions("-no-purityCheck");
        main.addOptions("-timeout=300"); // seconds
        main.addOptions("-jmltesting");
        main.addUncheckedOption("openjml.defaultProver=z3_4_3");
        addOptions(options);
        if (solver != null) main.addOptions(JmlOption.PROVER.optionName(),solver);
        specs = JmlSpecs.instance(context);
        expectedExit = 0;
        expectedErrors = 0;
        noAssociatedDeclaration = false;
        print = false;
        args = new String[]{};
        MethodProverSMT.benchmarkName = 
                (this.getClass() + "." + testname.getMethodName()).replace("[0]", "").substring(6);
    }

    public void escOnFiles(String sourceDirname, String outDir, String ... opts) {
    	boolean print = false;
    	try {
    		java.util.List<String> args = setupForFiles(sourceDirname, outDir, opts);
    		String actCompile = outDir + "/actual";
    		new File(actCompile).delete();
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

    public java.util.List<String> setupForFiles(String sourceDirname, String outDir, String ... opts) {
        new File(outDir).mkdirs();
        java.util.List<String> args = new LinkedList<String>();
        args.add("-esc");
        args.add("-no-purityCheck");
        args.add("-jmltesting");
        args.add("-progress");
        args.add("-timeout=300");
        args.add("-code-math=java");
        if (new File(sourceDirname).isDirectory()) args.add("-dir");
        args.add(sourceDirname);
        if (solver != null) args.add("-prover="+solver);
        addOptionsToArgs(options,args);        
        args.addAll(Arrays.asList(opts));
        return args;
    }
    
    
    
    @Override
    public void tearDown() throws Exception {
        super.tearDown();
        specs = null;
        captureOutput = false;
        MethodProverSMT.benchmarkName = null;
    }

    
    protected void helpTCX2(String classname, String s, String classname2, String s2, Object... list) {
        try {
            String filename = classname.replace(".","/")+".java";
            JavaFileObject f = new TestJavaFileObject(filename,s);
            String filename2 = classname2.replace(".","/")+".java";
            JavaFileObject f2 = new TestJavaFileObject(filename2,s2);
            Log.instance(context).useSource(f);
            helpTCXB(List.of(f,f2),list);
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }

    protected void helpTCX(String classname, String s, Object... list) {
        try {
            String filename = classname.replace(".","/")+".java";
            JavaFileObject f = new TestJavaFileObject(filename,s);
            Log.instance(context).useSource(f);
            helpTCXB(List.of(f),list);
        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        }
    }

    protected void helpTCXB(List<JavaFileObject> files, Object... list) {
        try {
            for (JavaFileObject f: mockFiles) files = files.append(f);
            
            int ex = main.compile(args, null, context, files, null);
            if (captureOutput) collectOutput(false);
            
            if (print) printDiagnostics();
            expectedErrors = compareResults(list);
            assertEquals("Errors seen",expectedErrors,collector.getDiagnostics().size());
            if (ex != expectedExit) fail("Compile ended with exit code " + ex);

        } catch (Exception e) {
            e.printStackTrace(System.out);
            fail("Exception thrown while processing test: " + e);
        } catch (AssertionError e) {
            if (!print && !noExtraPrinting) printDiagnostics();
            throw e;
        }
    }
    
    protected interface Special {}
    
    protected class Optional implements Special {
        public Object[] list;
        public Optional(Object[] list) {
            this.list = list;
        }
    }
    
    protected class OneOf implements Special {
        public Object[][] lists;
        public OneOf(Object[] ... lists) {
            this.lists = lists;
        }
    }
    
    protected class Seq implements Special {
        public Object[] list;
        public Seq(Object ... list) {
            this.list = list;
        }
    }
    
    protected class AnyOrder implements Special {
        public Object[][] lists;
        public AnyOrder(Object[] ... lists) {
            this.lists = lists;
        }
    }

    protected OneOf oneof(Object[] ... lists) { return new OneOf(lists); }
    protected AnyOrder anyorder(Object[] ... lists) { return new AnyOrder(lists); }
    protected Optional optional(Object[] ... lists) { return new Optional(lists); }
    protected Object[] seq(Object ... list) { return list; }
    

    protected boolean comparePair(Object[] list, int i, int j) {
        int col = ((Integer)list[i+1]).intValue();
        String act = noSource(collector.getDiagnostics().get(j));
        String exp = list[i].toString().replace("$SPECS", specsdir);
        if (!exp.equals(act) 
                && !exp.replace('\\','/').equals(act.replace('\\','/'))) {
            failureLocation = j;
            failureString = list[i].toString();
            return false;
        } else if (col != Math.abs(collector.getDiagnostics().get(j).getColumnNumber())) {
            failureLocation = j;
            failureString = null;
            failureCol = col;
            return false;
        } else {
            return true;
        }
    }
    
    protected int compareResults(Object[] list) {
        int j = 0; // counts the errors in list, accounting for optional or null entries
        int i = 0;
        while (i < list.length) {
            if (list[i] == null) { i+=2; continue; }
            if (!(list[i] instanceof Special)) {
                int col = ((Integer)list[i+1]).intValue();
                if (col < 0) {
                    // allowed to be optional
                    if (j >= collector.getDiagnostics().size()) {
                        // OK - just skip
                    } else if (list[i].equals(noSource(collector.getDiagnostics().get(j))) &&
                            -col == Math.abs(collector.getDiagnostics().get(j).getColumnNumber())) {
                        j++;
                    } else {
                        // Not equal and the expected error is optional so just skip
                    }
                } else {
                    if (noAssociatedDeclaration && list[i].toString().contains("Associated declaration")) {
                        // OK - skip
                    } else {
                        if (j < collector.getDiagnostics().size()) {
                            if (!comparePair(list,i,j)) {
                                assertEquals("Error " + j, list[i], noSource(collector.getDiagnostics().get(j)));
                                assertEquals("Error " + j, col, collector.getDiagnostics().get(j).getColumnNumber());
                            }
                        }
                        j++;
                    }
                }
                i += 2;
            } else if (list[i] instanceof AnyOrder) {
                j = compareAnyOrder(((AnyOrder)list[i]).lists, j);
                ++i;
            } else if (list[i] instanceof OneOf) {
                j = compareOneOf(((OneOf)list[i]).lists, j);
                ++i;
            } else if (list[i] instanceof Optional) {
                j = compareOptional(((Optional)list[i]).list, j);
                ++i;
            }
        }
        return j;
    }
    
    protected int failureLocation;
    protected String failureString;
    protected int failureCol;
    
    protected int compareOptional(Object[] list, int j) {
        int i = 0;
        int jj = j;
        while (i < list.length) {
            if (!comparePair(list,i,j)) {
                // Comparison failed - failureLocation set
                return jj;
            }
            i += 2;
            j++;
        }
        return j;
    }

    protected int compareOneOf(Object[][] lists, int j) {
        // None of lists[i] may be null or empty
        int i = 0;
        int jj = j;
        int latestFailure = -2;
        String latestString = null;
        int latestCol = 0;
        while (i < lists.length) {
            int jjj = compareOptional(lists[i],j);
            if (jjj > j) {
                // Matched
                return jjj;
            }
            i++;
            if (failureLocation > latestFailure) {
                latestFailure = failureLocation;
                latestString = failureString;
                latestCol = failureCol;
            }
        }
        failureLocation = latestFailure;
        // None matched;
        assertEquals("Error " + failureLocation, latestString, noSource(collector.getDiagnostics().get(failureLocation)));
        assertEquals("Error " + failureLocation, latestCol, collector.getDiagnostics().get(failureLocation).getColumnNumber());
        return jj;
    }

    protected int compareAnyOrder(Object[][] lists, int j) {
        // None of lists[i] may be null or empty
        boolean[] used = new boolean[lists.length];
        for (int i=0; i<used.length; ++i) used[i] = false;
        
        int latestFailure = -2;
        String latestString = null;
        int latestCol = 0;
        int toMatch = lists.length;
        more: while (toMatch > 0) {
            for (int i = 0; i < lists.length; ++i) {
                if (used[i]) continue;
                int jjj = compareOptional(lists[i],j);
                if (jjj > j) {
                    // Matched
                    j = jjj;
                    used[i] = true;
                    toMatch--;
                    continue more;
                } else {
                    if (failureLocation > latestFailure) {
                        latestFailure = failureLocation;
                        latestString = failureString;
                        latestCol = failureCol;
                    }
                }
            }
            // No options match
            break;
        }
        if (toMatch > 0) {
            failureLocation = latestFailure;
            // None matched;
            assertEquals("Error " + failureLocation, latestString, noSource(collector.getDiagnostics().get(failureLocation)));
            assertEquals("Error " + failureLocation, latestCol, collector.getDiagnostics().get(failureLocation).getColumnNumber());
        }
        return j;
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
    protected void addMockJavaFile(String filename, JavaFileObject file) {
        mockFiles.add(file);
    }


}
