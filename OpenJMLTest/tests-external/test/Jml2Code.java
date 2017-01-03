   package test;

    import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

public class Jml2Code {

        static private boolean dotests = true;  // Change this to enable/disable tests
        
        
        ByteArrayOutputStream berr;
        ByteArrayOutputStream bout;
        PrintStream savederr;
        PrintStream savedout;
        static String eol = System.getProperty("line.separator");
        static String z = java.io.File.pathSeparator;
        boolean print = false;
        boolean capture = false;
        
        protected void setUp() throws Exception {
            capture = false;
            print = true;
            super.setUp();
            savederr = System.err;
            savedout = System.out;
            if (capture) System.setErr(new PrintStream(berr=new ByteArrayOutputStream(10000)));
            if (capture) System.setOut(new PrintStream(bout=new ByteArrayOutputStream(10000)));
        }
        
        protected void tearDown() {
            berr = null;
            bout = null;
            System.setErr(savederr);
            System.setOut(savedout);
        }
        
        /** This is a helper method that runs the compiler on the given set of
         * command-line arguments, checking the result
         * @param args the command-line arguments
         * @param exitcode the expected exit code (0=OK, 1=completed with error messages
         *      2=command-line problems, 3=system errors, 4=abort)
         * @param all whether the expected output is all of (0) or just the prefix
         *      of (1) or a part of (2) the actual output
         * @param output the expected output as one string
         */
        public void helper(String[] args, int exitcode, int all, String ... output) {
            int e = org.jmlspecs.openjml.Main.execute(args,false); // Put to standard out
            System.setErr(savederr);
            System.setOut(savedout);
            if (capture) {
                try {
                    if (print) System.out.println("TEST: " + getName() + " exit=" + e + eol + berr.toString());
                    if (all==0) assertEquals("The error message is wrong",output[0],berr.toString());
                    else if (all == 1 && !berr.toString().startsWith(output[0])) {
                        fail("Output does not begin with: " + output[0] + eol + "Instead is: " + berr.toString());
                    } else if (all == 2 && berr.toString().indexOf(output[0]) == -1) {
                        fail("Output does not end with: " + output[0] + eol + "Instead is: " + berr.toString());
                    }
                    if (output.length > 1) {
                        if (print) System.out.println("TEST: " + getName() + " STANDARD OUT: " + eol + bout.toString());
                        if (all == 0) {
                            assertEquals("The standard out is wrong",output[1],bout.toString());
                        } else if (all == 2 && bout.toString().indexOf(output[1]) == -1) {
                            fail("Output does not end with: " + output[1] + eol + "Instead is: " + bout.toString());
                        }
                    }
                    assertEquals("The exit code is wrong",exitcode,e);
                } catch (AssertionFailedError ex) {
                    if (!print) System.out.println("TEST: " + getName() + " exit=" + e + eol + berr.toString());
                    throw ex;
                }
            } else {
                assertEquals("The exit code is wrong",exitcode,e);
            }
        }

        public void testESCTest() throws Exception {
            String sp = "C:/home/projects/JML4/ESCTools/Utils;C:/home/projects/JML4/ESCTools/Escjava/java;C:/home/projects/JML4/ESCTools/Javafe/java;C:/home/projects/JML4/ESCTools/Escjava/mochalib/java";
            String cp = "C:/home/projects/JML4/ESCTools/Utils;C:/home/projects/JML4/ESCTools/Utils/junit.jar;C:/home/projects/JML4/ESCTools/Utils/ant.jar;C:/home/projects/JML4/ESCTools/Utils/BCEL/bcel-5.2/bcel-5.2.jar;C:/home/projects/JML4/ESCTools/Escjava/xmlrpc-1.2-b1-modified.jar;C:/home/projects/JML4/ESCTools/Javafe/java;C:/home/projects/JML4/ESCTools/Escjava/java;C:/home/projects/JML4/ESCTools/Escjava/mochalib/java";
            String[] args = {
                   "-noPurityCheck",
                   "-specspath","$SY"+";"+sp,
                   //"-specspath","C:/home/projects/Specs/trunk/java6;C:/home/projects/Specs/trunk/java5;C:/home/projects/Specs/trunk/java4;C:/home/projects/OpenJML/trunk/OpenJML/runtime",
                   "-classpath", cp,
                   //"-jmlverbose",
                   "-nullableByDefault",
                   "-esc"};
            String[] files = {
                    "C:/home/projects/JML4/ESCTools/Escjava/java/escjava/ant/ESCJavaTask.java",
                    //"C:/home/projects/JML4/ESCTools/Escjava/java/escjava/sortedProver/Lifter.java",
                    //"C:/home/projects/JML4/ESCTools/Javafe/java/javafe/filespace/TreeWalker.java",
                   };
            List<String> f = expand(files);
            for (int i=0; i< args.length; i++) f.add(i,args[i]);
            args = f.toArray(new String[f.size()]);
            helper(args,0,1,"");
        }
        
        public void testESCTOOLS() throws Exception {
            String sp = "C:/home/projects/JML4/ESCTools/Utils;C:/home/projects/JML4/ESCTools/Escjava/java;C:/home/projects/JML4/ESCTools/Javafe/java;C:/home/projects/JML4/ESCTools/Escjava/mochalib/java";
            String cp = "C:/home/projects/JML4/ESCTools/Utils;C:/home/projects/JML4/ESCTools/Utils/junit.jar;C:/home/projects/JML4/ESCTools/Utils/ant.jar;C:/home/projects/JML4/ESCTools/Utils/BCEL/bcel-5.2/bcel-5.2.jar;C:/home/projects/JML4/ESCTools/Escjava/xmlrpc-1.2-b1-modified.jar;C:/home/projects/JML4/ESCTools/Javafe/java;C:/home/projects/JML4/ESCTools/Escjava/java;C:/home/projects/JML4/ESCTools/Escjava/mochalib/java";
            String[] args = {
                   "-noPurityCheck",
                   "-specspath","$SY"+";"+sp,
                   //"-specspath","C:/home/projects/Specs/trunk/java6;C:/home/projects/Specs/trunk/java5;C:/home/projects/Specs/trunk/java4;C:/home/projects/OpenJML/trunk/OpenJML/runtime",
                   "-classpath", cp,
                   "-nullableByDefault",
                   //"-jmlverbose",
                   "-esc"};
            String[] files = {
                    "C:/home/projects/JML4/ESCTools/Escjava/java/escjava/*.java",
                    "C:/home/projects/JML4/ESCTools/Escjava/java/escjava/*/*.java",
                   "C:/home/projects/JML4/ESCTools/Utils/junitutils/*.java",
                   "C:/home/projects/JML4/ESCTools/Javafe/java/javafe/*.java",
                   "C:/home/projects/JML4/ESCTools/Javafe/java/javafe/*/*.java",
                   };
            List<String> f = expand(files);
            for (int i=0; i< args.length; i++) f.add(i,args[i]);
            args = f.toArray(new String[f.size()]);
            helper(args,0,1,"");
        }
        
        public void testESCTOOLSindividually() throws Exception {
            String sp = "C:/home/projects/JML4/ESCTools/Utils;C:/home/projects/JML4/ESCTools/Escjava/java;C:/home/projects/JML4/ESCTools/Javafe/java;C:/home/projects/JML4/ESCTools/Escjava/mochalib/java";
            String[] args = {
                    "-Xmaxerrs","10000",
                    "-Xmaxwarns","10000",
                   "-noPurityCheck",
                   "-nullableByDefault",
                   "-specspath","$SY"+";"+sp,
                   //"-specspath","C:/home/projects/Specs/trunk/java6;C:/home/projects/Specs/trunk/java5;C:/home/projects/Specs/trunk/java4;C:/home/projects/OpenJML/trunk/OpenJML/runtime",
                   "-classpath", "C:/home/projects/JML4/ESCTools/Utils;C:/home/projects/JML4/ESCTools/Utils/junit.jar;C:/home/projects/JML4/ESCTools/Utils/ant.jar;C:/home/projects/JML4/ESCTools/Utils/BCEL/bcel-5.2/bcel-5.2.jar;C:/home/projects/JML4/ESCTools/Escjava/xmlrpc-1.2-b1-modified.jar;C:/home/projects/JML4/ESCTools/Javafe/java;C:/home/projects/JML4/ESCTools/Escjava/java;C:/home/projects/JML4/ESCTools/Escjava/mochalib/java",
                   //"-jmlverbose",//"-jmldebug",
                   "-esc",
                   ""};
            String[] files = {
                    "C:/home/projects/JML4/ESCTools/Escjava/java/escjava/*.java",
                    "C:/home/projects/JML4/ESCTools/Escjava/java/escjava/*/*.java",
                   "C:/home/projects/JML4/ESCTools/Utils/junitutils/*.java",
                   "C:/home/projects/JML4/ESCTools/Javafe/java/javafe/*.java",
                   "C:/home/projects/JML4/ESCTools/Javafe/java/javafe/*/*.java",
                   };
            List<String> f = expand(files);
            
            loop: for (String fn : f) {
                for (String o: omit) {
                    if (fn.endsWith(o)) continue loop;
                }
                System.out.println("DOING " + fn);
                args[args.length-1] = fn;
                helper(args,0,1,"");
            }
        }
        
        String[] omit = {
                "ModifierPragmaVec.java"
        };
        
        public List<String> expand(String[] args) {
            List<String> list = new LinkedList<String>();
            for (String arg: args) expand(arg,list);
            return list;
        }
        
        public void expand(String arg, List<String> list) {
            if (!arg.endsWith("*.java")) { list.add(arg); return; }
            String darg = arg.substring(0,arg.length()-"*.java".length());
            List<String> dirs = expandDir(darg);
            for (String sdir: dirs) {
                File dir = new File(sdir);
                if (!dir.exists()) System.out.println("NOT EXIST " + dir);
                else for (String f: dir.list()) {
                    if (f.endsWith(".java")) list.add(sdir+f);
                }
            }
        }
        
        public List<String> expandDir(String darg) {
            List<String> list = new LinkedList<String>();
            int k = darg.lastIndexOf('*');
            if (k == -1) { list.add(darg); return list; }
            String ddarg = darg.substring(0,k);
            File dir = new File(ddarg);
            if (!dir.exists()) System.out.println("NOT EXIST " + dir);
            else for (File f: dir.listFiles()) {
                if (f.isDirectory()) list.add(f+"/");
            }
            return list;
        }
        

    }
