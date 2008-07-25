package org.jmlspecs.openjml.provers;

import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.Writer;
import java.nio.CharBuffer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.jmlspecs.openjml.proverinterface.Counterexample;
import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.ProverException;
import org.jmlspecs.openjml.proverinterface.ProverResult;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;


public class YicesProver implements IProver {
    /** A debugging flag - 0 = show nothing; 1 = show errors; 2 = show something; 3 = show everything */
    static protected int showCommunication = 2;
    
    /** The process that is the actual prover */
    protected Process process = null;
    
    /** The stream connection to send information to the prover process. */
    //@ invariant process != null ==> toProver != null;
    protected Writer toProver;
    
    /** The stream connection to read information from the prover process. */
    //@ invariant process != null ==> fromProver != null;
    protected Reader fromProver;
    
    /** The error stream connection to read information from the prover process. */
    //@ invariant process != null ==> errors != null;
    protected Reader errors;
    
    /** A buffer to hold input */
    /*@ non_null */
    protected CharBuffer buf = CharBuffer.allocate(10000);

    /** A handy StringBuilder to build strings internally */
    /*@ non_null */
    protected StringBuilder builder = new StringBuilder();
    
    /** The accumulated list of input sent to the prover process */
    /*@ non_null */
    protected List<String> sent = new LinkedList<String>();
    
    /** The String by which to invoke the prover */
    /*@ nullable */
    protected String app = System.getProperty("openjml.prover.yices");

    /** A counter of assumptions sent to the prover */
    int assumeCounter = 0;
    
    // FIXME - will need to separate start from construction so there is an opportunity to set parameters (e.g. timeout)
    /** Creates and starts the prover process, sending any startup information */
    public YicesProver(Context context) throws ProverException {
        start();
    }
    
    /**The background predicate that is sent prior to anything else.  Do not include any newline characters. */
    /*@ non_null */
    private final static String backgroundPredicate =
          "(define-type REF) (define null::REF) "
        + "(define length$0::(-> REF int)) (assert (forall (a::REF) (>= (length$0 a) 0)))"
        + "\n";
    
    /** Does the startup work */
    public void start() throws ProverException {
        if (app == null) {
            throw new ProverException("No path to the executable found; specify it using -Dopenjml.prover.yices");
        } else if (!new java.io.File(app).exists()) {
            throw new ProverException("The sepcified executable does not appear to exist: " + app);
        }
        try {
            // The interactive mode is used so that we get a prompt back, thereby
            // knowing when we have received the prover's response
            process = Runtime.getRuntime().exec(new String[]{app,"-i","-e","-v","0"});
        } catch (IOException e) {
            process = null;
            throw new ProverException("Failed to launch prover process: " + app + " " + e);
        }
        toProver = new OutputStreamWriter(process.getOutputStream());
        fromProver = new InputStreamReader(process.getInputStream()); // FIXME should we use buffered readers/writers
        errors = new InputStreamReader(process.getErrorStream());
        eatPrompt();
        // Send the background predicate
        send(backgroundPredicate);
        //send("\n");
        eatPrompt();
        defined.add("length$0");
    }
    
    public String eatPrompt() throws ProverException {
        // We read characters until we get to the sequence "> ", which is the
        // end of the Yices prover's prompt (which is "yices> ").  Be careful 
        // that sequence is not elsewhere in the input as well.
        // FIXME - need a better way to read both inputs
        // FIXME - this probably can be made a lot more efficient
        try {
            buf.position(0);
            outer: while (true) {
                int n = fromProver.read();
                if (n < 0) {
                    throw new ProverException("Prover died");
                }
                char c = (char)n;
                buf.append(c);
                if (c != '>') continue;
                while (true) {
                    n = fromProver.read();
                    if (n < 0) {
                        throw new ProverException("Prover died");
                    }
                    c = (char)n;
                    buf.append(c);
                    if (c == ' ') break outer;
                    if (c != '>') break;
                }
            }
            buf.limit(buf.position());
            buf.rewind();
            String s = buf.toString();
            buf.clear();
            if (errors.ready()) {
                while (errors.ready()) {
                    int n = errors.read(buf);
                    if (n <= 0) break;
                }
                if (buf.position() > 0) {
                    buf.limit(buf.position());
                    buf.rewind();
                    if (!buf.toString().startsWith("\nWARNING"))
                        throw new ProverException("Prover error message: " + buf);
                }
                buf.clear();
            }
            if (showCommunication >= 3) System.out.println("HEARD " + s);
            return s;
        } catch (IOException e) {
            throw new ProverException("IO Error on reading from prover: " + e);
        }
    }
    
    public int assume(JCExpression tree) throws ProverException {
        try {
            String t = YicesJCExpr.toYices(tree,this);
            builder.setLength(0);
            builder.append("(assert+ ");
            builder.append(t);
            builder.append(")\n");
            send(builder.toString());
            eatPrompt();
        } catch (ProverException e) {
            e.mostRecentInput = builder.toString();
            throw e;
        }
        // We use this assume counter, but the more robust method is to
        // look at the output returned from eatPrompt (FIXME)
        return ++assumeCounter;
    }
    
    public int assume(JCExpression tree, int weight) throws ProverException {
        try {
            String t = YicesJCExpr.toYices(tree,this);
            builder.setLength(0);
            builder.append("(assert+ ");
            builder.append(t);
            builder.append(" ");
            builder.append(weight);
            builder.append(")\n");
            send(builder.toString());
            eatPrompt();
        } catch (ProverException e) {
            e.mostRecentInput = builder.toString();
            throw e;
        }
        return ++assumeCounter;
    }
    
    /** Does the actual work of sending information to the prover process.  You 
     * need to call eatPrompt for each newline you send.  This method does not 
     * add any newlines to the supplied String. 
     * @param s the String to send
     * @throws ProverException if something goes wrong
     */
    protected void send(String s) throws ProverException {
        sent.add(s);
        if (showCommunication >= 2) System.out.print("SENDING " + s);
        try {
            toProver.append(s);
            toProver.flush();
        } catch (IOException e) {
            throw new ProverException("Failed to write to prover: " + e);
        }
    }
    
    /** Converts an AST type to a type that Yices knows
     * 
     * @param t the AST type
     * @return the Yices equivalent
     */
    public String convertType(Type t) {
        String s;
        if (!t.isPrimitive()) {
            if (t instanceof ArrayType) {
                t = ((ArrayType)t).getComponentType();
//                s = convertType(t);
//                s = "(-> int " + s + ")";
                s = "array$" + convertType(t);
            } else {
                s = "REF";
            }
        } else if (t.tag == TypeTags.BOOLEAN) {
            s = "bool";
        } else {
            s = "int";
        }
        return s;
    }
    
    /** The set of variables already defined in Yices (since Yices objects if
     * a variable is defined more than once).
     */
    private Set<String> defined = new HashSet<String>();
    
    /** A stack holding lists of defined variables between various push() calls,
     * since a pop removes the definitions as well.
     */
    private Deque<List<String>> stack = new LinkedList<List<String>>();
    
    /** The list of definitions since the last push (duplicates some of those
     * in 'defined'.
     */
    private List<String> top = new LinkedList<String>();
    
    /** Checks if the argument is already defined, recording it as defined
     *  if it is not.
     * @param id the variable to define
     * @return true if it was already recorded as defined, false if it was not
     */
    public boolean checkAndDefine(String id) {
        if (!defined.add(id)) return true;
        top.add(id);
        return false;
    }

    public void define(String id, Type t) throws ProverException {
        if (checkAndDefine(id)) return; // DO nothing if already defined
        builder.setLength(0);
        String s = convertType(t);
        if (s.indexOf('$') != -1) {
            // A user-defined type
            if (!checkAndDefine(s)) {
                builder.append("(define-type ");
                builder.append(s);
                builder.append(") ");
            }
        }
        builder.append("(define ");
        builder.append(id);
        builder.append("::");
        builder.append(s);
        builder.append(")\n");
        try {
            send(builder.toString());
            eatPrompt();
        } catch (ProverException e) {
            e.mostRecentInput = builder.toString();
            throw e;
        }
    }


//    public boolean isSat() throws ProverException {
//        send("(check)\n");
//        String output = eatPrompt();
//        //System.out.println("HEARD " + output);
//        boolean sat = output.startsWith("sat") || output.startsWith("unknown");
//        boolean unsat = output.startsWith("unsat");
//        if (sat == unsat) throw new ProverException("Improper response to (check) query: \"" + output + "\"");
//        satResult = output.substring(0,output.length()-8);
//        return sat;
//    }

    /** A pattern to interpret Yices counterexample information */
    static private Pattern pattern = Pattern.compile("\\(=[ ]+(.+)[ ]+([^)]+)\\)");

    public IProverResult check() throws ProverException {
        send("(check)\n");
        String output = eatPrompt();
        boolean sat = output.startsWith("sat");
        boolean unknown = output.startsWith("unknown");
        boolean unsat = output.startsWith("unsat");
        if (sat == unsat && !unknown) throw new ProverException("Improper response to (check) query: \"" + output + "\"");
        ProverResult r = new ProverResult();
        if (sat || unknown) {
            r.result(ProverResult.SAT);
            Counterexample ce = new Counterexample();
            Matcher m = pattern.matcher(output);
            while (m.find()) {
                ce.put(m.group(1),m.group(2));
            }
            r.add(ce);
        } else if (unsat) {
            r.result(ProverResult.UNSAT);
            output = output.substring(0,output.length()-8);
            if (showCommunication >= 2) System.out.println("UNSAT INFO:" + output);

            int index = output.indexOf("unsat core ids:");
            if (index >= 0) {
                CoreIds cids = new CoreIds();
                String[] sids = output.substring(index+"unsat core ids: ".length()).split("[ \n\r]");
                for (int i=0; i<sids.length; i++) cids.add(Integer.parseInt(sids[i]));
                r.add(cids);
            }                 
        } else {
            r.result(ProverResult.UNKNOWN);
        }
        return r;
    }
    
    public void maxsat() throws ProverException {
        send("(max-sat)\n");
        String output = eatPrompt();
        if (showCommunication >= 2) System.out.println("MAXSAT INFO:" + output);
    }
    
    public void pop() throws ProverException {
        send("(pop)\n");
        eatPrompt();
        defined.removeAll(top);
        top = stack.removeFirst();
    }

    public void push() throws ProverException {
        send("(push)\n");
        eatPrompt();
        stack.addFirst(top);
        top = new LinkedList<String>();
    }

    // FIXME - does not reproduce current environment
    public void restartProver() throws ProverException {
        kill();
        start();
    }

    public void retract() throws ProverException {
        throw new ProverException("retract() not suppported by YicesProver"); // FIXME
    }
    
    public void retract(int n) throws ProverException {
        send("(retract " + n + ")\n");
        eatPrompt();
    }
    
    public void kill() throws ProverException {
        if (process != null) process.destroy();
        process = null;
    }
    
    static public class CoreIds implements IProverResult.ICoreIds {
        Collection<Integer> coreIds = new ArrayList<Integer>();
        
        @Override
        public Collection<Integer> coreIds() {
            return coreIds;
        }
        
        public void add(int i) {
            coreIds.add(i);
        }
    }
}
