package org.jmlspecs.openjml.provers;

import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.Writer;
import java.nio.CharBuffer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.proverinterface.Counterexample;
import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.ProverException;
import org.jmlspecs.openjml.proverinterface.ProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;


public class YicesProver implements IProver {
    public final static String NULL = "NULL";
    public final static String REF = "REF";
    public final static String ARRAY = "ARRAY";
    public final static String ARRAYorNULL = "ARRAYorNULL";
    public static final String TYPE = "TYPE$";
    public static final String TYPEOF = "typeof$";
    public static final String SUBTYPE = "subtype$";
    public static final String CAST = "cast$";
    
    /** A debugging flag - 0 = show nothing; 1 = show errors; 2 = show something; 3 = show everything */
    @edu.umd.cs.findbugs.annotations.SuppressWarnings("MS_SHOULD_BE_FINAL")
    static public int showCommunication = 1;
    
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
    protected CharBuffer buf = CharBuffer.allocate(100000);

    /** A handy StringBuilder to build strings internally */
    /*@ non_null */
    protected StringBuilder builder = new StringBuilder();
    
    /** The accumulated list of input sent to the prover process */
    /*@ non_null */
    protected List<String> sent = new LinkedList<String>();
    
    /** The String by which to invoke the prover */
    /*@ nullable */
    protected String app = System.getProperty("openjml.prover.yices");

    /** The one instance of the associated translator */
    /*@ non_null */
    protected YicesJCExpr translator;
    
    // FIXME - will need to separate start from construction so there is an opportunity to set parameters (e.g. timeout)
    /** Creates and starts the prover process, sending any startup information */
    public YicesProver(Context context) throws ProverException {
        assumeCounter = 0;
        int k = 1;
        while (k>0) {
            assumeCounter++;
            k = backgroundPredicate.indexOf("assert+",k)+1;
        }
        translator = new YicesJCExpr(this);
//        if (org.jmlspecs.openjml.esc.JmlEsc.escdebug && showCommunication <= 1) showCommunication = 2;
        start();
    }
    
    private final static String[][] predefined = { 
        { REF, null},
        { NULL, REF },
        { "isType", "(-> REF bool)"},
        { TYPE, "(subtype (r::REF) (isType r))" },
        { "isArray", "(-> REF bool)"},
        { ARRAY, "(subtype (r::REF) (isArray r))"},
        { ARRAYorNULL, "(subtype (r::REF) (or (= r NULL) (isArray r)))"},
        { "T$java.lang.Object$$A", TYPE},
        { TYPEOF, "(-> REF "+TYPE+")"},
        { SUBTYPE, "(-> "+TYPE+" "+TYPE+" bool)"},
        { CAST, "(-> REF "+TYPE+" REF)"},
        { "length", "(-> REF int)"},
        { "length$0", "(-> REF int)"},
        { "idiv", "(-> int int int)"},
        { "rdiv", "(-> real real real)"},
        { "imod", "(-> int int int)"},
        { "rmod", "(-> real real real)"},
        { "imul", "(-> int int int)"},
        { "rmul", "(-> real real real)"},
        { "distinct$", "(-> "+TYPE+" int)"},
        { "loc$", "(-> "+REF+" int)"},
        };
    
    // This lists names builtin to Yices
    private final static String[][] otherpredefined = {
      { "bool", TYPE},
      { "int", TYPE},
      { "real", TYPE},
      { "div", "(-> int int int)"},
      { "mod", "(-> real real real)"},
      { "and", "(-> bool bool bool)"},
      { "or", "(-> bool bool bool)"},
      { "=>", "(-> bool bool bool)"},
      { "not", "(-> bool bool)"},
      { "+", "(-> int int int)"},   // Real?
      { "-", "(-> int int int)"},  // Real
      { "*", "(-> int int int)"},  // Real
      { "/", "(-> real real real)"},
      // Also bit vector functions
    };
    
    public static final String BASSERT = "assert+";
    
    /**The background predicate that is sent prior to anything else.  Do not include any newline characters. */
    /*@ non_null */
    private final static String backgroundPredicate =
          "("+BASSERT+" (not (isType NULL)))"
        + "("+BASSERT+" (not (isArray NULL)))"
        + "("+BASSERT+" (forall (a::REF) (>= (length a) 0)))"
        + "("+BASSERT+" (= length length$0))"
        + "("+BASSERT+" (forall (r::REF t::"+TYPE+") (=> (and (/= r NULL) ("+SUBTYPE+" ("+TYPEOF+" r) t))  (= ("+CAST+" r t) r) ) ))"
        + "("+BASSERT+" (forall (t::"+TYPE+") (= ("+CAST+" NULL t) NULL) ))"
        + "("+BASSERT+" (forall (t::" + TYPE + ") ("+SUBTYPE + " t t)))"
        + "("+BASSERT+" (forall (t1::" + TYPE + " t2::" + TYPE + ") (= (and ("+SUBTYPE + " t1 t2) ("+SUBTYPE + " t2 t1)) (=  t1 t2)) ))"
        + "("+BASSERT+" (forall (t1::" + TYPE + " t2::" + TYPE + " t3::" + TYPE + ") (=> (and ("+SUBTYPE + " t1 t2)("+SUBTYPE + " t2 t3)) ("+SUBTYPE + " t1 t3)) ))"
        + "("+BASSERT+" (forall (i::int j::int) (= (imul i j) (imul j i)) ))"
        + "("+BASSERT+" (forall (i::int) (and (= (imul i 0) 0) (= (imul 0 i) 0) (= (imul 1 i) i) (= (imul i 1) i) (= (imul -1 i) (- 0 i)) (= (imul i -1) (- 0 i)) )))"
//        + "("+BASSERT+" (forall (i::int j::int) (= (imul i (+ j 1)) (+ (imul i j) i) ) ))"
//        + "("+BASSERT+" (forall (i::int j::int) (= (imul i (- j 1)) (- (imul i j) i) ) ))"
        + "("+BASSERT+" (forall (i::int j::int) (=> (/= j 0) (= (imod (imul i j) j) 0)) ))"
        + "("+BASSERT+" (forall (i::int) (and (= (imod i 1) 0) (= (imod i -1) 0) )))"
        + "("+BASSERT+" (= (distinct$ T$java.lang.Object$$A) 99))"
        + "\n";
    
    /** A counter of assumptions sent to the prover */
    int assumeCounter;
    
    /** Does the startup work */
    public void start() throws ProverException {
        if (app == null) {
            throw new ProverException("No path to the executable found; specify it using -Dopenjml.prover.yices");
        } else if (!new java.io.File(app).exists()) {
            throw new ProverException("The specified executable does not appear to exist: " + app);
        }
        try {
            // The interactive mode is used so that we get a prompt back, thereby
            // knowing when we have received the prover's response
            process = Runtime.getRuntime().exec(new String[]{app,"-i","-tc","--timeout=300","-e","-v","2"});
        } catch (IOException e) {
            process = null;
            throw new ProverException("Failed to launch prover process: " + app + " " + e);
        }
        toProver = new OutputStreamWriter(process.getOutputStream());
        fromProver = new InputStreamReader(process.getInputStream()); // FIXME should we use buffered readers/writers
        errors = new InputStreamReader(process.getErrorStream());
        eatPrompt();
        background();
    }
    
    private void background() throws ProverException {
        for (String[] pairs: otherpredefined) {
            defined.put(pairs[0],pairs[1]);
        }
        // Send predefined values
        StringBuilder s = new StringBuilder();;
        for (String[] pairs: predefined) {
            if (pairs[1] == null) {
                s.append("(define-type ");
                s.append(pairs[0]);
                s.append(")");
            } else if (pairs[1].startsWith("(subtype")) {
                s.append("(define-type ");
                s.append(pairs[0]);
                s.append(" ");
                s.append(pairs[1]);
                s.append(")");
            } else {
                s.append("(define ");
                s.append(pairs[0]);
                s.append("::");
                s.append(pairs[1]);
                s.append(")");
            }
            defined.put(pairs[0],pairs[1]);
        }
        s.append(backgroundPredicate);
        send(s.toString());
        eatPrompt();
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
                    if (n < 0) throw new ProverException("Prover died");
                    if (n == 0) break;
                }
                if (buf.position() > 0) {
                    buf.limit(buf.position());
                    buf.rewind();
                    String errorString = buf.toString();
                    if (!errorString.startsWith("\nWARNING") &&
                            !errorString.startsWith("Yices (version") &&
                            !errorString.startsWith("searching")) {
                        if (showCommunication >= 1) System.out.println("HEARD ERROR: " + errorString);
                        throw new ProverException("Prover error message: " + errorString);
                    } else {
                        if (showCommunication >= 3) System.out.println("HEARD ERROR: " + errorString);
                    }
                }
                buf.clear();
            }
            if (showCommunication >= 3) System.out.println("HEARD: " + s);
            return s;
        } catch (IOException e) {
            throw new ProverException("IO Error on reading from prover: " + e);
        }
    }
    
    public int assume(JCExpression tree) throws ProverException {
        try {
            String t = translator.toYices(tree);
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
        return assumeCounter++;
    }
    
    public int assume(JCExpression tree, int weight) throws ProverException {
        try {
            String t = translator.toYices(tree);
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
        return assumeCounter++;
    }
    
    public int rawassume(String t) throws ProverException {
        try {
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
        return assumeCounter++;
    }
    
    /** Does the actual work of sending information to the prover process.  You 
     * need to call eatPrompt for each newline you send.  This method does not 
     * add any newlines to the supplied String. 
     * @param s the String to send
     * @throws ProverException if something goes wrong
     */
    protected void send(String s) throws ProverException {
        sent.add(s);
        if (showCommunication >= 2) {
            String ss = pretty(s);
//            if (ss.startsWith("(define i1::int)")) {
//                ss = ss.trim();
//            }
            //System.out.print("SENDING " + ss);
            System.out.print("SENDING ["+assumeCounter+"]" + ss);
        }
        try {
            toProver.append(s);
            toProver.flush();
        } catch (IOException e) {
            throw new ProverException("Failed to write to prover: " + e);
        }
    }
    
    public void reassertCounterexample(ICounterexample ce) {
        //System.out.println("REASSERTING");
        for (Map.Entry<String,String> entry : ce.sortedEntries()) {
            String v = entry.getKey();
            String s = "(= " + v + " " + entry.getValue() +")";
            if (v.charAt(0) == '(') continue;
            //System.out.println("REASSERTING " + s);
            try {
                rawassume(s);
            } catch (ProverException e) {
                System.out.println("FAILED TO ASSERT " + s);
                System.out.println(e);
            }
        }
//        try {
//            IProverResult r = check(false);
//            System.out.println("STATUS " + r.result());
//        } catch (ProverException e) {
//            System.out.println("FAILED TO REASSERT " );
//            System.out.println(e);
//
//        }
    }


    
    protected String pretty(String s) {
        if (s.length() <= 50) return s;
        StringBuilder sb = new StringBuilder();
        //System.out.println("CONVERTING " + s);
        char[] cc = s.toCharArray();
        int nparens = 0;
        int nind = 2;
        for (int i=0; i<cc.length; ++i) {
            char c = cc[i];
            if (c == ')') { nparens--; sb.append(c); continue; }
            if (c == '(') { 
                if (cc[i+1]=='=' && cc[i+2]=='>' && nind == nparens) {
                    nind++;
                    nparens++;
                    sb.append("\n                    ");
                    int k = nparens;
                    while (--k >= 0) sb.append(' ');
                    sb.append("(=>");
                    i += 2;
                    continue;
                } else if (cc[i+1] == 'a' && cc[i+2] == 'n' && nind == nparens) {
                    nind++;
                    nparens++;
                    sb.append("\n                    ");
                    int k = nparens;
                    while (--k >= 0) sb.append(' ');
                    sb.append("(an");
                    i += 2;
                    continue;
                }
                if (i != 0 && nparens == 0) sb.append("\n               ");
                nparens++; 
                sb.append(c);
                continue; 
            }
            sb.append(c);
        }
        return sb.toString();
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
                s = "refA$" + convertType(t);
            } else {
                s = REF;
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
    private Map<String,String> defined = new HashMap<String,String>();
    
    /** A stack holding lists of defined variables between various push() calls,
     * since a pop removes the definitions as well.
     */
    private List<List<String>> stack = new LinkedList<List<String>>();
    
    /** The list of definitions since the last push (duplicates some of those
     * in 'defined'.
     */
    private List<String> top = new LinkedList<String>();
    
    /** Checks if the argument is already defined, recording it as defined
     *  if it is not.
     * @param id the variable to define
     * @return true if it was already recorded as defined, false if it was not
     */
    public boolean checkAndDefine(String id, String typeString) {
        if (isDefined(id)) return true;
        defined.put(id,typeString);
        top.add(id);
        return false;
    }
    
    public void declare(String id, String typeString) {
        defined.put(id,typeString);
        top.add(id);
    }
    
    public boolean removeDeclaration(String id) {
        defined.remove(id);
        top.remove(id);
        return false;
    }
    
    public boolean isDefined(String id) {
        return defined.containsKey(id); 
    }
    
    public String getTypeString(String id) {
        return defined.get(id);
    }
    
    public String defineType(Type t) {
        String s = convertType(t);
        if (isDefined(s)) return s; // DO nothing if already defined
        builder.setLength(0);
        if (t.tag == TypeTags.ARRAY) {
            Type ct = ((ArrayType)t).elemtype;
            if (ct instanceof ArrayType) defineType(ct);
            String ss = "(subtype (a::ARRAY) (subtype$ (typeof$ a) T$java.lang.Object$$A))";
            builder.append("(define-type " + s + " " + ss + ")\n");
            declare(s,ss);
        } else {
            builder.append("(define-type ");
            builder.append(s);
            builder.append(")\n");
            declare(s,null);
        }
        try {
            send(builder.toString());
            eatPrompt();
        } catch (ProverException e) {
            e.mostRecentInput = builder.toString();
            throw new RuntimeException(e);
        }
        return s;
    }

    public String defineType(String s, boolean array) throws ProverException {
        if (isDefined(s)) return s; // DO nothing if already defined
        builder.setLength(0);
        if (array) {
            String cs = s.substring("refA$".length());
            defineType(cs,cs.startsWith("refA"));
            builder.append("(define-type " + s + " (subtype (a::ARRAY) (subtype$ (typeof$ a) T$java.lang.Object$$A)))\n");
        } else {
            builder.append("(define-type ");
            builder.append(s);
            builder.append(")\n");
        }
        try {
            send(builder.toString());
            eatPrompt();
        } catch (ProverException e) {
            e.mostRecentInput = builder.toString();
            throw e;
        }
        return s;
    }
    
    public void define(String id, Type t) throws ProverException {
        if (isDefined(id)) return; // DO nothing if already defined
        builder.setLength(0);
        String s = defineType(t);
        declare(id,s);
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

    /** Defines an id as a given (raw) type; returns true and does nothing if the
     * id was already defined.
     * @param id the identifier to be defined
     * @param typeString the string denoting the already converted type
     * @return true if already defined, false if now newly defined
     * @throws ProverException
     */
    public boolean rawdefine(String id, String typeString) throws ProverException {
        if (checkAndDefine(id,typeString)) return true; // DO nothing if already defined
        builder.setLength(0);
        if (!typeString.startsWith("(")) defineType(typeString,typeString.startsWith("refA"));
        builder.append("(define ");
        builder.append(id);
        builder.append("::");
        builder.append(typeString);
        builder.append(")\n");
        try {
            send(builder.toString());
            eatPrompt();
        } catch (ProverException e) {
            e.mostRecentInput = builder.toString();
            throw e;
        }
        return false;
    }

    public boolean rawdefinetype(String id, String typeString, String recordedtype) throws ProverException {
        if (isDefined(id)) return true; // DO nothing if already defined
        declare(id,recordedtype);
        builder.setLength(0);
        builder.append("(define-type ");
        builder.append(id);
        builder.append(" ");
        builder.append(typeString);
        builder.append(")\n");
        try {
            send(builder.toString());
            eatPrompt();
        } catch (ProverException e) {
            e.mostRecentInput = builder.toString();
            throw e;
        }
        return false;
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

    //Utils.Timer timer = new Utils.Timer();

    public IProverResult check() throws ProverException {
        return check(true);
    }
    public IProverResult check(boolean details) throws ProverException {
        //timer.reset();
        send("(check)\n");
        String output = eatPrompt();
        //System.out.println("CHECK TIME " + timer.elapsed()/1000.);
        boolean sat = output.startsWith("sat");
        boolean unknown = output.startsWith("unknown");
        boolean unsat = output.startsWith("unsat");
        if (sat == unsat && !unknown) throw new ProverException("Improper response to (check) query: \"" + output + "\"");
        ProverResult r = new ProverResult();
        if (sat || unknown) {
            if (unknown) r.result(ProverResult.POSSIBLYSAT);
            else r.result(ProverResult.SAT);
            if (details) {
                Counterexample ce = createCounterexample(output);
                r.add(ce);
            }
        } else if (unsat) {
            r.result(ProverResult.UNSAT);
            output = output.substring(0,output.length()-8);
            if (showCommunication >= 2) System.out.println("UNSAT INFO:" + output);

            if (details) {
                int index = output.indexOf("unsat core ids:");
                if (index >= 0) {
                    CoreIds cids = new CoreIds();
                    String[] sids = output.substring(index+"unsat core ids: ".length()).split("[ \n\r]");
                    for (int i=0; i<sids.length; i++) cids.add(Integer.parseInt(sids[i]));
                    r.add(cids);
                }
            }
        } else {
            r.result(ProverResult.UNKNOWN);
        }
        return r;
    }
    
    Map<String,String> epairs = new HashMap<String,String>();
//    { 
//        epairs.put(NULL,NULL); 
//    }
    
    protected int getArg(String output, int pos) {
        int count = 0;
        while (true) {
            char c = output.charAt(pos);
            if (c == '(') {
                count++;
            } else if (c == ')') {
                if (count == 0) break;
                count--;
                if (count == 0) { pos++; break;}
            } else if (Character.isWhitespace(c)) {
                if (count == 0) break;
            }
            pos++;
        }
        return pos;
    }
    
    protected int skipWS(String output, int pos) {
        while (Character.isWhitespace(output.charAt(pos))) pos++;
        return pos;
    }
    
    protected int findStart(String output, int pos) {
        int len = output.length();
        while (pos < len) {
            char c = output.charAt(pos);
            pos++;
            if (c == '(') {
                c = output.charAt(pos);
                pos++;
                if (c == '=') return pos;
            }
        }
        return -1;
    }

    /**
     * @param output text returned by prover
     * @return a Counterexample object with locations translated
     * @throws ProverException
     */
    protected Counterexample createCounterexample(String output)
            throws ProverException {
        Counterexample ce = new Counterexample();
        Counterexample newce = new Counterexample();
        Map<String,String> canonical = new HashMap<String,String>();
        //StringBuilder sb = new StringBuilder();
        //Matcher m = pattern.matcher(output);
        int pos = 0;
        while (true) {
            pos = findStart(output,pos);
            if (pos < 0) break;
            pos = skipWS(output,pos);
            int ipos = pos;
            pos = getArg(output,pos);
            String name = output.substring(ipos,pos);
            pos = skipWS(output,pos);
            ipos = pos;
            pos = getArg(output,pos);
            String res = output.substring(ipos,pos);
            String typeString = defined.get(name);
            ce.put(name,res);
            if (res.charAt(0) != '(' && typeString != null && isARefType(typeString)) {
                if (Character.isDigit(res.charAt(0))) {
                    // The result is a Yices number  - need to be able to translate that 
                    // back to logical variable
                    String s1 = canonical.get(res);
                    if (s1 == null) {
                        canonical.put(res,canonical(name));
                        //System.out.println("IMAP: " + res + " -> " + name);
                    } else {
                        String s2 = canonical(name);
                        if (s2.equals(NULL)) epairs.put(s1,s2);
                        else epairs.put(s2,s1);
                        newce.put(name,s1);
                        //System.out.println("IMAP: " + res + "   SO " + name + " -> " + s1);
                    }
                } else {
                    String s1 = canonical(name);
                    String s2 = canonical(res);
                    if (!s1.equals(s2)) { 
                        if (s1.equals(NULL)) epairs.put(s2,s1);
                        else epairs.put(s1,s2);
                        newce.put(name,s2); 
                    }
                    //if (!s1.equals(s2)) System.out.println("EMAP: " + name + "=" + res + "   SO " + s1 + " -> " + s2);
                }
            }
        }
            
        for (Map.Entry<String,String> entry : ce.sortedEntries()) {
            String nm = entry.getKey();
            String res = entry.getValue();
            if (nm.charAt(0) == '(') {
                YTree t = parse(nm);
                t.attachType(this);
                String tr = t.toString(canonical);
                String trr = res;
                if (isARefType(t.type)) {
                    trr = canonical.get(res);
                    if (trr == null) trr = res;
                }
                //System.out.println("CHANGED: " + nm + " ::> " + res + "  TO  " + tr + " ::> " + trr);
                newce.put(tr,res);
            } else {
                String typeString = defined.get(nm);
                if (isARefType(typeString)) {
                    String c = epairs.get(res);
                    if (c == null) {
                        c = canonical.get(res);
                        if (c == null) c = res; // FIXME - should not need this
                    }
                    c = canonical(c);
                    if (!nm.equals(c)) {
                        rawassume("(= " + nm + " " + c +")");
                        newce.put(nm,c);
                    }
                } else {
                    newce.put(nm,res);
                }
            }
        }
        for (String n : canonical.values()) {
            if (locs.get(n) == null) {
                Integer u = (locs.size()) + 50000;
                rawassume("(= (loc$ " + n +") " + u + ")");
                locs.put(n,u);
            }
        }
        //System.out.println("CE STATUS " + check(false).result());
        return newce;
    }
    
    Map<String,Integer> locs = new HashMap<String,Integer>();
    {
        locs.put(NULL,0);
    }
    
    static protected boolean isARefType(String typeString) {
        return !("int".equals(typeString) || "bool".equals(typeString) || "real".equals(typeString) || (typeString != null && typeString.startsWith("(->")));
    }

    protected String canonical(String s) {
        while (true) {
            String c = epairs.get(s);
            if (c == null || c.equals(s)) break;
            s = c;
        } 
        return s;
    }
    
    int pos;
    
    public YTree parse(String val) {
        pos = 0;
        return parseTree(val);
    }
    
    public YTree parseTree(String val) {
        YTree t;
        int len = val.length();
        while (pos < len && Character.isWhitespace(val.charAt(pos))) pos++;
        if (pos == len) {
            t = null;
        } else if (val.charAt(pos) == '(') {
            pos++;
            t = parseFcn(val);
        } else if (val.charAt(pos) == ')') {
            pos++;
            t = null;
        } else {
            t = parseId(val);
        }
        return t;
    }
    
    public YId parseId(String val) {
        int i = pos;
        int len = val.length();
        while (pos < len) {
            char c = val.charAt(pos);
            if (c == ')' || Character.isWhitespace(c)) break;
            pos++;
        }
        YId id = new YId();
        id.id = val.substring(i,pos);
        return id;
    }
    
    public YFcn parseFcn(String val) {
        YFcn f = new YFcn();
        f.fcn = parseTree(val);
        while (true) {
            YTree t = parseTree(val);
            if (t == null) break;
            f.args.add(t);
        }
        return f;
    }
    
    abstract public static class YTree {
        String type;
        abstract public void attachType(YicesProver p);
        abstract public String toString(Map<String,String> canonical);
    }
    
    public static class YId extends YTree {
        String id;
        
        public int parse(String val, int pos) {
            int i = pos;
            int len = val.length();
            while (pos < len && !Character.isWhitespace(val.charAt(pos))) pos++;
            id = val.substring(i,pos);
            return pos;
        }
        
        public void attachType(YicesProver p) {
            if (type == null) type = p.defined.get(id);
        }
        
        public int attachType(String typeString, int pos) {
            int i = pos;
            int len = typeString.length();
            int count = 0;
            while (pos < len) {
                char c = typeString.charAt(pos);
                if (c == '(') count++;
                else if (c == ')') { count--; if (count == 0) break; }
                else if (Character.isWhitespace(c)) {
                    if (count == 0) break;
                }
                pos++;
            }
            type = typeString.substring(i,pos);
            return pos;
        }
        
        public String toString(Map<String,String> canonical) {
            if (isARefType(type) && Character.isDigit(id.charAt(0))) {
                return canonical.get(id);
            }
            return id; 
        }
        
    }
    public static class YFcn extends YTree {
        // The type field in the superclass is the result type
        YTree fcn; // The function, usually but not necessarily an identifier
        List<YTree> args = new LinkedList<YTree>();
        
        public String toString(Map<String,String> canonical) {
            StringBuilder s = new StringBuilder();
            s.append("(");
            s.append(fcn.toString(canonical));
            s.append(" ");
            for (YTree t: args) { s.append(t.toString(canonical)); s.append(" "); }
            s.append(")");
            return s.toString();
        }
        
        public void attachType(YicesProver p) {
            fcn.attachType(p);
            attachTypeArgs(p);
        }
        
        public void attachTypeArgs(YicesProver p) {
            int pos = 3;  // The 3 skips the initial (->
            for (YTree a: args) {
                pos = attachType(p,a,fcn.type,pos);
                a.attachType(p);
            }
            attachType(p,this,fcn.type,pos);
        }
        
        public int attachType(YicesProver p, YTree arg, String typeString, int pos) {
            int len = typeString.length();
            int count = 0;
            while (pos < len && Character.isWhitespace(typeString.charAt(pos))) pos++;
            int i = pos;
            while (pos < len) {
                char c = typeString.charAt(pos);
                if (c == '(') count++;
                else if (c == ')') { if (count == 0) break; count--; }
                else if (Character.isWhitespace(c)) {
                    if (count == 0) break;
                }
                pos++;
            }
            arg.type = typeString.substring(i,pos);
            return pos;
        }
    }
    
    public void maxsat() throws ProverException {
        send("(max-sat)\n");
        String output = eatPrompt();
        if (showCommunication >= 2) System.out.println("MAXSAT INFO:" + output);
    }
    
    public void pop() throws ProverException {
        send("(pop)\n");
        eatPrompt();
        for (String t: top) defined.remove(t);
        top = stack.remove(0);
    }

    public void push() throws ProverException {
        send("(push)\n");
        eatPrompt();
        stack.add(0,top);
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
        
        public Collection<Integer> coreIds() {
            return coreIds;
        }
        
        public void add(int i) {
            coreIds.add(i);
        }
    }
}
