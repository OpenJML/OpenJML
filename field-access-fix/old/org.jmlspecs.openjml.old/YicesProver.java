package org.jmlspecs.openjml.provers;

import java.io.BufferedReader;
import java.io.BufferedWriter;
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
import org.jmlspecs.openjml.esc.JmlEsc;
import org.jmlspecs.openjml.proverinterface.Counterexample;
import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.ProverException;
import org.jmlspecs.openjml.proverinterface.ProverResult;
import org.jmlspecs.openjml.proverinterface.IProver.Supports;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;


public class YicesProver extends AbstractProver implements IProver {
    static public final String NAME = "yices";
    
    public final static String NULL = "NULL";
    public final static String REF = "REF";
    public final static String JMLTYPE = "JMLTYPE$";
    public final static String ARRAY = "ARRAY";
    public final static String ARRAYorNULL = "ARRAYorNULL";
    public static final String JAVATYPE = "JAVATYPE$";
    public static final String ERASEDTYPEOF = "etypeof$";
    public static final String TYPEOF = "typeof$";
    public static final String JMLSUBTYPE = "subtypeJML$";
    public static final String JAVASUBTYPE = "subtypeJava$";
    public static final String CAST = "cast$";

    @Override
    public String name() { return NAME; }

    /** A handy StringBuilder to build strings internally */
    /*@ non_null */
    protected StringBuilder builder = new StringBuilder();

    /** The accumulated list of input sent to the prover process */
    /*@ non_null */
    protected List<String> sent = new LinkedList<String>();

    /** The String by which to invoke the prover */
    /*@ nullable */
    protected String app = getProverPath(name());

    /** The one instance of the associated translator */
    /*@ non_null */
    protected YicesJCExpr translator;

    protected boolean interactive = true;

    // FIXME - will need to separate start from construction so there is an opportunity to set parameters (e.g. timeout)
    /** Creates and starts the prover process, sending any startup information */
    public YicesProver(Context context) throws ProverException {
        super(context);
        assumeCounter = -1;
        int k = 1;
        String bp = backgroundPredicate();
        while (k>0) {
            ++assumeCounter;
            k = bp.indexOf(BASSERTPLUS,k)+1;
        }
        translator = new YicesJCExpr(this);
        if (org.jmlspecs.openjml.esc.JmlEsc.escdebug && showCommunication <= 1) showCommunication = 2;
        start();
    }

    private final static String[][] predefined = { 
        { REF, null},
       // { JMLTYPE, null },
        { NULL, REF },
        { "isType", "(-> REF bool)"},
        { "isJMLType", "(-> REF bool)"},
        { JMLTYPE, "(subtype (r::REF) (isJMLType r))" },
        { JAVATYPE, "(subtype (r::REF) (isType r))" },
        { "isArray", "(-> REF bool)"},
        { ARRAY, "(subtype (r::REF) (isArray r))"},
        { ARRAYorNULL, "(subtype (r::REF) (or (= r NULL) (isArray r)))"},
        { "T$java.lang.Object$$A", JAVATYPE},
        { TYPEOF, "(-> REF "+JMLTYPE+")"},
        { ERASEDTYPEOF, "(-> REF "+JAVATYPE+")"},
        { JMLSUBTYPE, "(-> "+JMLTYPE+" "+JMLTYPE+" bool)"},
        { JAVASUBTYPE, "(-> "+JAVATYPE+" "+JAVATYPE+" bool)"},
        { CAST, "(-> REF "+JAVATYPE+" REF)"},
        { "length", "(-> REF int)"},
        { "length$0", "(-> REF int)"},
        { "idiv", "(-> int int int)"},
        { "rdiv", "(-> real real real)"},
        { "imod", "(-> int int int)"},
        { "rmod", "(-> real real real)"},
        { "imul", "(-> int int int)"},
        { "rmul", "(-> real real real)"},
        { "distinct$", "(-> "+JAVATYPE+" int)"},
        { "loc$", "(-> "+REF+" int)"},
    };

    // This lists names builtin to Yices
    private final static String[][] otherpredefined = {
        { "bool", JAVATYPE},
        { "int", JAVATYPE},
        { "real", JAVATYPE},
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

    public static boolean evidence = true;
    public static boolean assertPlus = true;
    public static final String BASSERTPLUS = "assert+";
    public static final String BASSERTNOPLUS = "assert";
    public static String BASSERT;

    /**The background predicate that is sent prior to anything else.  Do not include any newline characters. */
    /*@ non_null */
    private static String backgroundPredicate() {
        BASSERT = assertPlus ? BASSERTPLUS : BASSERTNOPLUS;
        return
        "("+BASSERT+" (not (isType NULL)))"
        + "("+BASSERT+" (not (isArray NULL)))"
        + "("+BASSERT+" (forall (a::REF) (>= (length a) 0)))"
        + "("+BASSERT+" (= length length$0))"
        //+ "("+BASSERT+" (forall (r::REF t::"+JAVATYPE+") (=> (and (/= r NULL) ("+JMLSUBTYPE+" ("+TYPEOF+" r) t))  (= ("+CAST+" r t) r) ) ))"
        + "("+BASSERT+" (forall (t::"+JAVATYPE+") (= ("+CAST+" NULL t) NULL) ))"
        + "("+BASSERT+" (forall (t::" + JAVATYPE + ") ("+ JAVASUBTYPE + " t t)))"
        + "("+BASSERT+" (forall (t1::" + JAVATYPE + " t2::" + JAVATYPE + ") (= (and ("+JAVASUBTYPE + " t1 t2) ("+JAVASUBTYPE + " t2 t1)) (=  t1 t2)) ))"
        + "("+BASSERT+" (forall (t1::" + JAVATYPE + " t2::" + JAVATYPE + " t3::" + JAVATYPE + ") (=> (and ("+JAVASUBTYPE + " t1 t2)("+JAVASUBTYPE + " t2 t3)) ("+JAVASUBTYPE + " t1 t3)) ))"
        + "("+BASSERT+" (forall (t::" + JMLTYPE + ") ("+JMLSUBTYPE + " t t)))"
        + "("+BASSERT+" (forall (t1::" + JMLTYPE + " t2::" + JMLTYPE + ") (= (and ("+JMLSUBTYPE + " t1 t2) ("+JMLSUBTYPE + " t2 t1)) (=  t1 t2)) ))"
        + "("+BASSERT+" (forall (t1::" + JMLTYPE + " t2::" + JMLTYPE + " t3::" + JMLTYPE + ") (=> (and ("+JMLSUBTYPE + " t1 t2)("+JMLSUBTYPE + " t2 t3)) ("+JMLSUBTYPE + " t1 t3)) ))"
        + "("+BASSERT+" (forall (i::int j::int) (= (imul i j) (imul j i)) ))"
        + "("+BASSERT+" (forall (i::int) (and (= (imul i 0) 0) (= (imul 0 i) 0) (= (imul 1 i) i) (= (imul i 1) i) (= (imul -1 i) (- 0 i)) (= (imul i -1) (- 0 i)) )))"
        //        + "("+BASSERT+" (forall (i::int j::int) (= (imul i (+ j 1)) (+ (imul i j) i) ) ))"
        //        + "("+BASSERT+" (forall (i::int j::int) (= (imul i (- j 1)) (- (imul i j) i) ) ))"
        + "("+BASSERT+" (forall (i::int j::int) (=> (/= j 0) (= (imod (imul i j) j) 0)) ))"
        + "("+BASSERT+" (forall (i::int) (and (= (imod i 1) 0) (= (imod i -1) 0) )))"
        + "("+BASSERT+" (= (distinct$ T$java.lang.Object$$A) 99))"
        + "("+BASSERT+" (forall (o::REF) (=> (/= o NULL) (/= ("+TYPEOF+" o) NULL))))"
        + "\n";
    }

    /** A counter of assumptions sent to the prover */
    int assumeCounter;

    public String[] app() {
        if (!evidence) {
            if (interactive)
                return (new String[]{app,"-i","-tc","--timeout=120","-v","2"});
            else
                return (new String[]{app,"-tc","--timeout=120","-v","2"});
        } else {
            if (interactive)
                return (new String[]{app,"-i","-tc","--timeout=120","-e","-v","2"});
            else
                return (new String[]{app,"-tc","--timeout=120","-e","-v","2"});
        }
    }

    public String prompt() {
        return "yices> ";
    }

    /** Does the startup work */
    public void start() throws ProverException {
        if (app == null) {
            throw new ProverException("No registered executable found; specify it using -D" + getProverPathKey(name()));
        } else if (!new java.io.File(app).exists()) {
            throw new ProverException("The specified executable does not appear to exist: " + app);
        }
        try {
            // The interactive mode is used so that we get a prompt back, thereby
            // knowing when we have received the prover's response
            if (false) {
                log.noticeWriter.print("About to exec: " + app + " :");
                for (String s: app()) log.noticeWriter.print(" " + s);
                log.noticeWriter.println("");
            }
            process = Runtime.getRuntime().exec(app());
        } catch (IOException e) {
            process = null;
            throw new ProverException("Failed to launch prover process: " + app + " " + e);
        }
        // TODO: assess performance of using buffered readers/writers
        toProver = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
        fromProver = new BufferedReader(new InputStreamReader(process.getInputStream()));
        errors = new InputStreamReader(process.getErrorStream());
        eatPrompt(false);  // Whether there is output to eat depends on the level of -v
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
        s.append(backgroundPredicate());
        send(s.toString());
        eatPrompt(interactive);
    }

    public String eatPrompt() throws ProverException {
        return eatPrompt(interactive);
    }

    public String eatPrompt(boolean wait) throws ProverException {
        // We read characters until we get to the sequence "> ", which is the
        // end of the Yices prover's prompt (which is "yices> ").  Be careful 
        // that sequence is not elsewhere in the input as well.
        // FIXME - need a better way to read both inputs
        // FIXME - this probably can be made a lot more efficient
        try {
            //            if (interactive && false) {
            //                buf.position(0);
            //                outer: while (true) {
            //                    int n = fromProver.read();
            //                    if (n < 0) {
            //                        throw new ProverException("Prover died");
            //                    }
            //                    char c = (char)n;
            //                    buf.append(c);
            //                    if (c != '>') continue;
            //                    while (true) {
            //                        n = fromProver.read();
            //                        if (n < 0) {
            //                            throw new ProverException("Prover died");
            //                        }
            //                        c = (char)n;
            //                        buf.append(c);
            //                        if (c == ' ') break outer;
            //                        if (c != '>') break;
            //                    }
            //                }
            //                buf.limit(buf.position());
            //                buf.rewind();
            //                String s = buf.toString();
            //                buf.clear();
            //                if (errors.ready()) {
            //                    while (errors.ready()) {
            //                        int n = errors.read(buf);
            //                        if (n < 0) throw new ProverException("Prover died");
            //                        if (n == 0) break;
            //                    }
            //                    if (buf.position() > 0) {
            //                        buf.limit(buf.position());
            //                        buf.rewind();
            //                        String errorString = buf.toString();
            //                        if (!errorString.startsWith("\nWARNING") &&
            //                                !errorString.startsWith("Yices (version") &&
            //                                !errorString.startsWith("searching")) {
            //                            if (showCommunication >= 1) log.noticeWriter.println("HEARD ERROR: " + errorString);
            //                            throw new ProverException("Prover error message: " + errorString);
            //                        } else {
            //                            if (showCommunication >= 3) log.noticeWriter.println("HEARD ERROR: " + errorString);
            //                        }
            //                    }
            //                    buf.clear();
            //                }
            //                if (showCommunication >= 3) log.noticeWriter.println("HEARD: " + s);
            //                return s;
            //            } else 
            if (interactive) {
                int offset = 0;
                String s = "";
                int truncated = 0;
                while (true) { // There is always a prompt to read, so it is OK to block
                    // until it is read.  That gives the prover process time to
                    // do its processing.
                    int n = fromProver.read(cbuf,offset,cbuf.length-offset);
                    if (n < 0) {
                        int off = 0;
                        while (errors.ready()) {
                            int nn = errors.read(cbuf,off,cbuf.length-off);
                            if (nn < 0) {
                                if (showCommunication >= 2) log.noticeWriter.print("Prover died-eStream");
                                throw new ProverException("Prover died-eStream: read so far: " + String.valueOf(cbuf,0,off));
                            }
                            if (nn == 0) break;
                            off += nn;
                        }
                        String serr = String.valueOf(cbuf,0,off);
                        if (showCommunication >= 2) log.noticeWriter.println("NO INPUT - ERROR READ: " + serr);
                        try {
                            process.exitValue();
                            throw new ProverException("Prover has terminated");
                        } catch (IllegalThreadStateException e) {
                            try { Thread.sleep(2000); } catch (InterruptedException ee) {}
                        }
                        continue;
                    }
                    offset += n;
                    if (offset > 1 && cbuf[offset-2] == '>' && cbuf[offset-1] ==' ') break;
                    if (offset > cbuf.length-1000) {
                        if (s.length() > 180000) {
                            // excessive length
                            String sss = String.valueOf(cbuf,0,200);
                            truncated += offset;
                            log.noticeWriter.println("TRUNCATING " + s.length() + " " + truncated );//+ " " + sss);
                        } else {
                            String sss = String.valueOf(cbuf,0,200);
                            s = s + String.valueOf(cbuf,0,offset);
                            log.noticeWriter.println("BUFFER FULL " + s.length() );//+ " " + sss);
                        }
                        offset = 0;
                    }
                }
                if (truncated == 0) s = s + String.valueOf(cbuf,0,offset);
                //                if (truncated > 0) {
                //                    log.noticeWriter.println("OUTPUT LENGTH " + s.length() + " " + truncated);
                //                    throw new ProverException("Excessive output: " + s.length() + " " + truncated);
                //                }

                if (truncated == 0 && JmlEsc.escdebug) {
                    // Check that output assertion identifiers are correct
                    String pat = "id: ";
                    int k = s.lastIndexOf(pat)+ pat.length();
                    int kk = s.indexOf("\n",k);
                    int kkk = s.indexOf("\r",k);
                    kk = kk == -1 ? kkk : kkk == -1 ? kk : kkk < kk ? kkk : kk;
                    if (k >= pat.length()) {
                        k = Integer.valueOf(s.substring(k,kk));
                        if (k != assumeCounter) {
                            log.noticeWriter.println("Warning: prover returned id = " + k + " but assumeCounter is " + assumeCounter);
                        }
                    }
                }
                offset = 0;
                if (errors.ready()) {
                    while (errors.ready()) {
                        int n = errors.read(cbuf,offset,cbuf.length-offset);
                        if (n < 0) throw new ProverException("Prover died");
                        if (n == 0) break;
                        offset += n;
                    }
                    if (offset > 0) {
                        String errorString = new String(cbuf,0,offset);
                        //if (errorString.startsWith("searching")) log.noticeWriter.println("SEARCHING " + errorString.length());
                        if (!errorString.startsWith("\nWARNING") &&
                                !errorString.startsWith("Yices (version") &&
                                !errorString.startsWith("searching")) {
                            if (showCommunication >= 1) log.noticeWriter.println("HEARD ERROR: " + errorString);
                            throw new ProverException("Prover error message: " + errorString);
                        } else {
                            if (showCommunication >= 3) {
                                log.noticeWriter.println("HEARD ERROR: " + errorString);
                            }
                        }
                    }
                }
                if (showCommunication >= 3) log.noticeWriter.println("HEARD: " + s);
                return s;
            } else {
                // In non-interactive mode, there may be no input at all
                // We sleep briefly, hoping that the target process will have time to put out any output
                try { Thread.sleep(1); } catch (Exception e) { /* No action needed */ }
                int offset = 0;
                if (wait) {
                    // TODO: Problem: When the prover produces a counterexample, it does not always do so promptly.
                    // So the loop below tends to exit before all (or any) counterexample information is retrieved.
                    do {
                        int n = fromProver.read(cbuf,offset,cbuf.length-offset);
                        if (n < 0) {
                            throw new ProverException("Prover died");
                        }
                        offset += n;
                    } while (fromProver.ready());
                } else {
                    while (fromProver.ready()) {
                        int n = fromProver.read(cbuf,offset,cbuf.length-offset);
                        if (n < 0) {
                            throw new ProverException("Prover died");
                        }
                        offset += n;
                    }
                }
                String s = new String(cbuf,0,offset);
                offset = 0;
                if (errors.ready()) {
                    while (errors.ready()) {
                        int n = errors.read(cbuf,offset,cbuf.length-offset);
                        if (n < 0) throw new ProverException("Prover died");
                        if (n == 0) break;
                        offset += n;
                    }
                    if (offset > 0) {
                        String errorString = new String(cbuf,0,offset);
                        if (!errorString.startsWith("\nWARNING") &&
                                !errorString.startsWith("Yices (version") &&
                                !errorString.startsWith("searching")) {
                            if (showCommunication >= 1) log.noticeWriter.println("HEARD ERROR: " + errorString);
                            throw new ProverException("Prover error message: " + errorString);
                        } else {
                            if (showCommunication >= 3) log.noticeWriter.println("HEARD ERROR: " + errorString);
                        }
                    }
                }
                if (showCommunication >= 3) log.noticeWriter.println("HEARD: " + s);
                return s;
            }
        } catch (IOException e) {
            throw new ProverException("IO Error on reading from prover: " + e);
        }
    }

    public int assume(JCExpression tree) throws ProverException {
        try {
            String t = translator.toYices(tree);
            builder.setLength(0);
            builder.append("(");
            builder.append(assertPlus ? BASSERTPLUS : BASSERTNOPLUS);
            builder.append(" ");
            builder.append(t);
            builder.append(")\n");
            if (assertPlus) ++assumeCounter;
            send(builder.toString());
            eatPrompt(interactive);
        } catch (ProverException e) {
            e.mostRecentInput = builder.toString();
            throw e;
        }
        // We use this assume counter, but the more robust method is to
        // look at the output returned from eatPrompt (FIXME)
        return assumeCounter;
    }

    public int assumePlus(JCExpression tree) throws ProverException {
        try {
            String t = translator.toYices(tree);
            builder.setLength(0);
            builder.append("(");
            builder.append(BASSERTPLUS);
            builder.append(" ");
            builder.append(t);
            builder.append(")\n");
            ++assumeCounter;
            send(builder.toString());
            eatPrompt(interactive);
        } catch (ProverException e) {
            e.mostRecentInput = builder.toString();
            throw e;
        }
        // We use this assume counter, but the more robust method is to
        // look at the output returned from eatPrompt (FIXME)
        return assumeCounter;
    }

    public int assume(JCExpression tree, int weight) throws ProverException {
        try {
            String t = translator.toYices(tree);
            builder.setLength(0);
            builder.append("(");
            builder.append(assertPlus ? BASSERTPLUS : BASSERTNOPLUS);
            builder.append(" ");
            builder.append(t);
            builder.append(" ");
            builder.append(weight);
            builder.append(")\n");
            if (assertPlus) ++assumeCounter;
            send(builder.toString());
            eatPrompt(interactive);
        } catch (ProverException e) {
            e.mostRecentInput = builder.toString();
            throw e;
        }
        return assumeCounter;
    }

    public int rawassume(String t) throws ProverException {
        if (assertPlus) ++assumeCounter;
        try {
            builder.setLength(0);
            builder.append("(");
            builder.append(BASSERT);
            builder.append(" ");
            builder.append(t);
            builder.append(")\n");
            send(builder.toString());
            eatPrompt(interactive);
        } catch (ProverException e) {
            e.mostRecentInput = builder.toString();
            throw e;
        }
        return assumeCounter;
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
            //log.noticeWriter.print("SENDING " + ss);
            log.noticeWriter.print("SENDING ["+assumeCounter+":" + s.length()+ "]" + ss);
            log.noticeWriter.flush();
        }
        //log.noticeWriter.println("SENDING ["+assumeCounter+":" + s.length()+ "]");
        try {
            if (s.length() > 2000) {
                int i = 0;
                for (; i< s.length()-2000; i+= 2000) {
                    toProver.append(s.substring(i,i+2000));
                    try { Thread.sleep(1); } catch (Exception e) {}
                }
                toProver.append(s.substring(i));
            } else {
                toProver.append(s);
            }
            toProver.flush();
        } catch (IOException e) {
            String se = e.toString();
            if (se.length() > 100) se = se.substring(0,100) + " .....";
            String msg = "Failed to write to prover: (" + s.length() + " chars) " + se;
            if (showCommunication >= 2) log.noticeWriter.print(msg);
            throw new ProverException(msg);
        }
    }

    public void reassertCounterexample(ICounterexample ce) {
        //log.noticeWriter.println("REASSERTING");
        for (Map.Entry<String,String> entry : ce.sortedEntries()) {
            String v = entry.getKey();
            String val = entry.getValue();
//            if (v.indexOf("long") != -1) {
//                log.noticeWriter.println("REASSERTING " + v + " AS " + val);
//            }
            String s;
            if (v.indexOf("&&") != -1) continue;
            if (v.indexOf(".length") != -1) continue;
            if (v.indexOf("<=") != -1) continue;
            if (v.indexOf("<:") != -1) continue;
            if (v.indexOf(">") != -1) continue;
            if (v.indexOf("+") != -1) continue;
            if (val.equals("?")) continue;
            if (v.equals(val)) continue;
            v = v.replace("null", "NULL");

//            } else if (val.equals("true")) {
//                s = v;
//            } else if (val.equals("false")) {
//                s = "(not " + v + ")";

            if (v.charAt(0) == '!' && val.equals("false")) {
                v = v.substring(1);
                val = "true";
            } else if (v.charAt(0) == '!' && val.equals("true")) {
                v = v.substring(1);
                val = "false";
            }

            int kk = v.indexOf("!=");
            if (kk != -1) {
                s = "(/= " + v.substring(0,kk) + " " + v.substring(kk+2) + ")";
            } else {
                s = "(= " + v + " " + val +")";
                int k = v.indexOf("==");
                if ( k != -1) {
                    String s1 = v.substring(0,k).trim();
                    if (s1.charAt(0) == '(') continue;
                    String s2 = v.substring(k+2).trim();
                    if (s2.equals("long")) s2 = "T$long";
                    s = "(= " + s1 + " " + s2 + ")";
                    v = s1;
                }
                if (v.charAt(0) == '(') continue;
            }
            if (s.indexOf("==") != -1) continue;
            //log.noticeWriter.println("      " + s);
            try {
                rawassume(s);
            } catch (ProverException e) {
                log.noticeWriter.println("FAILED TO ASSERT " + s);
                log.noticeWriter.println(e);
            }
        }
        //        try {
        //            IProverResult r = check(false);
        //            log.noticeWriter.println("STATUS " + r.result());
        //        } catch (ProverException e) {
        //            log.noticeWriter.println("FAILED TO REASSERT " );
        //            log.noticeWriter.println(e);
        //
        //        }
    }



    protected String pretty(String s) {
        if (s.length() <= 50) return s;
        StringBuilder sb = new StringBuilder();
        //log.noticeWriter.println("CONVERTING " + s);
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
            } else if (t.tsym.flatName().toString().endsWith("IJMLTYPE")) {
                s = YicesProver.JMLTYPE;
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
            String ss = "(subtype (a::ARRAY) (" + JAVASUBTYPE + " (" + ERASEDTYPEOF + " a) T$java.lang.Object$$A))";
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
            eatPrompt(interactive);
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
            builder.append("(define-type " + s + " (subtype (a::ARRAY) (" + JAVASUBTYPE + " (" + ERASEDTYPEOF + " a) T$java.lang.Object$$A)))\n");
        } else {
            builder.append("(define-type ");
            builder.append(s);
            builder.append(")\n");
        }
        try {
            send(builder.toString());
            eatPrompt(interactive);
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
            eatPrompt(interactive);
        } catch (ProverException e) {
            e.mostRecentInput = builder.toString();
            throw e;
        }
    }

    public void define(String id, Type t, JCExpression e) throws ProverException {
        throw new ProverException("Definitions not implemented in Yices");
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
        if (!typeString.startsWith("(")) defineType(typeString,typeString.startsWith("refA"));
        builder.setLength(0);
        builder.append("(define ");
        builder.append(id);
        builder.append("::");
        builder.append(typeString);
        builder.append(")\n");
        try {
            send(builder.toString());
            eatPrompt(interactive);
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
            eatPrompt(interactive);
        } catch (ProverException e) {
            e.mostRecentInput = builder.toString();
            throw e;
        }
        return false;
    }


    //    public boolean isSat() throws ProverException {
    //        send("(check)\n");
    //        String output = eatPrompt();
    //        //log.noticeWriter.println("HEARD " + output);
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
        String output = eatPrompt(true);
        //log.noticeWriter.println("CHECK TIME " + timer.elapsed()/1000.);
        boolean sat = output.startsWith("sat");
        boolean unknown = output.startsWith("unknown");
        boolean unsat = output.startsWith("unsat") || output.startsWith("Logical context is inconsistent");
        if (sat == unsat && !unknown) throw new ProverException("Improper response to (check) query: \"" + output + "\"");
        details  &= evidence;
        ProverResult r = new ProverResult("yices");
        if (sat || unknown) {
            if (unknown) r.result(ProverResult.POSSIBLY_SAT);
            else r.result(ProverResult.SAT);
            if (details) {
                Counterexample ce = createCounterexample(output);
                r.add(ce);
            }
        } else if (unsat) {
            r.result(ProverResult.UNSAT);
            if (interactive) output = output.substring(0,output.length()-8);
            if (showCommunication >= 2) log.noticeWriter.println("UNSAT INFO:" + output);

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

    Map<String, String> epairs = new HashMap<String,String>();
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

    /** The method translates a Yices counterexample into something more
     * understandable.  In particular, Yices maps some types into integers,
     * which have no meaning outside the prover and cannot even be reexpressed
     * back to the prover.  So we pick canonical values by which to represent
     * these internal values.
     * @param output text returned by prover
     * @return a Counterexample object with locations translated
     * @throws ProverException
     */
    protected Counterexample createCounterexample(String output)
    throws ProverException {
        Counterexample ce = new Counterexample(); // The Yices produced counterexample
        Counterexample newce = new Counterexample(); // The rewritten counterexample information
        Map<String,String> canonical = new HashMap<String,String>(); // A map from integers to canonical values for those integers
        epairs = new HashMap<String,String>(); // a map of canonical representations for sets of things that are 
                    // equivalent.  This map is used by the canonical() method to
                    // map a name to an equivalent name that is more canonical

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
                        //log.noticeWriter.println("IMAP: " + name + " -> " + res + " SO " + res + " -> " + canonical(name));
                    } else {
                        String s2 = canonical(name);
                        // res maps to s1; name maps to s2
                        if (!s1.equals(s2)) {
                            if (s2.equals(name)) {
                                epairs.put(s2,s1);
                                //log.noticeWriter.println( name + " -> " + res + " SO " + s2 + " -> " + s1);
                            } else { 
                                epairs.put(s2,s1);
                                //log.noticeWriter.println("IMAP: " + res + "   SO " + name + " -> " + s1);
                                //log.noticeWriter.println( name + " -> " + res + " SO " + s2 + " -> " + s1);
                            }
                            //newce.put(name,s1);
                        }
                    }
                } else {
                    String s1 = canonical(name);
                    String s2 = canonical(res);
                    if (!s1.equals(s2)) { 
                        if (s1.equals(NULL)) {
                            epairs.put(s2,s1);
                            //log.noticeWriter.println( name + " -> " + res + " SO " + s2 + " -> " + s1);
                        } else {
                            epairs.put(s1,s2);
                            //log.noticeWriter.println( name + " -> " + res + " SO " + s1 + " -> " + s2);
                            //newce.put(name,s2); 
                        }
                        //log.noticeWriter.println("EMAP: " + name + "=" + res + "   SO " + s1 + " -> " + s2);
                    }
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
                //log.noticeWriter.println("CHANGED: " + nm + " ::> " + res + "  TO  " + tr + " ::> " + trr);
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
                        //rawassume("(= " + nm + " " + c +")");
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
                //rawassume("(= (loc$ " + n +") " + u + ")");
                locs.put(n,u);
            }
        }
        //log.noticeWriter.println("CE STATUS " + check(false).result());
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
        String output = eatPrompt(true);
        if (showCommunication >= 2) log.noticeWriter.println("MAXSAT INFO:" + output);
    }

    public void pop() throws ProverException {
        send("(pop)\n");
        eatPrompt(interactive);
        for (String t: top) defined.remove(t);
        top = stack.remove(0);
    }

    public void push() throws ProverException {
        send("(push)\n");
        eatPrompt(interactive);
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
        eatPrompt(interactive);
    }

    public void kill() throws ProverException {
        if (process != null) process.destroy();
        process = null;
    }

    public Supports supports() {
        Supports s = super.supports();
        s.retract = true;
        s.unsatcore = true;
        return s;
    }



    static public class CoreIds implements IProverResult.ICoreIds {
        Collection<Integer> coreIds = new ArrayList<Integer>();

        public Collection<Integer> coreIds() {
            return coreIds;
        }

        public void add(int i) {
            coreIds.add(i);
        }
        public String toString() {
            StringBuilder ss = new StringBuilder();
            for (Integer i: coreIds) { ss.append(" "); ss.append(i); }
            return ss.toString();
        }
    }
}
