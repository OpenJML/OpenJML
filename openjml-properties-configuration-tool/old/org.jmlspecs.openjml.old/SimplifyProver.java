package org.jmlspecs.openjml.provers;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

import org.jmlspecs.openjml.proverinterface.Counterexample;
import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;
import org.jmlspecs.openjml.proverinterface.ProverException;
import org.jmlspecs.openjml.proverinterface.ProverResult;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Options;

// FIXME - needs implementation

/**
 * Used to interact with Simplify.
 * 
 * TODO keep track whether the prover is alive or is known to be dead
 * TODO Abstract the prompt-based interaction in another class
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class SimplifyProver extends AbstractProver implements IProver {
    /** The name of the prover */
    public final static String NAME = "simplify";
    
        public final static String NULL = "NULL";
        public final static String REF = "REF";
        public final static String ARRAY = "ARRAY";
        public final static String ARRAYorNULL = "ARRAYorNULL";
        public static final String TYPE = "TYPEZ";
        public static final String TYPEOF = "typeofZ";
        public static final String SUBTYPE = "subtypeZ";
        public static final String CAST = "castZ";
        
        /** A handy StringBuilder to build strings internally */
        /*@ non_null */
        protected StringBuilder builder = new StringBuilder();
        
//        /** The accumulated list of input sent to the prover process */
//        /*@ non_null */
//        protected List<String> sent = new LinkedList<String>();
    //    
        /** The String by which to invoke the prover */
        /*@ nullable */
        protected String app;
        
        /** The one instance of the associated translator */
        /*@ non_null */
        protected SimplifyTranslator translator;
        
        protected boolean interactive = true;

        @Override
        public String name() { return NAME; }

        protected String prompt() {
            return ">\t";
        }
        // FIXME - will need to separate start from construction so there is an opportunity to set parameters (e.g. timeout)
        /** Creates and starts the prover process, sending any startup information */
        public SimplifyProver(Context context) throws ProverException {
            super(context);
            app = getProverPath(name());
            translator = new SimplifyTranslator(this);
            if (org.jmlspecs.openjml.esc.JmlEsc.escdebug && showCommunication <= 1) showCommunication = 2;
            start();
        }
        
        private final static String[][] predefined = { 
            { REF, "JAVATYPE"},
            { TYPE, "JAVATYPE"},
            { NULL, REF },
//            { "isType", "(-> REF bool)"},
//            { JAVATYPE, "(subtype (r::REF) (isType r))" },
//            { "isArray", "(-> REF bool)"},
//            { ARRAY, "(subtype (r::REF) (isArray r))"},
//            { ARRAYorNULL, "(subtype (r::REF) (or (= r NULL) (isArray r)))"},
//            { "T$java.lang.Object$$A", JAVATYPE},
//            { TYPEOF, "(-> REF "+JAVATYPE+")"},
//            { JMLSUBTYPE, "(-> "+JAVATYPE+" "+JAVATYPE+" bool)"},
//            { CAST, "(-> REF "+JAVATYPE+" REF)"},
//            { "length", "(-> REF int)"},
//            { "length$0", "(-> REF int)"},
//            { "idiv", "(-> int int int)"},
//            { "rdiv", "(-> real real real)"},
//            { "imod", "(-> int int int)"},
//            { "rmod", "(-> real real real)"},
//            { "imul", "(-> int int int)"},
//            { "rmul", "(-> real real real)"},
            { "distinct$", TYPE+" -> INT"},
            { "subtype$", "("+TYPE+","+TYPE+") -> BOOLEAN"},
            { "_alloc$$", REF+" -> INT"},
            { "typeof$", REF+" -> "+TYPE},
//            { "loc$", "(-> "+REF+" int)"},
            };
        
        // This lists names builtin to CVC3
        private final static String[][] otherpredefined = {
          { "BOOLEAN", TYPE},
          { "INT", TYPE},
          { "REAL", TYPE},
          { "BITVECTOR(1)", TYPE},
//          { "div", "(-> int int int)"},
//          { "mod", "(-> real real real)"},
//          { "and", "(-> bool bool bool)"},
//          { "or", "(-> bool bool bool)"},
//          { "=>", "(-> bool bool bool)"},
//          { "not", "(-> bool bool)"},
//          { "+", "(-> int int int)"},   // Real?
//          { "-", "(-> int int int)"},  // Real
//          { "*", "(-> int int int)"},  // Real
//          { "/", "(-> real real real)"},
          // Also bit vector functions
        };
        
        
        /**The background predicate that is sent prior to anything else.  Do not include any newline characters. */
        /*@ non_null */
        private static String backgroundPredicate() {
            //String BASSERT = "ASSERT ";
            return 
                "(DEFPRED (subtypeZ t1 t2))"
                +"\n";
//              "ASSERT (not (isType NULL)));"
//            + "("+BASSERT+" (not (isArray NULL)))"
//            + "("+BASSERT+" (forall (a::REF) (>= (length a) 0)))"
//            + "("+BASSERT+" (= length length$0))"
//            + "("+BASSERT+" (forall (r::REF t::"+JAVATYPE+") (=> (and (/= r NULL) ("+JMLSUBTYPE+" ("+TYPEOF+" r) t))  (= ("+CAST+" r t) r) ) ))"
//            + "("+BASSERT+" (forall (t::"+JAVATYPE+") (= ("+CAST+" NULL t) NULL) ))"
//            + "("+BASSERT+" (forall (t::" + JAVATYPE + ") ("+JMLSUBTYPE + " t t)))"
//            + "("+BASSERT+" (forall (t1::" + JAVATYPE + " t2::" + JAVATYPE + ") (= (and ("+JMLSUBTYPE + " t1 t2) ("+JMLSUBTYPE + " t2 t1)) (=  t1 t2)) ))"
//            + "("+BASSERT+" (forall (t1::" + JAVATYPE + " t2::" + JAVATYPE + " t3::" + JAVATYPE + ") (=> (and ("+JMLSUBTYPE + " t1 t2)("+JMLSUBTYPE + " t2 t3)) ("+JMLSUBTYPE + " t1 t3)) ))"
//            + "("+BASSERT+" (forall (i::int j::int) (= (imul i j) (imul j i)) ))"
//            + "("+BASSERT+" (forall (i::int) (and (= (imul i 0) 0) (= (imul 0 i) 0) (= (imul 1 i) i) (= (imul i 1) i) (= (imul -1 i) (- 0 i)) (= (imul i -1) (- 0 i)) )))"
////            + "("+BASSERT+" (forall (i::int j::int) (= (imul i (+ j 1)) (+ (imul i j) i) ) ))"
////            + "("+BASSERT+" (forall (i::int j::int) (= (imul i (- j 1)) (- (imul i j) i) ) ))"
//            + "("+BASSERT+" (forall (i::int j::int) (=> (/= j 0) (= (imod (imul i j) j) 0)) ))"
//            + "("+BASSERT+" (forall (i::int) (and (= (imod i 1) 0) (= (imod i -1) 0) )))"
//            + "("+BASSERT+" (= (distinct$ T$java.lang.Object$$A) 99))"
//            + "\n";
        }
        
        @Override
        protected String[] app() {
            return new String[]{app,"-noprune"};
        }
        
        /** Does the startup work */
        @Override
        protected void start() throws ProverException {
            super.start();
            background();
        }
        
        private void background() throws ProverException {
            for (String[] pairs: otherpredefined) {
                defined.put(pairs[0],pairs[1]);
            }
            // Send predefined values
            StringBuilder s = new StringBuilder();;
//            for (String[] pairs: predefined) {
//                if (pairs[1] == null) {
//                    s.append("(define-type ");
//                    s.append(pairs[0]);
//                    s.append(")");
//                } else if (pairs[1].startsWith("(subtype")) {
//                    s.append("(define-type ");
//                    s.append(pairs[0]);
//                    s.append(" ");
//                    s.append(pairs[1]);
//                    s.append(")");
//                } else {
//                    s.append(pairs[0]);
//                    s.append(" : ");
//                    s.append(pairs[1]);
//                    s.append(";  ");
//                }
//                defined.put(pairs[0],pairs[1]);
//            }
            s.append(backgroundPredicate());
            send(s.toString());
            eatPrompt(interactive);
        }
        
        public int assume(JCExpression tree) throws ProverException {
            try {
                String t = translator.translate(tree);
                builder.setLength(0);
                builder.append("(BG_PUSH ");
                builder.append(t);
                builder.append(")\n");
                send(builder.toString());
                eatPrompt(interactive);
            } catch (ProverException e) {
                e.mostRecentInput = builder.toString();
                throw e;
            }
            // We use this assume counter, but the more robust method is to
            // look at the output returned from eatPrompt (FIXME)
            return 0;
        }
        
//        public int assumePlus(JCExpression tree) throws ProverException {
//            try {
//                String t = translator.toCVC3(tree);
//                builder.setLength(0);
//                builder.append("ASSERT ");
//                builder.append(t);
//                builder.append(";\n");
//                send(builder.toString());
//                eatPrompt(interactive);
//            } catch (ProverException e) {
//                e.mostRecentInput = builder.toString();
//                throw e;
//            }
//            // We use this assume counter, but the more robust method is to
//            // look at the output returned from eatPrompt (FIXME)
//            return 0;
//        }
        
        public int assume(JCExpression tree, int weight) throws ProverException {
            return assume(tree);
        }
        
        public int rawassume(String t) throws ProverException {
            try {
                builder.setLength(0);
                builder.append("(BG_PUSH ");
                builder.append(t);
                builder.append(")\n");
                send(builder.toString());
                eatPrompt(interactive);
            } catch (ProverException e) {
                e.mostRecentInput = builder.toString();
                throw e;
            }
            return 0;
        }
        
        
        
        public void reassertCounterexample(ICounterexample ce) {
            // CVC3 reasserts its own proverResults when a QUERY is requested
        }


        
        protected String pretty(String s) {
            return s;
//            if (s.length() <= 50) return s;
//            StringBuilder sb = new StringBuilder();
//            //System.out.println("CONVERTING " + s);
//            char[] cc = s.toCharArray();
//            int nparens = 0;
//            int nind = 2;
//            for (int i=0; i<cc.length; ++i) {
//                char c = cc[i];
//                if (c == ')') { nparens--; sb.append(c); continue; }
//                if (c == '(') { 
//                    if (cc[i+1]=='=' && cc[i+2]=='>' && nind == nparens) {
//                        nind++;
//                        nparens++;
//                        sb.append("\n                    ");
//                        int k = nparens;
//                        while (--k >= 0) sb.append(' ');
//                        sb.append("(=>");
//                        i += 2;
//                        continue;
//                    } else if (cc[i+1] == 'a' && cc[i+2] == 'n' && nind == nparens) {
//                        nind++;
//                        nparens++;
//                        sb.append("\n                    ");
//                        int k = nparens;
//                        while (--k >= 0) sb.append(' ');
//                        sb.append("(an");
//                        i += 2;
//                        continue;
//                    }
//                    if (i != 0 && nparens == 0) sb.append("\n               ");
//                    nparens++; 
//                    sb.append(c);
//                    continue; 
//                }
//                sb.append(c);
//            }
//            return sb.toString();
        }
        
        /** Converts an AST type to a type that CVC3 knows
         * 
         * @param t the AST type
         * @return the CVC3 equivalent
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
                s = "BOOLEAN";
            } else {
                s = "INT";
            }
            return s;
        }
        
        /** The set of variables already defined in CVC3 (since CVC3 objects if
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
//            String s = convertType(t);
//            if (isDefined(s)) return s; // DO nothing if already defined
//            builder.setLength(0);
//            if (t.tag == TypeTags.ARRAY) {
//                Type ct = ((ArrayType)t).elemtype;
//                if (ct instanceof ArrayType) defineType(ct);
//                String ss = "(subtype (a::ARRAY) (subtype$ (typeof$ a) T$java.lang.Object$$A))";
//                builder.append("(define-type " + s + " " + ss + ")\n");
//                declare(s,ss);
//            } else {
//                builder.append(s);
//                builder.append(" : JAVATYPE;\n");
//                declare(s,null);
//            }
//            try {
//                send(builder.toString());
//                eatPrompt(interactive);
//            } catch (ProverException e) {
//                e.mostRecentInput = builder.toString();
//                throw new RuntimeException(e);
//            }
//            return s;
            return "";
        }

        public String defineType(String s, boolean array) throws ProverException {
//            if (checkAndDefine(s,"JAVATYPE")) return s; // DO nothing if already defined
//            builder.setLength(0);
//            if (array) {
//                String cs = s.substring("refA$".length());
//                defineType(cs,cs.startsWith("refA"));
//                builder.append("(define-type " + s + " (subtype (a::ARRAY) (subtype$ (typeof$ a) T$java.lang.Object$$A)))\n");
//            } else {
//                builder.append(s);
//                builder.append(" : JAVATYPE;\n");
//            }
//            try {
//                send(builder.toString());
//                eatPrompt(interactive);
//            } catch (ProverException e) {
//                e.mostRecentInput = builder.toString();
//                throw e;
//            }
            return s;
        }
        
        public void define(String id, Type t) throws ProverException {
            if (isDefined(id)) return; // DO nothing if already defined
            builder.setLength(0);
            String s = defineType(t);
            declare(id,s);
            builder.append(id);
            builder.append(" : ");
            builder.append(s);
            builder.append(";\n");
            try {
                send(builder.toString());
                eatPrompt(interactive);
            } catch (ProverException e) {
                e.mostRecentInput = builder.toString();
                throw e;
            }
        }

        public void define(String id, Type t, JCExpression e) throws ProverException {
            throw new ProverException("Definitions not implemented in Simplify");
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
//            if (typeString.indexOf("->")<0) defineType(typeString,typeString.startsWith("refA"));
//            builder.setLength(0);
//            builder.append(" ");
//            builder.append(id);
//            builder.append(":");
//            builder.append(typeString);
//            builder.append(";\n");
//            try {
//                send(builder.toString());
//                eatPrompt(interactive);
//            } catch (ProverException e) {
//                e.mostRecentInput = builder.toString();
//                throw e;
//            }
//            return false;
            return true;
        }

        public boolean rawdefinetype(String id, String typeString, String recordedtype) throws ProverException {
//            if (isDefined(id)) return true; // DO nothing if already defined
//            declare(id,recordedtype);
//            builder.setLength(0);
//            builder.append("(define-type ");
//            builder.append(id);
//            builder.append(" ");
//            builder.append(typeString);
//            builder.append(")\n");
//            try {
//                send(builder.toString());
//                eatPrompt(interactive);
//            } catch (ProverException e) {
//                e.mostRecentInput = builder.toString();
//                throw e;
//            }
//            return false;
            return true;
        }


        /** A pattern to interpret CVC3 counterexample information */
        static private Pattern pattern = Pattern.compile("\\(=[ ]+(.+)[ ]+([^)]+)\\)");

        //Utils.Timer timer = new Utils.Timer();

        public IProverResult check(boolean details) throws ProverException {
            //timer.reset();
            //send("FALSE\n");
            send("BLZStart\n");
            String output = eatPrompt(true);
            //System.out.println("CHECK TIME " + timer.elapsed()/1000.);
            boolean sat = output.startsWith("Invalid.") || output.startsWith("Counterexample");
            boolean unknown = output.startsWith("Unknown.");
            boolean unsat = output.indexOf("Valid.") != -1;
            if (sat == unsat && !unknown) {
                throw new ProverException("Improper response to (check) query: \"" + output + "\"");
            }
            ProverResult r = new ProverResult("simplify");
            if (sat || unknown) {
                if (unknown) r.result(ProverResult.POSSIBLY_SAT);
                else r.result(ProverResult.SAT);
                if (details) {
                    Counterexample ce = createCounterexample(output);
                    r.add(ce);
                }
            } else if (unsat) {
                r.result(ProverResult.UNSAT);
                if (interactive) output = output.substring(0,output.length()-prompt().length());
                if (showCommunication >= 2) System.out.println("UNSAT INFO:" + output);

            } else {
                r.result(ProverResult.UNKNOWN);
            }
            return r;
        }
        

        /**
         * @param output text returned by prover
         * @return a Counterexample object with locations translated
         * @throws ProverException
         */
        protected Counterexample createCounterexample(String output)
                throws ProverException {
            //System.out.println("OUTPUT: " + output);
            Counterexample newce = new Counterexample();
            int k = output.indexOf("YYassumeCheckCount");
            k += "YYassumeCheckCount".length()+1;
            int kk = output.indexOf(')',k);
            String ps = output.substring(k,kk);
            newce.put("YYassumeCheckCount",ps);
            newce.put("__assumeCheckCount",ps);
            newce.put("$$assumeCheckCount",ps);
            
//            Map<String,String> canonical = new HashMap<String,String>();
//            //StringBuilder sb = new StringBuilder();
//            //Matcher m = pattern.matcher(output);
//            int pos = 0;
//            while (true) {
//                pos = findStart(output,pos);
//                if (pos < 0) break;
//                pos = skipWS(output,pos);
//                int ipos = pos;
//                pos = getArg(output,pos);
//                String name = output.substring(ipos,pos);
//                pos = skipWS(output,pos);
//                ipos = pos;
//                pos = getArg(output,pos);
//                String res = output.substring(ipos,pos);
//                String typeString = defined.get(name);
//                ce.put(name,res);
//                if (res.charAt(0) != '(' && typeString != null && isARefType(typeString)) {
//                    if (Character.isDigit(res.charAt(0))) {
//                        // The result is a CVC3 number  - need to be able to translate that 
//                        // back to logical variable
//                        String s1 = canonical.get(res);
//                        if (s1 == null) {
//                            canonical.put(res,canonical(name));
//                            //System.out.println("IMAP: " + res + " -> " + name);
//                        } else {
//                            String s2 = canonical(name);
//                            if (s2.equals(NULL)) epairs.put(s1,s2);
//                            else epairs.put(s2,s1);
//                            newce.put(name,s1);
//                            //System.out.println("IMAP: " + res + "   SO " + name + " -> " + s1);
//                        }
//                    } else {
//                        String s1 = canonical(name);
//                        String s2 = canonical(res);
//                        if (!s1.equals(s2)) { 
//                            if (s1.equals(NULL)) epairs.put(s2,s1);
//                            else epairs.put(s1,s2);
//                            newce.put(name,s2); 
//                        }
//                        //if (!s1.equals(s2)) System.out.println("EMAP: " + name + "=" + res + "   SO " + s1 + " -> " + s2);
//                    }
//                }
//            }
//                
//            for (Map.Entry<String,String> entry : ce.sortedEntries()) {
//                String nm = entry.getKey();
//                String res = entry.getValue();
//                if (nm.charAt(0) == '(') {
//                    YTree t = parse(nm);
//                    t.attachType(this);
//                    String tr = t.toString(canonical);
//                    String trr = res;
//                    if (isARefType(t.type)) {
//                        trr = canonical.get(res);
//                        if (trr == null) trr = res;
//                    }
//                    //System.out.println("CHANGED: " + nm + " ::> " + res + "  TO  " + tr + " ::> " + trr);
//                    newce.put(tr,res);
//                } else {
//                    String typeString = defined.get(nm);
//                    if (isARefType(typeString)) {
//                        String c = epairs.get(res);
//                        if (c == null) {
//                            c = canonical.get(res);
//                            if (c == null) c = res; // FIXME - should not need this
//                        }
//                        c = canonical(c);
//                        if (!nm.equals(c)) {
//                            rawassume("(= " + nm + " " + c +")");
//                            newce.put(nm,c);
//                        }
//                    } else {
//                        newce.put(nm,res);
//                    }
//                }
//            }
//            for (String n : canonical.values()) {
//                if (locs.get(n) == null) {
//                    Integer u = (locs.size()) + 50000;
//                    rawassume("(= (loc$ " + n +") " + u + ")");
//                    locs.put(n,u);
//                }
//            }
            //System.out.println("CE STATUS " + check(false).result());
            return newce;
        }
        
        Map<String,Integer> locs = new HashMap<String,Integer>();
        {
            locs.put(NULL,0);
        }
        
        static protected boolean isARefType(String typeString) {
            return !("int".equals(typeString) || "bool".equals(typeString) || "real".equals(typeString) || (typeString != null && typeString.indexOf("->")>0));
        }

        
        public void maxsat() throws ProverException {
            throw new ProverException("maxsat() not suppported by CVC3Prover"); // FIXME
//            send("(max-sat)\n");
//            String output = eatPrompt(true);
//            if (showCommunication >= 2) System.out.println("MAXSAT INFO:" + output);
        }
        
        public void pop() throws ProverException {
            send("(BG_POP)\n");
            eatPrompt(interactive);
//            for (String t: top) defined.remove(t);
//            top = stack.remove(0);
        }

        public void push() throws ProverException {
            send("(BG_PUSH TRUE)\n");
            eatPrompt(interactive);
//            stack.add(0,top);
//            top = new LinkedList<String>();
        }


        public void retract() throws ProverException {
            send("(BG_POP)\n");
            eatPrompt(interactive);
        }
        
        public void retract(int n) throws ProverException {
            throw new ProverException("retract(int) not suppported by SimplifyProver"); // FIXME
        }
        
    }
