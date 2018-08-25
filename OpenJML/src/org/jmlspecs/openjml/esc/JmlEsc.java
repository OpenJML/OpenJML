/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.Date;
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.IAPI;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.ProverResult;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.PropagatedException;

/**
 * This class is the main driver for executing ESC on a Java/JML AST. It
 * formulates the material to be proved, initiates the proofs, and obtains and
 * reports the results. The class is also a TreeScanner so that it can easily
 * walk the tree to find all class and method declarations.
 * <P>
 * To use, instantiate an instance of JmlEsc, and then call either visitClassDef
 * or visitMethodDef; various options from JmlOptions will be used. In particular,
 * the -boogie option affects which implementation of ESC is used,
 * and the -prover and -exec options (and the openjml.prover... properties)
 * determine which prover is used.
 * 
 * @author David R. Cok
 */
public class JmlEsc extends JmlTreeScanner {

    /** The key used to register an instance of JmlEsc in the compilation context */
    protected static final Context.Key<JmlEsc> escKey =
        new Context.Key<JmlEsc>();

    /** The method used to obtain the singleton instance of JmlEsc for this compilation context */
    public static JmlEsc instance(Context context) {
        JmlEsc instance = context.get(escKey);
        if (instance == null) {
            instance = new JmlEsc(context);
            context.put(escKey,instance);
        }
        return instance;
    }
    
//    public IAPI.IProofResultListener proofResultListener = null;
    
    /** The compilation context, needed to get common tools, but unique to this compilation run*/
    @NonNull Context context;

    /** Used to obtain cached symbols, such as basic types */
    @NonNull Symtab syms;
    
    /** The tool to log problem reports */ 
    @NonNull Log log;
    
    /** The OpenJML utilities object */
    @NonNull Utils utils;
    
    /** true if compiler options are set to a verbose mode */
    boolean verbose;
    
    /** Just for debugging esc */
    public static boolean escdebug = false; // May be set externally to enable debugging while testing
    
    /** The assertion adder instance used to translate */
    public JmlAssertionAdder assertionAdder;
    
    /** The JmlEsc constructor, which initializes all the tools and other fields. */
    public JmlEsc(Context context) {
        this.context = context;
        this.syms = Symtab.instance(context);
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        
    }

    /** Initializes assertionAdder and proverToUse and translates the argument */
    public void check(JCTree tree) {
        this.verbose = escdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
                || utils.jmlverbose >= Utils.JMLVERBOSE;
        this.assertionAdder = new JmlAssertionAdder(context, true, false);
        try {
            // We convert the whole tree first
        	assertionAdder.convert(tree); // get at the converted tree through the map
        	// And then we walk the tree to see which items are to be proved
        	tree.accept(this);
        } catch (PropagatedException | Main.JmlCanceledException e) {
        	// Canceled
    		Main.instance(context).canceled = true;
    		count(IProverResult.ERROR);
    		throw e;
        } catch (Exception e) {
            // No further error messages needed - FIXME - is this true?
            count(IProverResult.ERROR);
            log.error("jml.internal","Should not be catching an exception in JmlEsc.check: "+ e.toString());
        } catch (Throwable e) {
            // No further error messages needed - FIXME - is this true?
            count(IProverResult.ERROR);
            log.error("jml.internal","Should not be catching a Java error in JmlEsc.check: "+ e.toString());
        }
    }
    
    /** Visit a class definition */
    @Override
    public void visitClassDef(JCClassDecl node) {
        Main.instance(context).pushOptions(node.mods);

        // The super class takes care of visiting all the methods
        utils.progress(0,1,"Proving methods in " + utils.classQualifiedName(node.sym) ); //$NON-NLS-1$
        long classStart = System.currentTimeMillis();
        boolean doDefsInSortedOrder = true;
        if (doDefsInSortedOrder && !Utils.testingMode) { // Don't sort in tests because too many golden outputs were created before sorting
            scan(node.mods);
            scan(node.typarams);
            scan(node.extending);
            scan(node.implementing);
            JCTree[] arr = node.defs.toArray(new JCTree[node.defs.size()]);
            Arrays.sort(arr, new java.util.Comparator<JCTree>() { public int compare(JCTree o, JCTree oo) { 
                Name n = o instanceof JCClassDecl ? ((JCClassDecl)o).name : o instanceof JCMethodDecl ? ((JCMethodDecl)o).getName() : null;
                Name nn = oo instanceof JCClassDecl ? ((JCClassDecl)oo).name : oo instanceof JCMethodDecl ? ((JCMethodDecl)oo).getName() : null;
                return n == nn ? 0 : n == null ? -1 : nn == null ? 1 : n.toString().compareToIgnoreCase(nn.toString());
            	} });
            for (JCTree d: arr) {
            	scan(d);
            }
        } else {
            super.visitClassDef(node);
        }
        long classDuration = System.currentTimeMillis() - classStart;
        utils.progress(0,1,"Completed proving methods in " + utils.classQualifiedName(node.sym) +  //$NON-NLS-1$
                (Utils.testingMode ? "" : String.format(" [%4.2f secs]", (classDuration/1000.0)))); //$NON-NLS-1$
        Main.instance(context).popOptions();
    }
    
    /** When we visit a method declaration, we translate and prove the method;
     * we do not walk into the method any further from this call, only through
     * the translation mechanism.  
     */
    @Override
    public void visitMethodDef(@NonNull JCMethodDecl decl) {
        Main.instance(context).pushOptions(decl.mods);
        IProverResult res = null;
        if (decl.body == null) return; // FIXME What could we do with model methods or interfaces, if they have specs - could check that the preconditions are consistent
        if (!(decl instanceof JmlMethodDecl)) {
            JCDiagnostic d = (log.factory().warning(log.currentSource(), decl.pos(), "jml.internal","Unexpected non-JmlMethodDecl in JmlEsc - not checking " + utils.qualifiedMethodSig(decl.sym)));
            log.report(d);
            //log.warning(decl.pos(),"jml.internal","Unexpected non-JmlMethodDecl in JmlEsc - not checking " + utils.qualifiedMethodSig(decl.sym)); //$NON-NLS-2$
            res = new ProverResult("",ProverResult.ERROR,decl.sym).setOtherInfo(d);
            return;
        }
        JmlMethodDecl methodDecl = (JmlMethodDecl)decl;

        if (skip(methodDecl)) {
            markMethodSkipped(methodDecl," (excluded by skipesc)"); //$NON-NLS-1$
            return;
        }

        if (!filter(methodDecl)) {
            markMethodSkipped(methodDecl," (excluded by -method)"); //$NON-NLS-1$ // FIXME excluded by -method or -exclude
            return;
        }

        // Do any nested classes and methods first (which will recursively call
        // this method)
        super.visitMethodDef(methodDecl);

        try {
    	    res = doMethod(methodDecl);
        } catch (PropagatedException e) {
            IAPI.IProofResultListener proofResultListener = context.get(IAPI.IProofResultListener.class);
            if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, new ProverResult("",IProverResult.CANCELLED,methodDecl.sym));
            throw e;
        }
        Main.instance(context).popOptions();
        return;        
    }
    
    public static boolean skip(JmlMethodDecl methodDecl) {
        if (methodDecl.mods != null) {
            for (JCTree.JCAnnotation a : methodDecl.mods.annotations) {
                if (a != null && a.type.toString().equals("org.jmlspecs.annotation.SkipEsc")) { // FIXME - do this without converting to string
                    return true;
                }
            }
        }
        return false;
    }
    
    // FIXME - perhaps shoud not be in JmlEsc
    public static boolean skipRac(JmlMethodDecl methodDecl) {
        if (methodDecl.mods != null) {
            for (JCTree.JCAnnotation a : methodDecl.mods.annotations) {
                if (a != null && a.type.toString().equals("org.jmlspecs.annotation.SkipRac")) { // FIXME - do this without converting to string
                    return true;
                }
            }
        }
        return false;
    }
    
    public IProverResult markMethodSkipped(JmlMethodDecl methodDecl, String reason) {
        if (JmlOption.isOption(context, JmlOption.SKIPPED)) utils.progress(1,1,"Skipping proof of " + utils.qualifiedMethodSig(methodDecl.sym) + reason); //$NON-NLS-1$ //$NON-NLS-2$
        
        // FIXME - this is all a duplicate from MethodProverSMT
        IProverResult.IFactory factory = new IProverResult.IFactory() {
            @Override
            public IProverResult makeProverResult(MethodSymbol msym, String prover, IProverResult.Kind kind, java.util.Date start) {
                ProverResult pr = new ProverResult(prover,kind,msym);
                pr.methodSymbol = msym;
                if (start != null) {
                    pr.accumulateDuration((pr.timestamp().getTime()-start.getTime())/1000.);
                    pr.setTimestamp(start);
                }
                return pr;
            }
        };
        IProverResult res = factory.makeProverResult(methodDecl.sym,"",IProverResult.SKIPPED,new java.util.Date());
        IAPI.IProofResultListener proofResultListener = context.get(IAPI.IProofResultListener.class);
        if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, res);
        count(IProverResult.SKIPPED);
        return res;
    }
    
    /** Returns the prover specified by the options. */
    public String pickProver() {
        // Pick a prover to use
        String proverToUse = JmlOption.value(context,JmlOption.PROVER);
        if (proverToUse == null || proverToUse.isEmpty()) proverToUse = Options.instance(context).get(Strings.defaultProverProperty);
        if (proverToUse == null || proverToUse.isEmpty() || proverToUse.equals("z3")) {
            proverToUse = "z3_4_3";
        }
        return proverToUse;
    }
    
    // FIXME _ need synchronizatipon on this field
    MethodProverSMT currentMethodProver = null;

    public void abort() {
        if (currentMethodProver != null) currentMethodProver.abort();
    }
    
    /** Do the actual work of proving the method */
    protected IProverResult doMethod(@NonNull JmlMethodDecl methodDecl) {
        boolean printPrograms = this.verbose || JmlOption.includes(context, JmlOption.SHOW, "translated");
        boolean printSMT = this.verbose || JmlOption.includes(context, JmlOption.SHOW, "smt");
        
        if (skip(methodDecl)) {
            return markMethodSkipped(methodDecl," (because of SkipEsc annotation)");
        }
        
        String proverToUse = pickProver();
        
        utils.progress(0,1,"Starting proof of " + utils.qualifiedMethodSig(methodDecl.sym) + " with prover " + (Utils.testingMode ? "!!!!" : proverToUse)); //$NON-NLS-1$ //$NON-NLS-2$
        long methodStart = System.currentTimeMillis();
        log.resetRecord();
//        int prevErrors = log.nerrors;

        IAPI.IProofResultListener proofResultListener = context.get(IAPI.IProofResultListener.class);
        if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, new ProverResult(proverToUse,IProverResult.RUNNING,methodDecl.sym));

        // The code in this method decides whether to attempt a proof of this method.
        // If so, it sets some parameters and then calls proveMethod
        
        boolean isConstructor = methodDecl.sym.isConstructor();
        boolean doEsc = ((methodDecl.mods.flags & (Flags.SYNTHETIC|Flags.ABSTRACT|Flags.NATIVE)) == 0);
            // TODO: Could check that abstract or native methods have consistent specs

        // Don't do ESC on the constructor of Object
        // FIXME - why?  (we don't have the source anyway, so how would we get here?)
        if (methodDecl.sym.owner == syms.objectType.tsym && isConstructor) doEsc = false;
        if (!doEsc) return null; // FIXME - SKIPPED?

        // print the body of the method to be proved
        if (printPrograms) {
            PrintWriter noticeWriter = log.getWriter(WriterKind.NOTICE);
            noticeWriter.println(Strings.empty);
            noticeWriter.println("--------------------------------------"); //$NON-NLS-1$
            noticeWriter.println(Strings.empty);
            noticeWriter.println("STARTING PROOF OF " + utils.qualifiedMethodSig(methodDecl.sym)); //$NON-NLS-1$
            noticeWriter.println(JmlPretty.write(methodDecl.body));
        }
        
        IProverResult res = null;
        try {
            if (JmlOption.isOption(context, JmlOption.BOOGIE)) {
                res = new MethodProverBoogie(this).prove(methodDecl);
            } else {
                currentMethodProver = new MethodProverSMT(this);
                res = currentMethodProver.prove(methodDecl,proverToUse);
                currentMethodProver = null;
            }
            long duration = System.currentTimeMillis() - methodStart;
            utils.progress(1,1,"Completed proof of " + utils.qualifiedMethodSig(methodDecl.sym)  //$NON-NLS-1$ 
                    + " with prover " + (Utils.testingMode ? "!!!!" : proverToUse)  //$NON-NLS-1$ 
                    + " - "
                    + (  res.isSat() ? "with warnings" 
                       : res.result() == IProverResult.UNSAT ? "no warnings"
                               : res.result().toString())
                    + (Utils.testingMode ? "" : String.format(" [%4.2f secs]", (duration/1000.0)))
                    );
            count(res.result());
            
//            if (log.nerrors != prevErrors) {
//                res = new ProverResult(proverToUse,IProverResult.ERROR,methodDecl.sym);
//            }

        } catch (Main.JmlCanceledException | PropagatedException e) {
            res = new ProverResult(proverToUse,ProverResult.CANCELLED,methodDecl.sym); // FIXME - I think two ProverResult.CANCELLED are being reported
           // FIXME - the following will throw an exception because progress checks whether the operation is cancelled
            utils.progress(1,1,"Proof CANCELLED of " + utils.qualifiedMethodSig(methodDecl.sym)  //$NON-NLS-1$ 
            + " with prover " + (Utils.testingMode ? "!!!!" : proverToUse)  //$NON-NLS-1$ 
            + " - exception"
            );
            throw (e instanceof Main.JmlCanceledException) ? new PropagatedException(e) : e;
        } catch (Throwable e) {
            JCDiagnostic d;
            if (e instanceof SMTTranslator.JmlBVException) {
                d = log.factory().error(log.currentSource(), methodDecl, "jml.message", "Proof aborted because bit-vector operations are not supported. Use option -escBV=true");
            } else {
                d = log.factory().error(log.currentSource(), null, "jml.internal","Prover aborted with exception: " + e.toString());
                e.printStackTrace(System.out);
            }
            log.report(d);
            count(IProverResult.ERROR);

            res = new ProverResult(proverToUse,ProverResult.ERROR,methodDecl.sym).setOtherInfo(d);
            //log.error("jml.internal","Prover aborted with exception: " + e.getMessage());
            utils.progress(1,1,"Proof ABORTED of " + utils.qualifiedMethodSig(methodDecl.sym)  //$NON-NLS-1$ 
                    + " with prover " + (Utils.testingMode ? "!!!!" : proverToUse)  //$NON-NLS-1$ 
                    + " - exception"
                    );
            // FIXME - add a message? use a factory?
        } finally {
        	if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, res);
        	if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, new ProverResult(proverToUse,IProverResult.COMPLETED,methodDecl.sym));
        }
        return res;
    }
        
    /** Return true if the method is to be checked, false if it is to be skipped.
     * A warning that the method is being skipped is issued if it is being skipped
     * and the verbosity is high enough.
     * */
    public boolean filter(JCMethodDecl methodDecl) {
        String fullyQualifiedName = utils.qualifiedName(methodDecl.sym);
        String simpleName = methodDecl.name.toString();
        if (methodDecl.sym.isConstructor()) {
            String constructorName = methodDecl.sym.owner.name.toString();
            fullyQualifiedName = fullyQualifiedName.replace("<init>", constructorName);
            simpleName = simpleName.replace("<init>", constructorName);
        }
        String fullyQualifiedSig = utils.qualifiedMethodSig(methodDecl.sym);

        String excludes = JmlOption.value(context,JmlOption.EXCLUDE);
        if (excludes != null && !excludes.isEmpty()) {
            String[] splits = excludes.contains("(") || excludes.contains(";") ? excludes.split(";") : excludes.split(",");
            for (String exclude: splits) { //$NON-NLS-1$
                if (fullyQualifiedName.equals(exclude) ||
                        fullyQualifiedSig.equals(exclude) ||
                        simpleName.equals(exclude)) {
                    if (utils.jmlverbose > Utils.PROGRESS)
                        log.getWriter(WriterKind.NOTICE).println("Skipping " + fullyQualifiedName + " because it is excluded by " + exclude); //$NON-NLS-1$ //$NON-NLS-2$
                    return false;
                }
                try {
                    if (Pattern.matches(exclude,fullyQualifiedName)) {
                        if (utils.jmlverbose > Utils.PROGRESS)
                            log.getWriter(WriterKind.NOTICE).println("Skipping " + fullyQualifiedName + " because it is excluded by " + exclude); //$NON-NLS-1$ //$NON-NLS-2$
                        return false;
                    }
                } catch(PatternSyntaxException e) {
                    // The methodToDo can be a regular string and does not
                    // need to be legal Pattern expression
                    // skip
                }
            }
        }

        String methodsToDo = JmlOption.value(context,JmlOption.METHOD);
        if (methodsToDo != null && !methodsToDo.isEmpty()) {
            match: {
                if (fullyQualifiedSig.equals(methodsToDo)) break match; // A hack to allow at least one signature-containing item in the methods list
                String[] splits = methodsToDo.contains("(") || methodsToDo.contains(";") ? methodsToDo.split(";") : methodsToDo.split(",");
                for (String methodToDo: splits) { //$NON-NLS-1$ 
                	methodToDo = methodToDo.trim();
                	if (methodToDo.isEmpty()) continue;
                	// Match if methodToDo
                	//    is the full FQN
                	//    is just the name of the method
                	//    contains a "." character before a "(" and is the same as the FQ signature
                	//    does not contain a "." character before a "(" and is the tail of the FQ signature
                    if (fullyQualifiedName.equals(methodToDo) ||
                            methodToDo.equals(simpleName) ||
                            ( methodToDo.contains(".") && methodToDo.contains("(") && methodToDo.indexOf(".") > methodToDo.indexOf("(") ? fullyQualifiedSig.equals(methodToDo) : fullyQualifiedSig.endsWith(methodToDo))) {
                        break match;
                    }
                    try {
                        // Also check whether methodToDo, interpreted as a regular expression
                        // matches either the signature or the name
                        if (Pattern.matches(methodToDo,fullyQualifiedSig)) break match;
                        if (Pattern.matches(methodToDo,fullyQualifiedName)) break match;
                    } catch(PatternSyntaxException e) {
                        // The methodToDo can be a regular string and does not
                        // need to be legal Pattern expression
                        // skip
                        int x = 0;
                    }
                }
                if (utils.jmlverbose > Utils.PROGRESS) {
                    log.getWriter(WriterKind.NOTICE).println("Skipping " + fullyQualifiedName + " because it does not match " + methodsToDo);  //$NON-NLS-1$//$NON-NLS-2$
                }
                return false;
            }
        }
        
        return true;
    }
    
    public Map<IProverResult.Kind,Integer> counts = new HashMap<>();
    
    private long startTime;
    
    public void initCounts() {
        counts = new HashMap<>();
        startTime = System.currentTimeMillis();
    }
    
    public void count(IProverResult.Kind r) {
        counts.put(r,  value(r) + 1);
    }
    
    public int value(IProverResult.Kind r) {
        Integer i = counts.get(r);
        return i == null ? 0 : i;
    }
    
    public String reportCounts() {
        StringBuilder s = new StringBuilder();
        int t = 0; int tt;
        s.append("Summary:" + Strings.eol);
        s.append("  Valid:      " + (tt=value(IProverResult.UNSAT)) + Strings.eol);
        t += tt;
        s.append("  Invalid:    " + (tt=value(IProverResult.SAT)+value(IProverResult.POSSIBLY_SAT)+value(IProverResult.UNKNOWN)) + Strings.eol);
        t += tt;
        s.append("  Infeasible: " + (tt=value(IProverResult.INFEASIBLE)) + Strings.eol);
        t += tt;
        s.append("  Timeout:    " + (tt=value(IProverResult.TIMEOUT)) + Strings.eol);
        t += tt;
        s.append("  Error:      " + (tt=value(IProverResult.ERROR)) + Strings.eol);
        t += tt;
        s.append("  Skipped:    " + (tt=value(IProverResult.SKIPPED)) + Strings.eol);
        t += tt;
        s.append(" TOTAL:       " + t + Strings.eol);
        long duration = System.currentTimeMillis() - startTime;
        s.append(" DURATION: " + String.format("%12.1f",(duration/1000.0)) + " secs" + Strings.eol);
        return s.toString();
    }
    
//    // FIXME - move these away from being globals
//    
//    static public IProverResult mostRecentProofResult = null;
    
    
}

