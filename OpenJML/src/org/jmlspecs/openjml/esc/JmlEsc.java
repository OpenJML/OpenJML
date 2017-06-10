/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.IAPI;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
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
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
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
    
    /** The prover to use  - initialized here and then used in visitMethods */
    protected /*@NonNull*/ String proverToUse;
    
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
        	assertionAdder.convert(tree); // get at the converted tree through the map
        	proverToUse = pickProver();
        	tree.accept(this);
        } catch (Exception e) {
        	// No further error messages needed - FIXME - is this true?
            log.error("jml.internal","Should not be catching an exception in JmlEsc.check");
        }
    }
    
    /** Returns the prover specified by the options. */
    public String pickProver() {
        // Pick a prover to use
        String proverToUse = JmlOption.value(context,JmlOption.PROVER);
        if (proverToUse == null) proverToUse = Options.instance(context).get(Strings.defaultProverProperty);
        if (proverToUse == null) {
            proverToUse = "z3_4_4";
        }
        return proverToUse;
    }
    
    /** Visit a class definition */
    @Override
    public void visitClassDef(JCClassDecl node) {
        Main.instance(context).pushOptions(node.mods);
        if (node.sym.isInterface()) return;  // Nothing to verify in an interface
            // TODO: not so - could check that specs are consistent
        // The super class takes care of visiting all the methods
        utils.progress(1,1,"Proving methods in " + utils.classQualifiedName(node.sym) ); //$NON-NLS-1$
        super.visitClassDef(node);
        utils.progress(1,1,"Completed proving methods in " + utils.classQualifiedName(node.sym) ); //$NON-NLS-1$
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
            log.warning(decl.pos(),"jml.internal","Unexpected non-JmlMethodDecl in JmlEsc - not checking " + utils.qualifiedMethodSig(decl.sym)); //$NON-NLS-2$
            res = new ProverResult(proverToUse,ProverResult.ERROR,decl.sym);
            return;
        }
        JmlMethodDecl methodDecl = (JmlMethodDecl)decl;

        if (skip(methodDecl)) {
            markMethodSkipped(methodDecl," (excluded by skipesc)"); //$NON-NLS-1$
            return;
        }
        // Do any nested classes and methods first (which will recursively call
        // this method)
        super.visitMethodDef(methodDecl);

        if (!filter(methodDecl)) {
            markMethodSkipped(methodDecl," (excluded by -method)"); //$NON-NLS-1$ 
            return;
        }
    	res = doMethod(methodDecl);
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
        utils.progress(1,1,"Skipping proof of " + utils.qualifiedMethodSig(methodDecl.sym) + reason); //$NON-NLS-1$ //$NON-NLS-2$
        
        // FIXME - this is all a duplicate from MethodProverSMT
        IProverResult.IFactory factory = new IProverResult.IFactory() {
            @Override
            public IProverResult makeProverResult(MethodSymbol msym, String prover, IProverResult.Kind kind, java.util.Date start) {
                ProverResult pr = new ProverResult(prover,kind,msym);
                pr.methodSymbol = msym;
                if (start != null) {
                    pr.setDuration((pr.timestamp().getTime()-start.getTime())/1000.);
                    pr.setTimestamp(start);
                }
                return pr;
            }
        };
        IProverResult res = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.SKIPPED,new java.util.Date());
        IAPI.IProofResultListener proofResultListener = context.get(IAPI.IProofResultListener.class);
        if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, res);
        return res;
    }
    
    /** Do the actual work of proving the method */
    protected IProverResult doMethod(@NonNull JmlMethodDecl methodDecl) {
        boolean printPrograms = this.verbose || JmlOption.isOption(context, JmlOption.SHOW);

        if (skip(methodDecl)) {
            return markMethodSkipped(methodDecl," (because of SkipEsc annotation)");
        }
        utils.progress(1,1,"Starting proof of " + utils.qualifiedMethodSig(methodDecl.sym) + " with prover " + (Utils.testingMode ? "!!!!" : proverToUse)); //$NON-NLS-1$ //$NON-NLS-2$
        
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
        
        IProverResult res;
        try {
            if (JmlOption.isOption(context, JmlOption.BOOGIE)) {
                res = new MethodProverBoogie(this).prove(methodDecl);
            } else {
                res = new MethodProverSMT(this).prove(methodDecl,proverToUse);
            }
            utils.progress(1,1,"Completed proof of " + utils.qualifiedMethodSig(methodDecl.sym)  //$NON-NLS-1$ 
                    + " with prover " + (Utils.testingMode ? "!!!!" : proverToUse)  //$NON-NLS-1$ 
                    + " - "
                    + (  res.isSat() ? "with warnings" 
                       : res.result() == IProverResult.UNSAT ? "no warnings"
                               : res.result().toString())
                    );
        } catch (Exception e) {
            log.error("jml.internal","Prover aborted with exception: " + e.getMessage());
            utils.progress(1,1,"Proof ABORTED of " + utils.qualifiedMethodSig(methodDecl.sym)  //$NON-NLS-1$ 
                    + " with prover " + (Utils.testingMode ? "!!!!" : proverToUse)  //$NON-NLS-1$ 
                    + " - exception"
                    );
            res = new ProverResult(proverToUse,ProverResult.ERROR,methodDecl.sym);
            // FIXME - add a message? use a factory?
        }
        
        //proverResults.put(methodDecl.sym,res);
        IAPI.IProofResultListener proofResultListener = context.get(IAPI.IProofResultListener.class);
        if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, res);
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

        String methodsToDo = JmlOption.value(context,JmlOption.METHOD);
        if (methodsToDo != null) {
            match: {
                if (fullyQualifiedSig.equals(methodsToDo)) break match; // A hack to allow at least one signature-containing item in the methods list
                for (String methodToDo: methodsToDo.split(",")) { //$NON-NLS-1$  //FIXME - this does not work when the methods list contains signatures containing commas
                    if (fullyQualifiedName.equals(methodToDo) ||
                            methodToDo.equals(simpleName) ||
                            fullyQualifiedSig.equals(methodToDo)) {
                        break match;
                    }
                    try {
                        if (Pattern.matches(methodToDo,fullyQualifiedName)) break match;
                    } catch(PatternSyntaxException e) {
                        // The methodToDo can be a regular string and does not
                        // need to be legal Pattern expression
                        // skip
                    }
                }
                if (utils.jmlverbose > Utils.PROGRESS) {
                    log.getWriter(WriterKind.NOTICE).println("Skipping " + fullyQualifiedName + " because it does not match " + methodsToDo);  //$NON-NLS-1$//$NON-NLS-2$
                }
                return false;
            }
        }
        
        String excludes = JmlOption.value(context,JmlOption.EXCLUDE);
        if (excludes != null) {
            for (String exclude: excludes.split(",")) { //$NON-NLS-1$
                if (fullyQualifiedName.equals(exclude) ||
                        fullyQualifiedSig.equals(exclude) ||
                        simpleName.equals(exclude) ||
                        Pattern.matches(exclude,fullyQualifiedName)) {
                    if (utils.jmlverbose > Utils.PROGRESS)
                        log.getWriter(WriterKind.NOTICE).println("Skipping " + fullyQualifiedName + " because it is excluded by " + exclude); //$NON-NLS-1$ //$NON-NLS-2$
                    return false;
                }
            }
        }

        return true;
    }
    
//    // FIXME - move these away from being globals
//    
//    static public IProverResult mostRecentProofResult = null;
    
    
}

