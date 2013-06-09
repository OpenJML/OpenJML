/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.provers.YicesProver;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
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
    
    /** The compilation context, needed to get common tools, but unique to this compilation run*/
    @NonNull Context context;

    /** Used to obtain cached symbols, such as basic types */
    @NonNull Symtab syms;
    
    /** The database of JML specifications for methods, classes, fields, ... */
    @NonNull JmlSpecs specs;
    
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
    
//    /** The prover instance most recently used */
//    static public IProver mostRecentProver = null; 
    
    /** The most recent program whose proof was attempted. */ // TODO - REVIEW
    static public BasicProgram mostRecentProgram = null;
    
    /** A map that stores all the proof results of proofs initiated through this JmlEsc object. */
    public Map<MethodSymbol,IProverResult> proverResults = new HashMap<MethodSymbol,IProverResult>();
    
    /** The prover to use  - initialized here and then used in visitMethods */
    protected /*@NonNull*/ String proverToUse;
    
    /** The JmlEsc constructor, which initializes all the tools and other fields. */
    public JmlEsc(Context context) {
        this.context = context;
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        
        escdebug = escdebug || utils.jmlverbose >= Utils.JMLDEBUG; // FIXME - clean this up?
        this.verbose = escdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
            || utils.jmlverbose >= Utils.JMLVERBOSE;
    }
    
    public void check(JCTree tree) {
        //new JmlAssertionAdder.PositionChecker().check(log,tree);
        this.assertionAdder = new JmlAssertionAdder(context, true,false);
        assertionAdder.convert(tree); // get at the converted tree through the map
        //log.noticeWriter.println("TRANSLATED CHECK");
        //new JmlAssertionAdder.PositionChecker().check(log,assertionAdder.bimap.getf(tree));
        proverToUse = pickProver();
        tree.accept(this);
    }
    
    /** Returns the prover specified by the options. */
    public String pickProver() {
        // Pick a prover to use
        String proverToUse = JmlOption.value(context,JmlOption.PROVER);
        if (proverToUse == null) proverToUse = Options.instance(context).get(Strings.defaultProverProperty);
        if (proverToUse == null) {
            proverToUse = "z3_4_3";
        }
        return proverToUse;
    }
    
    /** Returns the prover exec specified by the options */
    public String pickProverExec(String proverToUse) {
        String exec = JmlOption.value(context, JmlOption.PROVEREXEC);
        if (exec == null) exec = JmlOption.value(context, Strings.proverPropertyPrefix + proverToUse);
        return exec;
    }

    /** Visit a class definition */
    public void visitClassDef(JCClassDecl node) {
        if (node.sym.isInterface()) return;  // Nothing to verify in an interface
            // TODO: not so - could check that specs are consistent
        // The super class takes care of visiting all the methods
        progress(1,1,"Proving methods in " + node.sym.getQualifiedName() ); //$NON-NLS-1$
        super.visitClassDef(node);
        progress(1,1,"Completed proving methods in " + node.sym.getQualifiedName() ); //$NON-NLS-1$
    }
    
    /** When we visit a method declaration, we translate and prove the method;
     * we do not walk into the method any further from this call, only through
     * the translation mechanism.  
     */
    public void visitMethodDef(@NonNull JCMethodDecl decl) {
        if (!(decl instanceof JmlMethodDecl)) {
            log.warning(decl.pos(),"jml.internal","Unexpected non-JmlMethodDecl in JmlEsc - not checking " + utils.qualifiedMethodSig(decl.sym)); //$NON-NLS-2$
            return;
        }
        JmlMethodDecl methodDecl = (JmlMethodDecl)decl;

        // Do any nested classes and methods first (which will recursively call
        // this method)
        super.visitMethodDef(methodDecl);

        if (filter(methodDecl)) {
        	doMethod(methodDecl);
        }
                
    }
    
    protected IProverResult doMethod(@NonNull JCMethodDecl methodDecl) {
        boolean print = this.verbose;
        boolean printPrograms = print || JmlOption.isOption(context, JmlOption.SHOW);

        progress(1,1,"Starting proof of " + utils.qualifiedMethodSig(methodDecl.sym) + " with prover " + proverToUse); //$NON-NLS-1$ //$NON-NLS-2$
        
        // print the body of the method to be proved
        if (printPrograms) {
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("--------------------------------------"); //$NON-NLS-1$
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("STARTING PROOF OF " + utils.qualifiedMethodSig(methodDecl.sym)); //$NON-NLS-1$
            log.noticeWriter.println(JmlPretty.write(methodDecl.body));
        }
        
        // The code in this method decides whether to attempt a proof of this method.
        // If so, it sets some parameters and then calls proveMethod
        // We don't check abstract or native methods (no source)
        // nor synthetic methods.
        
        boolean isConstructor = methodDecl.sym.isConstructor();
        boolean doEsc = ((methodDecl.mods.flags & (Flags.SYNTHETIC|Flags.ABSTRACT|Flags.NATIVE)) == 0);
            // TODO: Could check that abstract or native methods have consistent specs
        
        // Don't do ESC on the constructor of Object
        // FIXME - why?  (we don't have the source anyway, so how would we get here?)
        if (methodDecl.sym.owner == syms.objectType.tsym && isConstructor) doEsc = false;
        if (!doEsc) return null; // FIXME - SKIPPED?

        
        JmlMethodDecl mdecl = (JmlMethodDecl)methodDecl;
        IProverResult res;
        if (JmlOption.isOption(context, JmlOption.BOOGIE)) {
            res = new MethodProverBoogie(this).prove(mdecl);
        } else {
            res = new MethodProverSMT(this).prove(mdecl);
        }
        
        progress(1,1,"Completed proof of " + utils.qualifiedMethodSig(methodDecl.sym)  //$NON-NLS-1$ 
                + " with prover " + proverToUse  //$NON-NLS-1$ 
                + (res.isSat() ? " - with warnings" : " - no warnings")  //$NON-NLS-1$ //$NON-NLS-2$
                );
        proverResults.put(methodDecl.sym,res);
        return res;
    }
        
    /** Reports progress to the registered IProgressListener; also checks if
     * the progress listener has received a user-cancellation, in which case
     * this method throws an exception to terminate processing
     * @param ticks amount of work to report
     * @param level level of the message (lower levels are more likely to be printed)
     * @param message the progress message
     */
    public void progress(int ticks, int level, String message) {
        org.jmlspecs.openjml.Main.IProgressListener pr = context.get(org.jmlspecs.openjml.Main.IProgressListener.class);
        boolean cancelled = pr == null ? false : pr.report(ticks,level,message);
        if (cancelled) {
            throw new PropagatedException(new Main.JmlCanceledException("ESC operation cancelled"));
        }
    }
    
    /** Return true if the method is to be checked, false if it is to be skipped.
     * A warning that the method is being skipped is issued if it is being skipped
     * and the verbosity is high enough.
     * */
    public boolean filter(JCMethodDecl methodDecl) {
        String fullyQualifiedName = utils.qualifiedMethodName(methodDecl.sym);
        if (methodDecl.sym.isConstructor()) fullyQualifiedName = fullyQualifiedName.replace("<init>", methodDecl.sym.owner.name.toString());
        String fullyQualifiedSig = utils.qualifiedMethodSig(methodDecl.sym);

        String methodsToDo = JmlOption.value(context,JmlOption.METHOD);
        if (methodsToDo != null) {
            match: {
                for (String methodToDo: methodsToDo.split(",")) { //$NON-NLS-1$
                    if (fullyQualifiedName.equals(methodToDo) ||
                            methodToDo.equals(methodDecl.name.toString()) ||
                            Pattern.matches(methodToDo,fullyQualifiedName) ||
                            fullyQualifiedSig.equals(methodToDo)) {
                        break match;
                    }
                }
                if (Utils.instance(context).jmlverbose > Utils.PROGRESS) {
                    log.noticeWriter.println("Skipping " + fullyQualifiedName + " because it does not match " + methodsToDo);  //$NON-NLS-1$//$NON-NLS-2$
                }
                return false;
            }
        }
        
        String excludes = JmlOption.value(context,JmlOption.EXCLUDE);
        if (excludes != null) {
            for (String exclude: excludes.split(",")) { //$NON-NLS-1$
                if (fullyQualifiedName.equals(exclude) ||
                        fullyQualifiedSig.equals(exclude) ||
                        exclude.equals(methodDecl.name.toString()) ||
                        Pattern.matches(exclude,fullyQualifiedName)) {
                    if (Utils.instance(context).jmlverbose > Utils.PROGRESS)
                        log.noticeWriter.println("Skipping " + fullyQualifiedName + " because it is excluded by " + exclude); //$NON-NLS-1$ //$NON-NLS-2$
                    return false;
                }
            }
        }


//      Pattern doPattern = 
//          null; 
//      //Pattern.compile("escjava[.]ast[.]ArrayRangeRefExpr[.]getTag[(].*"); 
//      //Pattern.compile("escjava[.]sortedProver[.]Lifter[.]FnTerm[.]dump[(].*"); 
//      Pattern[] avoids = {
////             Pattern.compile(".*anonymous.*"),
//
////              Pattern.compile("escjava[.]sortedProver[.]Lifter[.]FnTerm[.]printTo[(].*"), // too much time
////              Pattern.compile("escjava[.]sortedProver[.]Lifter[.]Term[.]toString[(].*"), // too much time
////              Pattern.compile("escjava[.]sortedProver[.]Lifter[.]Term[.]printTo[(].*"), // too much time
////              Pattern.compile("escjava[.]sortedProver[.]Lifter[.]QuantVariableRef[.]printTo[(].*"), // too much time
////              Pattern.compile("escjava[.]sortedProver[.]Lifter[.]FnTerm[.]dump[(].*"), // too much memory
////              Pattern.compile("escjava[.]sortedProver[.]Lifter[.]SortVar[.]toString[(].*"), // too much time
////              Pattern.compile("escjava[.]sortedProver[.]Lifter[.]warn[(].*"), // failed to write to prover
////              Pattern.compile("escjava[.]sortedProver[.]Lifter[.]convert[(].*"), // failed to write to prover
////              Pattern.compile("escjava[.]sortedProver[.]Lifter[.]newMethod[(].*"), // binary generic
////              Pattern.compile("escjava[.]sortedProver[.]Lifter[.]Lifter[(].*"), // failed to write to prover
////            Pattern.compile("javafe[.]ast[.][a-zA-Z]*[.]getTag[(].*"), // too much time
////              Pattern.compile("javafe[.]ast[.]CompoundName[.]prefix[(].*"), // out of resources
////              Pattern.compile("javafe[.]ast[.]BinaryExpr[.]getStartLoc[(].*"), // out of resources
////              Pattern.compile("javafe[.]ast[.]BinaryExpr[.]postCheck[(].*"), // out of resources
////              Pattern.compile("javafe[.]ast[.]BinaryExpr[.]accept[(].*"), // out of resources
////              Pattern.compile("javafe[.]Options[.]processOption[(].*"), // out of resources
////              Pattern.compile("javafe[.]parser[.]Token[.]ztoString[(].*"), // out of resources
////
////              Pattern.compile("javafe[.]ast[.].*[.]toString[(].*"), // out of resources
////              Pattern.compile("escjava[.]AnnotationHandler[.]NestedPragmaParser[.]parseAlsoSeq[(].*"), // out of resources
////              Pattern.compile("escjava[.]AnnotationHandler[.]NestedPragmaParser[.]parseSeq[(].*"), // out of resources
//      
//      };
//      if (doPattern != null) {
//          if (!doPattern.matcher(fully_qualified_name).matches()) return;//{log.noticeWriter.println("skipping " + name); return; }
//      }
//      for (Pattern avoid: avoids) {
//          if (avoid.matcher(fully_qualified_name).matches()) {log.noticeWriter.println("skipping " + fully_qualified_name); return; }
//      }


        return true;
    }
    
    // FIXME - move these away from being globals
    
    static public IProverResult mostRecentProofResult = null;
    
    
}

