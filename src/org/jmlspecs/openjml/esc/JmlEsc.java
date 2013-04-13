/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.io.Writer;
import java.util.*;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.esc.BasicBlocker.Counter;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.proverinterface.Counterexample;
import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICoreIds;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;
import org.jmlspecs.openjml.proverinterface.IProverResult.Span;
import org.jmlspecs.openjml.proverinterface.ProverException;
import org.jmlspecs.openjml.proverinterface.ProverResult;
import org.jmlspecs.openjml.provers.AbstractProver;
import org.jmlspecs.openjml.provers.CVC3Prover;
import org.jmlspecs.openjml.provers.SimplifyProver;
import org.jmlspecs.openjml.provers.YicesProver;
import org.jmlspecs.openjml.utils.ExternalProcess;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IResponse;
import org.smtlib.IResponse.IError;
import org.smtlib.ISolver;
import org.smtlib.IVisitor.VisitorException;
import org.smtlib.SMT;
import org.smtlib.sexpr.ISexpr;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCConditional;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.*;

/**
 * This class is the main driver for executing ESC on a Java/JML AST. It
 * formulates the material to be proved, initiates the proofs, and obtains and
 * reports the results. The class is also a TreeScanner so that it can easily
 * walk the tree to find all class and method declarations.
 * <P>
 * To use, instantiate an instance of JmlEsc, and then call either visitClassDef
 * or visitMethodDef; various options from JmlOptions will be used. In particular,
 * the -custom and -boogie options affect which implementation of ESC is used,
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
    
    /** The names database */
    @NonNull Names names;
    
    /** The factory for making AST nodes */
    @NonNull JmlTree.JmlFactory factory;
    
    /** The tool to log problem reports */ 
    @NonNull Log log;
    
    /** The OpenJML utilities object */
    @NonNull Utils utils;
    
    /** true if compiler options are set to a verbose mode */
    boolean verbose;
    
    /** Just for debugging esc */
    public static boolean escdebug = false; // May be set externally to enable debugging while testing
    
    /** true if counterexample information is desired */
    boolean showCounterexample;
    
    /** true if counterexample trace information is desired */
    boolean showTrace; // FIXME - need to distinguish computing the trace information (for use in the GUI) vs. printing it out
    
    /** true if trace information with respect to the basic block program is to be output */
    boolean showBBTrace;
    
    /** true if subexpression trace information is desired */
    boolean showSubexpressions;
    
    /** Whether to check that key assumptions are feasible */
    public boolean checkAssumptions = true;

    /** If true, then cross reference information is generated. */ // FIXME - should this just always be on? - need to fix tests
    public boolean cfInfo = false;
    
    /** The assertion adder instance used to translate */
    public JmlAssertionAdder assertionAdder;
    
    /** A map that stores all the proof results of proofs initiated through this JmlEsc object. */
    public Map<MethodSymbol,IProverResult> proverResults = new HashMap<MethodSymbol,IProverResult>();
    
    /** The prover to use  - initialized here and then used in visitMethods */
    protected /*@NonNull*/ String proverToUse;
    
    // FIXME DOCUMENT
    protected Tracer tracer;
    
    /** The JmlEsc constructor, which initializes all the tools and other fields. */
    public JmlEsc(Context context) {
        this.context = context;
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.log = Log.instance(context);
        this.names = Names.instance(context);
        this.factory = JmlTree.Maker.instance(context);
        this.utils = Utils.instance(context);
        
        escdebug = escdebug || utils.jmlverbose >= Utils.JMLDEBUG;
        this.verbose = escdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
            || utils.jmlverbose >= Utils.JMLVERBOSE;
        this.showSubexpressions = this.verbose || JmlOption.isOption(context,JmlOption.SUBEXPRESSIONS);
        this.showTrace = verbose || this.showSubexpressions || JmlOption.isOption(context,JmlOption.TRACE);
        this.showCounterexample = this.showTrace || JmlOption.isOption(context,JmlOption.COUNTEREXAMPLE);
        this.checkAssumptions = !JmlOption.isOption(context,JmlOption.NO_RAC_CHECK_ASSUMPTIONS);
        this.cfInfo = JmlOption.isOption(context,JmlOption.ASSOCINFO);
        this.showBBTrace = verbose;
    }
    
    public void check(JCTree tree) {
        if (!JmlOption.isOption(context,"-custom")) {
            //new JmlAssertionAdder.PositionChecker().check(log,tree);
            this.assertionAdder = new JmlAssertionAdder(context, true,false);
            assertionAdder.convert(tree); // get at the converted tree through the map
            //log.noticeWriter.println("TRANSLATED CHECK");
            //new JmlAssertionAdder.PositionChecker().check(log,assertionAdder.bimap.getf(tree));
        }
        proverToUse = pickProver();
        tree.accept(this); 
    }
    
    /** Returns the prover specified by the options. */
    public String pickProver() {
        // Pick a prover to use
        String proverToUse = JmlOption.value(context,JmlOption.PROVER);
        if (proverToUse == null) proverToUse = Options.instance(context).get(Strings.defaultProverProperty);
        if (proverToUse == null) {
            if (JmlOption.isOption(context,JmlOption.CUSTOM)) proverToUse = YicesProver.NAME;
            else proverToUse = "z3_4_3";
        }
        return proverToUse;
    }
    
    /** Returns the prover exec specified by the options */
    public String pickProverExec(String proverToUse) {
        String exec = JmlOption.value(context, JmlOption.PROVEREXEC);
        if (exec == null) exec = JmlOption.value(context, Strings.proverPropertyPrefix + proverToUse);
        return exec;
    }

    // TODO - turn these into options
    static boolean usePush = true;
    static boolean useRetract = false;
    static boolean useSearch = false;
    static boolean useCoreIds = false;
    static boolean useTree = false;
    int timingTest;

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
    public void visitMethodDef(@NonNull JCMethodDecl methodDecl) {
        if (!(methodDecl instanceof JmlMethodDecl)) {
            log.warning(methodDecl.pos(),"jml.internal","Unexpected non-JmlMethodDecl in JmlEsc - not checking " + methodDecl.sym); //$NON-NLS-2$
            return;
        }

        super.visitMethodDef(methodDecl);

        String fully_qualified_name = utils.qualifiedMethodName(methodDecl.sym) ;

        String methodsToDo = JmlOption.value(context,JmlOption.METHOD);
        if (methodsToDo != null) {
            match: {
                for (String methodToDo: methodsToDo.split(",")) { //$NON-NLS-1$
                    if (fully_qualified_name.equals(methodToDo) ||
                            methodToDo.equals(methodDecl.name.toString()) ||
                            Pattern.matches(methodToDo,fully_qualified_name)) {
                        break match;
                    }
                }
                if (Utils.instance(context).jmlverbose > Utils.QUIET) {
                    log.noticeWriter.println("Skipping " + fully_qualified_name + " because it does not match " + methodsToDo);  //$NON-NLS-1$//$NON-NLS-2$
                    return;
                }
            }
        }
        
        String excludes = JmlOption.value(context,JmlOption.EXCLUDE);
        if (excludes != null) {
            for (String exclude: excludes.split(",")) { //$NON-NLS-1$
                if (fully_qualified_name.equals(exclude) ||
                        exclude.equals(methodDecl.name.toString()) ||
                        Pattern.matches(exclude,fully_qualified_name)) {
                    if (Utils.instance(context).jmlverbose > Utils.QUIET)
                        log.noticeWriter.println("Skipping " + fully_qualified_name + " because it is excluded by " + exclude); //$NON-NLS-1$ //$NON-NLS-2$
                    return;
                }
            }
        }

        doMethod(methodDecl);
                

//        Pattern doPattern = 
//            null; 
//        //Pattern.compile("escjava[.]ast[.]ArrayRangeRefExpr[.]getTag[(].*"); 
//        //Pattern.compile("escjava[.]sortedProver[.]Lifter[.]FnTerm[.]dump[(].*"); 
//        Pattern[] avoids = {
////               Pattern.compile(".*anonymous.*"),
//
////                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]FnTerm[.]printTo[(].*"), // too much time
////                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]Term[.]toString[(].*"), // too much time
////                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]Term[.]printTo[(].*"), // too much time
////                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]QuantVariableRef[.]printTo[(].*"), // too much time
////                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]FnTerm[.]dump[(].*"), // too much memory
////                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]SortVar[.]toString[(].*"), // too much time
////                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]warn[(].*"), // failed to write to prover
////                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]convert[(].*"), // failed to write to prover
////                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]newMethod[(].*"), // binary generic
////                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]Lifter[(].*"), // failed to write to prover
////              Pattern.compile("javafe[.]ast[.][a-zA-Z]*[.]getTag[(].*"), // too much time
////                Pattern.compile("javafe[.]ast[.]CompoundName[.]prefix[(].*"), // out of resources
////                Pattern.compile("javafe[.]ast[.]BinaryExpr[.]getStartLoc[(].*"), // out of resources
////                Pattern.compile("javafe[.]ast[.]BinaryExpr[.]postCheck[(].*"), // out of resources
////                Pattern.compile("javafe[.]ast[.]BinaryExpr[.]accept[(].*"), // out of resources
////                Pattern.compile("javafe[.]Options[.]processOption[(].*"), // out of resources
////                Pattern.compile("javafe[.]parser[.]Token[.]ztoString[(].*"), // out of resources
////
////                Pattern.compile("javafe[.]ast[.].*[.]toString[(].*"), // out of resources
////                Pattern.compile("escjava[.]AnnotationHandler[.]NestedPragmaParser[.]parseAlsoSeq[(].*"), // out of resources
////                Pattern.compile("escjava[.]AnnotationHandler[.]NestedPragmaParser[.]parseSeq[(].*"), // out of resources
//        
//        };
//        if (doPattern != null) {
//            if (!doPattern.matcher(fully_qualified_name).matches()) return;//{log.noticeWriter.println("skipping " + name); return; }
//        }
//        for (Pattern avoid: avoids) {
//            if (avoid.matcher(fully_qualified_name).matches()) {log.noticeWriter.println("skipping " + fully_qualified_name); return; }
//        }

    }
    
    protected void doMethod(@NonNull JCMethodDecl methodDecl) {
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
        if (!doEsc) return;

        

        if (JmlOption.isOption(context, JmlOption.BOOGIE)) {
            proveWithBoogie(methodDecl,proverToUse);
            return;
        }
        if (!JmlOption.isOption(context, JmlOption.CUSTOM)) {
            proveWithSMT(methodDecl,proverToUse);
            return;
        }
        
        // Old custom translation implementation
        // TODO - review all this - have a way to time all checking
        
        boolean doTimingTests = false;
        
        if (escdebug) log.noticeWriter.println(methodDecl.toString()); // print the method

        if (!doTimingTests) {
            timingTest = 0;
            proveMethodOld(methodDecl,proverToUse);
        } else {
            log.noticeWriter.println("METHOD: " + utils.qualifiedMethodName(methodDecl.sym));
            //int[] timingTests = { 3,  1,2,3,4,5,6,7, 8, 1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8};
            //int[] timingTests = {1, 9,10,11,15,16,17,12,13,14,9,10,11,15,16,17,12,13,14,9,10,11,15,16,17,12,13,14 };
            //int[] timingTests = {1, 9,10,11,9,10,11,9,10,11 };
            int[] timingTests = { 1, 11,16, 11, 16, 11,16,11,16,11,16};
            // 0 = normal default running
            // 1 = with assert, no push, with defs, no evidence
            // 2 = with assert, no push, with defs, evidence  // vs. 1 gives cost of generating proverResults
            // 3 = with assert, push, with defs, no evidence  // vs. 1 gives cost of assumption checking by push/pop and assumeChecks
            // 4 = with assert+, no push, with defs, no evidence // vs. 1 gives cost of assumption checking by retract 
            // 5 = with assert, push, with defs, evidence  // vs. 1 gives cost of assumption checking by push/pop and assumeChecks (when wanting evidence for CEs)
            // 6 = with assert+, no push, with defs, evidence // vs. 1 gives cost of assumption checking by retract (when wanting evidence for CEs)
            // 7 = with assert, no push, no defs, no evidence // vs. 1 gives cost of using definitions
            // 8 = with assert, no push, with defs, no evidence // vs. 1 gives cost of using tree form

            // Would like to measure the cost of using/not using definitions -- but some VCs get too big
            
            // UNSAT - all use assertion defs
            // 9 = like 10, but without truncating VC at a false assert
            // 10 = no evidence, with assert, no push, assume checks and defs, repeated checks with assert false
            // 11 = no evidence, with assert, push, assume checks and defs, repeated assume check with pop
            // 12 = no evidence, with assert+, no push, retract, assume checks and defs, repeated assume check with retract
            // 13 = evidence, with assert+, push, assume checks and defs, use core ids else repeated assume check with pop
            // 14 = evidence, with assert+, no push, retract, assume checks and defs, use core ids else repeated assume check with retract
            // 15 = like 11, but with evidence and with repeated checks for any CE
            // 16 = like 15, but with pushing and popping
            // 17 = like 15, but with retracting
            
            for (int ttest : timingTests) {
                timingTest = ttest;
                if (ttest >= 9) continue;
                YicesProver.assertPlus = true;
                JmlEsc.usePush = true;
                JmlEsc.useTree = false;
                BasicBlocker.insertAssumptionChecks = true;
                BasicBlocker.useAssertDefinitions = true;
                BasicBlocker.useAssumeDefinitions = true;
                
                if (timingTest > 0) {
                    YicesProver.assertPlus = timingTest == 4 || timingTest == 6 || timingTest == 12 || timingTest == 13 || timingTest == 14 || timingTest == 17;
                    YicesProver.evidence = timingTest == 2 || timingTest == 5 || timingTest == 6 || timingTest == 13 || timingTest == 14 || timingTest >= 15;
                    JmlEsc.usePush = timingTest == 3 || timingTest == 5 || timingTest == 11 || timingTest == 13 || timingTest == 15 || timingTest == 16;
                    JmlEsc.useRetract = timingTest == 12 || timingTest == 14 || timingTest == 17;
                    JmlEsc.useSearch = timingTest == 15 || timingTest == 16 || timingTest == 17;
                    JmlEsc.useCoreIds = timingTest == 13 || timingTest == 14;
                    BasicBlocker.insertAssumptionChecks = true;
                    BasicBlocker.useAssertDefinitions = timingTest != 7;
                    BasicBlocker.useAssumeDefinitions = timingTest != 7;
                    JmlEsc.useTree = timingTest == 8;
                }
                
                BasicBlocker.useCountedAssumeCheck = timingTest < 13;
                
                proveMethodOld(methodDecl,proverToUse);
            }
        }
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
    
    // FIXME: REVIEW THIS
    /** Perform an ESC check of the method using boogie+Z3 */
    public boolean proveWithBoogie(JCMethodDecl decl, String proverToUse) {
        boolean print = true; //true;
        if (print && decl.name.toString().equals("<init>")) {
            log.noticeWriter.println("SKIPPING PROOF OF " + decl.name);
            return true;
        }

        progress(1,2,"Starting proof of " + decl.sym.owner.getQualifiedName() + "." + decl.sym + " with prover " + proverToUse);
        
        if (print) {
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("--------------------------------------");
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("STARTING PROOF OF " + decl.sym.owner.getQualifiedName() + "." + decl.sym);
            log.noticeWriter.println(JmlPretty.write(decl.body));
        }
        
        JmlMethodDecl tree = (JmlMethodDecl)decl;
        JmlClassDecl currentClassDecl = (JmlClassDecl)JmlEnter.instance(context).getEnv((ClassSymbol)decl.sym.owner).tree;

        // Get the denested specs for the method - FIXME - when might they be null?
        if (tree.sym == null) {
            log.error("jml.internal.notsobad", "Unexpected null symbol for " + decl.name);
        }
        JmlMethodSpecs denestedSpecs = tree.sym == null ? null : specs.getDenestedSpecs(tree.sym);

        JmlAssertionAdder assertionAdder = new JmlAssertionAdder(context,true,false);
        JCBlock newblock = assertionAdder.convertMethodBody(tree,currentClassDecl);
        log.noticeWriter.println(JmlPretty.write(newblock));
        
        BoogieProgram program = new Boogier(context).convertMethodBody(newblock, decl, denestedSpecs, currentClassDecl, assertionAdder);
        String filename = "boogie_" + decl.getName() + ".bpl";
        StringWriter sw = new StringWriter();
        String programString;
        try {
            program.write(sw);
            FileWriter fw = new FileWriter(filename);
            programString = sw.toString();
            fw.append(programString);
            fw.close();
        } catch (IOException e) {
            log.noticeWriter.println("Could not write boogie output file"); // FIXME - error
            return false;
        }
        log.noticeWriter.println(programString);

        String boogie = Options.instance(context).get("openjml.prover.boogie");
        ExternalProcess p = new ExternalProcess(context,null,
                boogie,
                "/nologo",
                "/proverWarnings:1",
                "/coalesceBlocks:0",
                "/removeEmptyBlocks:0",
                filename);
        try {
            p.start();
            int exitVal = p.readToCompletion();
            log.noticeWriter.println("Boogie exit val " + exitVal); // FIXME - guard or delete verbose output
            String out = p.outputString.toString();
            log.noticeWriter.println("OUTPUT: " + out);
            log.noticeWriter.println("ERROR: " + p.errorString.toString());
            if (out.contains("This assertion might not hold")) {
                int k = out.indexOf('(');
                int kk = out.indexOf(',');
                int line = Integer.parseInt(out.substring(k+1,kk));
                k = 0;
                while (--line > 0) k = 1 + programString.indexOf('\n',k);
                kk = 1 + programString.indexOf("\"",programString.indexOf(":reason",k));
                int kkk = programString.indexOf('"',kk);
                String reason = programString.substring(kk,kkk);
                kk = 4 + programString.indexOf(":id",k);
                kkk = programString.indexOf('}',kk);
                String id = programString.substring(kk,kkk);
                JmlStatementExpr assertStat = program.assertMap.get(id);
                Label label = Label.find(reason);
                // FIXME - defensive chjeck assertStat not null
                
                kk = out.lastIndexOf(BasicBlockerParent.RETURN);
                if (kk < 0) kk = out.lastIndexOf(BasicBlockerParent.THROW);
                int terminationPos = 0;
                if (kk >= 0) {
                    kkk = out.lastIndexOf(BasicBlockerParent.blockPrefix,kk) + BasicBlockerParent.blockPrefix.length();
                    try {
                        terminationPos = Integer.parseInt(out.substring(kkk,kk));
                    } catch (NumberFormatException e) {
                        log.noticeWriter.println("NO RETURN FOUND"); // FIXME
                        // continue
                    }
                }
                if (terminationPos == 0) terminationPos = decl.pos;
                JavaFileObject prev = null;
                int pos = assertStat.pos;
                if (pos == Position.NOPOS || pos == decl.pos) pos = terminationPos;
                if (assertStat.source != null) prev = log.useSource(assertStat.source);
                String extra = Strings.empty;
                JCExpression optional = assertStat.optionalExpression;
                if (optional != null) {
                    if (optional instanceof JCTree.JCLiteral) extra = ": " + ((JCTree.JCLiteral)optional).getValue().toString();
                }
                log.warning(pos,"esc.assertion.invalid",label,decl.getName(),extra);
                // TODO - above we include the optionalExpression as part of the error message
                // however, it is an expression, and not evaluated for ESC. Even if it is
                // a literal string, it is printed with quotes around it.
                if (prev != null) log.useSource(prev);
                if (assertStat.associatedPos != Position.NOPOS) {
                    if (assertStat.associatedSource != null) prev = log.useSource(assertStat.associatedSource);
                    log.warning(assertStat.associatedPos, "jml.associated.decl");
                    if (assertStat.associatedSource != null) log.useSource(prev);
                }
                
//                if (label == Label.POSTCONDITION || label == Label.SIGNALS) {
//                    log.warning(terminationPos,"esc.assertion.invalid",label,decl.getName() + cf, Strings.empty);
//                    log.warning(assertStat.pos, "jml.associated.decl");
//                } else if (label == Label.ASSIGNABLE) {
//                    log.warning(assertStat.pos,"esc.assertion.invalid",label,decl.getName() + cf, Strings.empty);
//                    log.warning(assertStat.associatedPos, "jml.associated.decl");
//                } else if (label != Label.EXPLICIT_ASSERT && label != Label.EXPLICIT_ASSUME){
//                    log.warning(assertStat.pos,"esc.assertion.invalid",label,decl.getName() + cf, Strings.empty); 
//                    if (assertStat.pos != assertStat.associatedPos && assertStat.associatedPos != Position.NOPOS){
//                        log.warning(assertStat.associatedPos, "jml.associated.decl");
//                    }
//                } else {
//                    log.warning(assertStat.pos,"esc.assertion.invalid",label,decl.getName() + cf, Strings.empty); 
//                }

                return false;
            } else if (out.contains(" 0 errors")) {
                return true;
            } else {
                log.error(0,"jml.internal","Unknown result returned from prover"); // FIXME - use a different message
            }
        } catch (Exception e) {
            System.out.println("EXCEPTION: " + e); // FIXME
            return false;
        }
        
        return true;
    }
    
    protected JmlClassDecl getOwner(JmlMethodDecl methodDecl) {
        return (JmlClassDecl)JmlEnter.instance(context).getEnv((ClassSymbol)methodDecl.sym.owner).tree;
    }
    
    /** Perform an ESC check of the method using the SMT translation */
    public IProverResult proveWithSMT(JCMethodDecl decl, String proverToUse) {
        boolean print = this.verbose;
        boolean printPrograms = print || JmlOption.isOption(context, JmlOption.SHOW);
        
//        // FIXME - implement proving constructors
//        if (decl.sym.isConstructor()) {
//            log.noticeWriter.println("(NOT IMPLEMENTED) SKIPPING PROOF OF CONSTRUCTOR FOR " + decl.sym); //$NON-NLS-1$
//            return new ProverResult(proverToUse,IProverResult.SKIPPED);
//        }
        
        JmlMethodDecl methodDecl = (JmlMethodDecl)decl;

        JmlClassDecl currentClassDecl = getOwner(methodDecl);
        
        JmlMethodSpecs denestedSpecs = methodDecl.sym == null ? null : specs.getDenestedSpecs(methodDecl.sym);

        JCBlock newblock = assertionAdder.methodBiMap.getf(decl).getBody();
        if (printPrograms) {
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("--------------------------------------"); //$NON-NLS-1$
            log.noticeWriter.println(Strings.empty);
            log.noticeWriter.println("TRANSFORMATION OF " + utils.qualifiedMethodSig(methodDecl.sym)); //$NON-NLS-1$
            log.noticeWriter.println(JmlPretty.write(newblock));
        }

        // determine the executable
        String exec = pickProverExec(proverToUse);
        if (exec == null) {
            log.warning("esc.no.exec",proverToUse); //$NON-NLS-1$
            return new ProverResult(proverToUse,IProverResult.SKIPPED);
        }
        
        // create an SMT object, adding any options
        SMT smt = new SMT();
        smt.processCommandLine(new String[]{}, smt.smtConfig);

        // Add a listener for errors and start the solver.
        // The listener is set to use the defaultPrinter for printing 
        // SMT abstractions and forwards all informational and error messages
        // to the OpenJML log mechanism
        smt.smtConfig.log.addListener(new SMTListener(log,smt.smtConfig.defaultPrinter));
        SMTTranslator smttrans = new SMTTranslator(context);

        ISolver solver;
        IResponse solverResponse ;
        BasicBlocker2 basicBlocker;
        BasicProgram program;
        {
            // now convert to basic block form
            basicBlocker = new BasicBlocker2(context);
            program = basicBlocker.convertMethodBody(newblock, decl, denestedSpecs, currentClassDecl, assertionAdder);
            if (printPrograms) {
                log.noticeWriter.println("BasicBlock2 FORM of " + utils.qualifiedMethodSig(methodDecl.sym) + JmlTree.eol +
                		program.toString());
            }

            // convert the basic block form to SMT
            ICommand.IScript script = smttrans.convert(program,smt);
            if (printPrograms) {
                try {
                    log.noticeWriter.println();
                    log.noticeWriter.println("SMT TRANSLATION OF " + utils.qualifiedMethodSig(methodDecl.sym));
                    org.smtlib.sexpr.Printer.write(new PrintWriter(log.noticeWriter),script);
                    log.noticeWriter.println();
                    log.noticeWriter.println();
                } catch (VisitorException e) {
                    log.noticeWriter.print("Exception while printing SMT script: " + e); //$NON-NLS-1$
                }
            }

            solver = smt.startSolver(smt.smtConfig,proverToUse,exec);

            // Try the prover
            if (verbose) log.noticeWriter.println("EXECUTION"); //$NON-NLS-1$
            solverResponse = script.execute(solver); // Note - the solver knows the smt configuration

        }
        
        
    
        IProverResult proofResult = null;

        {
            if (solverResponse.isError()) {
                solver.exit();
                log.error("jml.esc.badscript", decl.getName(), smt.smtConfig.defaultPrinter.toString(solverResponse)); //$NON-NLS-1$
                return new ProverResult(proverToUse,IProverResult.ERROR);
            }
            if (print) log.noticeWriter.println(smt.smtConfig.defaultPrinter.toString(solverResponse));
            if (solverResponse.toString().equals("unsat")) {// FIXME - should have a better means of checking this
                if (verbose) log.noticeWriter.println("Method checked OK");
                proofResult = new ProverResult(proverToUse,IProverResult.UNSAT);
                
                java.util.List<JCTree.JCParens> a = assertionAdder.assumptionChecks.get(methodDecl.sym);
                if (a != null) { // FIXME - warn if a null? perhaps just an artifact of assertig a constructor
                    a.get(0).expr = JmlTreeUtils.instance(context).falseLit;
                    BasicBlocker2 basicBlocker2 = new BasicBlocker2(context);
                    BasicProgram program2 = basicBlocker2.convertMethodBody(newblock, decl, denestedSpecs, currentClassDecl, assertionAdder);
                    if (printPrograms) {
                        log.noticeWriter.println("BASIC BLOCK FORM OF " 
                                + utils.qualifiedMethodSig(methodDecl.sym)
                                + " FOR CHECKING FEASIBILITY"
                                + JmlTree.eol
                                + program2.toString());
                    }

                    // create an SMT object, adding any options
                    smt.processCommandLine(new String[]{}, smt.smtConfig);

                    // convert the basic block form to SMT
                    SMTTranslator smttrans2 = new SMTTranslator(context);
                    ICommand.IScript script2 = smttrans2.convert(program2,smt);


                    ISolver solver2 = smt.startSolver(smt.smtConfig,proverToUse,exec);

                    // Try the prover
                    if (verbose) log.noticeWriter.println("EXECUTION"); //$NON-NLS-1$
                    solverResponse = script2.execute(solver2); // Note - the solver knows the smt configuration
                    if (solverResponse.toString().equals("unsat")) {
                        log.warning(decl.pos(), "esc.infeasible.preconditions", utils.qualifiedMethodSig(methodDecl.sym));
                    }
                    solver2.exit();
                }
                
                // TODO - optional checking that the method is actually feasible
            } else {
                int count = Utils.instance(context).maxWarnings;
                while (true) {
                    if (proofResult == null) proofResult = new ProverResult(proverToUse,
                            solverResponse.toString().equals("sat") ? IProverResult.SAT : IProverResult.POSSIBLY_SAT);
                    if (print) log.noticeWriter.println("Some assertion not valid");

                    if (showCounterexample) {
                        log.noticeWriter.println("\nCOUNTEREXAMPLE");
                        for (VarSymbol v: basicBlocker.premap.keySet()) {
                            Name n = basicBlocker.premap.getName(v);
                            String ns = n.toString();
                            if (ns.equals("this")) continue; // FIXME - use symbols for these
                            if (ns.equals("length")) continue;
                            if (ns.equals("_alloc__")) continue;
                            if (ns.equals("_heap__")) continue;

                            String s = getValue(n.toString(),smt,solver);
                            log.noticeWriter.println(n.toString() + " = " + s);
                        }
                        log.noticeWriter.println(Strings.empty);
                    }
                    
                    Map<JCTree,String> cemap = constructCounterexample(assertionAdder,basicBlocker,smttrans,smt,solver);
                    BiMap<JCTree,JCExpression> jmap = assertionAdder.bimap.compose(basicBlocker.bimap);
                    tracer = new Tracer(context,smt,solver,cemap,jmap);
                    mostRecentCEMap = cemap;

                    
                    // Report JML-labeled values and the path to the failed invariant
                    if (showTrace) log.noticeWriter.println("\nTRACE\n");
                    JCExpression pathCondition = reportInvalidAssertion(program,smt,solver,decl,cemap,jmap);
                    IProverResult.ICounterexample item = new Counterexample();
                    item.putPath(path);
                    
                    ((ProverResult)proofResult).add(item);
                    //                if (showCounterexample) {
                    //                    log.noticeWriter.println("\nTRACE with respect to ORIGINAL PROGRAM\n");
                    //                }

                    if (--count <= 0) break;

                    solver.pop(1);
                    solver.assertExpr(smttrans.convertExpr(pathCondition));
                    solver.push(1);
                    solverResponse = solver.check_sat();

                    if (solverResponse.isError()) {
                        log.error("jml.esc.badscript", decl.getName(), smt.smtConfig.defaultPrinter.toString(solverResponse)); //$NON-NLS-1$
                        return new ProverResult(proverToUse,IProverResult.ERROR);
                    }
                    if (solverResponse.toString().equals("unsat")) break;
                    // TODO -  checking each assertion separately
                }
            }
        }
        solver.exit();
        proverResults.put(methodDecl.sym,proofResult);
        mostRecentProgram = program;
        return proofResult;
    }
    
    static public Map<JCTree,String> mostRecentCEMap = null;
    
    protected List<IProverResult.Span> path = new ArrayList<IProverResult.Span>();
    
    /** Iterates through the basic blocks to find and report the invalid assertion
     * that caused the SAT result from the prover.
     */
    public JCExpression reportInvalidAssertion(BasicProgram program, SMT smt, ISolver solver, JCMethodDecl decl,
            Map<JCTree,String> cemap, BiMap<JCTree,JCExpression> jmap) {
        exprValues = new HashMap<JCTree,String>();
        JCExpression pathCondition = reportInvalidAssertion(program.startBlock(),smt,solver,decl,0, JmlTreeUtils.instance(context).falseLit,cemap,jmap);
        if (pathCondition == null) {
            log.warning("jml.internal.notsobad","Could not find an invalid assertion even though the proof result was satisfiable: " + decl.sym); //$NON-NLS-1$ //$NON-NLS-2$
        }
        return pathCondition;
    }
    
    Map<JCTree,String> exprValues = new HashMap<JCTree,String>();
    
    // These strings must mirror the strings used in JmlAsssertionAdder.visitJmlLblExpression
    private final static String prefix_lblpos = Strings.labelVarString + JmlToken.BSLBLPOS.internedName().substring(1) + "_";
    private final static String prefix_lblneg = Strings.labelVarString + JmlToken.BSLBLNEG.internedName().substring(1) + "_";
    private final static String prefix_lbl = Strings.labelVarString + JmlToken.BSLBLANY.internedName().substring(1) + "_";

    public int checkTerminationPosition(String id, int terminationPos) {
        // The BasicBlocker2 implementation creates special RETURN and 
        // THROWS blocks that just hold those statements. Thus we can 
        // identify terminating statements. This is relevant in the situations
        // in which the invalid assertion is a postcondition - then we want
        // to know which path through the method (ending at a return or
        // throws statement) causes the bad postcondition. Note also that
        // a return or throws statement might be overridden by a subsequent
        // return or throws statement in a later finally block.
        
        // The extraction of the terminationPos from the block id depends
        // on the format of the block id as generated in BasicBlocker2
        int k = id.indexOf(BasicBlockerParent.RETURN);
        if (k < 0) k = id.indexOf(BasicBlockerParent.THROW);
        if (k > 0) {
            int kk = BasicBlockerParent.blockPrefix.length();
            terminationPos = Integer.parseInt(id.substring(kk,k));
        }
        return terminationPos;
    }
    
    /** Helper method for iterating through the basic blocks to find and report the invalid assertion
     * that caused the SAT result from the prover; 
     * Returns true if an invalid assertion was found and reported */
    // How this works: If there is an invalid assertion, then the value of the blockid
    // of the bloc containing that assertion is false; recursively, the blockid
    // is false for any block that has a following block with a false blockid.
    // Thus if there is an invalid assertion the start block is false and there is
    // a path of false blocks to the invalid assertion. There could possibly be
    // other blocks with false ids as well.
    public JCExpression reportInvalidAssertion(BasicProgram.BasicBlock block, SMT smt, ISolver solver, JCMethodDecl decl, int terminationPos, JCExpression pathCondition,
            Map<JCTree,String> cemap, BiMap<JCTree,JCExpression> jmap) {
        String id = block.id.name.toString();
        boolean value = getBoolValue(id,smt,solver);
        if (utils.jmlverbose >= Utils.JMLVERBOSE || JmlOption.isOption(context,JmlOption.COUNTEREXAMPLE)) {
            log.noticeWriter.println("Block " + id + " is " + value);  //$NON-NLS-1$//$NON-NLS-2$
        }
        if (value) {
            // The value of the block id is true, so we don't pursue it
            return null;
        }
        terminationPos = checkTerminationPosition(id,terminationPos);
        pathCondition = JmlTreeUtils.instance(context).makeOr(Position.NOPOS,pathCondition,block.id);
        
        //showTrace = true;
        // FIXME - would like to have a range, not just a single position point,
        // for the terminationPos
        boolean printspans = false;        
        for (JCStatement stat: block.statements()) {
            // Report any statements that are JML-labeled
            if (stat instanceof JCVariableDecl) {
                Name n = ((JCVariableDecl)stat).name;
                String ns = n.toString();
                if (ns.startsWith(Strings.labelVarString)) {
                    boolean b = getBoolValue(ns,smt,solver);
                    if (ns.startsWith(prefix_lblpos)) {
                        if (b) log.warning(stat.pos,"esc.label.value",ns.substring(prefix_lblpos.length()),b); //$NON-NLS-1$
                    } else if (ns.startsWith(prefix_lblneg)) {
                        if (!b) log.warning(stat.pos,"esc.label.value",ns.substring(prefix_lblneg.length()),b); //$NON-NLS-1$
                    } else if (ns.startsWith(prefix_lbl)) {
                        log.warning(stat.pos,"esc.label.value",ns.substring(prefix_lbl.length()),b); //$NON-NLS-1$
                    } else {
                        log.warning(stat.pos,"jml.internal.notsobad","Unknown label: " + ns); //$NON-NLS-1$
                    }
                }
            }
            
            if (showTrace) {
                log.noticeWriter.println("STATEMENT: " + stat);
                if (stat instanceof JmlStatementExpr) {
                    JmlStatementExpr x = (JmlStatementExpr)stat;
                    traceSubExpr(x.expression);
                } else if (stat instanceof JCVariableDecl) {
                    JCVariableDecl vd = (JCVariableDecl)stat;
                	Name n = vd.name;
                    if (vd.init != null) traceSubExpr(vd.init);
                	log.noticeWriter.println("DECL: " + n + " === " + getValue(n.toString(),smt,solver));
                }
            }
            if (stat instanceof JmlVariableDecl) {
                if (!((JmlVariableDecl)stat).name.toString().startsWith(Strings.tmpVarString)) {
                    int sp = stat.getStartPosition();
                    int ep = stat.getEndPosition(log.currentSource().getEndPosTable());
                    //log.noticeWriter.println("SPAN " + sp + "  " + ep + " " + stat);
                    if (ep <= sp) {
                        if (printspans) log.noticeWriter.println("BAD SPAN " + sp + "  " + ep + " " + stat);
                    }
                    else path.add(new Span(sp,ep,Span.NORMAL));
                }
            } else if (stat instanceof JmlStatementExpr && ((JmlStatementExpr)stat).token == JmlToken.ASSUME) {
                JmlStatementExpr assumeStat = (JmlStatementExpr)stat;
                JCExpression e = assumeStat.expression;
                int sp = e.getStartPosition();
                int ep = e.getEndPosition(log.currentSource().getEndPosTable());
                Label label = assumeStat.label;
                if (label == Label.ASSIGNMENT) {
                    //log.noticeWriter.println("SPAN " + sp + "  " + ep + " " + e);
                    if (ep <= sp) {
                        if (printspans) log.noticeWriter.println("BAD SPAN " + sp + "  " + ep + " " + e);
                    }
                    else path.add(new Span(sp,ep,Span.NORMAL));
                } else if (label == Label.EXPLICIT_ASSUME) {
                    //log.noticeWriter.println("SPAN " + sp + "  " + ep + " " + stat);
                    if (ep <= sp) {
                        if (printspans) log.noticeWriter.println("BAD SPAN " + sp + "  " + ep + " " + e);
                    }
                    else {
//                        if (e instanceof JCTree.JCLiteral) {
//                            value = ((JCTree.JCLiteral)e).value.equals(1); // Boolean literals have 0 and 1 value
//                        } else if (e instanceof JCTree.JCParens) {
//                                value = ((JCTree.JCLiteral)((JCTree.JCParens)e).expr).value.equals(1); // Boolean literals have 0 and 1 value
//                        } else {
//                            id = ((JCIdent)e).name.toString(); // FIXME _ assumes are not necessarily IDENTS?
//                            value = getBoolValue(id,smt,solver);
//                        }
                        path.add(new Span(sp,ep,Span.NORMAL)); //value ? Span.TRUE : Span.FALSE));
                    }
                } else if (label == Label.BRANCHT || label == Label.BRANCHE || label == Label.SWITCH_VALUE || label == Label.CASECONDITION) {
                    //log.noticeWriter.println("SPAN " + sp + "  " + ep + " " + e);
                    if (ep <= sp) {
                        if (printspans) log.noticeWriter.println("BAD SPAN " + sp + "  " + ep + " " + e);
                    }
                    else path.add(new Span(sp,ep,
                    		label == Label.BRANCHT ? Span.TRUE : 
                    		label == Label.BRANCHE? Span.FALSE : Span.NORMAL));
                } else if (label == Label.DSA || label == Label.NULL_CHECK || label == Label.IMPLICIT_ASSUME) {
                    // Ignore
                } else {
                    // FIXME - at least PRECONDITION
                	//log.noticeWriter.println("UNHANDLED LABEL " + label);
                }
            } else if (stat instanceof JmlStatementExpr && ((JmlStatementExpr)stat).token == JmlToken.ASSERT) {
                JmlStatementExpr assertStat = (JmlStatementExpr)stat;
                JCExpression e = assertStat.expression;
                if (e instanceof JCTree.JCLiteral) {
                    value = ((JCTree.JCLiteral)e).value.equals(1); // Boolean literals have 0 and 1 value
                } else if (e instanceof JCTree.JCParens) {
                        value = ((JCTree.JCLiteral)((JCTree.JCParens)e).expr).value.equals(1); // Boolean literals have 0 and 1 value
                } else {
                    id = ((JCIdent)e).name.toString(); // Relies on all assert statements being reduced to identifiers
                    value = getBoolValue(id,smt,solver);
                }
                int sp = e.getStartPosition();
                int ep = e.getEndPosition(log.currentSource().getEndPosTable());
                //log.noticeWriter.println("SPAN " + sp + "  " + ep + " " + e);
                if (ep <= sp) {
                    if (printspans) log.noticeWriter.println("BAD SPAN " + sp + "  " + ep + " " + e);
                }
                else path.add(new Span(sp,ep,
                        value ? Span.TRUE : Span.FALSE));
                if (!value) {
                    pathCondition = JmlTreeUtils.instance(context).makeOr(Position.NOPOS, pathCondition, e);
                    if (terminationPos == 0) terminationPos = decl.pos;
                    Label label = assertStat.label;

                    JavaFileObject prev = null;
                    int pos = assertStat.pos;
                    if (pos == Position.NOPOS || pos == decl.pos) pos = terminationPos;
                    if (assertStat.source != null) prev = log.useSource(assertStat.source);
                    String extra = Strings.empty;
                    JCExpression optional = assertStat.optionalExpression;
                    if (optional != null) {
                        if (optional instanceof JCTree.JCLiteral) extra = ": " + ((JCTree.JCLiteral)optional).getValue().toString(); //$NON-NLS-1$
                    }
                    int epos = assertStat.getEndPosition(log.currentSource().getEndPosTable());
                    // FIXME: if (epos == Position.NOPOS) log.noticeWriter.println("INCOMPLETE WARNING RANGE " + assertStat.getStartPosition() + " " + ep + " " + assertStat);
                    if (epos == Position.NOPOS || pos != assertStat.pos) {
                        log.warning(pos,"esc.assertion.invalid",label,decl.getName(),extra); //$NON-NLS-1$
                    } else {
                        // FIXME - migrate to using pos() for terminationPos as well 
                        log.warning(assertStat.pos(),"esc.assertion.invalid",label,decl.getName(),extra); //$NON-NLS-1$
                    }
                    JCDiagnostic diag = JCDiagnostic.Factory.instance(context).note(log.currentSource(), new JCDiagnostic.SimpleDiagnosticPosition(pos), "esc.empty",Strings.empty); //$NON-NLS-1$
                    String msg = diag.toString();
                    msg = msg.substring(0,msg.indexOf("Note")); //$NON-NLS-1$
                    // TODO - above we include the optionalExpression as part of the error message
                    // however, it is an expression, and not evaluated for ESC. Even if it is
                    // a literal string, it is printed with quotes around it.
                    if (prev != null) log.useSource(prev);
                    if (assertStat.associatedPos != Position.NOPOS) {
                        if (assertStat.associatedSource != null) prev = log.useSource(assertStat.associatedSource);
                        log.warning(assertStat.associatedPos, "jml.associated.decl",msg); // FIXME - could add this information, but it would blow Aaway the test results
                        if (assertStat.associatedSource != null) log.useSource(prev);
                    }

                    // Found an invalid assertion, so we can terminate
                    // Negate the path condition
                    return pathCondition; 
                }
            }
        }
        
        // Since we have not found an invalid assertion in this block, we
        // inspect each follower. Since the blocks form a DAG, this will
        // terminate.
        for (BasicBlock b: block.followers()) {
            JCExpression p = reportInvalidAssertion(b,smt,solver,decl,terminationPos,pathCondition,cemap,jmap);
            if (p != null) return p;
        }
        return null; // DId not find anything in this block or its followers
    }
    
    /** Write out (through log.noticeWriter) the values of the given expression
     * and, recursively, of any subexpressions.
     */
    public void traceSubExpr(JCExpression e) {
        e.accept(tracer);
    }

    
//    /** Write out (through log.noticeWriter) the values of the given expression
//     * and, recursively, of any subexpressions.
//     */
//    public void traceSubExpr(JCExpression e, SMT smt, ISolver solver, Map<JCExpression,String> cemap, BiMap<JCExpression,JCExpression> jmap) {
//        e.accept(tracer);if (e instanceof JCIdent) {
//            Name n = ((JCIdent)e).name;
//            String value = getValue(n.toString(),smt,solver);
//            log.noticeWriter.println("VALUE: " + n + " = " + value);
//            String sv = cemap.get(e);
//            log.noticeWriter.println("V " + n + " : " + jmap.getr(e) + " = " + sv + " :: " + value);
//            return;
//        } else if (e instanceof JCBinary) {
//        } else if (e instanceof JCUnary) {
//            traceSubExpr(((JCUnary)e).arg,smt,solver,cemap,jmap);
//            String sv = cemap.get(e);
//            log.noticeWriter.println("V " + e + " : " + jmap.getr(e) + " = " + sv);
//        } else if (e instanceof JCConditional) {
//            traceSubExpr(((JCConditional)e).arg,smt,solver,cemap,jmap);
//            String sv = cemap.get(e);
//            log.noticeWriter.println("V " + e + " : " + jmap.getr(e) + " = " + sv);
//        }
//        // FIXME - this should be expanded to more kinds of expressions, but only those that might be in a basic program - actually should do this in relation to the original program
//    }
    
    // FIXME - document
    // Not static so we have access to getValue
    public class Tracer extends JmlTreeScanner {
        SMT smt;
        ISolver solver;
        Map<JCTree,String> cemap;
        BiMap<JCTree,JCExpression> jmap;
        Log log;
        String result;
        
        public Tracer(Context context, SMT smt, ISolver solver, Map<JCTree,String> cemap, BiMap<JCTree,JCExpression> jmap) {
            this.smt = smt;
            this.solver = solver;
            this.cemap = cemap;
            this.jmap = jmap;
            this.log = Log.instance(context);
        }
        
        @Override
        public void visitIdent(JCIdent e) {
            Name n = e.name;
            String sv = cemap.get(e);
            //log.noticeWriter.println("VALUE: " + n + " = " + value);
            if (sv == null) {
                sv = getValue(n.toString(),smt,solver);
                //log.noticeWriter.println("VALUE Retrieved: " + n + " = " + sv);
                cemap.put(e, sv);
            }
            JCTree ex = jmap.getr(e);
            if (ex != null) {
                log.noticeWriter.println(ex + " === " + sv);
            } else {
                //log.noticeWriter.println("VALUE unknown: " + n );
            }
            result = sv;
        }
        
        @Override
        public void visitBinary(JCBinary e) {
            e.lhs.accept(this);
            e.rhs.accept(this);
            String sv = cemap.get(e);
            JCTree ex = jmap.getr(e);
            if (sv != null && ex != null) {
                log.noticeWriter.println(ex + " === " + sv);
            }
            result = sv;
        }
        
        @Override
        public void visitUnary(JCUnary e) {
            e.arg.accept(this);
            String sv = cemap.get(e);
            JCTree ex = jmap.getr(e);
            if (sv != null && ex != null) {
                log.noticeWriter.println(ex + " === " + sv);
            }
            result = sv;
        }
        
        @Override
        public void visitConditional(JCConditional e) {
            e.cond.accept(this);
            if (result.equals("true")) {
                e.truepart.accept(this);
            } else {
                e.falsepart.accept(this);
            }
            String sv = cemap.get(e);
            JCTree ex = jmap.getr(e);
            if (sv != null && ex != null) {
                log.noticeWriter.println(ex + " === " + sv);
            }
            result = sv;
        }
        
        @Override
        public void visitSelect(JCFieldAccess tree) {
            if (!JmlTreeUtils.instance(context).isATypeTree(tree)) scan(tree.selected);
        }


        
    }
    
    /** Query the solver for the (boolean) value of an id in the current model */
    public boolean getBoolValue(String id, SMT smt, ISolver solver) {
        return !getValue(id,smt,solver).toString().contains("false");
    }
    
    /** Query the solver for the (int) value of an id in the current model */
    public int getIntValue(String id, SMT smt, ISolver solver) {
        return Integer.parseInt(getValue(id,smt,solver));
    }

    /** Query the solver for the (String) value of an id in the current model */
    public String getValue(String id, SMT smt, ISolver solver) {
        org.smtlib.IExpr.ISymbol s = smt.smtConfig.exprFactory.symbol(id);
        IResponse resp = solver.get_value(s);
        if (resp instanceof IResponse.IError) {
            log.error("jml.internal.notsobad", ((IResponse.IError)resp).errorMsg()); //$NON-NLS-1$
            return null;
        } else if (resp == null) {
            log.error("jml.internal.notsobad", "Could not find value of assertion: " + id); //$NON-NLS-1$
            return null;
        } else if (!(resp instanceof org.smtlib.sexpr.ISexpr.ISeq)){
            log.error("jml.internal.notsobad", "Unexpected response on requesting value of assertion: " + smt.smtConfig.defaultPrinter.toString(resp)); //$NON-NLS-1$
            return null;
        }

        org.smtlib.sexpr.ISexpr se = ((org.smtlib.sexpr.ISexpr.ISeq)resp).sexprs().get(0);
        if (se instanceof org.smtlib.sexpr.ISexpr.ISeq) se = ((org.smtlib.sexpr.ISexpr.ISeq)se).sexprs().get(1);
        return se.toString();
    }
    
    public Map<IExpr,String> constructSMTCounterexample(SMTTranslator smttrans, ISolver solver) {
//        IExpr[] e = smttrans.bimap.reverse.keySet().toArray(new IExpr[0]);
//        IResponse resp = solver.get_value(e);
//        if (resp instanceof ISexpr.ISeq) {
//            ISexpr.ISeq seq = (ISexpr.ISeq)resp;
//            for (ISexpr s: seq.sexprs()) {
//                // This is not helpful unless the result is in the same order as the input
//            }
//        }
        
        Map<IExpr,String> ce = new HashMap<IExpr,String>();
        IExpr[] ee = new IExpr[1];
        for (IExpr e: smttrans.bimap.reverse.keySet()) {
            ee[0] = e;
            IResponse resp = solver.get_value(ee);
            if (resp instanceof ISexpr.ISeq) {
                ISexpr pair = ((ISexpr.ISeq)resp).sexprs().get(0);
                ISexpr value = ((ISexpr.ISeq)pair).sexprs().get(1);
                ce.put(e, value.toString());
            }
        }
        return ce;
    }
    
    public Map<JCTree,String> constructCounterexample(JmlAssertionAdder assertionAdder, BasicBlocker2 basicBlocker, SMTTranslator smttrans, SMT smt, ISolver solver) {
        boolean verbose = false;
        if (verbose) {
            log.noticeWriter.println("ORIGINAL <==> TRANSLATED");
            for (JCTree e: assertionAdder.bimap.forward.keySet()) {
                JCTree v = assertionAdder.bimap.getf(e);
                if (v != null && assertionAdder.bimap.getr(v) == e) {
                    log.noticeWriter.println(e.toString() + " <==> " + v);
                } else {
                    log.noticeWriter.println(e.toString() + " ===> " + v);
                }
            }
            log.noticeWriter.println("\nTRANSLATED <==> BB");
            for (JCTree e: basicBlocker.bimap.forward.keySet()) {
                JCExpression v = basicBlocker.bimap.getf(e);
                if (v != null && basicBlocker.bimap.getr(v) == e) {
                    log.noticeWriter.println(e.toString() + " <==> " + v);
                } else {
                    log.noticeWriter.println(e.toString() + " ===> " + v);
                }
            }
            log.noticeWriter.println("\nBB <==> SMT");
            for (JCExpression e: smttrans.bimap.forward.keySet()) {
                IExpr v = smttrans.bimap.getf(e);
                if (v != null && smttrans.bimap.getr(v) == e) {
                    log.noticeWriter.println(e.toString() + " <==> " + v);
                } else {
                    log.noticeWriter.println(e.toString() + " ===> " + v);
                }
            }
            log.noticeWriter.println("\nORIGINAL <==> SMT");
        }
        BiMap<JCTree,IExpr> cb = assertionAdder.bimap.compose(basicBlocker.bimap).compose(smttrans.bimap);
        if (verbose) {
            for (JCTree e: cb.forward.keySet()) {
                IExpr v = cb.getf(e);
                if (v != null && cb.getr(v) == e) {
                    log.noticeWriter.println(e.toString() + " <==> " + v);
                } else {
                    log.noticeWriter.println(e.toString() + " ===> " + v);
                }
                // FIXME - should use proper printers, not toString()
            }
            log.noticeWriter.println("\nORIGINAL <==> VALUE");
        }
        Map<IExpr,String> ce = constructSMTCounterexample(smttrans,solver);
        Map<JCTree,String> values = cb.compose(ce);
        if (verbose) {
            SortedSet<String> set = new TreeSet<String>();
            for (JCTree e: values.keySet()) {
                int line = log.currentSource().getLineNumber(e.pos);
                set.add("line " + String.format("%1$3d",line) + ": " + e.type + " " + JmlPretty.write(e) + " = " + values.get(e));
            }
            for (String s: set) {
                log.noticeWriter.println(s);
            }
        }
        return values;
    }


    /** This is a listener for SMT log and error messages */
    public class SMTListener implements org.smtlib.Log.IListener {
        org.smtlib.IPrinter printer;
        com.sun.tools.javac.util.Log log;
        
        SMTListener(Log log, org.smtlib.IPrinter printer) {
            this.log = log;
            this.printer = printer;
        }
        
        @Override
        public void logOut(String msg) {
            log.noticeWriter.println(msg);
        }

        @Override
        public void logOut(IResponse result) {
            log.noticeWriter.println(printer.toString(result));
        }

        @Override
        public void logError(String msg) {
            log.error("jml.internal",msg); //$NON-NLS-1$
        }

        @Override
        public void logError(IError result) {
            log.error("jml.internal",printer.toString(result)); //$NON-NLS-1$
        }

        @Override
        public void logDiag(String msg) {
            log.noticeWriter.println(msg);
        }

        @Override
        public void indent(String chars) {
            // TODO - not sure how to enforce the indent
        }
        
    }
        
    
    // FIXME: REVIEW THIS - everything following is for proveMethodOld

    /** This is the entry point to attempt a proof of the given method.  It 
     * presumes that the method (and any it relies on is entered and typechecked.
     * @param node the method to prove
     * @return // FIXME - not currently used
     */
    public IProverResult proveMethodOld(@NonNull JCMethodDecl node, String proverToUse) {
        IProverResult proofResult;
        
        boolean verboseProgress = Utils.instance(context).jmlverbose >= Utils.PROGRESS;
        
        if (verboseProgress) 
        	progress(1,2,"Starting proof of " + node.sym.owner.flatName() + "." + node.sym + " with prover " + proverToUse);
        Utils.Timer timer = new Utils.Timer();
        
        
        JmlMethodDecl tree = (JmlMethodDecl)node;
        //JmlClassDecl currentClassDecl = JmlSpecs.instance(context).get((ClassSymbol)node.sym.owner).decl;
        JmlClassDecl currentClassDecl = (JmlClassDecl)JmlEnter.instance(context).getEnv((ClassSymbol)node.sym.owner).tree;
        
        // Get the denested specs for the method - FIXME - when might they be null?
        JmlMethodSpecs denestedSpecs = tree.sym == null ? null : specs.getDenestedSpecs(tree.sym);
        
        // Change the log's source file to represent the source for this method
        JavaFileObject source = tree.sourcefile;
        JavaFileObject prev = log.useSource(source);

        boolean ok = false;
        BasicProgram program = null;
            
        try {
            String name = node.sym.owner + "." + node.sym;
            
            if (JmlOption.isOption(context,"-showds") || escdebug) {
                log.noticeWriter.println(JmlPretty.write(tree)); // print the input tree
            }
            boolean doMetrics = false;
            VCmode = 0;
            if (timingTest > 0) doMetrics = false;
            boolean showTimes = false;
            Utils.Timer t = null;
            if (showTimes) t = new Utils.Timer();
            if (doMetrics) {
                boolean a = BasicBlocker.useAssertDefinitions;
                boolean b = BasicBlocker.useAssumeDefinitions;
                try {
                    BasicBlocker.useAssertDefinitions = false;
                    BasicBlocker.useAssumeDefinitions = false;
                    program = BasicBlocker.convertToBasicBlocks(context, tree, denestedSpecs, currentClassDecl);
                    metrics(node,program,name);
                } finally {
                    BasicBlocker.useAssertDefinitions = a;
                    BasicBlocker.useAssumeDefinitions = b;
                }
            }
            if (useTree) VCmode = 1;
            program = BasicBlocker.convertToBasicBlocks(context, tree, denestedSpecs, currentClassDecl);
            
            if (doMetrics || timingTest == 1) metrics(node,program,name);
            if (doMetrics) return new ProverResult(proverToUse,IProverResult.SKIPPED);

            try {
                if (JmlOption.isOption(context,"-show") || escdebug) {
                    program.write(log.noticeWriter); // print the basic block program
                }
                //if (showTimes) log.noticeWriter.println("    ... prep           " +  t.elapsed()/1000.);
                //log.noticeWriter.println("\t\t" + program.blocks().size() + " blocks, " + program.definitions().size() + " definitions, " + program.background().size() + " axioms, " + BasicBlocker.Counter.count(program) + " nodes");
                if (verboseProgress) 
                	progress(1,2,"Prover running on " + node.sym.flatName() + "." + node.sym + " with prover " + proverToUse);
                proofResult = prove(node,program);
                if (showTimes) log.noticeWriter.println("    ... prep and prove " +  t.elapsed()/1000.);
                if (showTimes) {
                    Runtime rt = Runtime.getRuntime();
                    log.noticeWriter.println("    ....... Memory free=" + rt.freeMemory() + "  max="+rt.maxMemory() + "  total="+rt.totalMemory());
                }
            } catch (RuntimeException e) {
                String se = e.toString();
                if (e.getCause() != null) se = e.getCause().toString();
                if (se.length() > 200) se = se.substring(0,200) + " .....";
                log.warning(node.pos(),"esc.prover.failure",se);
                // go on with next 
                proofResult = new ProverResult(proverToUse,IProverResult.ERROR);
                String message = e.getMessage();
                if (e.getCause() != null) message = e.getCause().getMessage();
                if (message != null) proofResult.setOtherInfo(message);
            } catch (Throwable e) {
                String se = e.toString();
                if (e.getCause() != null) se = e.getCause().toString();
                if (se.length() > 200) se = se.substring(0,200) + " .....";
                log.warning(node.pos(),"esc.prover.failure",se);
                System.gc();
                proofResult = new ProverResult(proverToUse,IProverResult.ERROR);
                String message = e.getMessage();
                if (e.getCause() != null) message = e.getCause().getMessage();
                if (message != null) proofResult.setOtherInfo(message);
            }
        } catch (RuntimeException e) {
            log.warning(node.pos(),"esc.vc.prep",e);
            // go on with next 
            proofResult = new ProverResult(proverToUse,IProverResult.ERROR);
            String message = e.getMessage();
            if (e.getCause() != null) message = e.getCause().getMessage();
            if (message != null) proofResult.setOtherInfo(message);
        } catch (Throwable e) {
            log.warning(node.pos(),"esc.vc.prep",e);
            System.gc();
            proofResult = new ProverResult(proverToUse,IProverResult.ERROR);
            String message = e.getMessage();
            if (e.getCause() != null) message = e.getCause().getMessage();
            if (message != null) proofResult.setOtherInfo(message);
        } finally {
            log.useSource(prev);
        }
        //progress(1,1,"Completed proof [" + (ok?"   ":"not") + " proved] of " + node.sym.getQualifiedName() + " [" + timer.elapsed()/1000. + "]");
        if (verboseProgress) {
        	String s = proofResult.result().toString();
        	if (s.equals("UNSAT")) s = "VALID";
        	String message = "Completed proof attempt (" + s + ") of " 
                    + node.sym.owner.flatName() + "." + node.sym // using just node.sym gives the signature 
                    + " [" + timer.elapsed()/1000. + "] using " + proverToUse;
        	if (proofResult.otherInfo() != null) {
        		message = message + JmlTree.eol + "  (" + proofResult.otherInfo() + ")";
        	}
        	progress(1,1,message);
        }
        mostRecentProgram = program;
        return proofResult;
    }
    
    public BasicProgram mostRecentProgram = null;
 
    
    /** Returns the VC expression for a basic block
     * 
     * @param block the block to convert
     * @return the equivalent expression
     */
    public @NonNull JCExpression blockExpr(@NonNull BasicBlock block) {
        java.util.List<JCStatement> statements = block.statements();
        Iterator<JCStatement> iterator = statements.iterator();
        return blockExpr(block,iterator);
    }
    
    public void metrics(JCMethodDecl node, BasicProgram program, String name) {
        VCmode = 0;
        int ast = BasicBlocker.Counter.countAST(node.body);
        int sts = BasicBlocker.Counter.countASTStatements(node.body);
        BasicBlocker.Counter c = BasicBlocker.Counter.count(program);
//        VCmode = 1;
//        JCTree f = blockExpr(program.startBlock());
//        int fan = BasicBlocker.Counter.countAST(f) + BasicBlocker.Counter.countx(program);

//        BasicProgram newbp = new BasicProgram();
//        newbp.definitions = program.definitions;
//        newbp.background = program.background;
//        java.util.List<JCStatement> list = new java.util.ArrayList<JCStatement>();
//        newblocks(list,program.startBlock(),program,newbp);
//        int lin = BasicBlocker.Counter.countx(newbp);
//        for (BasicBlock b: newbp.blocks) {
//            lin += BasicBlocker.Counter.countAST(blockExpr(b));
//        }
//        log.noticeWriter.println(ast + " AST; " + c + "  " + fan + " tree; " + lin + " linear; " + program.definitions.size() + " defs :: " + name);
        VCmode = 0;
        
        int oth =  Counter.countx(program);
        int fan1 = fanCount(program).nodes + oth;
        int lin1 = parCount(program,false).nodes + oth;
        int linf = parCount(program,true).nodes + oth;
        log.noticeWriter.println(ast + " AST; " + sts + " statements; " + c + "  " + fan1 + " tree; " + lin1 + " linear; " + linf + " fulllinear; " + (program.definitions.size()+program.pdefinitions.size()) + " defs :: " + name);

    }
    
    Map<BasicBlock,Counter> countCache = new HashMap<BasicBlock,Counter>();
    
    public Counter parCount(BasicProgram program, boolean full) {
        countCache.clear();
        Counter c = getParCount(program.startBlock(),program,full);
        c.nodes += c.paths;
        return c;
    }
    
    public Counter getParCount(BasicBlock block, BasicProgram program, boolean full) {
        Counter c = countCache.get(block);
        if (c == null) {
            c = parCount(block,program,full);
            //log.noticeWriter.println("CACHE " + block.id + " " + c.paths + " " + c.nodes);
            countCache.put(block,c);
        }
        return c;
    }
    
    public Counter parCount(BasicBlock block, BasicProgram program, boolean full) {
        Counter c = new Counter();
        Counter ca = new Counter();
        int n = 0;
        for (JCTree t: block.statements()) {
            t.accept(c);
            //c.nodes++;
            if (full && t instanceof JmlStatementExpr && ((JmlStatementExpr)t).token == JmlToken.ASSERT) {
                ca.add(c);
                n++;
            }
        }
        
//        log.noticeWriter.print(block.id + " " + c.nodes + " ");
//        for (BasicBlock b: block.succeeding) log.noticeWriter.print(" " + b.id);
//        log.noticeWriter.println();
//        
        if (block.followers.size() == 0) {
            ca.add(c);
            n++;
            ca.paths = n;
            return ca;
        }
        Counter cc = new Counter();
        for (BasicBlock b: block.followers) {
            Counter ccc = getParCount(b,program,full);
            for (int i=0; i<ccc.paths; i++) {
                cc.add(c);
            }
            cc.add(ccc);
            n += ccc.paths;
            //cc.nodes ++;
        }
        cc.add(ca);
        cc.paths = n;
        return cc;
    }
    
    public Counter fanCount(BasicProgram program) {
        countCache.clear();
        return fanCount(program.startBlock(),program);
    }
    
    public Counter getFanCount(BasicBlock block, BasicProgram program) {
        Counter c = countCache.get(block);
        if (c == null) {
            c = fanCount(block,program);
            countCache.put(block,c);
        }
        return c;
    }
    
    public Counter fanCount(BasicBlock block, BasicProgram program) {
        Counter c = new Counter();
        c.count(block);
        if (block.followers.size() == 0) {
            //c.nodes++;
            return c;
        }
        for (BasicBlock b: block.followers) {
            c.add(getFanCount(b,program));
            //c.nodes ++;
        }
        return c;
    }
    
//    public void newblocks(java.util.List<JCStatement> prefix, BasicBlock block, BasicProgram program, BasicProgram newp) {
//        //log.noticeWriter.println("NEWBLOCKS " + block.id + "   prefix = " + Counter.counts(prefix));
//        java.util.List<JCStatement> p = new java.util.ArrayList<JCStatement>();
//        p.addAll(prefix);
//        for (JCStatement s: block.statements) {
//            p.add(s);
//            if ((s instanceof JmlTree.JmlStatementExpr) && ((JmlTree.JmlStatementExpr)s).token == JmlToken.ASSERT) {
//                BasicBlock bb = new BasicBlock(null);
//                bb.statements.addAll(p);
//                newp.blocks.add(bb);
//                //log.noticeWriter.println(    "  BLOCK-A " + Counter.counts(bb));
//            }
//        }
//        if (block.followers.size() == 0) {
//            BasicBlock bb = new BasicBlock(null);
//            bb.statements.addAll(p);
//            newp.blocks.add(bb);
//            //log.noticeWriter.println(    "  BLOCK-B " + Counter.counts(bb));
//        } else {
//            for (BasicBlock bb: block.followers) {
//                newblocks(p,bb,program,newp);
//            }
//        }
//    }
    
    /** Helper method to determine the VC expression for a basic block.
     * 
     * @param block BasicBlock being translated
     * @param iterator an iterator over the statements of the block
     * @return the equivalent VC expression
     */
    protected @NonNull JCExpression blockExpr(@NonNull BasicBlock block, @NonNull Iterator<JCStatement> iterator) {
        if (iterator.hasNext()) {
            JCStatement st = iterator.next();
            JCExpression rest = null;
            if (st == targetStatement) {
                if (timingTest == 9) {
                    rest = blockExpr(block,iterator);
                    JCExpression e = factory.Literal(TypeTags.BOOLEAN,0); // FALSE
                    e.type = syms.booleanType;
                    e.pos = st.pos;
                    e = factory.Binary(JCTree.AND,e,rest);
                    e.type = syms.booleanType;
                    e.pos = st.pos;
                    return e;
                } else {
                    JCExpression e = factory.Literal(TypeTags.BOOLEAN,0); // FALSE
                    e.type = syms.booleanType;
                    e.pos = st.pos;
                    return e;
                }
            } else if (st instanceof JmlStatementExpr) {
                rest = blockExpr(block,iterator);
                JmlStatementExpr as = (JmlStatementExpr)st;
                if (as.token == JmlToken.ASSUME) {
                    JCExpression e = factory.JmlBinary(JmlToken.IMPLIES,as.expression,rest);
                    e.type = syms.booleanType;
                    e.pos = as.expression.pos;
                    return e;
                } else if (as.token == JmlToken.ASSERT) {
                    //JCExpression e = factory.JmlBinary(JmlToken.IMPLIES,as.expression,rest);
                    JCExpression e = factory.Binary(JCTree.AND,as.expression,rest);
                    e.type = syms.booleanType;
                    e.pos = as.expression.pos;
                    return e;
                } else if (as.token == JmlToken.COMMENT) {
                    // skip
                } else {
                    log.error("esc.internal.error","An unexpected statement type in a BasicBlock: " + as.token.internedName());
                }
            } else {
                log.error("esc.internal.error","An unexpected statement type in a BasicBlock: " + st.getClass());
            }
            return rest;
        } else {
            JCExpression expr = factory.Literal(TypeTags.BOOLEAN,1); // TRUE
            expr.type = syms.booleanType;
            if (VCmode == 0) {
                for (BasicBlock follower: block.followers()) {
                    JCExpression e = factory.Binary(JCTree.AND,expr,follower.id);
                    e.pos = follower.id.pos;
                    e.type = syms.booleanType;
                    expr = e;
                }
            } else if (VCmode == 1) {
                for (BasicBlock follower: block.followers()) {
                    JCExpression fexpr = blockExpr(follower);
                    JCExpression e = factory.Binary(JCTree.AND,expr,fexpr);
                    e.pos = follower.id.pos;
                    e.type = syms.booleanType;
                    expr = e;
                }
            }
            return expr;
        }
    }
    
    int VCmode = 0;  // 0 - basic blocks; 1 - tree; 2 - parallel

    /** Creates an AST node for a new identifier, meant as an auxiliary logical
     * variable in the eventual VC; the identifier has the given type and node
     * position (the given position is not encoded into the identifier name);
     * an associated VarSymbol is also created.
     * @param name the name of the identifier (including any encoded numbers)
     * @param type the Java type of the identifier (e.g. syms.booleanType)
     * @param nodepos the pseudo source position at which to place the node
     * @return the created identifier
     */
    protected @NonNull JCIdent newAuxIdent(@NonNull Name name, @NonNull Type type, int nodepos) {
        JCIdent id = factory.Ident(name);
        id.pos = nodepos;
        id.type = type;
        id.sym = new VarSymbol(0,name,type,null);
        // Note: the owner of the symbol is null, because we do not want it to
        // be interpreted as a Java declaration of some sort.
        return id;
    }
    
    BasicBlock containingBlock;
    JCStatement targetStatement;
    
    public IProver mostRecentProver = null;
    
    /** Initiate proving of the VC for the method.  The given program must be
     * the BasicProgram corresponding to the given method declaration.
     * @param methodDecl the method whose implementation is being proved
     * @param program the basic program corresponding to the method implementation
     */
    public IProverResult prove(@NonNull JCMethodDecl methodDecl, @NonNull BasicProgram program) {
        String name = methodDecl.sym.owner + "." + methodDecl.sym;
        
//        log.noticeWriter.println(methodDecl.toString());
//        log.noticeWriter.println(program.toString());


        IProverResult proofResult;
        IProverResult firstProofResult;
        IProver p = null;
    	try {
    		p = AbstractProver.getProver(context,proverToUse);
    		if (p == null) {
    			// Error is already reported
    			//log.error("esc.no.prover",proverToUse);
    			IProverResult r = new ProverResult(proverToUse,IProverResult.ERROR);
    			r.setOtherInfo("Failed to create prover");
    			return r;
    		}
    	} catch (ProverException e) {
    		throw new RuntimeException(e);
//            IProverResult r = new ProverResult(proverToUse,IProverResult.ERROR);
//            r.setOtherInfo(e.getMessage());
//            return r;
    	}
        try {

            boolean usingSMT = p instanceof org.jmlspecs.openjml.provers.SMTProver;
            
            if (useRetract && !p.supports().retract) { 
                log.error("esc.retract.not.supported",proverToUse);
                p.kill(); 
                return new ProverResult(proverToUse,IProverResult.SKIPPED);
            }
            if (useCoreIds && !p.supports().unsatcore) {
                log.error("esc.unsatcore.not.supported",proverToUse);
                p.kill(); 
                return new ProverResult(proverToUse,IProverResult.SKIPPED);
            }
            if (timingTest >= 15 && p instanceof CVC3Prover) { 
                p.kill(); 
                return new ProverResult(proverToUse,IProverResult.SKIPPED);
            }
            
            Map<Integer,JCExpression> defexpr = new HashMap<Integer,JCExpression>();

            boolean showTimes = timingTest > 0;
            Utils.Timer timer = null;
            if (showTimes) timer = new Utils.Timer();

            for (BasicProgram.BasicBlock block : program.blocks()) {
                p.define(block.id.toString(),syms.booleanType);
            }
            
            // For SMT, not Yices
            if (usingSMT) {
                for (BasicProgram.Definition def: program.definitions()) {
                    p.define(def.id.toString(),def.value.type,def.value); // FIXME - define with a define-fun ?
                }
            }
            
//            if (JmlOptionName.isOption(context,"-checkPreconditions")) {
//                // Check that the preconditions are satisfiable
//                // This is here in case one wants a quick smoke test of the 
//                // preconditions.  Normally one would do the general check of
//                // the method, and only if it is successful would one go on to
//                // check that the various assumptions are feasible.
//                p.push();
//                BasicBlock bl = program.startBlock();
//                JCExpression e = blockExpr(bl);
//                e = factory.Unary(JCTree.NOT,e);
//                e.type = syms.booleanType;
//                p.assume(e);
//                IProverResult b = p.check(false);
//                if (b.result() == ProverResult.UNSAT) {
//                    log.warning(methodDecl.pos(),"esc.infeasible.preconditions",methodDecl.getName());
//                    if (escdebug) log.noticeWriter.println("Invariants+Preconditions are NOT satisfiable in " + methodDecl.getName());
//                    // FIXME - print out core ids if available?
//                    p.pop();
//                    return false;
//                } else {
//                    if (verbose) log.noticeWriter.println("Invariants+Preconditions are satisfiable");
//                }
//                p.pop();
//            }
            
            // compute negated start block id
            
            JCExpression negateStart = null;
            if (!(p instanceof SimplifyProver)) {
                JCIdent id = program.startBlock().id();
                negateStart = factory.Unary(JCTree.NOT,id);
                negateStart.type = syms.booleanType;
                Integer idd = p.assume(negateStart);
                defexpr.put(idd,negateStart);
            }

            // send block equations

            containingBlock = null;
            for (BasicBlock bl : program.blocks()) {
                JCExpression e = blockExpr(bl);
                e = factory.JmlBinary(JmlToken.EQUIVALENCE,bl.id,e); 
                e.pos = bl.id.pos;
                e.type = syms.booleanType;
                //log.noticeWriter.println("BLOCK " + bl.id + " " + Counter.countAST(e));
                Integer assertionNumber = p.assume(e);
                defexpr.put(assertionNumber,e);
            }

            // send any other axioms and definitions
            
            int assertionNumber = 0;
            for (JCExpression expr: program.background()) {
                assertionNumber = p.assume(expr);
                defexpr.put(assertionNumber,expr);
            }
            
            Map<JCExpression,Integer> defnum = new HashMap<JCExpression,Integer>();
            if (!usingSMT) {
                for (BasicProgram.Definition def: program.definitions()) {
                    JCExpression expr = def.expr(context);
                    assertionNumber = p.assume(expr);
                    defnum.put(expr,assertionNumber);
                    defexpr.put(assertionNumber,expr);
                }
            }

            for (JCExpression expr: program.pdefinitions) {
                assertionNumber = p.assume(expr);
                defnum.put(expr,assertionNumber);
                defexpr.put(assertionNumber,expr);
            }

            if (checkAssumptions && usePush) p.push();

            int assumptionCheck =0;
            if (BasicBlocker.insertAssumptionChecks) { // We have to include this unless no assumption encoding is done
                if (BasicBlocker.useCountedAssumeCheck) {
                    JCExpression e = factory.Literal(TypeTags.INT,0);
                    e.type = syms.intType;
                    e = factory.Binary(JCTree.EQ, program.assumeCheckVar, e);
                    e.type = syms.booleanType;
                    assumptionCheck = p.assume(e);
                    defexpr.put(assumptionCheck,e);
                } else {
                    assumptionCheck = p.assume(BasicBlocker.booleanAssumeCheck);
                    defexpr.put(assumptionCheck,BasicBlocker.booleanAssumeCheck);
                }
            }

            long time2=0,time3=0;
            
            firstProofResult = proofResult = p.check(true); // FIXME - are details supported by the prover?
            proverResults.put(methodDecl.sym,proofResult);
            String message = "Prover reported " + proofResult.result() + " for " + methodDecl.sym.owner.flatName() + "." + methodDecl.sym + " with prover " + proverToUse;
            if (proofResult.result() != IProverResult.UNSAT) message = message + JmlTree.eol + "Checking for counterexample information";
            progress(1,2,message);
            //log.noticeWriter.println("Recorded proof for " + methodDecl.sym); log.noticeWriter.flush();

            if (showTimes) {
                time2 = timer.elapsed();
                timer.reset();
            }
            
            boolean ok = !proofResult.isSat();
            if (timingTest > 0 && timingTest < 9) {
                if (showTimes) log.noticeWriter.println("TIMES-" + timingTest + " " + time2 + " " + (proofResult.isSat()?"SAT":"UNSAT") + " :: " + name);
                return proofResult;
            }
            
            Utils.Timer timer2 = new Utils.Timer();
            Utils.Timer timer3 = new Utils.Timer();
            if (proofResult.isSat()) {
                if (showTimes) log.noticeWriter.println("TIMES-" + timingTest + " " + time2 + " SAT :: " + name);
                if (escdebug) log.noticeWriter.println("Method does NOT satisfy its specifications, it appears");
                if (timingTest == 0) {
                    proofResult.setOtherInfo(BasicBlocker.TracerBB.trace(context,program,proofResult.counterexample(),p));
                    String cexample = displayCounterexampleInfo(methodDecl, program, p, proofResult);
                    if (showCounterexample || escdebug) log.noticeWriter.println(cexample);
                }
                if (mostRecentProver != null) mostRecentProver.kill();
                mostRecentProver = p;
            } else if (proofResult.result() == IProverResult.UNSAT && (timingTest == 10 || timingTest==9)) {
                if (escdebug) log.noticeWriter.println("Method satisfies its specifications (as far as I can tell)");
                p.kill();
                if (!checkAssumptions) return firstProofResult;
                
                int numbad = 0;
                for (BasicBlock blk : program.blocks()) {
                    for (JCStatement stt: blk.statements) {
                        if (stt instanceof JmlStatementExpr && ((JmlStatementExpr)stt).label == Label.ASSUME_CHECK) {
                            timer3.reset();
                            targetStatement = stt;
                            containingBlock = blk;

                            JCIdent ek = (JCIdent)((JmlStatementExpr)stt).expression;

                            String eid = ek.name.toString();
                            int pp = eid.lastIndexOf('_');
                            int ps = eid.indexOf('_');
                            int pos = Integer.parseInt(eid.substring(ps+1,pp));
                            String label = eid.substring(pp+1);

                            
                            // Find the block containing the expression to check
                            //                    containingBlock = null;
                            //                    targetStatement = null;
                            //                    outer: for (BasicBlock bl : program.blocks()) {
                            //                        for (JCStatement st: bl.statements) {
                            //                            if (st instanceof JmlStatementExpr && ((JmlStatementExpr)st).expression == ek) {
                            //                                targetStatement = st;
                            //                                containingBlock = bl;
                            //                                break outer;
                            //                            }
                            //                        }
                            //                    }
                            //                    if (containingBlock == null) {
                            //                        log.noticeWriter.println("COULD NOT FIND ASSUMPTION");
                            //                        continue;
                            //                    }

                            Set<BasicBlock> neededBlocks = new HashSet<BasicBlock>();
                            List<BasicBlock> todo = new LinkedList<BasicBlock>();
                            todo.add(containingBlock);
                            while (!todo.isEmpty()) {
                                BasicBlock b = todo.remove(0);
                                if (neededBlocks.contains(b)) continue;
                                todo.addAll(b.preceders);
                                neededBlocks.add(b);
                            }
                            
                            p = AbstractProver.getProver(context,proverToUse);
                            defexpr = new HashMap<Integer,JCExpression>();
                            
//                            for (BasicProgram.BasicBlock block : program.blocks()) {
//                                p.define(block.id.toString(),syms.booleanType);
//                            }

                            // send negated start block id

                            if (!(p instanceof SimplifyProver)) {
                                Integer idd = p.assume(negateStart);
                                defexpr.put(idd,negateStart);

                            }

                            // send block equations

                            for (BasicBlock bl : program.blocks()) {
                                JCExpression e = factory.Literal(TypeTags.BOOLEAN,1);  // TRUE
                                if (timingTest == 9 || neededBlocks.contains(bl)) {
                                    e = blockExpr(bl);
                                }
                                e = factory.JmlBinary(JmlToken.EQUIVALENCE,bl.id,e); 
                                e.pos = bl.id.pos;
                                e.type = syms.booleanType;
                                //log.noticeWriter.println("BLOCK " + bl.id + " " + Counter.countAST(e));
                                Integer idd = p.assume(e);
                                defexpr.put(idd,e);

                            }

                            // send any other axioms and definitions

                            assertionNumber = 0;
                            for (JCExpression expr: program.background()) {
                                assertionNumber = p.assume(expr);
                                defexpr.put(assertionNumber,expr);
                            }

                            defnum = new HashMap<JCExpression,Integer>();
                            for (BasicProgram.Definition def: program.definitions()) {
                                JCExpression expr = def.expr(context);
                                assertionNumber = p.assume(expr);
                                defnum.put(expr,assertionNumber);
                                defexpr.put(assertionNumber,expr);
                            }
                            for (JCExpression expr: program.pdefinitions) {
                                assertionNumber = p.assume(expr);
                                defnum.put(expr,assertionNumber);
                                defexpr.put(assertionNumber,expr);
                            }

                            if (BasicBlocker.insertAssumptionChecks) { // We have to include this unless no assumption encoding is done
                                JCExpression e = factory.Literal(TypeTags.INT,0);
                                e.type = syms.intType;
                                e = factory.Binary(JCTree.EQ, program.assumeCheckVar, e);
                                e.type = syms.booleanType;
                                assumptionCheck = p.assume(e);
                                defexpr.put(assumptionCheck,e);
                            }

                            proofResult = p.check(true);
                            if (escdebug) log.noticeWriter.println("CHECKING " + assumptionCheck + " " + assertionNumber);
                            if (!proofResult.isSat() && timingTest == 0) {
                                reportAssumptionProblem(label,pos,utils.qualifiedMethodSig(methodDecl.sym));
                                if (escdebug) log.noticeWriter.println(label + " " + proofResult.coreIds());
                                proofResult.result(IProverResult.INCONSISTENT);
                            } else {
                                
                            }
                            if (!proofResult.isSat()) {
                                numbad++;
                            }
                            p.kill();
                            long t3 = timer3.elapsed();
                            //log.noticeWriter.println("CHECKING " + eid + " " + r.isSat() +  " " + t3);

                        }
                    }
                }

                if (showTimes) {
                    time3 = timer.elapsed();
                    log.noticeWriter.println("TIMES-" + timingTest + " " + time2 + " " + time3 + " UNSAT checks: " + program.assumptionsToCheck.size() + " " + numbad + " " + (-1) + " :: " + name);
                }

            } else if (proofResult.result() == IProverResult.UNSAT && timingTest == 15 && !(p instanceof CVC3Prover)) {
                if (escdebug) log.noticeWriter.println("Method satisfies its specifications (as far as I can tell)");
                if (!checkAssumptions) return firstProofResult;
                int numcore = -1;
                int numbad = 0;
                if (usePush) { p.pop();  }
                String pcname = program.assumeCheckVar.sym.toString();
                int num = program.assumptionsToCheck.size();
                List<Integer> list = new ArrayList<Integer>(num);
                JCExpression exx = factory.Literal(TypeTags.BOOLEAN,1); // TRUE
                exx.type = syms.booleanType;
                while (num > 0) {
                    timer2.reset();
                    if (p instanceof CVC3Prover) {
                        p.push();
                        p.assume(exx);
                    }
                    proofResult = p.check(true);
                    if (!proofResult.isSat()) {
//                        log.noticeWriter.println("CHECKING " + "UNSAT" + " " + r.isSat() + " " + timer2.elapsed());
//                        log.noticeWriter.println("EVERYTHING ELSE IS INFEASIBLE " + num);
                        numbad = num;
                        break;
                    }
                    String result = proofResult.counterexample().get(pcname);
                    if (result == null) {
//                        log.noticeWriter.println("NO RESULT");
                        break;
                    }
                    if (p instanceof CVC3Prover) p.pop();
//                    log.noticeWriter.println("RESULT IS " + result);
                    int pos = Integer.parseInt(result);
                    JCExpression ex = factory.Binary(JCTree.NE, program.assumeCheckVar, factory.Literal(TypeTags.INT,pos));
                    ex.type = syms.booleanType;
                    exx = factory.Binary(JCTree.AND,exx,ex);
                    exx.type = syms.booleanType;
                    if (!(p instanceof CVC3Prover)) p.assume(ex);
                    list.add(pos);
                    --num;
//                    long t2 = timer2.elapsed();
//                    log.noticeWriter.println("CHECKING " + result + " " + r.isSat() + " " + t2);
                }
                if (showTimes) {
                    time3 = timer.elapsed();
                    log.noticeWriter.println("TIMES-" + timingTest + " " + time2 + " " + time3 + " UNSAT checks: " + program.assumptionsToCheck.size() + " " + numbad + " " + (-1) + " :: " + name);
                }
                p.kill();
                for (Map.Entry<JCExpression,String> nme:   program.assumptionsToCheck) {
                    String nm = nme.getValue();
                    int k = nm.indexOf('$');
                    int kk = nm.indexOf('$',k+1);
                    int ps = Integer.parseInt(nm.substring(k+1,kk));
                    if (list.contains(ps)) continue;
                    if (timingTest == 0) {
                        reportAssumptionProblem(nm.substring(kk+1),ps,utils.qualifiedMethodSig(methodDecl.sym));
                        log.noticeWriter.println(nm.substring(kk+1) + " " + proofResult.coreIds());
                        proofResult.result(IProverResult.INCONSISTENT);
                    }
                }
                
            } else if (proofResult.result() == IProverResult.UNSAT) {  // 0, 11, 12, 13, 14, 16, 17
                if (escdebug) log.noticeWriter.println("Method satisfies its specifications (as far as I can tell)");
                if (!checkAssumptions) return firstProofResult;
                
                //boolean useCoreIds = true; // FIXME - use an option
                //if (timingTest > 0) useCoreIds = timingTest == 11;

                ICoreIds cid = proofResult.coreIds();
                if (useCoreIds && cid == null && verbose) log.noticeWriter.println("Warning: Core ids unexpectedly not returned");
                Collection<Integer> cids = cid == null ? null : cid.coreIds();
                Integer[] ids = new Integer[0];
                if (useCoreIds && cids != null) {
                  ids = new Integer[cids.size()]; 
                  ids = cids.toArray(ids);
                }
                Arrays.sort(ids);
                int numcore = 0;
                int numbad = 0;
                if (useSearch) numbad = program.assumptionsToCheck.size();
                if (usePush) p.pop();
                String pcname = program.assumeCheckVar.sym.toString();
                JCExpression exx = factory.Literal(TypeTags.BOOLEAN,1);
                exx.type = syms.booleanType;
                for (Map.Entry<JCExpression,String> nm: program.assumptionsToCheck) {
                    timer2.reset();
                    JCExpression e = nm.getKey();
                    String eid = nm.getValue();
                    int pp = eid.lastIndexOf('$');
                    int ps = eid.indexOf('$');
                    int pos = Integer.parseInt(eid.substring(ps+1,pp));
                    String label = eid.substring(pp+1);
                    if (useCoreIds) {
                        int k = defnum.get(e);
                        int found = Arrays.binarySearch(ids,k);
                        if (found < 0) {
                            // Already not part of the minimal core
                            numcore++;
                            numbad++;
                            //                            if (escdebug || timingTest > 0) log.noticeWriter.println("ALREADY NOT IN MINIMAL CORE: " + pos + " " + label);
                            if (timingTest == 0) {
                                reportAssumptionProblem(label,pos,utils.qualifiedMethodSig(methodDecl.sym));
                                if (escdebug) log.noticeWriter.println(label + " " + proofResult.coreIds());
                                proofResult.result(IProverResult.INCONSISTENT);
                                if (escdebug) minimize(p,defexpr, proofResult.coreIds().coreIds(), assumptionCheck);
                            }
                            continue;
                        }
                    }
                    if (useSearch) {
                        if (useRetract) {
                            p.retract(assumptionCheck);
                            assumptionCheck = ((YicesProver)p).assumePlus(exx);
                            proofResult = p.check(true);
                        } else if (usePush) {
                            p.push();
                            assumptionCheck = p.assume(exx);
                            proofResult = p.check(true);
                            p.pop();
                        }
                        if (!proofResult.isSat()) {
                            //                              log.noticeWriter.println("CHECKING " + "UNSAT" + " " + r.isSat() + " " + timer2.elapsed());
                            //                              log.noticeWriter.println("EVERYTHING ELSE IS INFEASIBLE " + num);
//                            long t2 = timer2.elapsed();
//                            log.noticeWriter.println("CHECKING " + r.result() + " " + t2 + " " + eid);
                            break;
                        }
                        String result;
                        if (!BasicBlocker.useCountedAssumeCheck) {
                            JCExpression rres = null;
                            for (Map.Entry<JCExpression,String> nmm: program.assumptionsToCheck) {
                                String res = proofResult.counterexample().get(nmm.getValue());
                                if (res == null || res.equals("true")) continue;
                                //log.noticeWriter.println(nmm.getValue() + " IS FALSE " + res);
                                if (hasFeasibleChain(findContainingBlock(nmm.getKey(),program),proofResult.counterexample())) {
                                    //log.noticeWriter.println(nmm.getValue() + " IS FEASIBLE");
                                    rres = nmm.getKey();
                                    break;
                                }
                            }
                            if (rres == null) {
                                log.noticeWriter.println("NO RESULT");
                                break;
                            }
                            exx = factory.Binary(JCTree.AND,rres,exx);
                            exx.type = syms.booleanType;
                        } else {
                            result = proofResult.counterexample().get(pcname);
                            if (result == null) {
                                //                              log.noticeWriter.println("NO RESULT");
                                break;
                            }
                            int pps = Integer.parseInt(result);
                            JCExpression ex = factory.Binary(JCTree.NE, program.assumeCheckVar, factory.Literal(TypeTags.INT,pps));
                            ex.type = syms.booleanType;
                            exx = factory.Binary(JCTree.AND,ex,exx);
                            exx.type = syms.booleanType;
                        }

                        //                      if (escdebug || timingTest > 0) {
                        //                      if (r.isSat()) {
                        //                          log.noticeWriter.println("NOW SAT - ASSUMPTION WAS OK: " + pos + " " + label);
                        //                      } else {
                        //                          if (useCoreIds) log.noticeWriter.println("STILL UNSAT - CORE WAS NOT MINIMAL - ASSUMPTION WAS INFEASIBLE: " + pos + " " + label);
                        //                          else log.noticeWriter.println("STILL UNSAT - ASSUMPTION WAS INFEASIBLE: " + pos + " " + label);
                        //                      }
                        //                      }
                        //                        if (!r.isSat() && timingTest == 0) {
                        //                            reportAssumptionProblem(label,pos,methodDecl.sym.toString());
                        //                             r.result(IProverResult.INCONSISTENT);
                        //                        }
                        numbad--;
//                        long t2 = timer2.elapsed();
//                        log.noticeWriter.println("CHECKING " + r.result() + " " + t2 + " " + pps);
                    } else {
                        JCExpression ex = factory.Binary(JCTree.EQ, program.assumeCheckVar, factory.Literal(TypeTags.INT,pos));
                        ex.type = syms.booleanType;
                        if (useRetract) {
                            p.retract(assumptionCheck);
                            assumptionCheck = ((YicesProver)p).assumePlus(ex);
                            proofResult = p.check(true);
                        } else if (usePush) {
                            p.push();
                            assumptionCheck = p.assume(ex);
                            proofResult = p.check(true);
                            p.pop();
                        }
                        //                      if (escdebug || timingTest > 0) {
//                                              if (r.isSat()) {
//                                                  log.noticeWriter.println("NOW SAT - ASSUMPTION WAS OK: " + pos + " " + label);
//                                              } else {
//                                                  if (useCoreIds) log.noticeWriter.println("STILL UNSAT - CORE WAS NOT MINIMAL - ASSUMPTION WAS INFEASIBLE: " + pos + " " + label);
//                                                  else log.noticeWriter.println("STILL UNSAT - ASSUMPTION WAS INFEASIBLE: " + pos + " " + label);
//                                              }
                        //                  }
                        if (!proofResult.isSat() && timingTest == 0) {
                            reportAssumptionProblem(label,pos,utils.qualifiedMethodSig(methodDecl.sym));
                            if (escdebug) log.noticeWriter.println(label + " " + proofResult.coreIds());
                            proofResult.result(IProverResult.INCONSISTENT);
                            minimize(p, defexpr, proofResult.coreIds().coreIds(), assumptionCheck);
                        }
                        if (!proofResult.isSat()) {
                            numbad++;
                        }
//                        long t2 = timer2.elapsed();
//                        log.noticeWriter.println("CHECKING " + r.result() + " " + t2 + " " + eid);
                    }
                }
                if (showTimes) {
                    time3 = timer.elapsed();
                    log.noticeWriter.println("TIMES-" + timingTest + " " + time2 + " " + time3 + " UNSAT checks: " + program.assumptionsToCheck.size() + " " + numbad + " " + (useCoreIds?numcore:-1) + " :: " + name);
                }
            } else {
                // Result is unknown
                // FIXME - need some tests and more output information here
                if (escdebug) log.noticeWriter.println("Status of method is UNKNOWN - prover failed");
                log.error("esc.proof.failed", proofResult.result(), methodDecl.sym);
                firstProofResult = new ProverResult(proverToUse,IProverResult.ERROR);
            }

        } catch (ProverException e) {
            String se = e.mostRecentInput == null ? Strings.empty :e.mostRecentInput;
            if (se.length() > 200) se = se.substring(0,200) + " .......";
            log.warning(methodDecl.pos(),"esc.prover.failure",methodDecl.sym.toString() + ": " + e.getLocalizedMessage() + ":" + se); // FIXME - change to error
            if (escdebug) {
                log.noticeWriter.println("PROVER FAILURE: " + e);
                if (e.mostRecentInput != null) log.noticeWriter.println("INPUT: " + se);
                e.printStackTrace(log.noticeWriter);
            }
            try {
                if (p != null) p.kill();
            } catch (ProverException ee) {
                log.warning(methodDecl.pos(),"esc.internal.error","Failed to kill process: " + ee);
                // Report but ignore any problems in killing
            }
            firstProofResult = new ProverResult(proverToUse,IProverResult.ERROR);
            firstProofResult.setOtherInfo(e.getMessage());
        } catch (Throwable e) {
            log.warning(methodDecl.pos(),"esc.prover.failure",methodDecl.sym.toString() + ": " + e.getLocalizedMessage());
            if (escdebug) log.noticeWriter.println("PROVER FAILURE: " + e.getClass() + " " + e);
            e.printStackTrace(log.noticeWriter);
            firstProofResult = new ProverResult(proverToUse,IProverResult.ERROR);
            // FIXME - set other info?
        }
        // FIXME - dmz: I added this extra kill to fix Yices processes hanging around
        // on OS X and causing problems for unit tests ("resource not available"), but
        // there should be some other way to just make sure that the process is always
        // dead when we exit this method.
        try {
            if (p != null) p.kill();
        } catch (ProverException e) {
            log.warning(methodDecl.pos(),"esc.internal.error", "Failed to kill process: " + e);
            // ignore any problems in killing
        }
        return firstProofResult;
    }
    
    public void minimize(IProver prover, Map<Integer,JCExpression> defexpr, Collection<Integer> coreIds, int assumeCount) {
        if (!escdebug) return;
        Integer[] ids = coreIds.toArray(new Integer[coreIds.size()]);
        Arrays.sort(ids);
        try {
            prover.push();
            // Remove everything but
            for (int i=1; i<=assumeCount; i++) {
                int found = Arrays.binarySearch(ids,i);
                if (found < 0) {
                    prover.retract(i);
                    log.noticeWriter.println("Retracted " + i);
                }
            }
            IProverResult rr = prover.check(true);
            if (rr.isSat()) {
                log.noticeWriter.println("Redacted problem now satisfiable ??? ");
                return;
            }
            log.noticeWriter.println("Redacted problem still unsatisfiable");
            java.util.List<Integer> keepers = new LinkedList<Integer>();
            for (int i: ids) {
                prover.retract(i);
                rr = prover.check(true);
                log.noticeWriter.println("Retracted " + i + ": " + rr.result());
                if (rr.isSat()) {
                    JCExpression e = defexpr.get(i);
                    prover.assume(e);
                    keepers.add(i);
                    log.noticeWriter.println("Restored and keeping " + i );
                } else {
                    log.noticeWriter.println("Continuing without restoring " + i );
                }
            }
            log.noticeWriter.println("The following appear to be a contradictory core:");
            for (Integer k: keepers) {
                log.noticeWriter.print(k + "] ");
                JmlPretty pw = new JmlPretty(log.noticeWriter,false);
                defexpr.get(k).accept(pw);
                log.noticeWriter.println(Strings.empty);
            }
            prover.pop();
        } catch (ProverException e) {
            log.noticeWriter.println("Could not retract " + e);
        }
        return;

    }


    /** For a SAT result, this prints out counterexample information in a human
     * usable form
     * @param methodDecl The declaration of the method being verified
     * @param program The Basic program for that method
     * @param p The prover being used
     * @param r The result from that prover
     */
    protected String displayCounterexampleInfo(JCMethodDecl methodDecl,
            BasicProgram program, IProver p, IProverResult r) {
        StringWriter sw = new StringWriter();
        Writer w = sw;
        ICounterexample s = r.counterexample();
        boolean noinfo = true;
        if (s != null) {
            // Find out the termination position; null means that the information
            // was not available from the counterexample - either because the
            // prover did not return it, or because of some bug in the
            // program
            String terminationValue = s.get(BasicBlocker.TERMINATION_VAR);
            int terminationPosition = terminationValue == null ? 0 :
                                Integer.valueOf(terminationValue);
            // Find the assert with the smallest uniqueness number, that is in a feasible block
            //    FIXME - we're presuming that the one with the smallest uniqueness number comes
            //     earliest in the block; subsequent assertions may also be reportable, but if
            //     they come after assumptions, they are suspect
            // Look for "assert$<number>$<number>(@<number>)?$<Label>$<number>"
            Pattern pat1 = Pattern.compile("\\Aassert\\$(\\d+)\\$(\\d+)(@(\\d+))?\\$(\\w+)\\$(\\d+)\\z");
            Matcher found = null;
            int foundNum = Integer.MAX_VALUE;
            for (Map.Entry<String,String> var: s.sortedEntries()) {
                String sname = var.getKey();
                if (!sname.startsWith("assert$")) continue;
                Matcher m = pat1.matcher(sname);
                if (var.getValue().equals("false") && m.find()) {
                    Name v = names.fromString(sname);
                    BasicBlock bl = findContainingBlock(v,program);
                    if (bl == null || hasFeasibleChain(bl,s) ) {
                        int nn = Integer.parseInt(m.group(6));
                        if (nn < foundNum) { foundNum = nn; found = m; }
                        if (escdebug) log.noticeWriter.println("Assertion " + sname + " is false");
                    }
                }
            }
            if (found != null) {
                Matcher m = found;
                String sname = m.group(0); // full name of the assertion
                String label = m.group(5); // the label part 
                int usepos = Integer.parseInt(m.group(1)); // the textual location of the assert statement
                int declpos = Integer.parseInt(m.group(2)); // the textual location of associated information (or same as usepos if no associated information)
                JavaFileObject jfo = null;
                String fintstr = m.group(4);
                if (fintstr != null) {
                	Integer i = Integer.valueOf(fintstr);
                	jfo = BasicBlocker.getFileForInt(i);
                }
                int termpos = usepos;
                if (terminationValue != null &&
                		(Label.POSTCONDITION.toString().equals(label) ||
                				Label.INVARIANT.toString().equals(label) ||
                				Label.CONSTRAINT.toString().equals(label) ||
                				Label.INITIALLY.toString().equals(label) ||
                				Label.SIGNALS.toString().equals(label) ||
                				Label.SIGNALS_ONLY.toString().equals(label))) {
                	// terminationPosition is, 
                	// if positive, the source code location of the return statement,
                	// if negative, the negative of the source code location of
                	//          the throw statement or method call of an exception exit
                	// if 0, the method exits out the end of the block.  
                	// In this last case, one would like to point the
                	// error message to the end of the block, but since
                	// we do not at the moment have support for 
                	// end positions, we use the position of the 
                	// method declaration. (TODO)
                	if (terminationPosition == 0) termpos = usepos; 
                	else if (terminationPosition > 0) termpos = terminationPosition;
                	else                             termpos = -terminationPosition;
                }
                Name v = names.fromString(sname);
                BasicBlock bl = findContainingBlock(v,program);
                // A 'false' assertion is spurious if it happens in a block 
                // which is not executed (its block variable is 'true')
                // So we list the assertion if
                //      - we cannot find a block containing the assertion (just to be safe)
                //      - we find a block but find no value for the block variable (just to be safe)
                //      - the block variable is 'false' (not 'true') and there is a chain of false blocks back to the beginning
                if (bl == null || hasFeasibleChain(bl,s) ) {
                	if (declpos != termpos || jfo != null) {

                		JavaFileObject prev = log.currentSourceFile();
                        // The suppress call here suppresses reporting warnings, but not actually testing them.
                        // We moved the suppression to avoid putting assert tests in, but here is where to 
                        // turn off the reporting.
//                		if (Nowarns.instance(context).suppress(log.currentSource(), termpos, label)) {
//                		    // nothing to do
//                		} else 
                		if (!cfInfo) {
                			log.warning(termpos,"esc.assertion.invalid",label,methodDecl.getName(), Strings.empty);

                			if (jfo != null) log.useSource(jfo);
                			log.warning(declpos,"esc.associated.decl",Strings.empty);

                		} else {
                			// This way of finding line numbers is a bit expensive - it reads in the
                			// whole file and scans from the beginning.
                			// Is there a way to use the endPos table?  FIXME

                			int line = new DiagnosticSource(prev,log).getLineNumber(termpos);

                			//if (jfo != null) log.useSource(jfo);
                			int aline = new DiagnosticSource(jfo==null?prev:jfo,log).getLineNumber(declpos);
                			//log.useSource(prev);

                			String cf = !cfInfo ? Strings.empty : " [ cf. " + (jfo==null?prev:jfo).getName() + ", line " + aline + "]";
                			log.warning(termpos,"esc.assertion.invalid",label,methodDecl.getName() + cf, Strings.empty);

                			if (jfo != null) log.useSource(jfo);
                			String assocPos = !cfInfo ? Strings.empty : " [" + prev.getName() + ", line " + line + "]";
                			log.warning(declpos,"esc.associated.decl",assocPos);
                		}
                		log.useSource(prev);
                	} else {
                		log.warning(termpos,"esc.assertion.invalid",label,methodDecl.getName(), Strings.empty);
                	}
                	//if (declpos != usepos) Log.printLines(log.noticeWriter,"Associated information");
                	noinfo = false;
                }
            }

        }

        if (noinfo) {
            log.warning(methodDecl.pos(),"esc.method.invalid",methodDecl.getName());
        } else {
            Pattern pat2 = Pattern.compile("^\\$\\$LBLPOS\\$(\\d+)\\$([^ ]+)");
            for (Map.Entry<String,String> var: s.sortedEntries()) {
                Matcher m = pat2.matcher(var.getKey());
                if (var.getValue().equals("true") && m.find()) {
                    int pos = Integer.parseInt(m.group(1));
                    String label = m.group(2);
                    log.warning(pos,"esc.label",label);
                    if (escdebug) log.noticeWriter.println("Label " + label + " has value " + var.getValue());
                }
            }
            Pattern pat3 = Pattern.compile("^\\$\\$LBLNEG\\$(\\d+)\\$([^ ]+)");
            for (Map.Entry<String,String> var: s.sortedEntries()) {
                Matcher m = pat3.matcher(var.getKey());
                if (var.getValue().equals("false") && m.find()) {
                    int pos = Integer.parseInt(m.group(1));
                    String label = m.group(2);
                    log.warning(pos,"esc.label",label);
                    if (escdebug) log.noticeWriter.println("Label " + label + " has value " + var.getValue());
                }
            }
            Pattern pat4 = Pattern.compile("^\\$\\$LBLANY\\$(\\d+)\\$([^ ]+)");
            for (Map.Entry<String,String> var: s.sortedEntries()) {
                Matcher m = pat4.matcher(var.getKey());
                if (m.find()) {
                    int pos = Integer.parseInt(m.group(1));
                    String label = m.group(2);
                    log.warning(pos,"esc.label.value",label,var.getValue());
                    if (escdebug) log.noticeWriter.println("Label " + label + " has value " + var.getValue());
                }
            }
        }
        String result = Strings.empty;
        
        if (showTrace || escdebug) {
            log.noticeWriter.println("Trace " + methodDecl.getName());
            //BasicBlocker.Tracer.trace(context,methodDecl,s);
            log.noticeWriter.println(result = BasicBlocker.TracerBB.trace(context,program,s,p));
        }
        if (showCounterexample || escdebug) {
            log.noticeWriter.println("Counterexample:");
            // Just some arbitrary number of spaces used to format lines
            String spaces = "                                ";
            for (Map.Entry<String,String> var: s.sortedEntries()) {
                int k = var.getKey().length();
                if (k >= spaces.length()) k = spaces.length()-1;
                log.noticeWriter.println("    " + var.getKey() + spaces.substring(k) + var.getValue());
            }
        }
        return result;
    }
    
    /** Reports the details of a problem when an assumption is infeasible.
     * This happens when the assumption is not needed, which is known when
     * the program is still valid (the VC is unsatisfiable) with a false
     * assertion following the assumption.
     * 
     * @param label the label given to the assumption
     * @param pos   the textual position of the associated statement
     * @param methodSignature the name or signature of the method being tested
     */
    public void reportAssumptionProblem(String label, int pos, String methodSignature) {
        // The suppress call here suppresses reporting warnings, but not actually testing them.
        // We moved the suppression to avoid putting assert tests in, but here is where to 
        // turn off the reporting.
        //if (Nowarns.instance(context).suppress(log.currentSource(), pos, label)) return;
        if (label.equals(Label.BRANCHT.toString())) {
            log.warning(Math.abs(pos),"esc.infeasible.branch","then",methodSignature);
            if (escdebug) log.noticeWriter.println("Branch is infeasible at " + pos);
        } else if (label.equals(Label.BRANCHE.toString())) {
            log.warning(Math.abs(pos),"esc.infeasible.branch","else",methodSignature);
            if (escdebug) log.noticeWriter.println("Branch is infeasible at " + pos);
        } else if (label.equals(Label.CASECONDITION.toString())) {
            log.warning(Math.abs(pos),"esc.infeasible.case",methodSignature);
            if (escdebug) log.noticeWriter.println("Switch case is infeasible at " + pos);
        } else if (label.equals(Label.PRECONDITION.toString())) {
            log.warning(Math.abs(pos),"esc.infeasible.preconditions",methodSignature);
            if (escdebug) log.noticeWriter.println("Preconditions are infeasible at " + pos);
        } else {
            log.warning(pos,"esc.infeasible.assumption",methodSignature);
            if (escdebug) log.noticeWriter.println("Assumption (" + label + ") is infeasible");
        }
    }
    
    /** Checks to see if the given BasicBLock has a feasible chain back to the
     * program start, within the set of variable assignments given in a
     * counterexample.  A BasicBlock is feasible if its block variable is 'false' in
     * the counterexample and either it is the start block or it follows a
     * feasible block.
     * @param bl the BasicBlock to check
     * @param s the counterexample whose assignments to use
     * @return true if feasible, false if not
     */
    public boolean hasFeasibleChain(/*@ non_null*/ BasicBlock bl, /*@ non_null*/ ICounterexample s) {
        if ("true".equals(s.get(bl.id.name.toString()))) return false;
        if (bl.preceders.size() == 0) return true; // presuming it is the start block, which may not be the case?? FIXME
        for (BasicBlock b: bl.preceders) {
            if (hasFeasibleChain(b,s)) return true;
        }
        return false;
    }
    
    /** Finds the basic block containing an assertion with the given name
     * 
     * @param assertName the name of the assertion as used in the definition
     * @param program the basic program in which to find the block
     * @return the BasicBlock in which the assertion occurs, or null if not found
     */
    public /*@ nullable */ BasicBlock findContainingBlock(/*@ non_null*/ Name assertName, /*@ non_null*/ BasicProgram program) {
        for (BasicBlock block: program.blocks) {
            for (JCStatement st: block.statements) {
                if ((st instanceof JmlStatementExpr) &&
                        ((JmlStatementExpr)st).token == JmlToken.ASSERT) {
                    JCExpression expr = ((JmlStatementExpr)st).expression;
                    if ((expr instanceof JCIdent) &&
                            ((JCIdent)expr).name == assertName) return block;
                }
            }
        }
        return null;
    }
    
    public /*@ nullable */ BasicBlock findContainingBlock(/*@ non_null*/ JCExpression expression, /*@ non_null*/ BasicProgram program) {
        for (BasicBlock block: program.blocks) {
            for (JCStatement st: block.statements) {
                if ((st instanceof JmlStatementExpr) &&
                        ((JmlStatementExpr)st).token == JmlToken.ASSERT) {
                    if (expression == ((JmlStatementExpr)st).expression) return block;
                }
            }
        }
        return null;
    }
}

