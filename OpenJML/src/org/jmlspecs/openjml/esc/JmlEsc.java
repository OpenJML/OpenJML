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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.esc.BasicBlocker.Counter;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICoreIds;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;
import org.jmlspecs.openjml.proverinterface.ProverException;
import org.jmlspecs.openjml.proverinterface.ProverResult;
import org.jmlspecs.openjml.provers.AbstractProver;
import org.jmlspecs.openjml.provers.CVC3Prover;
import org.jmlspecs.openjml.provers.SimplifyProver;
import org.jmlspecs.openjml.provers.YicesProver;
import org.jmlspecs.openjml.utils.ExternalProcess;
import org.smtlib.ICommand;
import org.smtlib.IResponse;
import org.smtlib.IResponse.IError;
import org.smtlib.ISolver;
import org.smtlib.IVisitor.VisitorException;
import org.smtlib.SMT;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.DiagnosticSource;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Position;
import com.sun.tools.javac.util.PropagatedException;

/**
 * This class is the main driver for executing ESC on a Java/JML AST. It
 * formulates the material to be proved, initiates the proofs, and obtains and
 * reports the results. The class is also a TreeScanner so that it can easily
 * walk the tree to find all class and method declarations.
 * 
 * FIXME - describe calling mechanism
 * 
 * @author David R. Cok
 */
public class JmlEsc extends JmlTreeScanner {

    public boolean cfInfo = false;
    
    public Map<MethodSymbol,IProverResult> proverResults = new HashMap<MethodSymbol,IProverResult>();
    
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
    
    /** true if compiler options are set to a verbose mode */
    boolean verbose;
    
    /** Just for debugging esc */
    public static boolean escdebug;
    
    /** true if counterexample information is desired */
    boolean showCounterexample;
    
    /** true if counterexample trace information is desired */
    boolean showTrace;
    
    /** true if subexpression trace information is desired */
    boolean showSubexpressions;
    
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
    
    /** Whether to check that key assumptions are feasible */
    public boolean checkAssumptions = true;

    /** The prover to use */
    public /*@NonNull*/ String proverToUse;
    
//    @NonNull final static public String arraysRoot = "$$arrays";  // Reference in masicblocker?

    // FIXME - check whether a new JmlEsc is created for each new check,
    // if not, the option values will not be updated
    
    /** The JmlEsc constructor, which initializes all the tools and other fields. */
    public JmlEsc(Context context) {
        this.context = context;
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.log = Log.instance(context);
        this.names = Names.instance(context);
        this.factory = JmlTree.Maker.instance(context);
        this.verbose = JmlOption.isOption(context,"-verbose") ||
            Utils.instance(context).jmlverbose >= Utils.JMLVERBOSE;
        this.showCounterexample = JmlOption.isOption(context,"-ce") || JmlOption.isOption(context,JmlOption.COUNTEREXAMPLE) || JmlOption.isOption(context,JmlOption.JMLVERBOSE);
        this.showSubexpressions = JmlOption.isOption(context,JmlOption.SUBEXPRESSIONS);
        this.showTrace = showCounterexample || JmlOption.isOption(context,JmlOption.TRACE) || showSubexpressions;
        this.checkAssumptions = !JmlOption.isOption(context,"-noCheckAssumptions");
        escdebug = escdebug || Utils.instance(context).jmlverbose >= Utils.JMLDEBUG;
        this.cfInfo = JmlOption.isOption(context,"-crossRefAssociatedInfo");
    }
    
    public void pickProver() {
        // Pick a prover to use
        proverToUse = JmlOption.value(context,JmlOption.PROVER);
        if (proverToUse == null) proverToUse = Options.instance(context).get(Strings.defaultProverProperty);
        if (proverToUse == null) proverToUse = YicesProver.NAME;
        
        //proverToUse = "cvc";
        //proverToUse = "simplify";
        //proverToUse = "smt";
    }

    /** Visit a class definition */
    public void visitClassDef(JCClassDecl node) {
        if (node.sym.isInterface()) return;  // Nothing to verify in an interface
            // TODO: not so - could check that specs are consistent
        //log.noticeWriter.println("DOING CLASS " + node.sym);
        // The super class takes care of visiting all the methods
        super.visitClassDef(node);
    }

    // TODO - turn these into options
    static boolean usePush = true;
    static boolean useRetract = false;
    static boolean useSearch = false;
    static boolean useCoreIds = false;
    static boolean useTree = false;

    int timingTest;

    /** When we visit a method declaration, we translate and prove the method;
     * we do not walk into the method any further from this call, only through
     * the translation mechanism.  
     */  // FIXME - what about local classes or anonymous classes
    public void visitMethodDef(@NonNull JCMethodDecl node) {
        if (!(node instanceof JmlMethodDecl)) {
            // TODO - I would think this is an internal error
            log.warning(node.pos(),"esc.not.implemented","Unexpected non-JmlMethodDecl in JmlEsc - not checking " + node.sym);
            return;
        }
        
        // The code in this method decides whether to attempt a proof of this method.
        // If so, it sets some parameters and then calls proveMethod
        // We don't check abstract or native methods (no source)
        // nor synthetic methods.
        
        boolean isConstructor = node.sym.isConstructor();
        boolean doEsc = ((node.mods.flags & (Flags.SYNTHETIC|Flags.ABSTRACT|Flags.NATIVE)) == 0);
            // TODO: Could check that abstract or native methods have consistent specs
        
        // Don't do ESC on the constructor of Object
        // FIXME - why?  (we don't have the source anyway, so how would we get here?)
        if (node.sym.owner == syms.objectType.tsym && isConstructor) doEsc = false;
        if (!doEsc) return;

        String name = node.sym.owner + "." + node.sym;

        String methodToDo = Options.instance(context).get(JmlOption.METHOD.optionName());
        if (methodToDo != null && !name.contains(methodToDo)) {
            if (escdebug) log.noticeWriter.println("Skipping " + name + " because it does not contain " + methodToDo);
            return ;  // TODO - pattern match? include class name?
        }

        Pattern doPattern = 
            null; 
        //Pattern.compile("escjava[.]ast[.]ArrayRangeRefExpr[.]getTag[(].*"); 
        //Pattern.compile("escjava[.]sortedProver[.]Lifter[.]FnTerm[.]dump[(].*"); 
        Pattern[] avoids = {
//               Pattern.compile(".*anonymous.*"),

//                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]FnTerm[.]printTo[(].*"), // too much time
//                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]Term[.]toString[(].*"), // too much time
//                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]Term[.]printTo[(].*"), // too much time
//                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]QuantVariableRef[.]printTo[(].*"), // too much time
//                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]FnTerm[.]dump[(].*"), // too much memory
//                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]SortVar[.]toString[(].*"), // too much time
//                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]warn[(].*"), // failed to write to prover
//                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]convert[(].*"), // failed to write to prover
//                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]newMethod[(].*"), // binary generic
//                Pattern.compile("escjava[.]sortedProver[.]Lifter[.]Lifter[(].*"), // failed to write to prover
//              Pattern.compile("javafe[.]ast[.][a-zA-Z]*[.]getTag[(].*"), // too much time
//                Pattern.compile("javafe[.]ast[.]CompoundName[.]prefix[(].*"), // out of resources
//                Pattern.compile("javafe[.]ast[.]BinaryExpr[.]getStartLoc[(].*"), // out of resources
//                Pattern.compile("javafe[.]ast[.]BinaryExpr[.]postCheck[(].*"), // out of resources
//                Pattern.compile("javafe[.]ast[.]BinaryExpr[.]accept[(].*"), // out of resources
//                Pattern.compile("javafe[.]Options[.]processOption[(].*"), // out of resources
//                Pattern.compile("javafe[.]parser[.]Token[.]ztoString[(].*"), // out of resources
//
//                Pattern.compile("javafe[.]ast[.].*[.]toString[(].*"), // out of resources
//                Pattern.compile("escjava[.]AnnotationHandler[.]NestedPragmaParser[.]parseAlsoSeq[(].*"), // out of resources
//                Pattern.compile("escjava[.]AnnotationHandler[.]NestedPragmaParser[.]parseSeq[(].*"), // out of resources
        
        };
        if (doPattern != null) {
            if (!doPattern.matcher(name).matches()) return;//{log.noticeWriter.println("skipping " + name); return; }
        }
        for (Pattern avoid: avoids) {
            if (avoid.matcher(name).matches()) {log.noticeWriter.println("skipping " + name); return; }
        }
        

        // FIXME - turn off in quiet mode? 
        //Log.printLines(log.noticeWriter,"["+(++ord)+"] "+ "ESC: Checking method "+ name);
        if (escdebug) log.noticeWriter.println(node.toString()); // print the method

        if (JmlOption.isOption(context, JmlOption.BOOGIE)) {
            proveWithBoogie(node);
            return;
        }
        boolean doTimingTests = false;
        
        if (!doTimingTests) {
            timingTest = 0;
            proveMethod(node);
        } else {
            log.noticeWriter.println("METHOD: " + name);
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
                
                proveMethod(node);
            }
        }
    }

    public void progress(int ticks, int level, String message) {
        org.jmlspecs.openjml.Main.IProgressListener pr = context.get(org.jmlspecs.openjml.Main.IProgressListener.class);
        boolean cancelled = pr == null ? false : pr.report(ticks,level,message);
        if (cancelled) {
            throw new PropagatedException(new Main.JmlCanceledException("ESC operation cancelled"));
        }
    }
    
    public boolean proveWithBoogie(JCMethodDecl decl) {
        boolean print = true; //true;
        if (print && decl.name.toString().equals("<init>")) {
            log.noticeWriter.println("SKIPPING PROOF OF " + decl.name);
            return true;
        }
        proverToUse = "z3_4_3";
        progress(1,2,"Starting proof of " + decl.sym.owner.flatName() + "." + decl.sym + " with prover " + proverToUse);
        
        if (print) {
            log.noticeWriter.println("");
            log.noticeWriter.println("--------------------------------------");
            log.noticeWriter.println("");
            log.noticeWriter.println("STARTING PROOF OF " + decl.name);
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
                if (kk < 0) kk = id.lastIndexOf(BasicBlockerParent.THROW);
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
                String extra = "";
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
    
    public IProverResult newProveMethod(JCMethodDecl decl) {
        boolean print = true; //true;
        if (print && decl.name.toString().equals("<init>")) {
            log.noticeWriter.println("SKIPPING PROOF OF " + decl.name);
            return new ProverResult(proverToUse,IProverResult.SKIPPED);
        }
        proverToUse = "z3_4_3";
        progress(1,2,"Starting proof of " + decl.sym.owner.name + "." + decl.name + " with prover " + proverToUse);
        
        if (print) {
            log.noticeWriter.println("");
            log.noticeWriter.println("--------------------------------------");
            log.noticeWriter.println("");
            log.noticeWriter.println("STARTING PROOF OF " + decl.name);
            log.noticeWriter.println(JmlPretty.write(decl.body));
        }
        
        JmlMethodDecl methodDecl = (JmlMethodDecl)decl;
        JmlClassDecl currentClassDecl = (JmlClassDecl)JmlEnter.instance(context).getEnv((ClassSymbol)decl.sym.owner).tree;
        
        // Get the denested specs for the method - FIXME - when might they be null?
        if (methodDecl.sym == null) {
            log.error("jml.internal.notsobad", "Unexpected null symbol for " + decl.name);
        }
        JmlMethodSpecs denestedSpecs = methodDecl.sym == null ? null : specs.getDenestedSpecs(methodDecl.sym);

        JmlAssertionAdder assertionAdder = new JmlAssertionAdder(context,true,false);
        JCBlock newblock = assertionAdder.convertMethodBody(methodDecl,currentClassDecl);
        
        if (newblock == null) {
            IProverResult pr =  new ProverResult(proverToUse,IProverResult.ERROR);
            pr.setOtherInfo("Aborting proof attempt because of internal error");
            return pr;
        }
        
        if (print) log.noticeWriter.println(JmlPretty.write(newblock));
        
        BasicProgram program = new BasicBlocker2(context).convertMethodBody(newblock, decl, denestedSpecs, currentClassDecl, assertionAdder);
        
        if (print) log.noticeWriter.println(program.toString());
        
        ICommand.IScript script = new SMTTranslator(context).convert(program);
                
        if (print) try {
            org.smtlib.sexpr.Printer.write(new PrintWriter(log.noticeWriter),script);
            log.noticeWriter.println();
            log.noticeWriter.println();
        } catch (VisitorException e) {
        }
        
        SMT smt = new SMT();
        //smt.processCommandLine(new String[]{"-L","C:/cygwin/home/dcok/eprojects/SMTProjects/SMT/logics"}, smt.smtConfig);
        smt.processCommandLine(new String[]{}, smt.smtConfig);
        
        String exec = proverToUse.equals("test") ? null : Options.instance(context).get("openjml.prover." + proverToUse);
        ISolver solver = smt.startSolver(smt.smtConfig,proverToUse,exec);
        
        smt.smtConfig.log.addListener(new SMTListener(log,smt.smtConfig.defaultPrinter));
        
        if (print) log.noticeWriter.println("EXECUTION");
        IResponse r = script.execute(solver);
        IProverResult proofResult;
        if (r.isError()) {
            log.error("jml.esc.badscript", decl.getName(), smt.smtConfig.defaultPrinter.toString(r));
            return new ProverResult(proverToUse,IProverResult.ERROR);
        }
        if (print) log.noticeWriter.println(smt.smtConfig.defaultPrinter.toString(r));
        if (r.toString().equals("unsat")) {// FIXME - should have a better means of checking this
            if (print) log.noticeWriter.println("Method checked OK");
            proofResult = new ProverResult(proverToUse,IProverResult.UNSAT);
        } else {
            proofResult = new ProverResult(proverToUse,
                    r.toString().equals("sat") ? IProverResult.SAT : IProverResult.POSSIBLY_SAT);
            if (print) log.noticeWriter.println("Some assertion not valid"); // FIXME - counterexample
            if (trace) log.noticeWriter.println("\nTRACE\n");
            reportInvalidAssertion(program,smt,solver,decl);
//            if (!assertionAdder.labels.isEmpty()) {
//                java.util.List<IExpr.ISymbol> smtsymbols = new LinkedList<IExpr.ISymbol>();
//                for (String label: assertionAdder.labels) {
//                    smtsymbols.add(smt.smtConfig.exprFactory.symbol(label));
//                }
//                IResponse resp = solver.get_value(smtsymbols.toArray(new IExpr.ISymbol[smtsymbols.size()]));
//                for (ISexpr s: ((Sexpr.Seq)resp).sexprs()) {
//                    if (s instanceof Sexpr.Seq) {
//                        String nm = ((Sexpr.Seq)s).sexprs().get(0).toString();
//                        String val = ((Sexpr.Seq)s).sexprs().get(1).toString();
//                        boolean b = Boolean.parseBoolean(val);
//                        log.noticeWriter.println(smt.smtConfig.defaultPrinter.toString(s));
//                    }
//                }
//                //log.noticeWriter.println(smt.smtConfig.defaultPrinter.toString(resp));
//            }
        }
        return proofResult;
    }
    
    public void reportInvalidAssertion(BasicProgram program, SMT smt, ISolver solver, JCMethodDecl decl) {
        terminationPos = 0;
        boolean ok = reportInvalidAssertion(program.startBlock(),smt,solver,decl);
        if (!ok) {
            log.noticeWriter.println("COULD NOT FIND INVALID ASSERTION"); // FIXME
            // COULD NOT FIND
        }
        
//        for (Map.Entry<String,DiagnosticPositionSES> entry: assertionAdder.positionMap.entrySet()) {
//            
//            String n = entry.getKey();
//            org.smtlib.IExpr.ISymbol s = smt.smtConfig.exprFactory.symbol(n,null);
//            IResponse resp = solver.get_value(s);
//            IExpr e = ((IResponse.IValueResponse)resp).values().get(0).second();
//            System.out.println(n + " :: " + resp);
//            if (e instanceof IExpr.ISymbol && e.toString().equals("true")) {
//                System.out.println("    " + assertionAdder.positionMap.get(n));
//            }
//        }

    }
    
    public boolean getBoolValue(String id, SMT smt, ISolver solver) {
        org.smtlib.IExpr.ISymbol s = smt.smtConfig.exprFactory.symbol(id);
        IResponse resp = solver.get_value(s);
        if (resp instanceof org.smtlib.sexpr.ISexpr.ISeq){
            org.smtlib.sexpr.ISexpr se = ((org.smtlib.sexpr.ISexpr.ISeq)resp).sexprs().get(0);
            return !se.toString().contains("false"); // FIXME - really should test the second item of the returned pair
        } else if (resp instanceof IResponse.IError) {
            log.error("jml.internal.notsobad", ((IResponse.IError)resp).errorMsg());
            return true;
        } else if (resp == null) {
            log.error("jml.internal.notsobad", "Could not find value of assertion: " + id);
            return true;
        } else {
            log.error("jml.internal.notsobad", "Unexpected response on requesting value of assertion: " + smt.smtConfig.defaultPrinter.toString(resp));
            return true;
        }
    }
    
    public int getIntValue(String id, SMT smt, ISolver solver) {
        org.smtlib.IExpr.ISymbol s = smt.smtConfig.exprFactory.symbol(id);
        IResponse resp = solver.get_value(s);
        org.smtlib.sexpr.ISexpr se = ((org.smtlib.sexpr.ISexpr.ISeq)resp).sexprs().get(0);
        return Integer.parseInt(se.toString());
    }

    public String getValue(String id, SMT smt, ISolver solver) {
        org.smtlib.IExpr.ISymbol s = smt.smtConfig.exprFactory.symbol(id);
        IResponse resp = solver.get_value(s);
        if (resp instanceof IResponse.IError) {
            return resp.toString();
        } else {
            org.smtlib.sexpr.ISexpr se = ((org.smtlib.sexpr.ISexpr.ISeq)resp).sexprs().get(0);
            return se.toString();
        }
    }

    int terminationPos = 0;
    
    boolean trace = true;

    /** Returns true if an invalid assertion was found and reported */
    public boolean reportInvalidAssertion(BasicProgram.BasicBlock block, SMT smt, ISolver solver, JCMethodDecl decl) {
        String id = block.id.name.toString();
        boolean value = getBoolValue(id,smt,solver);
        if (trace) log.noticeWriter.println("Block " + id + " is " + value);
        if (value) {
            return false;
        }
        {
            int k = id.indexOf(BasicBlockerParent.RETURN);
            if (k < 0) k = id.indexOf(BasicBlockerParent.THROW);
            if (k > 0) {
                int kk = BasicBlockerParent.blockPrefix.length();
                terminationPos = Integer.parseInt(id.substring(kk,k));
            }
        }
        
        // FIXME - would like to have a range, not just a single position point,
        // for both the 'pos' value below, which is the position of the return statement
        // Also for the postcondition assertion.
        
        // The termination variable is assigned the location of the result statement
        // that occurs on the counterexample path.
        // TODO: we may not need to put this in the actual proof script - we could 
        // determine it after the fact from the counterexample path
        //resultpos = getIntValue(JmlAssertionAdder.terminationString,smt,solver);
        
        
        for (JCStatement stat: block.statements()) {
            if (stat instanceof JCVariableDecl) {
                Name n = ((JCVariableDecl)stat).name;
                String ns = n.toString();
                if (ns.startsWith(Strings.labelVarString + "lbl")) {
                    boolean b = getBoolValue(ns,smt,solver);
                    if (ns.startsWith(Strings.labelVarString + "lblpos")) {
                        if (b) log.warning(stat.pos,"esc.label.value",ns.substring(13),b);
                    } else if (ns.startsWith(Strings.labelVarString + "lblneg")) {
                        if (!b) log.warning(stat.pos,"esc.label.value",ns.substring(13),b);
                    } else {
                        log.warning(stat.pos,"esc.label.value",ns.substring(10),b);
                    }
                    
                    
                }
            }

            if (trace) {
                log.noticeWriter.println("STATEMENT: " + stat);
                if (stat instanceof JmlStatementExpr && ((JmlStatementExpr)stat).token == JmlToken.ASSUME) {
                    JmlStatementExpr x = (JmlStatementExpr)stat;
                    if (x.expression instanceof JCBinary) {
                        JCExpression lhs = ((JCBinary)x.expression).lhs;
                        log.noticeWriter.println("VALUE: " + lhs + " = " + getValue(lhs.toString(),smt,solver));
                    } else if (x.expression instanceof JCIdent) {
                        Name n = ((JCIdent)x.expression).name;
                        log.noticeWriter.println("VALUE: " + n + " = " + getValue(n.toString(),smt,solver));
                    } 
                } else if (stat instanceof JCVariableDecl) {
                        Name n = ((JCVariableDecl)stat).name;
                        log.noticeWriter.println("VALUE: " + n + " = " + getValue(n.toString(),smt,solver));
                }
            }
            if (stat instanceof JmlStatementExpr && ((JmlStatementExpr)stat).token == JmlToken.ASSERT) {
                JmlStatementExpr assertStat = (JmlStatementExpr)stat;
                JCExpression e = assertStat.expression;
                id = ((JCIdent)e).name.toString();
                value = getBoolValue(id,smt,solver);
                if (!value) {
                    
                    String cf = "";//!cfInfo ? "" : " [ cf. " + (jfo==null?prev:jfo).getName() + ", line " + aline + "]";
                    if (terminationPos == 0) terminationPos = decl.pos;
                    Label label = assertStat.label;
                    if (Options.instance(context).get("-newesc") != null) {
                        JavaFileObject prev = null;
                        int pos = assertStat.pos;
                        if (pos == Position.NOPOS || pos == decl.pos) pos = terminationPos;
                        if (assertStat.source != null) prev = log.useSource(assertStat.source);
                        String extra = "";
                        JCExpression optional = assertStat.optionalExpression;
                        if (optional != null) {
                            if (optional instanceof JCTree.JCLiteral) extra = ": " + ((JCTree.JCLiteral)optional).getValue().toString();
                        }
                        log.warning(pos,"esc.assertion.invalid",label,decl.getName() + cf,extra);
                        // TODO - above we include the optionalExpression as part of the error message
                        // however, it is an expression, and not evaluated for ESC. Even if it is
                        // a literal string, it is printed with quotes around it.
                        if (prev != null) log.useSource(prev);
                        if (assertStat.associatedPos != Position.NOPOS) {
                            if (assertStat.associatedSource != null) prev = log.useSource(assertStat.associatedSource);
                            log.warning(assertStat.associatedPos, "jml.associated.decl");
                            if (assertStat.associatedSource != null) log.useSource(prev);
                        }

                    } else {
                        if (label == Label.POSTCONDITION || label == Label.SIGNALS) {
                            log.warning(terminationPos,"esc.assertion.invalid",label,decl.getName() + cf, "");
                            log.warning(assertStat.pos, "jml.associated.decl");
                        } else if (label == Label.ASSIGNABLE) {
                            log.warning(assertStat.pos,"esc.assertion.invalid",label,decl.getName() + cf, "");
                            log.warning(assertStat.associatedPos, "jml.associated.decl");
                        } else if (label != Label.EXPLICIT_ASSERT && label != Label.EXPLICIT_ASSUME){
                            log.warning(assertStat.pos,"esc.assertion.invalid",label,decl.getName() + cf, ""); 
                            if (assertStat.pos != assertStat.associatedPos && assertStat.associatedPos != Position.NOPOS){
                                log.warning(assertStat.associatedPos, "jml.associated.decl");
                            }
                        } else {
                            log.warning(assertStat.pos,"esc.assertion.invalid",label,decl.getName() + cf, ""); 
                        }
                    }
                    
//                    if (jfo != null) log.useSource(jfo);
//                    String assocPos = !cfInfo ? "" : " [" + prev.getName() + ", line " + line + "]";
//                    log.warning(declpos,"esc.associated.decl",assocPos);

                    // log the error
                    return true;
                }
            }
//            if (stat instanceof JmlStatementExpr && ((JmlStatementExpr)stat).label == Label.RETURN) {
//                resultpos = stat.pos;
//            }
//            // FIXME - hardcoded string that is also used in JmlAssertionAdder
//            // FIXME - looking for RESULT does not work for void functcinos
//            if (stat instanceof JCVariableDecl && ((JCVariableDecl)stat).name.toString().startsWith(Strings.terminationVarString)) {
//                terminationPos = stat.pos;
//            }
        }
        for (BasicBlock b: block.followers()) {
            value = reportInvalidAssertion(b,smt,solver,decl);
            if (value) return true;
        }
        return false;
    }
    
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
            log.error("jml.internal",msg);
        }

        @Override
        public void logError(IError result) {
            log.error("jml.internal",printer.toString(result));
        }

        @Override
        public void logDiag(String msg) {
            // TODO Auto-generated method stub
            
        }

        @Override
        public void indent(String chars) {
            // TODO Auto-generated method stub
            
        }
        
    }
    

    /** This is the entry point to attempt a proof of the given method.  It 
     * presumes that the method (and any it relies on is entered and typechecked.
     * @param node the method to prove
     * @return // FIXME - not currently used
     */
    public IProverResult proveMethod(@NonNull JCMethodDecl node) {
        IProverResult proofResult;
        
        if (Options.instance(context).get("-newesc") != null) {
            return newProveMethod(node);
        }
        
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
                if (JmlOption.isOption(context,"-showbb") || escdebug) {
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
    
    public void newblocks(java.util.List<JCStatement> prefix, BasicBlock block, BasicProgram program, BasicProgram newp) {
        //log.noticeWriter.println("NEWBLOCKS " + block.id + "   prefix = " + Counter.counts(prefix));
        java.util.List<JCStatement> p = new java.util.ArrayList<JCStatement>();
        p.addAll(prefix);
        for (JCStatement s: block.statements) {
            p.add(s);
            if ((s instanceof JmlTree.JmlStatementExpr) && ((JmlTree.JmlStatementExpr)s).token == JmlToken.ASSERT) {
                BasicBlock bb = new BasicBlock(null);
                bb.statements.addAll(p);
                newp.blocks.add(bb);
                //log.noticeWriter.println(    "  BLOCK-A " + Counter.counts(bb));
            }
        }
        if (block.followers.size() == 0) {
            BasicBlock bb = new BasicBlock(null);
            bb.statements.addAll(p);
            newp.blocks.add(bb);
            //log.noticeWriter.println(    "  BLOCK-B " + Counter.counts(bb));
        } else {
            for (BasicBlock bb: block.followers) {
                newblocks(p,bb,program,newp);
            }
        }
    }
    
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
        boolean ok = false;
        IProver p = null;
    	pickProver();
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
            
            ok = !proofResult.isSat();
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
                                reportAssumptionProblem(label,pos,methodDecl.sym.toString());
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
                        reportAssumptionProblem(nm.substring(kk+1),ps,methodDecl.sym.toString());
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
                                reportAssumptionProblem(label,pos,methodDecl.sym.toString());
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
                            reportAssumptionProblem(label,pos,methodDecl.sym.toString());
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
            String se = e.mostRecentInput == null ? "" :e.mostRecentInput;
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
                log.noticeWriter.println("");
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
                			log.warning(termpos,"esc.assertion.invalid",label,methodDecl.getName(), "");

                			if (jfo != null) log.useSource(jfo);
                			log.warning(declpos,"esc.associated.decl","");

                		} else {
                			// This way of finding line numbers is a bit expensive - it reads in the
                			// whole file and scans from the beginning.
                			// Is there a way to use the endPos table?  FIXME

                			int line = new DiagnosticSource(prev,log).getLineNumber(termpos);

                			//if (jfo != null) log.useSource(jfo);
                			int aline = new DiagnosticSource(jfo==null?prev:jfo,log).getLineNumber(declpos);
                			//log.useSource(prev);

                			String cf = !cfInfo ? "" : " [ cf. " + (jfo==null?prev:jfo).getName() + ", line " + aline + "]";
                			log.warning(termpos,"esc.assertion.invalid",label,methodDecl.getName() + cf, "");

                			if (jfo != null) log.useSource(jfo);
                			String assocPos = !cfInfo ? "" : " [" + prev.getName() + ", line " + line + "]";
                			log.warning(declpos,"esc.associated.decl",assocPos);
                		}
                		log.useSource(prev);
                	} else {
                		log.warning(termpos,"esc.assertion.invalid",label,methodDecl.getName(), "");
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
        String result = "";
        
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

class ClassCollector extends JmlTreeScanner {
    
    public static ClassCollector collect(JmlClassDecl cd, JmlMethodDecl md) {
        ClassCollector collector = new ClassCollector();
        collector.doMethods = false;
        //System.out.println("COLLECTING FOR CLASS " + cd.sym);
        collector.scan(cd);
        //System.out.println("COLLECTING FOR METHOD " + md.sym);
        collector.doMethods = true;
        collector.scan(md);
        return collector;
    }
    
    boolean doMethods;
    Set<ClassSymbol> classes = new HashSet<ClassSymbol>();
    Collection<JCTree> literals = new ArrayList<JCTree>();
    
    public ClassCollector() {
        scanMode = AST_SPEC_MODE;
    }
    
    @Override
    public void visitClassDef(JCClassDecl tree) {
        //System.out.println("ADDING-CD " + tree.sym);
        classes.add(tree.sym);
        super.visitClassDef(tree);
    }
    
    @Override
    public void visitMethodDef(JCMethodDecl tree) {
        if (!doMethods) return;
        super.visitMethodDef(tree);
    }
    
    @Override
    public void visitIdent(JCIdent tree) {
        if (tree.sym instanceof ClassSymbol) {
            ClassSymbol c = (ClassSymbol)tree.sym;
            //System.out.println("ADDING-I " + c);
            classes.add(c);
        } else if (tree.sym instanceof VarSymbol) {
            ClassSymbol c = (ClassSymbol)tree.type.tsym;
            //System.out.println("ADDING-II " + c);
            classes.add(c);
        }
        super.visitIdent(tree);
    }
    
    @Override
    public void visitSelect(JCFieldAccess tree) {
        if (tree.sym instanceof ClassSymbol) {
            ClassSymbol c = (ClassSymbol)tree.sym;
            //System.out.println("ADDING-SC " + c);
            classes.add(c);
        } else if (tree.sym instanceof VarSymbol) {
            ClassSymbol c = (ClassSymbol)tree.type.tsym;
            //System.out.println("ADDING-SI " + c);
            classes.add(c);
        }
        super.visitSelect(tree);
    }
    
    @Override
    public void visitIndexed(JCArrayAccess tree) {
            ClassSymbol c = (ClassSymbol)tree.indexed.type.tsym;
            //System.out.println("ADDING-A " + c);
            classes.add(c);
        super.visitIndexed(tree);
    }
    
    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation tree) {
        // FIXME - return types ?
        super.visitJmlMethodInvocation(tree);
    }
    
    @Override
    public void visitApply(JCMethodInvocation tree) {
        if (tree.type != null) {
            ClassSymbol c = (ClassSymbol)tree.type.tsym;
            //System.out.println("ADDING-M " + c);
            classes.add(c);
       }
        super.visitApply(tree);
    }
    
//    static public class JmlDiagnostic extends JCDiagnostic {
//        public JmlDiagnostic(DiagnosticFormatter<JCDiagnostic> formatter,
//                       DiagnosticType dt,
//                       boolean mandatory,
//                       DiagnosticSource source,
//                       DiagnosticPosition pos,
//                       String key,
//                       Object ... args) {
//            super(formatter,dt,mandatory,source,pos,key,args);
//        }
//        
//        static JmlDiagnostic warning(int pos, String key, Object ... args) {
//            return new JmlDiagnostic(formatter, WARNING, false, source, pos, qualify(WARNING, key), args);
//            
//        }
//    }
}
