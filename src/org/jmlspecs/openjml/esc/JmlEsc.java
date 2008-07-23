package org.jmlspecs.openjml.esc;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotations.*;
import org.jmlspecs.openjml.JmlOptionName;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.ProverException;
import org.jmlspecs.openjml.proverinterface.ProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;
import org.jmlspecs.openjml.provers.YicesProver;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

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

    /** true if compiler options are set to a verbose mode */
    boolean verbose;
    
    /** Just for debugging esc */
    static boolean escdebug = true || Utils.jmldebug;
    
    /** true if counterexample information is desired */
    boolean showCounterexample;
    
    /** The compilation context, needed to get common tools, but unique to this compilation run*/
    @NonNull Context context;

    /** Used to obtain cached symbols, such as basic types */
    @NonNull Symtab syms;
    
    /** The database of JML specifications for methods, classes, fields, ... */
    @NonNull JmlSpecs specs;
    
    /** The factory for making AST nodes */
    @NonNull JmlTree.JmlFactory factory;
    
    // FIXME - used in just one place - do we need it?
    @NonNull JmlAttr attr;

    /** The tool to log problem reports */ 
    @NonNull Log log;

    @NonNull final static public String arraysRoot = "$$arrays";

    /** The tool constructor, which initializes all the tools. */
    public JmlEsc(Context context, Env<AttrContext> env) {
        this.context = context;
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.attr = (JmlAttr)JmlAttr.instance(context);
        this.log = Log.instance(context);
        this.factory = (JmlTree.JmlFactory)JmlTree.Maker.instance(context);
        this.verbose = JmlOptionName.isOption(context,"-verbose") ||
            JmlOptionName.isOption(context,JmlOptionName.JMLVERBOSE) || 
            Utils.jmldebug || true;
        this.showCounterexample = JmlOptionName.isOption(context,"-ce") || escdebug ; // FIXME
    }

    /** Set to the currently owning class declaration while visiting JCClassDecl and its children. */
    @Nullable JCClassDecl currentClassDecl = null;
    
    public void visitClassDef(JCClassDecl node) {
        // Save the information in case classes are nested
        JCClassDecl prev = currentClassDecl;
        try {
            currentClassDecl = node;
            super.visitClassDef(node);
        } finally {
            currentClassDecl = prev;
        }
    }


    /** When we visit a method declaration, we translate and prove the method;
     * we do not walk into the method any further from this call, only through
     * the translation mechanism.
     */  // FIXME - what about local classes or anonymous classes
    //@ requires node instanceof JmlMethodDecl;
    public void visitMethodDef(@NonNull JCMethodDecl node) {
        if (!(node instanceof JmlMethodDecl)) {
            log.warning("esc.not.implemented","Unexpected non-JmlMethodDecl in JmlEsc - not checking " + node.sym);
            return;
        }
        
        JmlMethodDecl tree = (JmlMethodDecl)node;
        // Get the denested specs for the method - FIXME - when might they be null?
        JmlMethodSpecs denestedSpecs = tree.sym == null ? null : specs.getDenestedSpecs(tree.sym);
        // Change the log's source file to represent the source for this method
        JavaFileObject source = tree.sourcefile;
        JavaFileObject prev = log.useSource(source);
        try {
            boolean isConstructor = tree.getReturnType() == null;
            boolean doEsc = ((((JCMethodDecl)tree).mods.flags & (Flags.SYNTHETIC|Flags.ABSTRACT|Flags.NATIVE)) == 0);

            // Don't do ESC on the constructor of Object
            // FIXME - why?  (we don't have the source anyway, so how would we get here?)
            if (currentClassDecl.sym == syms.objectType.tsym && isConstructor) doEsc = false;
            if (!doEsc) return;

            // FIXME - turn off in quiet mode? 
            log.note("esc.checking.method",node.sym); 
            if (verbose) System.out.println("CHECKING METHOD " + node.sym);
            if (escdebug) System.out.println(node.toString());
            BasicProgram program = BasicBlocker.convertToBasicBlocks(context, tree, denestedSpecs, currentClassDecl);
            if (escdebug) program.write();
            prove(node,program);
        } finally {
            log.useSource(prev);
        }
    }
    
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
    
    /** Helper method to determine the VC expression for a basic block.
     * 
     * @param block BasicBlock being translated
     * @param iterator an iterator over the statements of the block
     * @return the equivalent VC expression
     */
    protected @NonNull JCExpression blockExpr(@NonNull BasicBlock block, @NonNull Iterator<JCStatement> iterator) {
        if (iterator.hasNext()) {
            JCStatement st = iterator.next();
            JCExpression rest = blockExpr(block,iterator);
            if (st instanceof JmlStatementExpr) {
                JmlStatementExpr as = (JmlStatementExpr)st;
                if (as.token == JmlToken.ASSUME) {
                    return factory.JmlBinary(JmlToken.IMPLIES,as.expression,rest);
                } else if (as.token == JmlToken.ASSERT) {
                    return factory.Binary(JCTree.AND,as.expression,rest);
                } else {
                    log.error("esc.internal.error","An unexpected statement type in a BasicBlock: " + as.token.internedName());
                }
            } else {
                log.error("esc.internal.error","An unexpected statement type in a BasicBlock: " + st.getClass());
            }
            return rest;
        } else {
            JCExpression expr = factory.Literal(TypeTags.BOOLEAN,1);
            for (BasicBlock follower: block.succeeding()) {
                expr = factory.Binary(JCTree.AND,expr,follower.id);
            }
            return expr;
        }
    }

    /** Creates an AST node for a new identifier, meant as an auxiliary logical
     * variable in the eventual VC; the identifier has the given type and node
     * position (the given position is not encoded into the identifier name);
     * an associated VarSymbol is also created.
     * @param name the name of the identifier (including any encoded incarnation number)
     * @param type the Java type of the identifier (e.g. syms.booleanType)
     * @param nodepos the position at which to place the node
     * @return the created identifier
     */
    protected @NonNull JCIdent newAuxIdent(@NonNull Name name, @NonNull Type type, int nodepos) {
        JCIdent id = factory.Ident(name);
        id.pos = nodepos;
        id.type = type;
        id.sym = new VarSymbol(0,name,type,null);
        // Note: the owner of the symbol is null - FIXME: should that be the method or something - this does not seem to cause any harm to date
        // FIXME - set the end position?
        return id;
    }
 
    /** Initiate proving of the VC for the method.  The given program must be
     * the BasicProgram corresponding to the given method declaration.
     * @param methodDecl the method whose implementation is being proved
     * @param program the basic program corresponding to the method implementation
     */
    public void prove(@NonNull JCMethodDecl methodDecl, @NonNull BasicProgram program) {
        LinkedList<JCIdent> trackedAssumes = new LinkedList<JCIdent>();
        IProver p;
        try {

            // Pick a prover to use
            p = new YicesProver(context);
            
            // FIXME - find another way to get the assumeChecks so that we can get rid of the declarations
            for (JCIdent var: program.declarations()) {
                String s = var.toString();
                if (s.startsWith("assumeCheck$")) trackedAssumes.add(var);
            }

            for (BasicProgram.BasicBlock block : program.blocks()) {
                p.define(block.id.toString(),syms.booleanType);
            }
            
            {
             // Check that the preconditions are satisfiable
             // FIXME - move this check to after the overall satisfiability check
                p.push();
                BasicBlock bl = program.startBlock();
                JCExpression e = blockExpr(bl);
                e = factory.Unary(JCTree.NOT,e);
                p.assume(e);
                IProverResult b = p.check();
                if (b.result() == ProverResult.UNSAT) { // FIXME - control with verbosity
                    log.warning(methodDecl.pos(),"esc.unsat.preconditions",methodDecl.getName());
                    if (escdebug) System.out.println("Invariants+Preconditions are NOT satisfiable in " + methodDecl.getName());
                    // FIXME - print out core ids if available?
                    p.pop();
                    return ;
                } else {
                    if (escdebug) System.out.println("Invariants+Preconditions are satisfiable");
                }
                p.pop();
            }
            
            // send negated start block id
            
            JCIdent id = program.startBlock().id();
            JCExpression negateStart = factory.Unary(JCTree.NOT,id);
            negateStart.type = syms.booleanType;
            p.assume(negateStart,100000);

            // send block equations

            for (BasicBlock bl : program.blocks()) {
                JCExpression e = blockExpr(bl);
                e = factory.JmlBinary(JmlToken.EQUIVALENCE,bl.id,e); 
                e.pos = bl.id.pos;
                e.type = syms.booleanType;
                p.assume(e);
            }

            // send any other axioms, including definitions
            
            int n = 0;
            for (JCExpression expr: program.definitions()) {
                n = p.assume(expr,10);
            }

            p.push();

            if (trackedAssumes.size() != 0) {
                JCExpression e = factory.Binary(JCTree.EQ, program.assumeCheckVar, factory.Literal(TypeTags.INT,0));
                p.assume(e);
            }

            IProverResult r = p.check();
            if (r.result() == IProverResult.SAT) {
                if (escdebug) System.out.println("Method does NOT satisfy its specifications, it appears");
                ICounterexample s = r.counterexample();
                // Look for "assert$<number>$<Label>$<number> false"
                Pattern pat1 = Pattern.compile("(assert\\$(\\d+)\\$(\\d+))\\$(\\w+)");
                boolean noinfo = true;
                if (s != null) for (Map.Entry<String,String> var: s.sortedEntries()) {
                    Matcher m = pat1.matcher(var.getKey());
                    if (var.getValue().equals("false") && m.find()) {
                        String sname = m.group(1); // full name of the assertion
                        String label = m.group(4); // the label part 
                        int usepos = Integer.parseInt(m.group(2)); // the textual location of the assert statement
                        int declpos = Integer.parseInt(m.group(3)); // the textual location of associated information (or same as usepos if no associated information)
                        if (escdebug) System.out.println("Assertion " + sname + " cannot be verified");
                        log.warning(usepos,"esc.assertion.invalid",label,methodDecl.getName());
                        if (declpos != usepos) log.warning(declpos,"esc.associated.decl");
                        noinfo = false;
                    }
                }
                if (noinfo) {
                    log.warning("esc.method.invalid",methodDecl.getName());
                } else {
                    Pattern pat2 = Pattern.compile("\\$\\$LBLPOS\\$(\\d+)\\$([^ ]+)");
                    for (Map.Entry<String,String> var: s.sortedEntries()) {
                        Matcher m = pat2.matcher(var.getKey());
                        if (var.getValue().equals("true") && m.find()) {
                            int pos = Integer.parseInt(m.group(1));
                            String label = m.group(2);
                            log.warning(pos,"esc.label",label);
                        }
                    }
                    Pattern pat3 = Pattern.compile("\\$\\$LBLNEG\\$(\\d+)\\$([^ ]+)");
                    for (Map.Entry<String,String> var: s.sortedEntries()) {
                        Matcher m = pat3.matcher(var.getKey());
                        if (var.getValue().equals("false") && m.find()) {
                            int pos = Integer.parseInt(m.group(1));
                            String label = m.group(2);
                            log.warning(pos,"esc.label",label);
                        }
                    }
                }
                if (showCounterexample) {
                    System.out.println("Trace");
                    BasicBlocker.Tracer.trace(context,methodDecl,s);
                    System.out.println("Counterexample:");
                    // Just some arbitrary number of spaces used to format lines
                    String spaces = "                                ";
                    for (Map.Entry<String,String> var: s.sortedEntries()) {
                        int k = var.getKey().length();
                        if (k >= spaces.length()) k = spaces.length()-1;
                        System.out.println("    " + var.getKey() + spaces.substring(k) + var.getValue());
                    }
                }
            } else if (r.result() == IProverResult.UNSAT) {
                if (escdebug) System.out.println("Method satisfies its specifications (as far as I can tell)");

                boolean useCoreIds = true;
                Collection<Integer> cids = r.coreIds().coreIds();
                if (useCoreIds && cids != null) {
                    Integer[] ids = new Integer[cids.size()]; 
                    ids = cids.toArray(ids);
                    Arrays.sort(ids);
                    int nn = n - program.definitions().size();
                    int k = 0;
                    while (n > nn) {
                        JCExpression e = program.definitions().get(n-nn-1);
                        if (!(e instanceof JCBinary)) { n--; continue; }
                        String name = ((JCIdent)((JCBinary)e).getLeftOperand()).getName().toString();
                        String[] parts = name.split("\\$");
                        if (parts.length != 3) { n--; continue; }
                        if (!parts[0].equals("checkAssumption")) { n--; continue;}
                        int pos = Integer.parseInt(parts[2]);
                        int found = Arrays.binarySearch(ids,n);
                        if (found < 0) {
                            // Already not part of the minimal core
                            p.retract(n--);
                            if (escdebug) System.out.println("ALREADY NOT IN MINIMAL CORE: " + name);
                            reportAssumptionProblem(parts[1],pos,methodDecl.sym.toString());
                            continue;
                        }
                        p.push(); k++;
                        p.retract(n--);
                        r = p.check();
                        if (r.isSat()) {
                            if (escdebug) System.out.println("NOW SAT - ASSUMPTION WAS OK: " + name);
                            p.pop(); k--;
                        } else {
                            if (escdebug) System.out.println("STILL UNSAT - CORE WAS NOT MINIMAL - ASSSUMPTION WAS INFEASIBLE: " + name);
                            reportAssumptionProblem(parts[1],pos,methodDecl.sym.toString());
                        }
                    }
                    while (k-- > 0) p.pop();

                    p.pop();

                } else {
                    p.pop();

                    for (JCIdent aux: trackedAssumes) {
                        p.push();
                        String nm = aux.toString();
                        String parts[] = nm.split("\\$");
                        int pos = Integer.parseInt(parts[1]);
                        JCExpression ex = factory.Binary(JCTree.EQ, program.assumeCheckVar, factory.Literal(TypeTags.INT,pos));
                        p.assume(ex);
                        r = p.check();
                        if (!r.isSat()) {
                            String label = parts[2];
                            reportAssumptionProblem(label,pos,methodDecl.sym.toString());
                        }
                        p.pop();
                    }
                }
            } else {
                // Result is unknown
                // FIXME - need some tests and more output information here
                if (escdebug) System.out.println("Status of method is UNKNOWN - prover failed");
            }

        } catch (ProverException e) {
            log.warning("esc.prover.failure",methodDecl.sym.toString() + ": " + e.getLocalizedMessage() + ":" + e.mostRecentInput);
            if (escdebug) {
                System.out.println("PROVER FAILURE: " + e);
                if (e.mostRecentInput != null) System.out.println("INPUT: " + e.mostRecentInput);
            }
        }
    }
    
    /** Reports the details of a problem when an assumption is infeasible.
     * This happens when the assumption is not needed, which is known when
     * the program is still valid (the VC is unsatisfiable) with a false
     * assertion following the assumption.
     * 
     * @param label the label given to the assumption
     * @param pos   the textual position of the associated statement
     * @param method the name of the method being tested
     */
    public void reportAssumptionProblem(String label, int pos, String methodSignature) {
        if (label.equals(Label.BRANCHT.toString())) {
            log.warning(Math.abs(pos),"esc.infeasible.branch","then",methodSignature);
            if (escdebug) System.out.println("Branch is infeasible at " + pos);
        } else if (label.equals(Label.BRANCHE.toString())) {
            log.warning(Math.abs(pos),"esc.infeasible.branch","else",methodSignature);
            if (escdebug) System.out.println("Branch is infeasible at " + pos);
        } else {
            log.warning(pos,"esc.infeasible.assumption",methodSignature);
            if (escdebug) System.out.println("Assumption (" + label + ") is infeasible");
        }
    }
}
