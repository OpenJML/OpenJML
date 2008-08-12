package org.jmlspecs.openjml.esc;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotations.NonNull;
import org.jmlspecs.annotations.Nullable;
import org.jmlspecs.openjml.JmlOptionName;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.ProverException;
import org.jmlspecs.openjml.proverinterface.ProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICoreIds;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;
import org.jmlspecs.openjml.provers.YicesProver;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
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
    public static boolean escdebug = Utils.jmldebug;
    
    /** true if counterexample information is desired */
    boolean showCounterexample;
    
    /** true if counterexample trace information is desired */
    boolean showTrace;
    
    /** The compilation context, needed to get common tools, but unique to this compilation run*/
    @NonNull Context context;

    /** Used to obtain cached symbols, such as basic types */
    @NonNull Symtab syms;
    
    /** The database of JML specifications for methods, classes, fields, ... */
    @NonNull JmlSpecs specs;
    
    /** The names database */
    @NonNull Name.Table names;
    
    /** The factory for making AST nodes */
    @NonNull JmlTree.JmlFactory factory;
    
    /** The tool to log problem reports */ 
    @NonNull Log log;
    
    /** Whether to check that key assumptions are feasible */
    boolean checkAssumptions = true;


    @NonNull final static public String arraysRoot = "$$arrays";  // Reference in masicblocker?

    /** The tool constructor, which initializes all the tools. */
    public JmlEsc(Context context) {
        this.context = context;
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.log = Log.instance(context);
        this.names = Name.Table.instance(context);
        this.factory = (JmlTree.JmlFactory)JmlTree.Maker.instance(context);
        this.verbose = JmlOptionName.isOption(context,"-verbose") ||
            JmlOptionName.isOption(context,JmlOptionName.JMLVERBOSE) || 
            Utils.jmldebug;
        this.showCounterexample = JmlOptionName.isOption(context,"-ce") || escdebug ; // FIXME - options
        this.showTrace = showCounterexample || JmlOptionName.isOption(context,"-trace");
        this.checkAssumptions = !JmlOptionName.isOption(context,"-noCheckAssumptions");
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
            if (verbose) System.out.println("ESC: Checking method " + node.sym);
            if (escdebug) System.out.println(node.toString()); // print the method
            
            //Utils.Timer t = new Utils.Timer();
            BasicProgram program = BasicBlocker.convertToBasicBlocks(context, tree, denestedSpecs, currentClassDecl);
            if (JmlOptionName.isOption(context,"-bb") || escdebug) program.write(); // print the basic block program // FIXME - the option
            //System.out.println("PREP  " +  t.elapsed()/1000.);
            prove(node,program);
            //System.out.println("PREP AND PROVE " +  t.elapsed()/1000.);
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
                    JCExpression e = factory.JmlBinary(JmlToken.IMPLIES,as.expression,rest);
                    e.type = syms.booleanType;
                    e.pos = as.expression.pos;
                    return e;
                } else if (as.token == JmlToken.ASSERT) {
                    JCExpression e = factory.Binary(JCTree.AND,as.expression,rest);
                    e.type = syms.booleanType;
                    e.pos = as.expression.pos;
                    return e;
                } else {
                    log.error("esc.internal.error","An unexpected statement type in a BasicBlock: " + as.token.internedName());
                }
            } else {
                log.error("esc.internal.error","An unexpected statement type in a BasicBlock: " + st.getClass());
            }
            return rest;
        } else {
            JCExpression expr = factory.Literal(TypeTags.BOOLEAN,1);
            expr.type = syms.booleanType;
            for (BasicBlock follower: block.succeeding()) {
                JCExpression e = factory.Binary(JCTree.AND,expr,follower.id);
                e.pos = follower.id.pos;
                e.type = syms.booleanType;
                expr = e;
            }
            return expr;
        }
    }

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
    
    /** Initiate proving of the VC for the method.  The given program must be
     * the BasicProgram corresponding to the given method declaration.
     * @param methodDecl the method whose implementation is being proved
     * @param program the basic program corresponding to the method implementation
     */
    public void prove(@NonNull JCMethodDecl methodDecl, @NonNull BasicProgram program) {
        IProver p;
        try {

            // Pick a prover to use
            p = new YicesProver(context);
            
            for (BasicProgram.BasicBlock block : program.blocks()) {
                p.define(block.id.toString(),syms.booleanType);
            }
            
            if (JmlOptionName.isOption(context,"-checkPreconditions")) {
                // Check that the preconditions are satisfiable
                // This is here in case one wants a quick smoke test of the 
                // preconditions.  Normally one would do the general check of
                // the method, and only if it is successful would one go on to
                // check that the various assumptions are feasible.
                p.push();
                BasicBlock bl = program.startBlock();
                JCExpression e = blockExpr(bl);
                e = factory.Unary(JCTree.NOT,e);
                e.type = syms.booleanType;
                p.assume(e);
                IProverResult b = p.check();
                if (b.result() == ProverResult.UNSAT) {
                    log.warning(methodDecl.pos(),"esc.unsat.preconditions",methodDecl.getName());
                    if (escdebug) System.out.println("Invariants+Preconditions are NOT satisfiable in " + methodDecl.getName());
                    // FIXME - print out core ids if available?
                    p.pop();
                    return ;
                } else {
                    if (verbose) System.out.println("Invariants+Preconditions are satisfiable");
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

            // send any other axioms and definitions
            
            int n = 0;
            for (JCExpression expr: program.background()) {
                n = p.assume(expr,10);
            }
            for (JCExpression expr: program.definitions()) {
                n = p.assume(expr,10);
            }

            if (checkAssumptions) p.push();

            { // FIXME - we have to include this unless no assumption encoding is done
                JCExpression e = factory.Literal(TypeTags.INT,0);
                e.type = syms.intType;
                e = factory.Binary(JCTree.EQ, program.assumeCheckVar, e);
                e.type = syms.booleanType;
                p.assume(e);
            }

            IProverResult r = p.check();
            if (r.isSat()) {
                if (escdebug) System.out.println("Method does NOT satisfy its specifications, it appears");
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
                    // Look for "assert$<number>$<Label>$<number> false"
                    Pattern pat1 = Pattern.compile("(assert\\$(\\d+)\\$(\\d+))\\$(\\w+)");
                    for (Map.Entry<String,String> var: s.sortedEntries()) {
                        Matcher m = pat1.matcher(var.getKey());
                        if (var.getValue().equals("false") && m.find()) {
                            String sname = m.group(1); // full name of the assertion
                            String label = m.group(4); // the label part 
                            int usepos = Integer.parseInt(m.group(2)); // the textual location of the assert statement
                            int declpos = Integer.parseInt(m.group(3)); // the textual location of associated information (or same as usepos if no associated information)
                            int termpos = usepos;
                            if (terminationValue != null &&
                                    (Label.POSTCONDITION.toString().equals(label) ||
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
                            Name v = names.fromString(var.getKey());
                            BasicBlock bl = findContainingBlock(v,program);
                            // A 'false' assertion is spurious if it happens in a block 
                            // which is not executed (its block variable is 'true')
                            // So we list the assertion if
                            //      - we cannot find a block containing the assertion (just to be safe)
                            //      - we find a block but find no value for the block variable (just to be safe)
                            //      - the block variable is 'false' (not 'true') and there is a chain of false blocks back to the beginning
                            if (bl == null || hasFeasibleChain(bl,s) ) {
                                if (escdebug) System.out.println("Assertion " + sname + " cannot be verified");
                                log.warning(termpos,"esc.assertion.invalid",label,methodDecl.getName());
                                if (declpos != usepos) log.warning(declpos,"esc.associated.decl");
                                noinfo = false;
                            }
                        }
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
                            if (escdebug) System.out.println("Label " + label + " has value " + var.getValue());
                        }
                    }
                    Pattern pat3 = Pattern.compile("\\$\\$LBLNEG\\$(\\d+)\\$([^ ]+)");
                    for (Map.Entry<String,String> var: s.sortedEntries()) {
                        Matcher m = pat3.matcher(var.getKey());
                        if (var.getValue().equals("false") && m.find()) {
                            int pos = Integer.parseInt(m.group(1));
                            String label = m.group(2);
                            log.warning(pos,"esc.label",label);
                            if (escdebug) System.out.println("Label " + label + " has value " + var.getValue());
                        }
                    }
                    Pattern pat4 = Pattern.compile("\\$\\$LBLANY\\$(\\d+)\\$([^ ]+)");
                    for (Map.Entry<String,String> var: s.sortedEntries()) {
                        Matcher m = pat4.matcher(var.getKey());
                        if (m.find()) {
                            int pos = Integer.parseInt(m.group(1));
                            String label = m.group(2);
                            log.warning(pos,"esc.label.value",label,var.getValue());
                            if (escdebug) System.out.println("Label " + label + " has value " + var.getValue());
                        }
                    }
                }
                
                if (showTrace) {
                    System.out.println("Trace");
                    //BasicBlocker.Tracer.trace(context,methodDecl,s);
                    BasicBlocker.TracerBB.trace(context,program,s,p);
                }
                if (showCounterexample) {
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
                if (!checkAssumptions) return;
                
                boolean useCoreIds = false; // FIXME - use an option
                ICoreIds cid = r.coreIds();
                if (useCoreIds && cid == null && verbose) System.out.println("Warning: Core ids unexpectedly not returned");
                Collection<Integer> cids = cid == null ? null : cid.coreIds();
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

                } else if (checkAssumptions) {
                    p.pop();

                    // Find assumptions that need tracking
                    SortedSet<String> trackedAssumes = new TreeSet<String>();
                    for (JCIdent var: BasicBlocker.VarFinder.findVars(program)) {
                        String s = var.toString();
                        if (s.startsWith("assumeCheck$")) {
                            trackedAssumes.add(s);
                        }
                    }

                    for (String nm: trackedAssumes) {
                        p.push();
                        String parts[] = nm.split("\\$");
                        int pos = Integer.parseInt(parts[1]);
                        JCExpression ex = factory.Binary(JCTree.EQ, program.assumeCheckVar, factory.Literal(TypeTags.INT,pos));
                        ex.type = syms.booleanType;
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
                log.error("esc.proof.failed", r.result(), methodDecl.sym);
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
        } else if (label.equals(Label.PRECONDITION.toString())) {
            log.warning(Math.abs(pos),"esc.infeasible.preconditions",methodSignature);
            if (escdebug) System.out.println("Preconditions are infeasible at " + pos);
        } else {
            log.warning(pos,"esc.infeasible.assumption",methodSignature);
            if (escdebug) System.out.println("Assumption (" + label + ") is infeasible");
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
        if (bl.preceding.size() == 0) return true; // presuming it is the start block, which may not be the case?? FIXME
        for (BasicBlock b: bl.preceding) {
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
}
