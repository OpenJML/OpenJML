package org.jmlspecs.openjml.esc;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotations.NonNull;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.ProverException;
import org.jmlspecs.openjml.proverinterface.ProverResult;
import org.jmlspecs.openjml.proverinterface.Sort;
import org.jmlspecs.openjml.proverinterface.Term;
import org.jmlspecs.openjml.provers.YicesJCExpr;
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
import com.sun.tools.javac.comp.Resolve;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

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

    Context context;

    Env<AttrContext> env;
    Env<AttrContext> attrEnv;
    Resolve rs;
    Symtab syms;
    Name.Table names;
    JmlSpecs specs;
    JmlTree.JmlFactory factory;
    DiagnosticPosition make_pos;
    JmlAttr attr;
//    Name resultName;
//    Name exceptionName;
//    Name exceptionCatchName;
    Log log;

    static public String arraysRoot = "$$arrays";

    ListBuffer<Symbol> symsEncountered = new ListBuffer<Symbol>();;

    Type integerType;

    public JmlEsc(Context context, Env<AttrContext> env) {
        this.context = context;
        this.env = env;
        this.attrEnv = env;
        this.syms = Symtab.instance(context);
        //this.rs = Resolve.instance(context);
        this.names = Name.Table.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.attr = (JmlAttr)JmlAttr.instance(context);
        this.log = Log.instance(context);
        this.factory = (JmlTree.JmlFactory)JmlTree.Maker.instance(context);

        // FIXME - are any of the following used
        ClassReader reader = ClassReader.instance(context);
        this.integerType = reader.enterClass(names.fromString("java.lang.Integer")).type;

//        this.resultName = Name.Table.instance(context).fromString("_JML$$$result");
//        this.exceptionName = Name.Table.instance(context).fromString("_JML$$$exception");
//        this.exceptionCatchName = Name.Table.instance(context).fromString("_JML$$$exceptionCatch");

    }

    /** This class holds specification information about a given class.
     * Note that all of the expressions are in conventional (i.e. not basic) AST form.
     * @author David Cok
     */
    public static class JmlClassInfo {
        public JmlClassInfo(JCClassDecl d) { this.decl = d; }
        JCClassDecl decl;
        JmlSpecs.TypeSpecs typeSpecs = null;
        public java.util.List<JmlTypeClauseConstraint> constraints = new LinkedList<JmlTypeClauseConstraint>();
        public java.util.List<JmlTypeClauseConstraint> staticconstraints = new LinkedList<JmlTypeClauseConstraint>();
        public java.util.List<JmlTypeClauseExpr> initiallys = new LinkedList<JmlTypeClauseExpr>();
        public java.util.List<JmlTypeClauseExpr> invariants = new LinkedList<JmlTypeClauseExpr>();
        public java.util.List<JmlTypeClauseExpr> staticinvariants = new LinkedList<JmlTypeClauseExpr>();
        public java.util.List<JmlTypeClauseExpr> axioms = new LinkedList<JmlTypeClauseExpr>();
    }

    /** Set to the currently owning class declaration while visiting JCClassDecl. */
    JCClassDecl currentClassDecl = null;
    
    /** Set to the class info structure of the owning class while visiting JCClassDecl */
    JmlClassInfo currentClassInfo = null;
    
    public void visitClassDef(JCClassDecl node) {
        // Save the information in case classes are nested
        JCClassDecl prev = currentClassDecl;
        JmlClassInfo prevInfo = currentClassInfo;
        currentClassDecl = node;
        currentClassInfo = getClassInfo(node); // Just precompute the class info
        super.visitClassDef(node);
        currentClassDecl = prev;
        currentClassInfo = prevInfo;
    }

    /** A Map that stores class info for a given class symbol */
    Map<Symbol,JmlClassInfo> classInfoMap = new HashMap<Symbol,JmlClassInfo>();

    
    JmlClassInfo getClassInfo(JCClassDecl cls) {
        JmlClassInfo mi = classInfoMap.get(cls.sym);
        if (mi == null) {
            mi = computeClassInfo(cls);
            classInfoMap.put(cls.sym,mi);
        }
        return mi;
    }
    
    public JmlClassInfo computeClassInfo(JCClassDecl tree) {
        if (tree.sym == null) return null;

        JmlClassInfo classInfo = new JmlClassInfo(tree);
        TypeSpecs typeSpecs = classInfo.typeSpecs = specs.get(tree.sym);


        // Remove any non-Java declarations from the Java AST before we do translation
        // After the superclass translation, we will add back in all the JML stuff.
        ListBuffer<JCTree> newlist = new ListBuffer<JCTree>();
        for (JCTree tt: tree.defs) {
            if (tt == null || tt.getTag() >= JmlTree.JMLFUNCTION) {
                // skip it
            } else {
                newlist.append(tt);
            }
        }

        // Divide up the various type specification clauses into the various types
        ListBuffer<JmlTypeClauseRepresents> represents = new ListBuffer<JmlTypeClauseRepresents>();
        ListBuffer<JCVariableDecl> modelFields = new ListBuffer<JCVariableDecl>();

        if (typeSpecs != null) for (JmlTypeClause c: typeSpecs.clauses) {
            boolean isStatic = c.modifiers != null && (c.modifiers.flags & Flags.STATIC) != 0;
            if (c instanceof JmlTypeClauseDecl) {
                JCTree tt = ((JmlTypeClauseDecl)c).decl;
                if (tt instanceof JCVariableDecl && attr.isModel(((JCVariableDecl)tt).mods)) {
                    // model field - find represents or make into abstract method
                    modelFields.append((JCVariableDecl)tt);
                } else {
                    // ghost fields, model methods, model classes are used as is
                    //t = translate(t);
                    newlist.append(tt);
                }
            } else {
                JmlToken token = c.token;
                if (token == JmlToken.INVARIANT) {
                    if (isStatic) classInfo.staticinvariants.add((JmlTypeClauseExpr)c);
                    else          classInfo.invariants.add((JmlTypeClauseExpr)c);
                } else if (token == JmlToken.REPRESENTS) {
                    JmlTypeClauseRepresents r = (JmlTypeClauseRepresents)c;
                    if (r.suchThat) log.warning(r.pos,"jml.not.implemented.rac","relational represents clauses (\\such_that)");
                    else represents.append(r);
                } else if (token == JmlToken.CONSTRAINT) {
                    if (isStatic) classInfo.staticconstraints.add((JmlTypeClauseConstraint)c);
                    else          classInfo.constraints.add((JmlTypeClauseConstraint)c);
                } else if (token == JmlToken.INITIALLY) {
                    classInfo.initiallys.add((JmlTypeClauseExpr)c);
                } else if (token == JmlToken.AXIOM) {
                    classInfo.axioms.add((JmlTypeClauseExpr)c);
                } else {
                    System.out.println("NOT IMPLEMENTED "); // FIXME - readable if, writable if, monitors for, in, maps
                }
            }
        }
        return classInfo;
    }

    public void visitMethodDef(JCMethodDecl node) {
        JCMethodDecl tree = (JCMethodDecl)node;
        JmlMethodSpecs denestedSpecs = tree.sym == null ? null : specs.getDenestedSpecs(tree.sym);
        JavaFileObject source = ((JmlMethodDecl)tree).sourcefile;
        JavaFileObject prev = log.useSource(source);
        try {
            boolean isConstructor = tree.getReturnType() == null;
            boolean doEsc = ((((JCMethodDecl)tree).mods.flags & (Flags.SYNTHETIC|Flags.ABSTRACT|Flags.NATIVE)) == 0);
            JmlClassInfo classInfo = getClassInfo(currentClassDecl);
            if (classInfo.decl.sym == syms.objectType.tsym && isConstructor) doEsc = false;
            if (!doEsc) return;

            System.out.println("CHECKING METHOD " + node.getName() + " " + node.getPreferredPosition() + " " + node.toString());
            BasicProgram program = BasicBlocker.convertToBasicBlocks(context, tree, denestedSpecs, currentClassInfo);
            program.write();

            prove(node,program);
        } finally {
            log.useSource(prev);
        }

    }


    public Sort convert(Type t) {
        Sort sort = Sort.ANY;
        if (!t.isPrimitive()) {
            sort = Sort.VARREF;
        } else if (t.tag == TypeTags.BOOLEAN) {
            sort = Sort.VARBOOL;
        } else {
            sort = Sort.VARINT;
        }
        return sort;
    }
    
    public JCExpression blockExpr(BasicBlock block) {
        java.util.List<JCStatement> statements = block.statements();
        Iterator<JCStatement> iterator = statements.iterator();
        return blockExpr(block,iterator);
    }
    
    public JCExpression blockExpr(BasicBlock block, Iterator<JCStatement> iterator) {
        if (iterator.hasNext()) {
            JCStatement st = iterator.next();
            JCExpression rest = blockExpr(block,iterator);
            if (st instanceof JmlStatementExpr) {
                JmlStatementExpr as = (JmlStatementExpr)st;
                if (as.token == JmlToken.ASSUME) {
                    return factory.JmlBinary(JmlToken.IMPLIES,as.expression,rest);
                } else if (as.token == JmlToken.ASSERT) {
                    return factory.Binary(JCTree.AND,as.expression,rest);
                }
            }
            System.out.println("NOT IMPLE");
            return rest;
        } else {
            JCExpression expr = factory.Literal(TypeTags.BOOLEAN,1);
            for (BasicBlock follower: block.succeeding()) {
                Name n = names.fromString(follower.name());
                JCExpression id = newAuxIdent(n,syms.booleanType,0);
                expr = factory.Binary(JCTree.AND,expr,id);
            }
            return expr;
        }
    }

    protected JCIdent newAuxIdent(@NonNull Name name, @NonNull Type type, int pos) {
        JCIdent id = factory.Ident(name);
        id.pos = pos;
        id.sym = new VarSymbol(0,name,type,null);
        id.type = type;
        return id;
    }
 
    public void prove(JCMethodDecl node, BasicProgram program) {
        LinkedList<JCIdent> trackedAssumes = new LinkedList<JCIdent>();
        IProver p;
        try {

            p = new YicesProver();
            // send any variable definitions
            // FIXME - find another way to get the assumeChecks so that we can get rid of the declarations
            for (JCIdent var: program.declarations()) {
                String s = var.toString();
                if (s.startsWith("assumeCheck$")) trackedAssumes.add(var);
//                p.define(s,var.type);
            }
//
            for (BasicProgram.BasicBlock block : program.blocks()) {
                p.define(block.name(),syms.booleanType);
            }
            
            {
             // send preconditions
                p.push();
                BasicBlock bl = program.startBlock();
                JCExpression e = blockExpr(bl);
                e = factory.Unary(JCTree.NOT,e);
                p.assume(context,e);
                IProverResult b = p.check();
                if (b.result() == ProverResult.SAT) { // FIXME - control with verbosity
                    System.out.println("Invariants+Preconditions are satisfiable");
                } else {
                    log.warning(node.pos(),"esc.unsat.preconditions",node.getName());
                    System.out.println("Invariants+Preconditions are NOT satisfiable in " + node.getName());
                    System.out.println(((YicesProver)p).satResult); // FIXME
                    p.pop();
                    return ;
                }
                p.pop();
            }
            
            // send negated start block id
            
            JCIdent id = factory.Ident(names.fromString(program.startId()));
            JCExpression negateStart = factory.Unary(JCTree.NOT,id);
            p.assume(context,negateStart,100000);

            // send block equations

            for (BasicBlock bl : program.blocks()) {
                JCExpression e = blockExpr(bl);
                JCExpression idd = newAuxIdent(names.fromString(bl.name()),syms.booleanType,0);
                e = factory.JmlBinary(JmlToken.EQUIVALENCE,idd,e); 
                p.assume(context,e);
            }

            // send definitions
            
            int n = 0;
            for (JCExpression expr: program.definitions()) {
                n = p.assume(context,expr,10);
            }

            p.push();

            JCExpression trueLiteral = factory.Literal(TypeTags.BOOLEAN,1);
            if (trackedAssumes.size() != 0) {
                JCExpression e = factory.Binary(JCTree.EQ, program.assumeCheckVar, factory.Literal(TypeTags.INT,0));
                p.assume(context,e);
            }

            IProverResult r = p.check();
            if (r.isSat()) {
                System.out.println("Method does NOT satisfy its specifications");
                String s = r.counterexample();
                // Look for "(assert$<Label>$<number> false"
                Matcher m = Pattern.compile("(assert\\$(\\w+)\\$(\\d+))\\$(\\d+) false").matcher(s);
                boolean noinfo = true;
                while (m.find()) {
                    String sname = m.group(1); // full name of the assertion
                    String label = m.group(2); // the label part (between 1st and 2nd $ signs)
                    int usepos = Integer.parseInt(m.group(3)); // the textual location of the assert statement
                    int declpos = Integer.parseInt(m.group(4)); // the textual location of associated information (or same as usepos if no associated information)
                    System.out.println("Assertion " + sname + " cannot be verified");
                    log.warning(usepos,"esc.assertion.invalid",label,node.getName());
                    if (declpos != usepos) log.warning(declpos,"esc.associated.decl");
                    noinfo = false;
                }
                if (noinfo) {
                    // No counterexample information
                    // FIXME - need a test for this
                    log.warning("esc.method.invalid",node.getName());
                } else {
                    m = Pattern.compile("\\$\\$LBLPOS\\$(\\d+)\\$([^ ]+) true").matcher(s);
                    while (m.find()) {
                        int pos = Integer.parseInt(m.group(1));
                        String label = m.group(2);
                        //System.out.println("Label " + label + " reported (expression true)");
                        log.warning(pos,"esc.label",label);
                    }
                    m = Pattern.compile("\\$\\$LBLNEG\\$(\\d+)\\$([^ ]+) false").matcher(s);
                    while (m.find()) {
                        int pos = Integer.parseInt(m.group(1));
                        String label = m.group(2);
                        //System.out.println("Label " + label + " reported (expression false)");
                        log.warning(pos,"esc.label",label);
                    }
                }
                if (true /*|| printCounterexample*/) {
                    int k = s.indexOf(' ');
                    System.out.println("Counterexample:" + s.substring(k+1));
                }
            } else {
                System.out.println("Method satisfies its specifications (as far as I can tell)");
                int index = ((YicesProver)p).satResult.indexOf("unsat core ids:");
                int[] ids = null;
                if (index >= 0) {
                    String[] sids = ((YicesProver)p).satResult.substring(index+"unsat core ids: ".length()).split("[ \n\r]");
                    ids = new int[sids.length];
                    for (int i=0; i<sids.length; i++) ids[i] = Integer.parseInt(sids[i]);
                    Arrays.sort(ids);
                }                 
                int nn = n - program.definitions().size();
                int k = 0;
                while (n > nn) {
                    JCExpression e = program.definitions().get(n-nn-1);
                    // Presuming this is an equality
                    String name = ((JCIdent)((JCBinary)e).getLeftOperand()).getName().toString();
                    System.out.println("LABEL " + name);
                    String[] parts = name.split("\\$");
                    if (parts.length != 3) { n--; continue; }
                    if (!parts[0].equals("checkAssumption")) { n--; continue;}
                    int pos = Integer.parseInt(parts[2]);
                    int found = Arrays.binarySearch(ids,n);
                    if (found < 0) {
                        // Already not part of the minimal core
                        ((YicesProver)p).send("(retract " + (n--) + ")\n");
                        ((YicesProver)p).eatPrompt();
                        System.out.println("ALREADY NOT IN MINIMAL CORE");
                        reportAssumptionProblem(parts[1],pos,node.getName(),p);
                        continue;
                    }
                    p.push(); k++;
                    ((YicesProver)p).send("(retract " + (n--) + ")\n");
                    ((YicesProver)p).eatPrompt();
                    r = p.check();
                    if (r.isSat()) {
                        System.out.println("NOW SAT - ASSUMPTION WAS OK");
                        p.pop(); k--;
                    } else {
                        System.out.println("STILL UNSAT - CORE WAS NOT MINIMAL - ASSSUMPTION WAS INFEASIBLE");
                        reportAssumptionProblem(parts[1],pos,node.getName(),p);
                    }
                }
                while (k-- > 0) p.pop();
                
            }
            p.pop();

            // Don't do this if we have done the core unsat method
            if (false) for (JCIdent aux: trackedAssumes) {
                p.push();
                String nm = aux.toString();
                String parts[] = nm.split("\\$");
                int pos = Integer.parseInt(parts[1]);
                JCExpression ex = factory.Binary(JCTree.EQ, program.assumeCheckVar, factory.Literal(TypeTags.INT,pos));
                p.assume(context,ex);
                r = p.check();
                if (!r.isSat()) {
                    String label = parts[2];
                    reportAssumptionProblem(label,pos,node.getName(),p);
                }
                p.pop();
            }

        } catch (ProverException e) {
            log.error("esc.prover.failure",e);
            System.out.println("PROVER FAILURE: " + e);
            if (e.mostRecentInput != null) System.out.println("INPUT: " + e.mostRecentInput);
        }
    }
    
    public void reportAssumptionProblem(String label, int pos, Name method, IProver p) {
        if (label.equals(Label.BRANCHT.toString())) {
            log.warning(Math.abs(pos),"esc.infeasible.branch","then",method);
            System.out.println("Branch is infeasible at " + pos);
            System.out.println(((YicesProver)p).satResult); // FIXME - contradictory items by number ???
        } else if (label.equals(Label.BRANCHE.toString())) {
            log.warning(Math.abs(pos),"esc.infeasible.branch","else",method);
            System.out.println("Branch is infeasible at " + pos);
            System.out.println(((YicesProver)p).satResult); // FIXME - contradictory items by number ???
        } else {
            log.warning(pos,"esc.infeasible.assumption",method);
            System.out.println("Assumption (" + label + ") is infeasible");
            System.out.println(((YicesProver)p).satResult); // FIXME - contradictory items by number ???
        }

    }


}
