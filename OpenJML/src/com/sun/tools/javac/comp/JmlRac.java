/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.comp;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.Label;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.Options;

/** This translator mutates an AST for runtime assertion checking.  The result
 * is passed on to the code-generation phase, so any changes to the AST must
 * still produce a fully-typechecked, valid Java AST.   In particular,
 * sym and type fields of new nodes must be filled in correctly for any new
 * or modified AST nodes.
 * As typechecking is already completed, any errors in this regard may cause 
 * unpredictable and incorrect behavior in code and VC generation.  Note that 
 * these changes are IN PLACE - they destructively change the AST.
 * 
 * The following transformations are performed here:(TODO- document this)
 * <UL>
 * <LI>In method statements:
 * <UL>
 * <LI>JML set and debug statements are converted to regular Java statements
 * <LI>JML unreachable statements are converted to JML assert statements
 * <LI>JML assert and assume statements are converted to tests of the predicates
 * <LI>ghost variables and local model class declarations are converted to
 * Java declarations
 * </UL>
 * <LI>JML expressions:
 * <UL>
 * <LI>The EQUIVALENCE, INEQUIVALENCE, IMPLIES and REVERSE_IMPLIES operations
 * are converted to equivalent forms using NOT, OR, EQUALITY
 * <LI>informal comment is converted to a true literal
 * <LI>All specification expressions that might be undefined are handled by 
 * testing and reporting undefinedness: null field access, divide or mod by zero,
 * method call with false preconditions, null arrays or array indices out of bounds,
 * FIXME - more
 * </UL>
 * </UL>
 * <P>
 * The following are ignored:
 * <UL>
 * <LI>hence_by statement
 * <LI>axiom clauses
 * <LI>method spec clauses: diverges, duration, working_space, FIXME
 * <LI>weakly modifier
 * <LI>FIXME modifiers
 * <LI>FIXME - refinining statements, type clauses, field clauses
 * </UL>
 * <P>
 * Runtime assertion checks that are added to the AST
 * <UL>
 * <LI>Tests for definedness of any specification expression
 * <LI>Test that the object of a field selection is non-null
 * <LI>Test that the array of an array index operation is non-null
 * <LI>Test that the array indices of an array index operation is in range
 * <LI> FIXME - method call precondition, in spec 
 * <LI> FIXME - assignable statements
 * <LI> FIXME - preconditions
 * <LI> FIXME - normal, exceptional postconditions, unexpected exceptions
 * <LI> FIXME - checking invariants before in-method method calls
 * <LI> FIXME - checking invariants when altering public fields
 * <LI> FIXME - checks of super class pre/post conditions
 * </UL>
 * 
 * TO DO:
 * <UL>
 * <LI>all other expression types
 * <LI>all other statement types: loop specs, refining specs
 * <LI>method clauses
 * <LI>variable specs: readable, writable, monitors, in, maps
 * <LI>type clauses
 * <LI>model classes
 * <LI>model methods
 * <LI>ghost fields
 * <LI>model fields
 * <LI>modifiers
 * <LI>redundantly, implies_that, for_example, weakly
 * </UL>
 * 
 * @author David Cok
 *
 */
public class JmlRac extends JmlTreeTranslator implements IJmlVisitor {
    
    /** The compilation context */
    @NonNull protected Context context;
    
    /** The log for error and warning messages */
    @NonNull protected Log log;
    
    /** The specifications database for this compilation context, initialized in the constructor */
    @NonNull protected JmlSpecs specs;
    
    /** The symbol table from the compilation context, initialized in the constructor */
    @NonNull protected Symtab syms;
    
    /** The Names table from the compilation context, initialized in the constructor */
    @NonNull protected Names names;
    
    /** Cached value of the utilities object */
    @NonNull protected Utils utils;
    
    /** Cached value of the JmlTreeUtils object */
    @NonNull protected JmlTreeUtils treeutils;
    
    /** The factory used to create AST nodes, initialized in the constructor */
    @NonNull protected JmlTree.Maker factory;
 
    /** Caching of the symbol for boolean equality, set in the constructor */
    protected Symbol booleqSymbol;
    
    /** Caching of the symbol for boolean inequality, set in the constructor */
    protected Symbol boolneSymbol;
    
    /** Caching of the symbol for a true literal, set in the constructor */
    protected JCLiteral trueLit;
    
    /** Caching of the symbol for a false literal, set in the constructor */
    protected JCLiteral falseLit;

    /** This is modified as the AST is walked; it is set true when a specification
     * expression is being processed.
     */
    boolean inSpecExpression;
    
//    /** The class declaration that we are currently within */
//    protected @NonNull JCClassDecl currentClassDecl = null;

    /** The method declaration that we are currently within */
    protected @NonNull JCMethodDecl currentMethodDecl = null;
    
    /** The info structure for the class declaration that we are currently within */
    protected @NonNull ClassInfo currentClassInfo = null;

    /** The info structure method declaration that we are currently within */
    protected @NonNull MethodInfo currentMethodInfo = null;

    /** Current source */
    protected JavaFileObject source;
    
    /** A stack of previous source files, manipulated through pushSource and
     * popSource.  The current source is the top element of the stack.
     */
    protected java.util.List<JavaFileObject> stack = new LinkedList<JavaFileObject>();
    
    /** Makes the argument the current source (and top element of the stack).
     * Does not set the source in log (that is done only when needed) */
    public void pushSource(JavaFileObject jfo) {
        stack.add(0,source);
        source = jfo;
    }
    
    /** Discards the top element of the stack and makes the new top element the
     * current source.
     */
    public void popSource() {
        source = stack.remove(0);
    }

    // TODO - need more documentation
    Env<AttrContext> env;
    DiagnosticPosition make_pos;
    ClassSymbol assertionFailureClass;
    ClassSymbol utilsClass;
    JCIdent utilsClassIdent;
    JmlAttr attr;
    Name resultName;
    Name exceptionName;
    Name exceptionCatchName;
    
    JCLiteral zero;
    JCLiteral nulllit;
    JCLiteral maxIntLit;
    
    static final public String invariantMethodString = org.jmlspecs.utils.Utils.invariantMethodString;
    Name invariantMethodName;
    static final public String staticinvariantMethodString = org.jmlspecs.utils.Utils.staticinvariantMethodString;
    Name staticinvariantMethodName;
    
    public final static String NULL_ASSIGNMENT = "assignment of null to non_null";

    public final static String NULL_INITIALIZATION = "null initialization of non_null variable";

    public final static String LOOP_VARIANT_NEGATIVE = "loop variant is less than 0";

    public final static String NULL_SELECTION = "selecting a field of a null object";

    /** The constructor for a new translator */
    // FIXME - sort out use of env here and in the translate call
    public JmlRac(Context context, Env<AttrContext> env) {
        this.context = context;
        this.env = env;
        this.syms = Symtab.instance(context);
        this.names = Names.instance(context);
        this.factory = JmlTree.Maker.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        //this.treeutils.setEnv(env);
        this.utils = Utils.instance(context);
        this.attr = JmlAttr.instance(context);
        this.log = Log.instance(context);
        
        ClassReader reader = ClassReader.instance(context);
        reader.init(syms);

        assertionFailureClass = reader.enterClass(names.fromString("org.jmlspecs.utils.Utils$JmlAssertionFailure"));
        utilsClass = reader.enterClass(names.fromString("org.jmlspecs.utils.Utils"));
        utilsClassIdent = factory.Ident(names.fromString("org.jmlspecs.utils.Utils"));
        utilsClassIdent.type = utilsClass.type;
        utilsClassIdent.sym = utilsClassIdent.type.tsym;
        
        booleqSymbol = treeutils.findOpSymbol(JCTree.EQ,syms.booleanType);
        boolneSymbol = treeutils.findOpSymbol(JCTree.NE,syms.booleanType);
        trueLit = treeutils.trueLit;
        falseLit = treeutils.falseLit;

        zero = treeutils.makeLit(0,syms.intType,0);
        nulllit = treeutils.makeLit(0,syms.botType, null);
        maxIntLit = treeutils.makeLit(0,syms.intType,Integer.MAX_VALUE);

        this.resultName = treeutils.resultName;
        this.exceptionName = Names.instance(context).fromString("_JML$$$exception");
        this.exceptionCatchName = Names.instance(context).fromString("_JML$$$exceptionCatch");

        //integerType = reader.enterClass(names.fromString("java.lang.Integer")).type;
        
        invariantMethodName = names.fromString(invariantMethodString);
        staticinvariantMethodName = names.fromString(staticinvariantMethodString);
    }
    
//    /** Translates the env.tree AST in the given env, replacing the value
//     * in env. */
//    // FIXME - perhaps do the correction of env.toplevel here instead of in
//    // JmlCompiler
//    public void translate(Env<AttrContext> env) {
//        pushSource(env.toplevel.sourcefile);
//        try {
//            env.tree = translate(env.tree);
//        } finally {
//            popSource();
//        }
//    }

    /** This structure holds specification information about a class.  It is
     * lazily constructed and saved.  FIXME - where is it saved?
     */
    public static class ClassInfo {
        public ClassInfo(JCClassDecl d) { this.decl = d; }
        JCClassDecl decl;
        JmlSpecs.TypeSpecs typeSpecs = null;
        JCMethodDecl invariantDecl = null;
        JCMethodDecl staticinvariantDecl = null;
        ListBuffer<JmlTypeClauseConstraint> constraints = new ListBuffer<JmlTypeClauseConstraint>();
        ListBuffer<JmlTypeClauseExpr> translatedInitiallys = new ListBuffer<JmlTypeClauseExpr>();
    }


    /** This structure holds specification information about a method.  It is
     * lazily constructed and saved.  FIXME - is it saved?
     */
    static public class MethodInfo {
        public MethodInfo(JCMethodDecl d) { 
            this.decl = d; 
            this.owner = d.sym; 
            this.source = ((JmlMethodDecl)d).sourcefile;
        }
        MethodSymbol owner;
        JCMethodDecl decl;
        JavaFileObject source;
        JCVariableDecl resultDecl;
        boolean resultUsed = false;
        JCExpression exceptionDecl;
        VarSymbol exceptionLocal;
        Map<JmlSpecificationCase,JCVariableDecl> preconditionDecls = new HashMap<JmlSpecificationCase,JCVariableDecl>();
        ListBuffer<JCVariableDecl> olds = new ListBuffer<JCVariableDecl>();
        Map<Name,JCLabeledStatement> labels = new HashMap<Name,JCLabeledStatement>();
        Map<JCLabeledStatement,ListBuffer<JCStatement>> labelDecls = new HashMap<JCLabeledStatement,ListBuffer<JCStatement>>();
        JCStatement preCheck;
        JCStatement postCheck;
        int variableDefs = 0;
    }

    /** Translate a list of nodes, adding checks that each
     * one is nonnull.
     */
    public <T extends JCExpression> List<T> translateNN(List<T> trees) {
        if (trees == null) return null;
        for (List<T> l = trees; l.nonEmpty(); l = l.tail)
            l.head = (T)makeNullCheck(l.head.pos,translate(l.head),
                    "ERROR",Label.UNDEFINED_NULL_DEREFERENCE);  // FIXME _ fix the error message if this stays
        return trees;
    }

    /** Creates a string that gives the location of an error; the output is a
     * combination of the file name (from source) and the line number, computed
     * from the character position.
     * @param source the source file relevant to this error
     * @param pos the character position to point to for this error
     * @return the resulting string
     */
    public String position(JavaFileObject source, int pos) {
        JavaFileObject prevSource = log.currentSourceFile();
        try {
            log.useSource(source);
            return (source==null?"":source.getName() + ":" + log.currentSource().getLineNumber(pos)) + ": JML ";
        } catch (UnsupportedOperationException e) {
            return (source==null?"":source.getName() + ": ? " ) + ": JML ";
        } finally {
            log.useSource(prevSource);
        }
    }
    
    /** Returns true if the given symbol has a Helper annotation */
    public boolean isHelper(Symbol symbol) {
        return symbol.attribute((attr).tokenToAnnotationSymbol.get(JmlToken.HELPER))!=null;

    }
    
    /** Returns true if the given symbol has a Model annotation */
    public boolean isModel(Symbol symbol) {
        return symbol.attribute((attr).tokenToAnnotationSymbol.get(JmlToken.MODEL))!=null;
    }
    


    /** Creates a method call that checks that the given expression is non-null,
     * returning the expression.
     * A runtime assertion violation occurs if the check fails.
     * @param pos the character position at which to point out an error (in the
     *          current source file)
     * @param expr the translated expression to test and return
     * @param msg the error message
     * @param label the kind of error
     * @return the new translated AST
     */
    protected JCExpression makeNullCheck(int pos, JCExpression expr, String msg, Label label) {
        String posDescription = position(source,pos);
        
        JCLiteral message = treeutils.makeStringLiteral(pos,posDescription + msg); // end -position ??? FIXME
        JCFieldAccess m = treeutils.findUtilsMethod(pos,"nonNullCheck");
        JmlMethodInvocation newv = factory.at(pos).JmlMethodInvocation(m,List.<JCExpression>of(message,expr));
        newv.type = expr.type.baseType();
        newv.label = label;
        return newv;
    }

    /** Creates a method call that checks that the given expression is true,
     * returning an alternate expression.
     * A runtime assertion violation occurs if the check fails.
     * @param pos the character position at which to point out an error (in the
     *          current source file)
     * @param condition the untranslated expression to test
     * @param that the untranslated expression to be returned
     * @param msg the error message
     * @param label the kind of error
     * @return the new translated AST
     */
    protected JCExpression makeTrueCheck(int pos, JCExpression condition, JCExpression that, String msg, Label label) {
        String posDescription = position(source,pos);
        
        JCLiteral message = treeutils.makeStringLiteral(pos,posDescription + msg); // end -position ??? FIXME
        JCFieldAccess m = treeutils.findUtilsMethod(pos,"trueCheck");
        JCExpression tcond = translate(condition);// Caution - translate resets the factory position
        JCExpression trans = that;  
        JmlMethodInvocation newv = factory.at(pos).JmlMethodInvocation(m,List.<JCExpression>of(message,tcond,trans));
        newv.type = that.type.baseType();
        newv.label = label;
        return newv;
    }
    
    /** Creates a method call that checks whether two Object expressions are equal 
     * (giving an assertion error if not) and returns the second expression.  
     * A runtime assertion violation occurs if the check fails.
     * @param pos the character position at which to point out an error (in the
     *          current source file)
     * @param obj the untranslated expression to test
     * @param that the untranslated expression to be returned
     * @param msg the error message
     * @param label the kind of error
     * @return the new translated AST
     */
    protected JCExpression makeEqCheck(int pos, JCExpression obj, JCExpression that, String msg, Label label) {
        String posDescription = position(source,pos);
        
        JCLiteral message = treeutils.makeStringLiteral(pos,posDescription + msg); // end -position ??? FIXME
        JCFieldAccess m = treeutils.findUtilsMethod(pos,"eqCheck");
        JmlMethodInvocation newv = factory.at(pos).JmlMethodInvocation(m,List.<JCExpression>of(message,obj,that));
        newv.type = that.type.baseType();
        newv.label = label;
        return newv;
    }
    
    /** Creates a method call that checks that the given expression is non-zero,
     * returning the expression.  A runtime assertion violation occurs if the
     * check fails.
     * @param pos the character position at which to point out an error (in the
     *          current source file)
     * @param that the untranslated expression to test and return
     * @param label the kind of error
     * @return the new translated AST
     */
    protected JCExpression makeZeroCheck(int pos, JCExpression that, Label label) {
        String s = position(source,pos);
        JCLiteral message = treeutils.makeStringLiteral(pos,s+"Division by zero"); // end -position ??? FIXME
        JCExpression newv = translate(that);
        JCFieldAccess m = null;
        int tag = that.type.tag;
        switch (tag) {
            case TypeTags.INT:
                m = treeutils.findUtilsMethod(pos,"zeroIntCheck");
                break;
            case TypeTags.LONG:
                m = treeutils.findUtilsMethod(pos,"zeroLongCheck");
                break;
            case TypeTags.DOUBLE:
                m = treeutils.findUtilsMethod(pos,"zeroDoubleCheck");
                break;
            case TypeTags.FLOAT:
                m = treeutils.findUtilsMethod(pos,"zeroFloatCheck");
                break;
            case TypeTags.SHORT:
                m = treeutils.findUtilsMethod(pos,"zeroShortCheck");
                break;
            case TypeTags.BYTE:
                m = treeutils.findUtilsMethod(pos,"zeroByteCheck");
                break;
            case TypeTags.CHAR:
                m = treeutils.findUtilsMethod(pos,"zeroCharCheck");
                break;
            default:
                // these should not type check anyway
                newv = that;
                break;
        }
        if (m != null) {
            JmlMethodInvocation call = factory.at(pos).JmlMethodInvocation(m,List.<JCExpression>of(message,newv));
            call.type = that.type.baseType();
            call.label = label;
            newv = call;
        }
        return newv;
    }

    // TODO - document - argument already translated
    protected void checkAssignable(JCAssign that) {
        if (that.lhs instanceof JCFieldAccess) checkFieldAssignable((JCFieldAccess)that.lhs,that.pos);
        else if (that.lhs instanceof JCIdent) {
            Symbol sym = ((JCIdent)that.lhs).sym;
// FIXME            if (!sym.isLocal()) that.lhs = checkIdentAssignable((JCIdent)that.lhs,that.pos);
        } else if (that.lhs instanceof JCArrayAccess) {
            checkArrayAssignable((JCArrayAccess)that.lhs,that.pos);
        }
    }
    
    // TODO - document - argument already translated
    // Identical to the above, except for the argument type
    protected void checkAssignableOp(JCAssignOp that) {
        if (that.lhs instanceof JCFieldAccess) checkFieldAssignable((JCFieldAccess)that.lhs,that.pos);
        else if (that.lhs instanceof JCIdent) {
            Symbol sym = ((JCIdent)that.lhs).sym;
            if (!sym.isLocal()) that.lhs = checkIdentAssignable((JCIdent)that.lhs,that.pos);
        } else if (that.lhs instanceof JCArrayAccess) {
            checkArrayAssignable((JCArrayAccess)that.lhs,that.pos);
        }
    }
    
    // TODO - document
    protected void checkFieldAssignable(JCFieldAccess assignee, int pos) {
        if (!(currentMethodDecl instanceof JmlMethodDecl)) return;
        JmlMethodSpecs mspecs = ((JmlMethodDecl)currentMethodDecl).methodSpecsCombined.cases.deSugared;
        if (mspecs == null) return;
        for (JmlSpecificationCase c: mspecs.cases) {
            JCVariableDecl vd = currentMethodInfo.preconditionDecls.get(c);
            JCExpression precond = vd == null ? trueLit : treeutils.makeIdent(c.pos,vd.sym);
            //JCExpression precond = trueLit; // FIXME - need the assignable clauses precondition
            for (JmlMethodClause m: c.clauses) {
//                if (m.token == JmlToken.REQUIRES) {
//                    precond = treeutils.makeAnd(m.pos,precond,((JmlMethodClauseExpr)m).expression);
//                    continue;
//                }
                if (m.token != JmlToken.ASSIGNABLE) continue;
                // if precond is true, then one of the items in the following list must match
                JCExpression cond = falseLit;
                for (JCExpression e : ((JmlMethodClauseStoreRef)m).list) {
                    if (e instanceof JmlStoreRefKeyword) {
                        JmlToken t = ((JmlStoreRefKeyword)e).token;
                        if (t == JmlToken.BSNOTHING) {
                            // No change - stays false if was already
                        } else if (t == JmlToken.BSEVERYTHING || t == JmlToken.BSNOTSPECIFIED) {
                            // OK
                            cond = trueLit;
                            break;
                        } else {
                            //FIXME - bad option
                        }
                    } else if (e instanceof JCIdent) {
                        JCIdent i = (JCIdent)e;
                        if (i.sym.equals(assignee.sym)) {
                            // They are the same declaration - check if they belong to the same object
                            // CHeck that 'this' equals assignee.selected
                            cond = trueLit;  // Just allow it for now FIXME
                        }
                    } else if (e instanceof JCFieldAccess) {
                        JCFieldAccess fa = (JCFieldAccess)e;
                        if (fa.sym == null || fa.sym.equals(assignee.sym)) {
                            // need to assert that assignee.selected and \old(fa.selected) are equal  // FIXME - need \old
                            JCExpression ex = treeutils.makeEqObject(fa.pos,assignee.selected,fa.selected);
                            ex = treeutils.makeImplies(e.pos,precond,ex);
                            cond = treeutils.makeOr(e.pos,cond,ex);
                        }
                    } else if (e instanceof JmlStoreRefArrayRange) {
                        // Not a match
                    } else {
                        // FIXME - bad option
                    }
                }
                if (cond != trueLit) {
                    // assert that (precond ==> cond)
                    // this does no translation
                    JCExpression e = treeutils.makeImplies(precond.pos,precond,cond);
                    assignee.selected = makeTrueCheck(pos,e,assignee.selected,"assignable",Label.ASSIGNABLE);
                }
            }
        }
    }
    
    // TODO - document
    protected void checkArrayAssignable(JCArrayAccess assignee, int pos) {
        if (!(currentMethodDecl instanceof JmlMethodDecl)) return;
        JmlMethodSpecs mspecs = ((JmlMethodDecl)currentMethodDecl).methodSpecsCombined.cases.deSugared;
        if (mspecs == null) return;
        for (JmlSpecificationCase c: mspecs.cases) {
            JCVariableDecl vd = currentMethodInfo.preconditionDecls.get(c);
            JCExpression precond = vd == null ? trueLit : treeutils.makeIdent(c.pos,vd.sym);
//            JCExpression precond = treeutils.trueLit; // FIXME - need the assignable clauses precondition
            for (JmlMethodClause m: c.clauses) {
//                if (m.token == JmlToken.REQUIRES) {
//                    precond = treeutils.makeAnd(m.pos,precond,((JmlMethodClauseExpr)m).expression);
//                    continue;
//                }
                if (m.token != JmlToken.ASSIGNABLE) continue;
                // if precond is true, then one of the items in the following list must match
                JCExpression cond = falseLit;
                for (JCExpression e : ((JmlMethodClauseStoreRef)m).list) {
                    if (e instanceof JmlStoreRefKeyword) {
                        JmlToken t = ((JmlStoreRefKeyword)e).token;
                        if (t == JmlToken.BSNOTHING) {
                            // No change - stays false if was already
                        } else if (t == JmlToken.BSEVERYTHING || t == JmlToken.BSNOTSPECIFIED) {
                            // OK
                            cond = trueLit;
                            break;
                        } else {
                            //FIXME - bad option
                        }
                    } else if (e instanceof JCIdent) {
                        // no match
                    } else if (e instanceof JCFieldAccess) {
                        // no match
                    } else if (e instanceof JmlStoreRefArrayRange) {
                        // possible match - if arrays are equal and the index is in range
                        JmlStoreRefArrayRange allowed = (JmlStoreRefArrayRange)e;
                        
                        // FIXME - this evaluates the array twice, and evaluates the index multiple times
                        JCExpression sameArrays = treeutils.makeEqObject(pos,assignee.indexed,allowed.expression);
                        if (allowed.lo == null && allowed.hi == null) {
                            // any index allowed
                        } else if (allowed.lo == allowed.hi) {
                            // require allowed.lo == assignee.index // these are ints // FIXME
                        } else if (allowed.hi == null) {
                            // requires allowed.lo <= assignee.index && assignee.index < array.length // FIXME
                        } else {
                            // requires allowed.lo <= assignee.index && assignee.index <= allowed.hi // FIXME
                        }
                        cond = treeutils.makeOr(pos,cond,sameArrays);
                    } else {
                        // FIXME - bad option
                    }
                }
                if (cond != trueLit) {
                    // assert that (precond ==> cond)
                    // this does no translation
                    JCExpression e = treeutils.makeImplies(precond.pos,precond,cond);
                    assignee.indexed = makeTrueCheck(pos,e,assignee.indexed,"assignable",Label.ASSIGNABLE);
                }
            }
        }
    }
    
    // TODO - document
    protected JCExpression checkIdentAssignable(JCIdent assignee, int pos) {
        JCExpression wrapped = assignee;
        if (!(currentMethodDecl instanceof JmlMethodDecl)) return wrapped;
        JmlMethodSpecs mspecs = ((JmlMethodDecl)currentMethodDecl).methodSpecsCombined.cases.deSugared;
        if (mspecs == null) return wrapped;
        for (JmlSpecificationCase c: mspecs.cases) {
            JCVariableDecl vd = currentMethodInfo.preconditionDecls.get(c);
            JCExpression precond = vd == null ? trueLit : treeutils.makeIdent(c.pos,vd.sym);
//            JCExpression precond = trueLit; // FIXME - need the assignable clauses precondition
            for (JmlMethodClause m: c.clauses) {
//                if (m.token == JmlToken.REQUIRES) {
//                    precond = treeutils.makeAnd(m.pos,precond,((JmlMethodClauseExpr)m).expression);
//                    continue;
//                }
                if (m.token != JmlToken.ASSIGNABLE) continue;
                // if precond is true, then one of the items in the following list must match
                JCExpression cond = falseLit;
                for (JCExpression e : ((JmlMethodClauseStoreRef)m).list) {
                    if (e instanceof JmlStoreRefKeyword) {
                        JmlToken t = ((JmlStoreRefKeyword)e).token;
                        if (t == JmlToken.BSNOTHING) {
                            // No change - stays false if was already
                        } else if (t == JmlToken.BSEVERYTHING || t == JmlToken.BSNOTSPECIFIED) {
                            // OK
                            cond = trueLit;
                            break;
                        } else {
                            //FIXME - bad option
                        }
                    } else if (e instanceof JCIdent) {
                        JCIdent i = (JCIdent)e;
                        if (i.sym.equals(assignee.sym)) {
                            // Matches - the identifiers refer to the same declaration and they are both implicitly qualified by 'this' 
                            cond = trueLit;
                            break;
                        }
                    } else if (e instanceof JCFieldAccess) {
                        JCFieldAccess fa = (JCFieldAccess)e;
                        if (assignee.sym.equals(fa.sym)) {
                            // Possible match: check if 'this' equals fa.selected // FIXME
                            cond = trueLit; // Just allow it for now FIXME
                        }
//                        if (fa.sym.equals(f.sym)) {
//                            // need to assert that f.selected and \old(fa.selected) are equal
//                            JCExpression ex = makeBinary(fa.pos,JCTree.EQ,objecteqSymbol,f.selected,fa.selected);
//                            ex = makeImplies(e.pos,precond,ex);
//                            cond = makeOr(e.pos,cond,ex);
//                        }
                        // FIXME _ unsupported option
                    } else if (e instanceof JmlStoreRefArrayRange) {
                        // Not a match
                    } else {
                        // FIXME - bad option
                    }
                }
                if (cond != treeutils.trueLit) {
                    // assert that (precond ==> cond)
                    // this does no translation
                    JCExpression e = treeutils.makeImplies(precond.pos,precond,cond);
                    wrapped = makeTrueCheck(pos,e,wrapped,"target not assignable",Label.ASSIGNABLE);
                }
            }
        }
        return wrapped;
    }
    
    /** Creates an AST for calling a method with the given name from the
     * org.jmlspecs.utils class (that is available at runtime)
     * @param methodName the name of the method 
     * @return the corresponding AST
     */
    public JCFieldAccess findUtilsMethod(String methodName) {  // FIXME - needs position informatino
        Name n = names.fromString(methodName);
        Scope.Entry e = utilsClass.members().lookup(n);
        Symbol ms = e.sym;
        JCFieldAccess m = factory.Select(utilsClassIdent,n);
        m.sym = ms;
        m.type = m.sym.type;
        return m;
    }
    
    // TODO - document
    public JCStatement findSuperMethod(ClassSymbol csym, Name methodName) {
        Symbol ms;
        do {
            Type t = csym.getSuperclass();
            if (t == null) return factory.Skip();
            csym = (ClassSymbol)t.tsym;
            Scope.Entry e = csym.members().lookup(methodName);
            ms = e.sym;
            if (ms != null) break;
        } while (true) ;
        JCIdent m = factory.Ident(methodName);
        m.sym = ms;
        m.type = m.sym.type;
        JCMethodInvocation a = factory.Apply(null,m,List.<JCExpression>nil());
        a.type = syms.voidType;
        return factory.Exec(a);
    }
    
    // TODO - document
    JCStatement undefinedCheck(Symbol owner, String prefix, JCStatement stat) {
        return undefinedCheck(owner,prefix,List.<JCStatement>of(stat));
    }
    
    // TODO - document
    JCStatement undefinedCheck(Symbol owner, String prefix, List<JCStatement> stats) {
        JCCatch ct = treeutils.makeCatcher(owner,syms.exceptionType);
        ct.body.stats = List.<JCStatement>of(methodCallUndefined(prefix));
        JCStatement s = factory.Try(factory.Block(0,stats), // FIXME - pos
                List.<JCCatch>of(ct),
                null
                );
        return s;
    }

    /** Creates a call of org.jmlspecs.utils.assertionFailure(s), where
     * s is a literal containing the value of the argument
     * @param sp the string to make into the literal argument of the call
     * @param pos the character position of the created AST
     * @return an assert statement indication an assertion failure
     */
    public JCStatement assertFailure(String sp, int pos) {
        factory.at(pos);
        JCExpression lit = treeutils.makeLit(pos,syms.stringType,sp);
        JCFieldAccess m = findUtilsMethod("assertionFailure");
        JCExpression c = factory.Apply(null,m,List.<JCExpression>of(lit));
        c.setType(syms.voidType);
        return factory.Exec(c);
    }
    
//    public JCExpression nullCheck(String message, int pos, JCExpression value) {
//        if (value.type.isPrimitive()) return value;
//        String s = "";
//        if (currentMethodInfo != null) s = position(currentMethodInfo.source,pos);
//        else if (currentClassInfo.decl instanceof JmlClassDecl) s = position(((JmlClassDecl)currentClassInfo.decl).sourcefile,pos);
//        else {
//            // FIXME - print out a warning
//        }
//        factory.at(pos);
//        JCExpression lit = treeutils.makeLit(pos,syms.stringType,s+message);
//        JCFieldAccess m = findUtilsMethod("nonNullCheck");
//        JCExpression c = factory.at(pos).Apply(null,m,List.<JCExpression>of(lit,value));
//        c.setType(value.type);
//        // FIXME - check for const value and if possible, omit this check
//        return c;
//    }
    
    // TODO - document
    public JCStatement methodCallPre(String sp, JCExpression tree) {
        String s = sp + "precondition is false";
        return assertFailure(s,tree.pos);
    }
    
    // TODO - document
    public JCStatement methodCallUndefined(String prefix) {
        int pos = 0;
        String s = prefix + " is undefined - exception thrown";
        JCExpression lit = treeutils.makeLit(pos,syms.stringType,s);
        JCFieldAccess m = findUtilsMethod("assertionFailure");
        JCExpression c = factory.at(pos).Apply(null,m,List.<JCExpression>of(lit));
        c.setType(syms.voidType);
        return factory.Exec(c);
    }
    
    // TODO - document
    public JCStatement methodCallCheckInvariant(JmlClassDecl tree, ClassSymbol csym, String classname) {
        Type currentType = csym.type;
        JCExpression lit = treeutils.makeStringLiteral(tree.pos,classname);
        JCFieldAccess m = findUtilsMethod("callClassInvariant");
//        Symbol psym = currentClassInfo.invariantDecl.params.head.sym;
//        JCIdent id = factory.at(tree.pos()).Ident(psym);
        Name thisName = names._this;
        JCIdent id = factory.at(tree.pos()).Ident(thisName);
        id.sym = tree.thisSymbol; //Resolve.instance(context).resolveSelf(tree.pos(),classEnv,csym,thisName);
        id.type = currentType;
        JCExpression c = factory.at(tree.pos).Apply(null,m,List.<JCExpression>of(id,lit));
        c.setType(syms.voidType);
        return factory.Exec(c);
        
//        JCIdent idd = factory.at(tree.pos()).Ident(names._super);
//        idd.sym = tree.superSymbol;
//        idd.type = idd.sym.type;
//        JCExpression c = factory.at(tree.pos).Apply(idd,m,List.<JCExpression>nil());
    }
    
    // TODO - document
    public JCStatement methodCallCheckStaticInvariant(String classname) {
        int pos = 0;
        JCExpression lit = treeutils.makeLit(pos,syms.stringType,classname);
        JCFieldAccess m = findUtilsMethod("callStaticClassInvariant");
        JCExpression c = factory.at(pos).Apply(null,m,List.<JCExpression>of(lit));
        c.setType(syms.voidType);
        return factory.Exec(c);
    }
    

    
    // TODO - document
    public JCStatement methodCallPost(String sp, JCExpression tree) {
        // org.jmlspecs.utils.Utils.assertionFailure();
        
        String s = sp + "postcondition is false";
        return assertFailure(s,tree.pos);
    }
    
    /** Creates an AST for a zero-argument call of the given method (from
     * org.jmlspecs.utils).
     * @param methodName the name of the method to call
     * @return the resulting AST
     */
    public JCStatement methodCallUtils(String methodName) {
        JCFieldAccess m = findUtilsMethod(methodName);
        JCExpression c = factory.Apply(null,m,List.<JCExpression>nil());
        c.setType(syms.voidType);
        JCStatement p = factory.Exec(c);
        p.setType(syms.voidType);
        return p;
    }
    
    /** Creates an AST for a one-argument call of the given method (from
     * org.jmlspecs.utils).
     * @param methodName the name of the method to call
     * @param translatedArg the AST which is the (already translated) argument
     * @return the resulting AST
     */
    public JCExpression methodCallUtilsExpression(String methodName, JCExpression translatedArg) {
        JCFieldAccess m = findUtilsMethod(methodName);
        JCExpression c = factory.Apply(null,m,List.<JCExpression>of(translatedArg));
        c.setType(((Type.MethodType)m.type).restype);
        return c;
    }
    
    /** Creates an AST for a two-argument call of the given method (from
     * org.jmlspecs.utils).
     * @param methodName the name of the method to call
     * @param translatedArg the AST which is the (already translated) argument
     * @param translatedArg2 the AST which is the (already translated) second argument
     * @return the resulting AST
     */
    public JCExpression methodCallUtilsExpression(String methodName, JCExpression translatedArg, JCExpression translatedArg2) {
        JCFieldAccess m = findUtilsMethod(methodName);
        JCExpression c = factory.Apply(null,m,List.<JCExpression>of(translatedArg,translatedArg2));
        c.setType(((Type.MethodType)m.type).restype);
        return c;
    }
    
//    public JCStatement methodCallThis(Name methodName) {
//        JCIdent m = findThisMethod(methodName);
//        JCExpression c = factory.Apply(null,m,List.<JCExpression>nil());
//        c.setType(syms.voidType);
//        JCStatement p = factory.Exec(c);
//        p.setType(syms.voidType);
//        return p;
//    }
    
    // TODO _ document
    public JCExpression methodCallThisExpression(JCMethodDecl methodDecl) {
        JCIdent m = factory.Ident(methodDecl.name);
        m.sym = methodDecl.sym;
        m.type = m.sym.type;
        JCExpression c = factory.Apply(null,m,List.<JCExpression>nil());
        c.setType(syms.voidType);
        return c;
    }
    
    // TODO _ document
    public JCStatement methodCallThis(JCMethodDecl methodDecl) {
        JCExpression c = methodCallThisExpression(methodDecl);
        JCStatement p = factory.Exec(c);
        p.setType(syms.voidType);
        return p;
    }
    
//    public JCStatement methodInvoke(JCExpression exp, ClassSymbol csym) {
//        try {
//            Method invoke = java.lang.reflect.Method.class.getMethod("invoke",new Class<?>[]{Object.class, Object[].class});
//            invoke.invoke
//        } catch (Exception e) {
//            log.noticeWriter.println("FAILED");
//        }
//    }
    
    // TODO _ document
    public JCExpression methodCallgetClass(JCExpression expr) {
        Name n = names.fromString("getClass");
        Scope.Entry e = syms.objectType.tsym.members().lookup(n);
        Symbol ms = e.sym;
        JCFieldAccess m = factory.Select(expr,n);
        m.sym = ms;
        m.type = m.sym.type;

        JCExpression c = factory.Apply(null,m,List.<JCExpression>nil());
        c.setType(syms.classType);
        return c;
    }
    
//    public JCStatement methodCall(JmlStatementExpr tree) {
//        // org.jmlspecs.utils.Utils.assertionFailure();
//        
//        //JmlToken t = tree.token;
//        //String s = t == JmlToken.ASSERT ? "assertion is false" : t == JmlToken.ASSUME ? "assumption is false" : "unreachable statement reached";
//        String s = 
//            tree.label == Label.EXPLICIT_ASSERT ? "assertion is false" :
//                tree.label == Label.EXPLICIT_ASSUME ? "assumption is false" :
//                    tree.label == Label.UNREACHABLE ? "unreachable statment reached" :
//                        tree.label.toString();
//        s = tree.source.getName() + ":" + tree.line + ": JML " + s;
//        JCExpression lit = makeLit(syms.stringType,s);
//        JCFieldAccess m = findUtilsMethod("assertionFailure");
//        JCExpression c = factory.Apply(null,m,List.<JCExpression>of(lit));
//        c.setType(syms.voidType);
//        return factory.Exec(c);
//    }
    
    /** This creates a Java statement implementing a JML assert or assume statement.
     * Both are converted into tests of the predicate, which, if false, causes
     * a runtime JML assertion violation to be raised.
     * @param tree the assert statement
     * @param translatedOptionalExpr the translated optional expression in the assert
     *      statement, which serves as an error message
     * @return the AST for the Java statement implementing this logic
     */
    public JCStatement methodCall(JmlStatementExpr tree, @Nullable JCExpression translatedOptionalExpr) {
        // org.jmlspecs.utils.Utils.assertionFailure();
        
        String s = 
            tree.label == Label.EXPLICIT_ASSERT ? "assertion is false" :
                tree.label == Label.EXPLICIT_ASSUME ? "assumption is false" :
                    tree.label == Label.UNREACHABLE ? "unreachable statement reached" :
                        tree.label.toString();
        JavaFileObject prev = log.useSource(tree.source);
        s = tree.source.getName() + ":" + log.currentSource().getLineNumber(tree.pos) + ": JML " + s;
        log.useSource(prev);
        JCExpression lit = treeutils.makeStringLiteral(tree.pos,s);
        // FIXME - I don't think we need the conditioning
        JCFieldAccess m = findUtilsMethod(translatedOptionalExpr == null ? "assertionFailure" : "assertionFailure2");
        JCExpression c = translatedOptionalExpr == null ? factory.Apply(null,m,List.<JCExpression>of(lit)) :
            factory.Apply(null,m,List.<JCExpression>of(lit,translatedOptionalExpr));
        c.pos = m.pos = tree.pos;
        c.setType(syms.voidType);
        return factory.at(tree.pos).Exec(c);
    }
    
    /////////////////// Tree visitor methods /////////////////////////////////
    
    public void visitAnnotation(JCAnnotation tree) {
        // No need to translate the annotations
        result = tree;
    }

    @Override
    public void visitAssign(JCAssign that) {
        boolean nonnull = false;
        if (that.lhs instanceof JCIdent) {
            Symbol sym = ((JCIdent)that.lhs).sym;
            if (sym instanceof VarSymbol) {
                VarSymbol vsym = (VarSymbol)((JCIdent)that.lhs).sym;
                nonnull = !vsym.type.isPrimitive() && specs.isNonNull(vsym,vsym.enclClass());
            } else {
                // Annotations can get here
                //log.noticeWriter.println("Unknown symbol type " + sym + " " + sym.getClass());
                nonnull = false;
            }
        } else if (that.lhs instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)that.lhs;
            VarSymbol vsym = (VarSymbol)fa.sym;
            nonnull = !vsym.type.isPrimitive() && specs.isNonNull(vsym,vsym.enclClass());
        }
        that.lhs = translate(that.lhs);
        checkAssignable(that);
        that.rhs = translate(that.rhs);
        if (nonnull) {
            that.rhs = makeNullCheck(that.pos,that.rhs,
                    NULL_ASSIGNMENT,
                    Label.POSSIBLY_NULL_ASSIGNMENT);
        }

        result = that;
    }

    @Override
    public void visitAssignop(JCAssignOp that) {
        that.lhs = translate(that.lhs);
        checkAssignableOp(that);
        if (that.getTag() == JCTree.DIV_ASG || that.getTag() == JCTree.MOD_ASG) {
            if (that.rhs instanceof JCLiteral && ((JCLiteral)that.rhs).value.equals(Integer.valueOf(0))) {
                log.noticeWriter.println("Explicit divide by zero");  // FIXME - how to translate this - proper warning message
            } else {
                that.rhs = makeZeroCheck(that.pos,that.rhs, inSpecExpression? Label.UNDEFINED_DIV0 : Label.POSSIBLY_DIV0);
            }
        } else {
            that.rhs = translate(that.rhs);
        }
        result = that;
    }

    @Override
    public void visitBinary(JCBinary that) {
        that.lhs = translate(that.lhs);
        if (that.getTag() == JCTree.DIV || that.getTag() == JCTree.MOD) {
            // This translation puts in a runtime-check for divide by zero.  This test is put
            // in logically in the BasicBlocker - that ought to be moved here eventually  TODO
            if (that.rhs instanceof JCLiteral && ((JCLiteral)that.rhs).value.equals(Integer.valueOf(0))) {
                log.noticeWriter.println("Explicit divide by zero");   // FIXME - proper warning message
                that.rhs = makeZeroCheck(that.pos,that.rhs,inSpecExpression ? Label.UNDEFINED_DIV0 : Label.POSSIBLY_DIV0);
            } else {
                that.rhs = makeZeroCheck(that.pos,that.rhs,inSpecExpression ? Label.UNDEFINED_DIV0 : Label.POSSIBLY_DIV0);
            }
        } else {
            that.rhs = translate(that.rhs);
        }
        result = that;
    }

    // We have to do something special here.  This translator only allows replacing
    // a tree by another tree - so a statement can only be replaced by a single 
    // statement.  Sometimes we want to insert a bunch of statements.  Now we
    // could insert a Block in place of a statement, but if the original statement
    // was a declaration we will have screwed up the visibility of that declaration.
    // So we allow the translation of a statement to return a block, but if the
    // statement was not a block and now is, we insert all of the statement of the
    // new block in line.  If you really wanted a block, then wrap it doubly.
    public void visitBlock(JCBlock tree) {
        List<JCStatement> trees = (tree.stats);
        if (trees == null) return; // FIXME - I would think that we should return result=tree in this case, but that gives an Exception - FIXME
        tree.stats = expandableTranslate(trees);
        
        // Put in any label stuff
        ListBuffer<JCStatement> newlist = new ListBuffer<JCStatement>();
        for (JCStatement s: tree.stats) {
            if (s instanceof JCLabeledStatement) {
                ListBuffer<JCStatement> stats = currentMethodInfo.labelDecls.get(s);
                newlist.appendList(stats);
            }
            newlist.append(s);
        }
        tree.stats = newlist.toList();
        result = tree;
    }

    /** Translates a list of JCStatement ASTs, returning a new list */
    public List<JCStatement> expandableTranslate(List<JCStatement> trees) {
        ListBuffer<JCStatement> newtrees = new ListBuffer<JCStatement>();
        for (List<JCStatement> l = trees; l.nonEmpty(); l = l.tail) {
            JCStatement r = translate(l.head);
            if (!(l.head instanceof JCBlock) && r instanceof JCBlock) {
                newtrees.appendList(((JCBlock)r).stats);
            } else {
                newtrees.append(r);
            }
        }
        return newtrees.toList();
    }

    /** We translate the JML operators into equivalent Java ones */
    @Override
    public void visitJmlBinary(JmlBinary that) {
        // FIXME - need to handle unboxing, casting
        
        // The following call translates the lhs and rhs and possibly produces
        // a new JmlBinary node
        super.visitJmlBinary(that);
        that = (JmlBinary)result;
        switch (that.op) {
            case IMPLIES:
                // P ==> Q is equivalent to !P || Q (short-circuit operator)
                result = treeutils.makeOr(that.pos,treeutils.makeUnary(that.lhs.pos,JCTree.NOT,that.lhs),that.rhs);
                result = translate(result);  // Handles definedness issues
                break;
            case REVERSE_IMPLIES:
                // P <== Q is equivalent to P || !Q (short-circuit operator)
                result = treeutils.makeOr(that.pos,that.lhs,treeutils.makeUnary(that.rhs.pos,JCTree.NOT,that.rhs));
                result = translate(result);  // Handles definedness issues
                break;
            case EQUIVALENCE:
                // P <==> Q is equivalent to P == Q  - but we need a boolean ==
                result = treeutils.makeBinary(that.pos,JCTree.EQ,booleqSymbol,that.lhs,that.rhs);
                result = translate(result);
                break;
            case INEQUIVALENCE:
                // P <=!=> Q is equivalent to P != Q  - but we need a boolean !=
                result = treeutils.makeBinary(that.pos,JCTree.EQ,boolneSymbol,that.lhs,that.rhs);
                result = translate(result);
                break;
            case SUBTYPE_OF:
            case JSUBTYPE_OF:
                // TODO - review this
                if (that.lhs.type.equals(JmlTypes.instance(context).TYPE)) {
                    // \TYPE <: \TYPE
                    JCExpression c = methodCallUtilsExpression("isSubTypeOf",that.lhs,that.rhs);
                    c.setType(syms.booleanType);
                    result = c;
                } else {
                    // Class <: Class - in case type checking allows it
                    Name n = names.fromString("isAssignableFrom");
                    Scope.Entry e = that.rhs.type.tsym.members().lookup(n);
                    Symbol ms = e.sym;
                    JCFieldAccess m = factory.Select(that.rhs,n);
                    m.sym = ms;
                    m.type = m.sym.type;
    
                    JCExpression c = factory.Apply(null,m,List.<JCExpression>of(that.lhs));
                    c.setType(syms.booleanType);
                    result = c;
                }
                // FIXME - do we intend that <: is always false among pairs of primitive types (even the same)
                break;
                
            default:
                // FIXME - what about the lock comparison operators
                log.error(that.pos(),"jml.unknown.operator",that.op.internedName(),"JmlRac");
                result = that;
                break;
            
        }
    }

    @Override 
    public void visitSelect(JCFieldAccess that) {
        result = that;
        if (that.name == null) {
            // wildcard access
            // still need to determine whether static or not
            return; // FIXME
        }
        if (that.sym.isStatic()) {
            super.visitSelect(that);
            return;
        }
        //        if (that.selected instanceof JCIdent) {
        //            if (((JCIdent)that.selected).sym instanceof ClassSymbol) {
        //                log.noticeWriter.println("CLASS");
        //                return;
        //            }
        //            if (((JCIdent)that.selected).sym instanceof PackageSymbol) {
        //                log.noticeWriter.println("PACKAGE-1");
        //                return;
        //            }
        //        }
        if (that.selected instanceof JCFieldAccess && ((JCFieldAccess)that.selected).sym instanceof PackageSymbol) {
            // The lhs is a package
            super.visitSelect(that);
            return;
        }
        if (that.selected instanceof JCIdent && ((JCIdent)that.selected).sym instanceof PackageSymbol) {
            // The lhs is a package
            super.visitSelect(that);
            return;
        }
        
        // FIXME - int.class?
        //        if (that.selected instanceof JCPrimitiveTypeTree) {
        //            log.noticeWriter.println("PRIM TYPE");
        //            return;
        //        }

        // This is a field-access operation in which the lhs is an object.
        // We need to check that
        //   - the lhs is non-null
        //   - the lhs is readable
        //   - if the rhs is a model field, we have to convert this to a method call

        that.selected = makeNullCheck(that.pos,translate(that.selected),NULL_SELECTION,
                inSpecExpression ? Label.UNDEFINED_NULL_DEREFERENCE : Label.POSSIBLY_NULL_DEREFERENCE);
        
        // FIXME - still need a readability check
        
        // FIXME - review the following
        result = that;
        if (that.sym != null && that.sym.kind == Kinds.VAR && attr.isModel(that.sym)) {
            Name name = names.fromString(Strings.modelFieldMethodPrefix + that.name);
            ClassSymbol sym = currentClassInfo.decl.sym;
            Scope.Entry e = sym.members().lookup(name);
            while (e.sym == null) {  // FIXME - do we need to look in interfaces?
                Type t = sym.getSuperclass();
                if (t == null) break;
                sym = (ClassSymbol)t.tsym;
                e = sym.members().lookup(name);
            }
            if (e.sym instanceof MethodSymbol) {
                MethodSymbol ms = (MethodSymbol)e.sym;
                JCFieldAccess m = factory.Select(translate(that.selected),name);
                m.sym = ms;
                m.type = m.sym.type;
                JCExpression c = factory.Apply(null,m,List.<JCExpression>nil());
                c.setType(that.type);
                result = c;
                return;
            } else {
                log.noticeWriter.println("COULD NOT FIND METHOD FOR MODEL FIELD " + that.sym);
                // FIXME - problem?
            }
        }
    }

    @Override
    public void visitVarDef(JCVariableDecl that) {
        // The super call translates everything
        try {
            super.visitVarDef(that);
        } catch (JmlRacNotImplemented ex) {
            notImplemented(ex.pos,"Variable declaration containing " + ex.location + " expression");
            // Presuming it is just the initializer - attempt to carry on
            // But the compiler checked for initialization, so we have to initialize the variable to something
            result = that;
            Type t = that.init.type;
            if (that.init.type.tag < TypeTags.VOID) {
                that.init = JmlTree.Maker.instance(context).Literal(that.init.type.tag,0);
                that.init.type = t;
            } else {
                that.init = JmlTree.Maker.instance(context).Literal(TypeTags.BOT,null);
                that.init.type = Symtab.instance(context).botType;
            }
        }

        that = (JCVariableDecl)result;
        
        // Put in a check for initializing a non-null variable with a null value
        if (that.init != null && that.init.type != null && !that.init.type.isPrimitive() && specs.isNonNull(that.sym,that.sym.enclClass())) {
            // FIXME _ fix this back at the declaration of $$values$...
            if (!that.getName().toString().startsWith("$$values$")) 
                that.init = makeNullCheck(that.pos,that.init,NULL_INITIALIZATION + " " + that.getName(),
                        Label.POSSIBLY_NULL_INITIALIZATION);
        }
        result = that;
    }

    // FIXME - check this
    @Override
    public void visitClassDef(JCClassDecl that) {
        JCClassDecl tree = that;
        ClassInfo prevClassInfo = currentClassInfo;
        if (tree.sym == null) return;
        pushSource(that.sym.sourcefile);
        try {
            //super.visitClassDef(that);
            result = tree;
            if (tree.sym.className().startsWith("org.jmlspecs")) return;  // FIXME - don't instrument runtime files (can get infinite loops)
            if (utils.isInstrumented(tree.mods.flags)) {
                // The file is already instrumented.
                // This can happen if desugarLater is called on a file, so that it
                // is put back on the todo list.  If we are in the mode of BY_FILE
                // in JavaCompiler, that means that it is run through the 
                // attribute/flow/desugar sequence again.  Thus we need to check
                // for and skip this case.
                return;
            }
    
            if ((tree.sym.flags() & Flags.INTERFACE) != 0) {
                // FIXME - what rewriting for an interface?
                result = tree;
                return;
            }
    
            Utils.instance(context).setInstrumented(tree.mods);
        
            currentClassInfo = new ClassInfo(tree);
            JmlSpecs.TypeSpecs typeSpecs = currentClassInfo.typeSpecs = specs.get(tree.sym);
            if (typeSpecs == null) {
                // FIXME - better error message
                log.noticeWriter.println("UNEXPECTEDLY NULL TYPESPECS");
                return;
            }
    
            JCMethodDecl invariantDecl = currentClassInfo.invariantDecl = typeSpecs.checkInvariantDecl;
            JCMethodDecl staticinvariantDecl = currentClassInfo.staticinvariantDecl = typeSpecs.checkStaticInvariantDecl;
    
            // For RAC, we need to add specification stuff as real Java members:
            //  ghost fields, model methods, model classes - normal Java members
            //    subject to the same additional processing as Java members
            //  model fields - get converted to methods - the content of the body
            //    comes from a represents clause; if no represents clause, then the
            //    body throws a non-implemented exception
            //  invariants - are made part of a checkInvariants or staticCheckInvariants method
            //  constraints - made part of method postconditions
            //  axioms - ignored
            //  initially - made part of constructor postconditions
            //  readable, writable, field annotations, monitors-for - checked when
            //    fields are read and written, so ignored here
            //  initializer spec - converted to a trailing Java initializer
            //    block that checks the given specs
            //  static_initializer spec - converted to a trailing static Java initializer
            //    block that checks the given specs; also must set the isInitialized flag
    
            ListBuffer<JCTree> newlist = new ListBuffer<JCTree>();
    
            // Add in all Java declarations
            newlist.appendList(tree.defs);
    
            // Divide up the various type specification clauses into the various types
            ListBuffer<JmlTypeClauseExpr> invariants = new ListBuffer<JmlTypeClauseExpr>();
            ListBuffer<JmlTypeClauseRepresents> represents = new ListBuffer<JmlTypeClauseRepresents>();
            ListBuffer<JCVariableDecl> modelFields = new ListBuffer<JCVariableDecl>();
            for (JmlTypeClause c: typeSpecs.clauses) {
                if (c instanceof JmlTypeClauseDecl) {
                    JCTree t = ((JmlTypeClauseDecl)c).decl;
                    if (t instanceof JCVariableDecl && attr.isModel(((JCVariableDecl)t).mods)) {
                        // model field - find represents or make into abstract method
                        modelFields.append((JCVariableDecl)t);
                    } else {
                        // ghost fields, model methods, model classes are used as is
                        newlist.append(t);
                    }
                } else {
                    JmlToken token = c.token;
                    if (token == JmlToken.INVARIANT) {
                        invariants.append((JmlTypeClauseExpr)c);
                    } else if (token == JmlToken.REPRESENTS) {
                        JmlTypeClauseRepresents r = (JmlTypeClauseRepresents)c;
                        if (r.suchThat) notImplemented(r.pos(),"relational represents clauses (\\such_that)");
                        else represents.append(r);
                    } else if (token == JmlToken.CONSTRAINT) {
                        currentClassInfo.constraints.append((JmlTypeClauseConstraint)c);
                    } else if (token == JmlToken.INITIALLY) {
                        try {
                            ((JmlTypeClauseExpr)c).expression = translate(((JmlTypeClauseExpr)c).expression);
                            currentClassInfo.translatedInitiallys.append((JmlTypeClauseExpr)c);
                        } catch (JmlRacNotImplemented ex) {
                            notImplemented(ex.pos,c.token.internedName() + " clause containing " + ex.location + " expression");
                        }
                    } else {
                        notImplemented(c.pos(),token.internedName());
                        // We ignore axioms
                    }
                }
            }
    
            for (JmlTypeClauseRepresents r : represents) {
                JCExpression e = r.ident;
                Symbol sym = null;
                if (e instanceof JCIdent) sym = ((JCIdent)e).sym;
                else if (e instanceof JCFieldAccess) sym = ((JCFieldAccess)e).sym;
                else {
                	// FIXME - on what occasions would it be a field access?
                    log.warning(r.pos(),"jml.internal.notsobad",
                            "The lhs of a represents clause is expected to be an identifier or field access (found "+e.getClass()+")");
                }
                if (sym != null) {
                    // Construct a method that implements the represents clause
                    Name name = names.fromString(Strings.modelFieldMethodPrefix + sym.name);
                    JmlMethodDecl mdecl = null;
                    // Check if we already have a method for this model field
                    for (JmlTypeClauseDecl m: typeSpecs.modelFieldMethods) {
                        mdecl = (JmlMethodDecl)m.decl;
                        if (! mdecl.name.equals(name)) continue;
                        try {
                            JCReturn st = factory.Return(translate(r.expression));
                            // We have a match
                            if (mdecl.body.stats.isEmpty()) {
                                // But no body yet
                                mdecl.body.stats = List.<JCStatement>of(st);
                            } else {
                                log.warning(r.pos,"jml.duplicate.represents");
                            }
                        } catch (JmlRacNotImplemented ee) {
                            // Can't implement this represents clause because
                            // of some non-translatable expression within it
                            notImplemented(r.pos(),"represents clause containing " + ee.location + " expression");
                        }
                        break;
                    }
                    if (mdecl == null) {
                        // We can get here if there is no model field at all, but then
                        // there would have been an error on resolving the target of
                        // the represents clause.  The usual route to this code is
                        // when a subclass has a represents clause for a super class's
                        // model field.
    
                        long flags = Flags.PUBLIC | Flags.SYNTHETIC;
                        flags |= (r.modifiers.flags & Flags.STATIC);
                        JCModifiers mods = factory.Modifiers(flags);
                        JCMethodDecl msdecl = treeutils.makeMethodDefNoArg(mods,name,r.ident.type,tree.sym);
                        try {
                            JCReturn st = factory.Return(translate(r.expression));
                            msdecl.body.stats = List.<JCStatement>of(st);
                        } catch (JmlRacNotImplemented ee) {
                            // Can't implement this represents clause because
                            // of some non-translatable expression within it
                            notImplemented(r.pos(),"represents clause containing " + ee.location + " expression");
                        }
                        newlist.append(msdecl);
                        JmlTypeClauseDecl tcd = factory.JmlTypeClauseDecl(msdecl);
                        tcd.modifiers = msdecl.mods;
                        typeSpecs.modelFieldMethods.append(tcd);
                    }
                }
            }
            // Now check for model field methods that have no body - because
            // there were no represents clauses for them
            for (JmlTypeClauseDecl m: typeSpecs.modelFieldMethods) {
                JmlMethodDecl mdecl = (JmlMethodDecl)m.decl;
                if (mdecl.body.stats.isEmpty()) {
                    //log.noticeWriter.println("NO IMPLEMENTATION " + mdecl.name);
                    String position = position(m.source,m.pos);
                    String s = mdecl.name.toString();
                    int p = s.lastIndexOf('$');
                    JCStatement st = assertFailure(position + "model field is not implemented: " + s.substring(p+1),m.pos);
                    JCStatement stt = factory.Return(treeutils.makeZeroEquivalentLit(m.pos,mdecl.getReturnType().type));
                    mdecl.body.stats = List.<JCStatement>of(st,stt);
                }
            }
    
            // Now we translate everything in the new class body
            // FIXME - we are retranslating the model field methods
            tree.defs = newlist.toList();
            super.visitClassDef(tree);  // FIXME - check that this does not translate type clauses
            if (env.tree == tree) env.tree = result;
    
    
            // We insert checks for the invariants into the bodies of the
            // previously created (in JmlMemberEnter) methods for that purpose
    
            ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
            ListBuffer<JCStatement> staticstats = new ListBuffer<JCStatement>();
            {
                // FIXME - put in super type calls
                ClassSymbol currentClass = tree.sym;
                Type superType = currentClass.getSuperclass(); 
                if (superType != null && superType.tsym instanceof ClassSymbol) {
                    String supername = ((ClassSymbol)superType.tsym).flatName().toString();
                    stats.append(methodCallCheckInvariant((JmlClassDecl)tree,tree.sym,supername));
                    staticstats.append(methodCallCheckStaticInvariant(supername));
                }
            }
            for (JmlTypeClause inv: invariants) {
                try {
                    JCExpression e = translate(((JmlTypeClauseExpr)inv).expression);
                    String position = position(inv.source(),inv.pos);
                    if ((inv.modifiers.flags & Flags.STATIC) != 0) {
                        JCStatement s = undefinedCheck(staticinvariantDecl.sym,
                                position+"static invariant",
                                factory.If(treeutils.makeUnary(inv.pos,JCTree.NOT,e),assertFailure(position+"static invariant is false",inv.pos),null));
                        staticstats.append(s);
                    } else {
                        JCStatement s = undefinedCheck(invariantDecl.sym,
                                position+"invariant",
                                factory.If(treeutils.makeUnary(inv.pos,JCTree.NOT,e),assertFailure(position+"invariant is false",inv.pos),null));
                        stats.append(s);
                    }
                } catch (JmlRacNotImplemented ex) {
                    notImplemented(inv.pos(),inv.token.internedName() + " clause containing " + ex.location + " expression");
                }
            }
    
            invariantDecl.body = factory.Block(0,stats.toList());
            staticinvariantDecl.body = factory.Block(0,staticstats.toList());
            tree.defs = newlist.toList();
            result = tree;
        } finally {
            currentClassInfo = prevClassInfo;
            popSource();
        }
    }

    // FIXME - check this - does it fit with visitClassDef?
    public void visitJmlClassDecl(JmlClassDecl that) {
//        // FIXME - do we do nothing with interfaces ?? At least translate the invariants etc.???
//        if ((that.sym.flags() & Flags.INTERFACE) != 0) {
//            result = that;
//            return;
//        }
//    
////        JCClassDecl prev = currentClassDecl;
////      currentClassDecl = that;
//        boolean prevSpecExpression = inSpecExpression;
//        pushSource(that.sym.sourcefile);
//        try {
    
            visitClassDef(that);
//            // Copy in the super class code (MAINTENANCE) since we need to skip
//            // the JML constructs in the body and instead process the consolidated
//            // collection in that.typespecs
//            that.mods = translate(that.mods);
//            that.typarams = translateTypeParams(that.typarams);
//            that.extending = translate(that.extending);
//            that.implementing = translate(that.implementing);
//            //that.defs = translate(that.defs); // Inlined below to exclude obsolete JML nodes
//            ListBuffer<JCTree> newlist = new ListBuffer<JCTree>();
//            for (JCTree t: that.defs) {
//                //            if (t == null) {log.noticeWriter.println("NULL ELEMENT IN DEFS OF CLASS " + that.name); continue; } // FIXME - this happes during JUnit tests
//                if (t != null && !(t instanceof JmlTypeClause)) {
//                    newlist.append(translate(t));
//                }
//            }
//    
//            inSpecExpression = true;
//            JmlSpecs.TypeSpecs tspecs = that.typeSpecsCombined;
//            if (true) {
//                if (tspecs != null) {
//                    ListBuffer<JmlTypeClause> nlist = new ListBuffer<JmlTypeClause>();
//                    for (JmlTypeClause d : tspecs.clauses) {
//                        if (d instanceof JmlTypeClauseDecl) {
//                            JCTree v = ((JmlTypeClauseDecl)d).decl;
//                            if (v instanceof JCVariableDecl) {
//                                JCVariableDecl vv = (JCVariableDecl)translate(v);
//                                newlist.append(vv);
//                            } else {
//                                nlist.append(translate(d));
//                            }
//                        } else {
//                            nlist.append(translate(d));
//                        }
//                    }
//                    tspecs.clauses = nlist;
//                }
//            }
//            that.defs = newlist.toList();
    
//        } finally {
//            result = that;
////            currentClassDecl = prev;
//            inSpecExpression = prevSpecExpression;
//            popSource();
//        }
    }

    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        System.out.println("CANT DO THIS"); // FIXME - better error
    }

    // FIXME - check this
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        if (that.loopSpecs == null || that.loopSpecs.isEmpty()) {
            super.visitDoLoop(that);
            return;
        }
        ListBuffer<JCStatement> checks = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> vars = new ListBuffer<JCStatement>();
        makeLoopChecks(that.loopSpecs,checks,vars);
        
        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
        stats.appendList(checks);
        stats.append(that.body);
        that.body = factory.Block(0,stats.toList());
        vars.append(that);
        vars.appendList(checks);
        result = factory.Block(0,vars.toList());
        //log.noticeWriter.println("REWRITTEN " + result);
    }

    // FIXME - check this
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        if (that.loopSpecs == null || that.loopSpecs.isEmpty()) {
            super.visitForeachLoop(that);
            return;
        }
        ListBuffer<JCStatement> checks = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> vars = new ListBuffer<JCStatement>();
        makeLoopChecks(that.loopSpecs,checks,vars);
        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
        stats.appendList(vars);
        ListBuffer<JCStatement> bodystats = new ListBuffer<JCStatement>();
        bodystats.appendList(checks);
        bodystats.append(translate(that.body));
        JCEnhancedForLoop loop = factory.ForeachLoop(translate(that.var), translate(that.expr), factory.Block(0,bodystats.toList()));
        stats.append(loop);
        stats.appendList(checks);
        result = factory.Block(0,stats.toList());
    }

    // FIXME - check this
    public void visitJmlForLoop(JmlForLoop that) {
        if (that.loopSpecs == null || that.loopSpecs.isEmpty()) {
            super.visitForLoop(that);
            return;
        }
        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
        stats.appendList(translate(that.init));
        ListBuffer<JCStatement> checks = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> vars = new ListBuffer<JCStatement>();
        makeLoopChecks(that.loopSpecs,checks,vars);
        stats.appendList(vars);
        ListBuffer<JCStatement> bodystats = new ListBuffer<JCStatement>();
        bodystats.appendList(checks);
        bodystats.append(translate(that.body));
        stats.append(factory.ForLoop(List.<JCStatement>nil(),translate(that.cond),translate(that.step),factory.Block(0,bodystats.toList())));
        stats.appendList(checks);
        result = factory.Block(0,stats.toList());
    }

    // FIXME - mark which of the type clauses are not implemented
    
    public void visitJmlGroupName(JmlGroupName that) {
        // source and position ?   FIXME
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlGroupName");
    }

    public void visitJmlImport(JmlImport that) {
        result = that; // Nothing else to do
    }

    public void visitJmlLblExpression(JmlLblExpression that) {
        JCExpression lit = treeutils.makeStringLiteral(that.pos,that.label.toString());
        JCFieldAccess m = null;
        int tag = that.expression.type.tag;
        switch (tag) {
            case TypeTags.INT:
                m = findUtilsMethod("reportInt");
                break;
            case TypeTags.BOOLEAN:
                m = findUtilsMethod("reportBoolean");
                break;
            case TypeTags.CLASS:
            case TypeTags.ARRAY:
                m = findUtilsMethod("reportObject");
                break;
            case TypeTags.LONG:
                m = findUtilsMethod("reportLong");
                break;
            case TypeTags.SHORT:
                m = findUtilsMethod("reportShort");
                break;
            case TypeTags.CHAR:
                m = findUtilsMethod("reportChar");
                break;
            case TypeTags.BYTE:
                m = findUtilsMethod("reportByte");
                break;
            case TypeTags.FLOAT:
                m = findUtilsMethod("reportFloat");
                break;
            case TypeTags.DOUBLE:
                m = findUtilsMethod("reportDouble");
                break;
            default:
                // Silently ignores
                result = translate(that.expression);
                return;
        }
        JCExpression c = factory.Apply(null,m,List.<JCExpression>of(lit,translate(that.expression)));
        c.pos = that.pos;
        c.setType(that.type.baseType());
        result = c;
    }

    //    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
    //        // TODO Auto-generated method stub
    //        
    //    }
    //
    //    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
    //        // TODO Auto-generated method stub
    //        
    //    }
    //
    //    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
    //        // TODO Auto-generated method stub
    //        
    //    }
    //
    //    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
    //        // TODO Auto-generated method stub
    //        
    //    }
    //
    //    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
    //        // TODO Auto-generated method stub
    //        
    //    }
    //
    //    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
    //        // TODO Auto-generated method stub
    //        
    //    }
    //
    //    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
    //        // TODO Auto-generated method stub
    //        
    //    }
    //
    //    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
    //        // TODO Auto-generated method stub
    //        
    //    }
    //
    //    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
    //        // TODO Auto-generated method stub
    //        
    //    }
    //
    //    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
    //        // FIXME - implement
    //        
    //    }
    //

    // FIXME - check this
    public void visitJmlMethodInvocation(JmlMethodInvocation tree) {
        JmlToken token = tree.token;
        JCExpression arg;
        if (token == null) {
            visitApply(tree);
            return;
        }
        switch (token) {
            case BSPAST:
            case BSOLD:
            case BSPRE:
                arg = translate(tree.args.get(0));
                int n = currentMethodInfo.olds.size();
                String s = "_JML$$$old_" + n;
                Name nm = names.fromString(s);
                JCVariableDecl v = treeutils.makeVarDef(arg.type,nm,currentMethodInfo.owner,arg);
                if (tree.args.size() > 1) {
                    JCExpression init = v.init;
                    v.init = treeutils.makeZeroEquivalentLit(tree.pos,tree.type);
                    factory.at(tree.pos);
                    JCIdent var = factory.Ident(v.sym);
                    JCExpressionStatement stat = factory.Exec(factory.Assign(var,init));
                    stat.expr.type = var.type;
                    JCIdent id = (JCIdent)tree.args.get(1);
                    JCLabeledStatement statement = currentMethodInfo.labels.get(id.name);
                    currentMethodInfo.labelDecls.get(statement).append(stat);
                }
                currentMethodInfo.olds.append(v);
                JCIdent r = factory.Ident(nm);
                r.sym = v.sym;
                r.type = v.sym.type;
                result = r;
                break;
    
            case BSTYPEOF:
                translateTypeOf(tree);
                break;
    
            case BSNONNULLELEMENTS :
                translateNonnullelements(tree);
                break;
    
            case BSTYPELC:
                translateTypelc(tree);
                break;
            
            case BSELEMTYPE:
                translateElemtype(tree);
                break;
                
            case BSMAX:
            case BSNOTMODIFIED:
            case BSNOTASSIGNED :
            case BSONLYASSIGNED :
            case BSONLYACCESSED :
            case BSONLYCAPTURED :
            case BSISINITIALIZED :
            case BSFRESH:
            case BSREACH:
            case BSINVARIANTFOR :
            case BSDISTINCT :
            case BSDURATION :
            case BSWORKINGSPACE :
    
            case BSSPACE:
            case BSNOWARN:
            case BSNOWARNOP:
            case BSWARN:
            case BSWARNOP:
            case BSBIGINT_MATH:
            case BSSAFEMATH:
            case BSJAVAMATH:
            case BSONLYCALLED:
                throw new JmlRacNotImplemented(tree.pos(),token.internedName());
//                utils.notImplemented(tree.pos(),token.internedName());
//                Log.instance(context).error(tree.pos, "jml.unimplemented.construct",token.internedName(),"JmlRac.visitApply");
//                // FIXME - recovery possible?
//                result = tree;
//                break;
    
            default:
                Log.instance(context).error(tree.pos, "jml.unknown.construct",token.internedName(),"JmlRac.visitApply");
            // FIXME - recovery possible?
                result = tree; // FIXME null?
                break;
        }
        return;
    }
    
    @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        if (that.racexpr != null) {
            that.racexpr.accept(this);
            // result is set
        } else {
            throw new JmlRacNotImplemented(that.pos,that.pos,"JML quantifier");
        }
    }



    // FIXME - check this
    @Override
    public void visitJmlSingleton(JmlSingleton that) {
        result = that;
        switch (that.token) {
            case BSRESULT:
                JCIdent id = factory.Ident(attr.resultName); // FIXME Why is this in attr?
                id.sym = currentMethodInfo.resultDecl.sym;
                id.type = currentMethodInfo.resultDecl.type;
                result = id;
                break;
    
            case INFORMAL_COMMENT:
                result = trueLit;
                break;
                
            case BSINDEX:
            case BSVALUES:
                result = that; // FIXME ???
                break;
                
            case BSLOCKSET:
            case BSSAME:
            case BSNOTSPECIFIED:
            case BSNOTHING:
            case BSEVERYTHING:
                Log.instance(context).error(that.pos, "jml.unimplemented.construct",that.token.internedName(),"JmlRac.visitJmlSingleton");
                // FIXME - recovery possible?
                break;
    
            default:
                JavaFileObject prev = log.useSource(source);
                log.error(that.pos,"jml.unknown.type.token",that.token.internedName(),"JmlAttr.visitJmlSingleton");
                log.useSource(prev);
                result = that;
                break;
        }
    }

    public void translateNonnullelements(JCMethodInvocation tree) {
        int n = tree.args.size();
        if (n == 0) {
            result = trueLit;
        } else {
            JCExpression arg = translate(tree.args.get(0));
            JCExpression e = methodCallUtilsExpression("nonnullElementCheck",arg);
            JCExpression r = e;
            for (int i = 1; i<tree.args.size(); i++) {
                arg = translate(tree.args.get(i));
                e = methodCallUtilsExpression("nonnullElementCheck",arg);
                r = treeutils.makeBinary(e.pos,JCTree.AND,r,e);
            }
            result = r;
        }
    }

//    // FIXME - This is not correct for generic types
//    public void translateTypelc(JCMethodInvocation tree) {
//        // Argument is a type, not an expression, so we
//        // replace it with a type literal
//        JCExpression arg = tree.args.get(0);
//        JCTree.JCFieldAccess f = factory.Select(arg,names._class);
//        f.type = syms.classType;
//        f.sym = f.type.tsym;
//        result = methodCallUtilsExpression("makeTYPE0",translate(f));
//    }

    // FIXME - check this is OK for rac
    public void translateTypelc(JmlMethodInvocation that) {
        // Presumes this is indeed a \type invocation and
        // that the one argument is a Type
        JCExpression type = that.args.get(0);
        result = treeutils.trType(that.pos, type);
    }


    // FIXME - what about generic types
    // FIXME - what about arrays of arrays
    public void translateTypeOf(JCMethodInvocation tree) {
        JCExpression arg = tree.args.get(0);
        int tag = arg.type.tag;
        switch (tag) {
            case TypeTags.ARRAY:
            case TypeTags.CLASS:
                result = methodCallgetClass(translate(arg));
                break;
            case TypeTags.BOOLEAN:
                result = treeutils.makePrimitiveClassLiteralExpression("java.lang.Boolean");
                break;
            case TypeTags.INT:
                result = treeutils.makePrimitiveClassLiteralExpression("java.lang.Integer");
                break;
            case TypeTags.LONG:
                result = treeutils.makePrimitiveClassLiteralExpression("java.lang.Long");
                break;
            case TypeTags.SHORT:
                result = treeutils.makePrimitiveClassLiteralExpression("java.lang.Short");
                break;
            case TypeTags.BYTE:
                result = treeutils.makePrimitiveClassLiteralExpression("java.lang.Byte");
                break;
            case TypeTags.FLOAT:
                result = treeutils.makePrimitiveClassLiteralExpression("java.lang.Float");
                break;
            case TypeTags.DOUBLE:
                result = treeutils.makePrimitiveClassLiteralExpression("java.lang.Double");
                break;
            case TypeTags.CHAR:
                result = treeutils.makePrimitiveClassLiteralExpression("java.lang.Character");
                break;
            default:
                log.error(arg.pos,"jml.unknown.construct","typeof for " + arg.type,"JmlRac.translateTypeOf");
                // We give it an arbitrary value // FIXME - or do we call it undefined
                result = treeutils.makePrimitiveClassLiteralExpression("java.lang.Boolean");
                break;
        }
        // Make a \TYPE from a Java class literal
        result = methodCallUtilsExpression("makeTYPE0",(JCExpression)result);
    }

    // FIXME - check this
    public void translateElemtype(JCMethodInvocation tree) {
        JCExpression arg = tree.args.head;
        if (tree.type.equals(JmlTypes.instance(context).TYPE)) {
            arg = methodCallUtilsExpression("erasure",arg);
        }
        Name n = names.fromString("getComponentType");
        Scope.Entry e = syms.classType.tsym.members().lookup(n);
        Symbol ms = e.sym;
        JCFieldAccess m = factory.Select(translate(arg),n);
        m.sym = ms;
        m.type = m.sym.type;
    
        JCExpression c = factory.Apply(null,m,List.<JCExpression>nil());
        c.setType(syms.classType);
        result = c;
        if (tree.type.equals(JmlTypes.instance(context).TYPE)) {
            result = methodCallUtilsExpression("makeTYPE0",c);
        }
    }

    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        // FIXME _ is this the case? log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlSpecificationCase");
        pushSource(that.sourcefile);
        try {
            super.visitJmlSpecificationCase(that);
        } finally {
            popSource();
        }
    }

    public void visitJmlStatement(JmlStatement that) {
        boolean prev = inSpecExpression;
        try {
            inSpecExpression = true;
            switch (that.token) {
                case SET:
                case DEBUG: // FIXME - if turned on by options
                    result = translate(that.statement);
                    break;

                case HENCE_BY:
                    result = factory.Skip();
                    notImplemented(that.pos(),"hence_by statement");
                    break;

                default:
                    // FIXME - unimplemented
                    result = that;
            }
        } catch (JmlRacNotImplemented ex) {
            result = factory.at(that.pos).Skip();
            notImplemented(that.pos(),that.token.internedName() + " statement containing " + ex.location + " expression");
        } finally {
            inSpecExpression = prev;
        }
    }

    public void visitJmlStatementDecls(JmlStatementDecls that) {
        // that.list is a list of declarations (local ghost variables
        // or local model classes)
        boolean prev = inSpecExpression;
        try {
            inSpecExpression = true;
            List<JCStatement> list = expandableTranslate(that.list);
            result = factory.at(that.pos).Block(0,list);
        } finally {
            inSpecExpression = prev;
        }
    }

    public void visitJmlStatementExpr(JmlStatementExpr tree) {
        boolean prev = inSpecExpression;
        try {
            inSpecExpression = true;
            int p = tree.pos;
            make_pos = tree;
            factory.at(p);
            switch (tree.token) {
                case ASSERT:
                {
                    if (Nowarns.instance(context).suppress(tree.source, p, tree.label.toString())) break;
                    result = factory.If(
                            translate(tree.expression),
                            factory.at(p).Skip(),
                            methodCall(tree,translate(tree.optionalExpression)));
                    result.pos = tree.pos;
                    break;
                }

                case ASSUME:
                {
                    result = factory.If(
                            translate(tree.expression),
                            factory.at(p).Skip(),
                            methodCall(tree,translate(tree.optionalExpression)));
                    result.pos = tree.pos;
                    break;
                }

                case UNREACHABLE:
                {  
                    result = methodCall(tree,null);
                    break;
                }

                case REACHABLE:
                {  
                    result = factory.at(tree.pos).Skip();
                    break;
                }

                case HENCE_BY:
                    result = factory.at(tree.pos).Skip();
                    notImplemented(tree.pos(),"hence_by statement");
                    break;

                default:
                    // FIXME - unknown
                    result = tree;
                    break;
            }
        } catch (JmlRacNotImplemented ex) {
            result = factory.at(tree.pos).Skip();
            notImplemented(tree.pos(),tree.token.internedName() + " statement containing " + ex.location + " expression");
        } finally {
            inSpecExpression = prev;
        }
    }

    // FIXME - mark which of the type clauses are not implemented
    
    @Override
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        pushSource(that.source);
        try {
            super.visitJmlTypeClauseConditional(that);
        } finally {
            popSource();
        }
    }

    @Override
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        pushSource(that.source);
        try {
            super.visitJmlTypeClauseConstraint(that);
        } finally {
            popSource();
        }
    }

    @Override
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        pushSource(that.source);
        try {
            super.visitJmlTypeClauseDecl(that);
        } finally {
            popSource();
        }
    }

    @Override
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        pushSource(that.source);
        try {
            super.visitJmlTypeClauseExpr(that);
        } finally {
            popSource();
        }
    }

    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        pushSource(that.source);
        try {
            super.visitJmlTypeClauseIn(that);
        } finally {
            popSource();
        }
    }

    @Override
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        pushSource(that.source);
        try {
            super.visitJmlTypeClauseInitializer(that);
        } finally {
            popSource();
        }
    }

    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        pushSource(that.source);
        try {
            super.visitJmlTypeClauseMaps(that);
        } finally {
            popSource();
        }
    }

    @Override
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        pushSource(that.source);
        try {
            super.visitJmlTypeClauseMonitorsFor(that);
        } finally {
            popSource();
        }
    }

    @Override
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        pushSource(that.source);
        try {
            super.visitJmlTypeClauseRepresents(that);
        } finally {
            popSource();
        }
    }

    public void visitJmlVariableDecl(JmlVariableDecl that) {
        boolean prev = inSpecExpression;
        try {
            pushSource(that.sourcefile);
            if (utils.isJML(that.mods)) inSpecExpression = true;
            visitVarDef(that);
            JCTree saved = result;
            inSpecExpression = true;
            if (that.fieldSpecsCombined != null) {
                that.fieldSpecsCombined.list = translate(that.fieldSpecsCombined.list); // FIXME - check why this is sometimes null
            }
            if (that.fieldSpecs != null) {
                that.fieldSpecs.list = translate(that.fieldSpecs.list); // FIXME - check why this is sometimes null
            }
            result = saved;
        } finally {
            inSpecExpression = prev;
            popSource();
        }
    }

    // TODO _ check this
    public void visitJmlWhileLoop(JmlWhileLoop that) {
        if (that.loopSpecs == null || that.loopSpecs.isEmpty()) {
            super.visitWhileLoop(that);
            return;
        }
        ListBuffer<JCStatement> checks = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> vars = new ListBuffer<JCStatement>();
        makeLoopChecks(that.loopSpecs,checks,vars);
        
        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
        stats.appendList(checks);
        stats.append(that.body);
        that.body = factory.Block(0,stats.toList());
        vars.append(that);
        vars.appendList(checks);
        result = factory.Block(0,vars.toList());
        //log.noticeWriter.println("REWRITTEN " + result);
    }

    // TODO _ check this
    public void makeLoopChecks(List<JmlStatementLoop> specs, ListBuffer<JCStatement> checks, ListBuffer<JCStatement> vars) {
        for (JmlStatementLoop s: specs) {
            if (s.token == JmlToken.LOOP_INVARIANT) {
                String sp = position(currentMethodInfo.source,s.pos);
                JCExpression t = translate(s.expression);
                factory.at(s.pos);
                JCStatement ss = undefinedCheck(currentMethodInfo.owner,
                        sp + "loop invariant",
                        factory.If(treeutils.makeUnary(s.pos,JCTree.NOT,translate(t)),
                                assertFailure(sp + "loop invariant is false",s.pos),null));
                checks.append(ss);
            } else if (s.token == JmlToken.DECREASES) {
                int n = ++currentMethodInfo.variableDefs;
                Name name1 = names.fromString("_JML$$$loop"+n);
                Name name2 = names.fromString("_JML$$$loopTemp"+n);
                JCExpression e = translate(s.expression);
                factory.at(s.pos);
                JCVariableDecl d = treeutils.makeIntVarDef(name1,maxIntLit,currentMethodInfo.owner);
                JCIdent id1 = factory.Ident(name1);
                id1.type = d.type;
                id1.sym = d.sym;
                vars.append(d);
                JCVariableDecl dd = treeutils.makeIntVarDef(name2,e,currentMethodInfo.owner);
                JCIdent id2 = factory.Ident(name2);
                id2.type = dd.type;
                id2.sym = dd.sym;
                String sp = position(currentMethodInfo.source,s.pos);
                JCStatement ss = factory.If(
                        treeutils.makeBinary(s.pos,JCTree.GE,id2,id1),
                        assertFailure(sp + "loop variant did not decrease",s.pos),null);
                JCStatement sss = factory.If(
                        treeutils.makeBinary(s.pos,JCTree.LT,id2,zero),
                        assertFailure(sp + "loop variant is less than 0",s.pos),null);
                e = factory.Assign(id1,id2);
                e.type = id1.type;
                JCStatement sa = factory.Exec(e);
                ss = undefinedCheck(currentMethodInfo.owner,sp + "loop variant",
                        List.<JCStatement>of(dd,ss,sss,sa));
                checks.append(ss);
            } else {
                // FIXME - unk nownd
            }
        }
    }

    @Override
    public void visitIdent(JCIdent tree) {
        if (tree.sym != null && tree.sym.kind == Kinds.VAR && attr.isModel(tree.sym)) {
            // A model field is converted to a method call
            Name name = names.fromString(Strings.modelFieldMethodPrefix + tree.name);
            ClassSymbol sym = currentClassInfo.decl.sym;
            Scope.Entry e = sym.members().lookup(name);
            while (e.sym == null) {// FIXME - do we need to look in interfaces?
                Type t = sym.getSuperclass();
                if (t == null) break;
                sym = (ClassSymbol)t.tsym;
                e = sym.members().lookup(name);
            }
            if (e.sym instanceof MethodSymbol) {
                MethodSymbol ms = (MethodSymbol)e.sym;
                JCIdent m = factory.Ident(name);
                m.sym = ms;
                m.type = m.sym.type;
                JCExpression c = factory.Apply(null,m,List.<JCExpression>nil());
                c.setType(tree.type);
                result = c;
                return;
            } else {
                log.noticeWriter.println("COULD NOT FIND METHOD FOR MODEL FIELD " + tree.sym);
                // FIXME - problem?
            }
        }
        if (currentMethodInfo != null && tree.sym == currentMethodInfo.exceptionLocal) {
            result = currentMethodInfo.exceptionDecl;
            return;
        }
        super.visitIdent(tree);
    }
    
    @Override
    public void visitLabelled(JCLabeledStatement tree) {
        super.visitLabelled(tree);
        ListBuffer<JCStatement> list = new ListBuffer<JCStatement>();
        currentMethodInfo.labels.put(tree.label,tree);
        currentMethodInfo.labelDecls.put(tree,list);
        result = tree;
    }


    @Override
    public void visitMethodDef(JCMethodDecl tree) {
        JmlMethodSpecs methodSpecs = null;
        JavaFileObject source = ((JmlMethodDecl)tree).sourcefile;
        JCMethodDecl prev = currentMethodDecl;
        currentMethodDecl = tree;
        MethodInfo prevMethodInfo = currentMethodInfo;
        currentMethodInfo = null;
        

        try {
            pushSource(source);
            ListBuffer<JCStatement> newbody = new ListBuffer<JCStatement>();
            
            // FIXME - why might tree.sym be null - aren't things attributed? but annotations have null symbol, constructors?
            boolean doRac = tree.sym != null && ((methodSpecs=specs.getDenestedSpecs(tree.sym)) != null || currentClassInfo.invariantDecl != null || currentClassInfo.staticinvariantDecl != null);
            doRac = doRac && ((tree.mods.flags & (Flags.SYNTHETIC|Flags.ABSTRACT|Flags.NATIVE)) == 0);
            boolean isConstructor = tree.restype == null;
            if (currentClassInfo.decl.sym == syms.objectType.tsym && isConstructor) doRac = false;

            if (doRac) {
                currentMethodInfo = new MethodInfo(tree);
                JCExpression resultType = tree.restype;
                if (!isConstructor && resultType.type.tag != TypeTags.VOID)
                    currentMethodInfo.resultDecl = treeutils.makeVarDefZeroInit(resultType,resultName,tree.sym);
                //currentMethodInfo.exceptionDecl = treeutils.makeVarDef(resultType,exceptionName,tree.sym);
            }

            super.visitMethodDef(tree);
            tree = (JCMethodDecl)result;

            if (doRac) {
                boolean isHelper = isHelper(tree.sym);
                
                // generate tests for preconditions
                if (methodSpecs != null && !isConstructor) {

                    JCExpression pre = methodSpecs.cases.size() == 0 ? trueLit : falseLit;
                    int num = 0;
                    String position = null;
                    ListBuffer<JCStatement> preconditionEvaluations = new ListBuffer<JCStatement>();
                    for (JmlSpecificationCase spc: methodSpecs.cases) {
                        pushSource(spc.sourcefile);
                        JCExpression spre = trueLit;
                        for (JmlMethodClause c: spc.clauses) {
                            if (c.token == JmlToken.REQUIRES) {
                                try {
                                    spre = treeutils.makeAnd(c.pos,spre,translate(((JmlMethodClauseExpr)c).expression));
                                    position = position(spc.sourcefile,c.pos);
                                    num++;
                                } catch (JmlRacNotImplemented ex) {
                                    notImplemented(c.pos(),c.token.internedName() + " clause containing " + ex.location + " expression");
                                }
                            }
                        }
                        popSource();
                        Name preName = names.fromString("_JML$$$PRE"+spc.hashCode());
                        JCVariableDecl vd = treeutils.makeVarDef(syms.booleanType,preName,currentMethodInfo.decl.sym,falseLit);
                        vd.pos = spc.pos;
                        currentMethodInfo.preconditionDecls.put(spc,vd);
                        newbody.append(vd);
                        spre = factory.Assign(treeutils.makeIdent(spc.pos,vd.sym),spre);
                        spre.type = vd.sym.type;
                        spre.pos = spc.pos;
                        JCExpressionStatement ex = factory.at(spre.pos).Exec(spre);
                        preconditionEvaluations.append(ex);
                        pre = treeutils.makeBitOr(pre.pos,pre,treeutils.makeIdent(spc.pos,vd.sym));
                    }
                    if (num > 1) position = position(source,tree.pos);
                    if (pre != trueLit  &&
                            !Nowarns.instance(context).suppress(source, tree.pos , Label.PRECONDITION.toString())) {
                        JCIf ifstat = factory.If(treeutils.makeUnary(pre.pos,JCTree.NOT,pre),methodCallPre(position,pre),null);
                        ifstat.pos = pre.pos;
                        preconditionEvaluations.append(ifstat);
                        currentMethodInfo.preCheck = undefinedCheck(currentMethodInfo.owner,
                                position+"precondition",
                                factory.at(pre.pos).Block(0,preconditionEvaluations.toList()));
                    }
                }

                Name n = names.fromString("_JML$$$signalsException");
                JCVariableDecl signalsEx = treeutils.makeVarDefZeroInit(factory.QualIdent(syms.exceptionType.tsym),n,tree.sym);  // FIXME - needs position

                // Generate tests for postconditions
                ListBuffer<JCStatement> postChecks = new ListBuffer<JCStatement>();
                if (methodSpecs != null) {
                    for (JmlSpecificationCase spc: methodSpecs.cases) {
                        //JCExpression spre = trueLit;
                        JCVariableDecl vd = currentMethodInfo.preconditionDecls.get(spc);
                        JCExpression spre = vd == null ? trueLit : treeutils.makeIdent(spc.pos,vd.sym);
//                        Name preName = names.fromString("_JML$$$PRE"+spc.hashCode());
//                        for (JmlMethodClause c: spc.clauses) {  // Note - do not translate the preconditions over again - they were translated in place
//                            // FIXME - we are not skipping the unimplemented ones
//                            if (c.token == JmlToken.REQUIRES) spre = treeutils.makeBinary(c.pos,JCTree.AND,spre,(((JmlMethodClauseExpr)c).expression));
//                        }
                        for (JmlMethodClause c: spc.clauses) {
                            if (c.token == JmlToken.ENSURES &&
                                    !Nowarns.instance(context).suppress(source, c.pos, Label.POSTCONDITION.toString())) {
                                try {
                                    factory.at(c.pos);
                                    JCExpression post = treeutils.makeBinary(c.pos,JCTree.AND,spre,treeutils.makeUnary(c.pos,JCTree.NOT,translate(((JmlMethodClauseExpr)c).expression)));
                                    String sp = position(spc.sourcefile,c.pos);
                                    JCStatement st = undefinedCheck(currentMethodInfo.owner,
                                            sp+"postcondition",
                                            factory.If(post,methodCallPost(sp,post),null));
                                    postChecks.append(st);
                                } catch (JmlRacNotImplemented ex) {
                                    notImplemented(c.pos(),c.token.internedName() + " clause containing " + ex.location + " expression");
                                }
                                
                            }
                        }
                    }
                }

                // Generate tests for exceptional postconditions and signals_only clauses
                ListBuffer<JCStatement> signalsChecks = new ListBuffer<JCStatement>();
                if (methodSpecs != null) {
                    for (JmlSpecificationCase spc: methodSpecs.cases) {
                        JCVariableDecl vd = currentMethodInfo.preconditionDecls.get(spc);
                        JCExpression spre = vd == null ? trueLit : treeutils.makeIdent(spc.pos,vd.sym);
//                        JCExpression spre = trueLit;
//                        for (JmlMethodClause c: spc.clauses) {  // Note - do not translate the preconditions over again - they were translated in place
//                            // FIXME - we are not skipping the unimplemented ones
//                            if (c.token == JmlToken.REQUIRES) spre = treeutils.makeBinary(c.pos,JCTree.AND,spre,(((JmlMethodClauseExpr)c).expression));
//                        }
                        boolean hasSignalsOnly = false;
                        for (JmlMethodClause c: spc.clauses) {
                            factory.at(c.pos);
                            if (c.token == JmlToken.SIGNALS) {
                                JmlMethodClauseSignals sig = (JmlMethodClauseSignals)c;
                                JCIdent id = treeutils.makeIdent(c.pos,signalsEx.sym);
                                JCExpression test = null; 
                                if (sig.vardef == null) {
                                    // If there is no vardef, there cannot be uses of the local variable to replace
                                    test = factory.TypeTest(id,factory.Type(syms.exceptionType));
                                    test.type = syms.booleanType;
                                    currentMethodInfo.exceptionDecl = null;
                                    currentMethodInfo.exceptionLocal = null;
                                } else {
                                    // During the walking of the tree, instances of exceptionLocal are replaced by the JCExpression exceptionDecl
                                    test = factory.TypeTest(id,sig.vardef.getType());
                                    test.type = syms.booleanType;
                                    currentMethodInfo.exceptionDecl = factory.TypeCast(sig.vardef.vartype,id).setType(sig.vardef.vartype.type);
                                    currentMethodInfo.exceptionLocal = sig.vardef.sym;
                                }
                                try {
                                    JCExpression post = treeutils.makeAnd(sig.expression.pos,spre,treeutils.makeAnd(sig.expression.pos,test,treeutils.makeUnary(sig.expression.pos,JCTree.NOT,translate(sig.expression))));
                                    currentMethodInfo.exceptionLocal = null;
                                    String sp = position(spc.sourcefile,c.pos);
                                    JCStatement st = undefinedCheck(currentMethodInfo.owner,
                                            sp+"signals condition",
                                            factory.If(post,assertFailure(sp+"signals condition is false",c.pos),null));
                                    signalsChecks.append(st);
                                } catch (JmlRacNotImplemented ex) {
                                    notImplemented(c.pos(),c.token.internedName() + " clause containing " + ex.location + " expression");
                                }

                            } else if (c.token == JmlToken.SIGNALS_ONLY) {
                                hasSignalsOnly = true;
                                JmlMethodClauseSignalsOnly sig = (JmlMethodClauseSignalsOnly)c;
                                JCExpression e = falseLit;
                                for (JCExpression t: sig.list) {
                                    JCIdent id = treeutils.makeIdent(t.pos,signalsEx.sym);
                                    JCInstanceOf test = factory.at(t.pos).TypeTest(id,translate(t));
                                    test.type = syms.booleanType;
                                    e = treeutils.makeOr(t.pos,e,test);
                                }
                                currentMethodInfo.exceptionLocal = null;
                                String sp = position(spc.sourcefile,c.pos);
                                JCStatement st = undefinedCheck(currentMethodInfo.owner,
                                        sp+"signals_only condition",
                                        factory.If(treeutils.makeUnary(c.pos,JCTree.NOT,e),assertFailure(sp+"signals_only condition is false",c.pos),null));
                                signalsChecks.append(st);
                            }
                        }
                        if (!hasSignalsOnly) {
                            JCExpression e = falseLit;
                            for (JCExpression t: currentMethodInfo.decl.getThrows()) {
                                t = translate(t);
                                factory.at(t.pos);
                                JCIdent id = treeutils.makeIdent(t.pos,signalsEx.sym);
                                JCInstanceOf test = factory.TypeTest(id,t); // Caution: these get translated multiple times - is that oK?
                                test.type = syms.booleanType;
                                e = treeutils.makeBinary(t.pos,JCTree.OR,e,test);
                            }
                            currentMethodInfo.exceptionLocal = null;
                            String sp = position(spc.sourcefile,currentMethodInfo.decl.pos);
                            factory.at(currentMethodInfo.decl.pos);
                            JCStatement st = undefinedCheck(currentMethodInfo.owner,
                                    sp+"default signals_only condition",
                                    factory.If(treeutils.makeUnary(currentMethodInfo.decl.pos,JCTree.NOT,e),assertFailure(sp+"unexpected exception",currentMethodInfo.decl.pos),null));
                            signalsChecks.append(st);
                        }
                    }
                }

                // add checks for constraint clauses
                if (!isConstructor) {
                    for (JmlTypeClauseConstraint constraint : currentClassInfo.constraints) {
                        factory.at(constraint.pos);
                        if ((constraint.modifiers.flags & Flags.STATIC) == 0 &&
                                (currentMethodInfo.decl.mods.flags & Flags.STATIC) != 0) continue;
                        // FIXME - check that method signature is present
                        String sp = position(constraint.source(),constraint.pos);
                        try {
                            // FIXME - why are we making a copy here?
                            JCExpression e = translate(treeutils.makeUnary(constraint.pos,JCTree.NOT,JmlTreeCopier.copy(factory,constraint.expression)));
                            JCStatement st = undefinedCheck(currentMethodInfo.owner,
                                    sp+"constraint",
                                    factory.If(e,assertFailure(sp+"constraint is false",constraint.pos),null));
                            postChecks.append(st);
                        } catch (JmlRacNotImplemented ex) {
                            notImplemented(constraint.pos(),constraint.token.internedName() + " clause containing " + ex.location + " expression");
                        }

                    }
                }
                
                // Generate checks for initially clauses [ FIXME - this does not do inherited initiallys ]
                if (isConstructor) {
                    for (JmlTypeClauseExpr initially : currentClassInfo.translatedInitiallys) {
                        factory.at(initially.pos);
                        String sp = position(initially.source(),initially.pos);
                        JCExpression e = treeutils.makeUnary(initially.pos,JCTree.NOT,initially.expression);
                        JCStatement st = undefinedCheck(currentMethodInfo.owner,
                                sp+"initially",
                                factory.If(e,assertFailure(sp+"initially is false",initially.pos),null));
                        postChecks.append(st);
                    }
                }

                JCIdent m = factory.Ident(invariantMethodName);
                m.sym = currentClassInfo.invariantDecl.sym;
                m.type = m.sym.type;
                m = factory.Ident(staticinvariantMethodName);
                m.sym = currentClassInfo.staticinvariantDecl.sym;
                m.type = m.sym.type;

                ListBuffer<JCStatement> finalChecks = new ListBuffer<JCStatement>();
                if (!isHelper) {
                    if ((tree.mods.flags & Flags.STATIC) == 0) {
                        finalChecks.append(methodCallThis(currentClassInfo.invariantDecl));
                    }
                    finalChecks.append(methodCallThis(currentClassInfo.staticinvariantDecl));
                }

                // Make the catchers for testing signal assertions
                boolean includeRuntime = true;
                ListBuffer<JCCatch> catchers = new ListBuffer<JCCatch>();
                ListBuffer<JCExpression> exceptions = new ListBuffer<JCExpression>();
                exceptions.appendList(tree.getThrows());
                while (!exceptions.isEmpty()) {
                    JCExpression ex;
                    loop: do {
                        ex = exceptions.next(); // removes from list
                        for (JCExpression exx: exceptions) {
                            // if ex is a superclass of exx then we can't do ex yet
                            if (Types.instance(context).isSuperType(ex.type,exx.type)) {
                                exceptions.append(ex);
                                continue loop;
                            }
                        }
                        break; // continue on with ex
                    } while (true);
                    if (Types.instance(context).isSuperType(ex.type,syms.runtimeExceptionType)) includeRuntime = false;
                    factory.at(tree.pos);
                    JCCatch catcher = treeutils.makeCatcher(currentMethodInfo.owner,ex.type); // FIXME - needs position
                    JCAssign assign = factory.Assign(treeutils.makeIdent(tree.pos,signalsEx.sym),treeutils.makeIdent(tree.pos,catcher.param.sym)); // FIXME - needs position
                    assign.type = signalsEx.type;
                    catcher.body.stats = catcher.body.stats.append(factory.Exec(assign)); // FIXME - needs position
                    JCThrow throwex = factory.Throw(treeutils.makeIdent(tree.pos,catcher.param.sym)); // FIXME - needs position
                    catcher.body.stats = catcher.body.stats.append(throwex);
                    catchers.append(catcher);
                }
                if (includeRuntime) {
                    factory.at(tree.pos);
                    JCCatch catcher = treeutils.makeCatcher(currentMethodInfo.owner,syms.runtimeExceptionType); // FIXME - needs position
                    JCAssign assign = factory.Assign(treeutils.makeIdent(tree.pos,signalsEx.sym),treeutils.makeIdent(tree.pos,catcher.param.sym));  // FIXME - needs position
                    assign.type = signalsEx.type;
                    catcher.body.stats = catcher.body.stats.append(factory.Exec(assign)); // FIXME - needs position
                    JCThrow throwex = factory.Throw(treeutils.makeIdent(tree.pos,catcher.param.sym)); // FIXME - needs position
                    catcher.body.stats = catcher.body.stats.append(throwex);
                    catchers.append(catcher);
                }  // FIXME _ binary below need position
                finalChecks.prepend(factory.If(treeutils.makeBinary(0,JCTree.EQ,treeutils.makeIdent(tree.pos,signalsEx.sym),nulllit),factory.Block(0,postChecks.toList()),factory.Block(0,signalsChecks.toList())));
                JCBlock finalBlock = factory.Block(0,finalChecks.toList());// FIXME - needs position
                finalBlock.type = Type.noType;
                JCBlock bl = tree.body;
                if (bl == null) {
                    String mge = position(currentMethodInfo.source,tree.pos) + "model method is not implemented: " + tree.name;  // FIXME - need the source of the model method
                    JCStatement sta = assertFailure(mge,tree.pos); 
                    bl = factory.at(tree.pos).Block(0,List.<JCStatement>of(sta));
                }
                JCTry tryBlock = factory.Try(bl,catchers.toList(),finalBlock); // FIXME - needs position
                tryBlock.type = Type.noType;

                if (!isConstructor) {
                    if (currentMethodInfo.preCheck != null) newbody.append(currentMethodInfo.preCheck);
                    if (!isHelper) {
                        newbody.append(methodCallThis(currentClassInfo.staticinvariantDecl)); // FIXME - needs position
                        if ((tree.mods.flags & Flags.STATIC) == 0) {
                            newbody.append(methodCallThis(currentClassInfo.invariantDecl)); // FIXME - needs position
                        }
                    }
                    if (currentMethodInfo.resultDecl != null) newbody.append(currentMethodInfo.resultDecl);
                    if (signalsEx != null) newbody.append(signalsEx);
                } else if (currentClassInfo.decl.sym == syms.objectType.tsym) {
                    if (signalsEx != null) newbody.append(signalsEx);
                } else {
                    newbody.append(tree.body.stats.head);
                    if (signalsEx != null) newbody.append(signalsEx);
                    tryBlock.body.stats = tree.body.stats.tail;
                }

                for (JCVariableDecl v: currentMethodInfo.olds) {
                    newbody.append(v);
                }
                newbody.append(tryBlock);

                tree.body = factory.Block(0,newbody.toList());

                //log.noticeWriter.println("REWRITTEN " + tree);
                if (methodSpecs != null) {
                    for (JmlSpecificationCase spc: methodSpecs.cases) {
                        // FIXME - FORALL, OLD kill the whole case?
                        // FIXME - what about replicated clauses because of grouping - they get multiply translated as well
                        for (JmlMethodClause mc: spc.clauses) {
                            switch (mc.token) {
                                case REQUIRES:
                                case ENSURES:
                                case ASSIGNABLE:
                                case SIGNALS:
                                case SIGNALS_ONLY:
                                    break;
                                default:
                                    notImplemented(mc.pos(),mc.token.internedName() + " clause");
                                    break;
                            }
                        }
                    }
                }

            }
        } finally {
            popSource();
            currentMethodInfo = prevMethodInfo;
            currentMethodDecl = prev;
            result = tree;
        }
    }

    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        //        if (that.name.toString().equals("m2")) {
        //            System.out.println("ZZZ");
        //        }
        boolean prevSpecExpression = inSpecExpression;
        JCMethodDecl prev = currentMethodDecl;
        try {
            pushSource(that.source());
            currentMethodDecl = that;

            visitMethodDef(that);

//            inSpecExpression = true;
//            JmlSpecs.MethodSpecs mspecs = that.methodSpecsCombined;
//            ListBuffer<JmlSpecificationCase> newcases = new ListBuffer<JmlSpecificationCase>();
//            if (mspecs != null) { // FIXME - why would this be null
//                for (JmlSpecificationCase c: mspecs.cases.cases) {
//                    newcases.append(translate(c));
//                }
//                mspecs.cases.cases = newcases.toList();
//            }
        } finally {
            currentMethodDecl = prev;
            inSpecExpression = prevSpecExpression;
            result = that;
            popSource();
        }
    }

    public void visitTypeCast(JCTypeCast tree) {
        if (tree.clazz.type.equals(JmlTypes.instance(context).TYPE)) {
            JCExpression e = translate(tree.expr);
            result = methodCallUtilsExpression("makeTYPE0",e);
        } else {
            super.visitTypeCast(tree);
        }
    }


    public void visitJmlSetComprehension(JmlSetComprehension that) {
        throw new JmlRacNotImplemented(that.pos(),"Set Comprehension");
    }

    @Override
    public void visitReturn(JCReturn tree) {
        super.visitReturn(tree);
        tree = (JCReturn)result;
        if (currentMethodInfo != null) {
            if (currentMethodInfo.resultDecl == null) {
                // FIXME - minternal error
            } else {
                // FIXME - what if boxing/autoboxing conversions are needed?
                JCIdent id = factory.Ident(attr.resultName);
                id.sym = currentMethodInfo.resultDecl.sym;
                id.type = currentMethodInfo.resultDecl.type;
                tree.expr = factory.at(tree.pos).Assign(id,tree.expr);
                tree.expr.type = id.type;
            }
        }
    }



//    public void visitJmlStatementDecls(JmlStatementDecls that) {
//        // FIXME - only handles the first one
//        //result = translate(that.list.first());
//    }
//
//    public void visitJmlStatementLoop(JmlStatementLoop that) {
//        // TODO Auto-generated method stub
//        
//    }
//
//    public void visitJmlStatementSpec(JmlStatementSpec that) {
//        // TODO Auto-generated method stub
//        
//    }
//
//    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
//        // TODO Auto-generated method stub
//        
//    }
//
//    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
//        // TODO Auto-generated method stub
//        
//    }
//
//    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
//        // TODO Auto-generated method stub
//        
//    }
//
//    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
//        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlTypeClauseConditional");
//    }
//
//    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
//        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlTypeClauseConstraint");
//    }
//
//    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
//        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlTypeClauseDecl");
//    }
//
//    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
//        // TODO Auto-generated method stub
//        
//    }
//
//    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
//        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlTypeClauseExpr");
//    }
//
//    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
//        // TODO Auto-generated method stub
//        
//    }
//
//    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
//        // TODO Auto-generated method stub
//        
//    }
//
//    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
//        // TODO Auto-generated method stub
//        
//    }
//
//    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
//        // TODO Auto-generated method stub
//        
//    }
//    


//    public void visitJmlClassDecl(JmlClassDecl that) {
//        visitClassDef(that);  // OK
//        //log.noticeWriter.println("REWRITTEN CLASS " + result);
//    }
//
//    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
//        visitTopLevel(that);  // FIXME
//    }
//
//    public void visitJmlMethodDecl(JmlMethodDecl that) {
//        visitMethodDef(that);  // FIXME
//    }
//
//    public void visitJmlVariableDecl(JmlVariableDecl that) {
//        visitVarDef(that);  // FIXME
//    }
//
//    public void visitJmlConstraintMethodSig(JmlConstraintMethodSig that) {
//        // TODO Auto-generated method stub
//        
//    }
//
//    public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
//        // TODO Auto-generated method stub
//        
//    }

//    public void visitAuxVarDSA(AuxVarDSA that) {
//        // TODO Auto-generated method stub
//        
//    }
//
//    public void visitProgVarDSA(ProgVarDSA that) {
//        // TODO Auto-generated method stub
//        
//    }
    
    public void notImplemented(DiagnosticPosition pos, String feature) {
        if (Options.instance(context).isSet(JmlOption.SHOW_NOT_IMPLEMENTED.optionName())) {
            JavaFileObject prev = log.useSource(source);
            log.note(pos.getStartPosition(),"jml.not.implemented.rac",feature);
            log.useSource(prev);
        }
    }

    public void notImplemented(int start, int end, String feature) {
        if (Options.instance(context).isSet(JmlOption.SHOW_NOT_IMPLEMENTED.optionName())) {
            JavaFileObject prev = log.useSource(source);
            log.note(new JmlScanner.DiagnosticPositionSE(start,end),"jml.not.implemented.rac",feature);
            log.useSource(prev);
        }
    }


    /** This exception class is used to exit out of walking an AST when a feature is
     * encountered that is not implemented in RAC. It should be caught at some top-level
     * where the non-implementation can be handled. For example, it is caught at the clause
     * level so that the clause itself can be ignored (and appropriately reported). It should
     * not be caught at nested expression levels unless the intention is to ignore sub-expressions.
     */
    static public class JmlRacNotImplemented extends RuntimeException {
        private static final long serialVersionUID = 1L;
        DiagnosticPosition pos;
        String location;
        protected JmlRacNotImplemented(int start, int end, String location) {
            this.pos = new JmlScanner.DiagnosticPositionSE(start,end);
            this.location = location;
        }
        protected JmlRacNotImplemented(DiagnosticPosition pos, String location) {
            this.pos = pos;
            this.location = location;
        }
    }
}
