package org.jmlspecs.openjml.esc;

import java.util.LinkedList;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlDoWhileLoop;
import org.jmlspecs.openjml.JmlTree.JmlEnhancedForLoop;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlStatement;
import org.jmlspecs.openjml.JmlTree.JmlStatementDecls;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefArrayRange;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefKeyword;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConstraint;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseIn;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMaps;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMonitorsFor;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTree.JmlWhileLoop;
import org.jmlspecs.openjml.JmlTreeTranslator;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCAssignOp;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Names;

/** This translator mutates an AST to simplify it, in ways that are common
 * (mostly) to both RAC and ESC and that still result in a valid Java AST.
 * Any transformations must result in a fully-typechecked
 * tree.  Thus the sym and type fields of new nodes must be filled in correctly.
 * As typechecking is already completed, any errors in this regard may cause 
 * unpredictable and incorrect behavior in code and VC generation.  Note that 
 * these changes are IN PLACE - they destructively change the AST; thus they
 * should be idempotent.  [ TODO: This will need to change when we make the 
 * OpenJML structure more reusable as part of an interactive environment.]
 * 
 * The following transformations are performed here:(TODO- document this)
 * <UL>
 * <LI>The EQUIVALENCE, INEQUIVALENCE, IMPLIES and REVERSE_IMPLIES operations
 * are converted to equivalent forms using NOT, OR, EQUALITY
 * <LI>In method statements:
 * <UL>
 * <LI>JML set and debug statements are converted to regular Java statements
 * <LI>JML unreachable statements are converted to assert statements
 * <LI>ghost variables and local model class declarations are converted to
 * Java declarations
 * </UL>
 * <LI>JML expressions:
 * <UL>
 * <LI>informal comment is converted to a true literal
 * </UL>
 * </UL>
 * <P>
 * The following are excised (and correspondingly ignored):
 * <UL>
 * <LI>JML hence_by statements
 * </UL>
 * <P>
 * This leaves the following to be dealt with later:
 * <UL>
 * <LI>JML assert and assume statements
 * <LI>subtype expressions
 * <LI>lock ordering expressions
 * <LI>
 * </UL>
 * <P>
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
 * <LI>redundantly, implies_that, for_example
 * </UL>
 * 
 * @author David Cok
 *
 */
public class JmlTranslator extends JmlTreeTranslator {
    
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
    
    boolean postState = false;
    
    /** The class declaration that we are currently within */
    protected @NonNull JCClassDecl currentClassDecl = null;

    /** The method declaration that we are currently within */
    protected @NonNull JCMethodDecl currentMethodDecl = null;
    
    /** Current source */
    protected JavaFileObject source;
    
    /** A stack of previous source files, manipulated through pushSource and
     * popSource.  The current source is not on the stack.
     */
    protected java.util.List<JavaFileObject> stack = new LinkedList<JavaFileObject>();
    
    /** Makes the argument the current source (and top element of the stack) */
    public void pushSource(JavaFileObject jfo) {
        stack.add(0,source);
        source = jfo;
    }
    
    /** Replaces the current source with the top element of the stack,
     * popping it from the stack.
     */
    public void popSource() {
        source = stack.remove(0);
    }

    /** Constructs and initializes a new translator.  Translators are not
     * kept in the compilation context.
     * @param context the current compilation context
     */
    public JmlTranslator(Context context) {
        this.context = context;
        this.utils = Utils.instance(context);
        this.log = Log.instance(context);
        this.factory = JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        booleqSymbol = treeutils.booleqSymbol;
        boolneSymbol = treeutils.boolneSymbol;
        trueLit = treeutils.trueLit;
        falseLit = treeutils.falseLit;
    }
    
    /** Generates a new translator tied to the given compilation context */
    public static JmlTranslator instance(Context context) {
        return new JmlTranslator(context);
    }
    
    /** Translates the env.tree AST in-place in the given env. */
    public void translate(Env<AttrContext> env) {
        pushSource(env.toplevel.sourcefile);
        try {
            env.tree = translate(env.tree);
        } finally {
            popSource();
        }
    }
    
    // TODO - all these explicit checks need to be moved out.  Although we
    // want the same checks in ESC and RAC they are constructed differently.
    
//    /** Visitor method: translate a list of nodes, adding checks that each
//     * one is nonnull.
//     */
//    public <T extends JCExpression> List<T> translateNN(List<T> trees) {
//        if (trees == null) return null;
//        for (List<T> l = trees; l.nonEmpty(); l = l.tail)
//            l.head = (T)makeNullCheck(l.head.pos,translate(l.head),
//                    "ERROR",Label.UNDEFINED_NULL);  // FIXME _ fix the error message if this stays
//        return trees;
//    }

    /** Creates a method call that checks that the given expression is non-null,
     * returning the expression.
     * @param pos the character position at which to point out an error (in the
     *          current source file)
     * @param expr the untranslated expression to test and return
     * @param msg the error message
     * @param label the kind of error
     * @return the new AST
     */
    protected JCExpression makeNullCheck(int pos, JCExpression expr, String msg, Label label) {
        String posDescription = position(source,pos);
        
        JCLiteral message = treeutils.makeStringLiteral(pos,posDescription + msg); // end -position ??? FIXME
        JCFieldAccess m = treeutils.findUtilsMethod(pos,"nonNullCheck");
        JCExpression trans = translate(expr);  // Caution - translate resets the factory position
        JmlMethodInvocation newv = factory.at(pos).JmlMethodInvocation(m,List.<JCExpression>of(message,trans));
        newv.type = expr.type;
        newv.label = label;
        return newv;
    }

    //that is presumed already translated, condition is presumed untranslated
    protected JCExpression makeTrueCheck(int pos, JCExpression condition, JCExpression that, String msg, Label label) {
        String posDescription = position(source,pos);
        
        JCLiteral message = treeutils.makeStringLiteral(pos,posDescription + msg); // end -position ??? FIXME
        JCFieldAccess m = treeutils.findUtilsMethod(pos,"trueCheck");
        JCExpression tcond = translate(condition);// Caution - translate resets the factory position
        JCExpression trans = that;  
        JmlMethodInvocation newv = factory.at(pos).JmlMethodInvocation(m,List.<JCExpression>of(message,tcond,trans));
        newv.type = that.type;
        newv.label = label;
        return newv;
    }
    
    /** Inserts a check that 'obj' and 'that' are equal, returning 'that';
     * both 'obj' and 'that' must be already translated.
     */
    protected JCExpression makeEqCheck(int pos, JCExpression obj, JCExpression that, String msg, Label label) {
        String posDescription = position(source,pos);
        
        JCLiteral message = treeutils.makeStringLiteral(pos,posDescription + msg); // end -position ??? FIXME
        JCFieldAccess m = treeutils.findUtilsMethod(pos,"eqCheck");
        JmlMethodInvocation newv = factory.at(pos).JmlMethodInvocation(m,List.<JCExpression>of(message,obj,that));
        newv.type = that.type;
        newv.label = label;
        return newv;
    }
    
    /** Inserts a check that 'that' does not equal 0 for the appropriate in type;
     * 'that' is presumed untranslated */ 
    protected JCExpression makeZeroCheck(int pos, JCExpression that, Label label) {
        JCLiteral message = treeutils.makeStringLiteral(pos,"Divide by zero"); // end -position ??? FIXME
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

 
    // We have to do something special here.  This translator only allows replacing
    // a tree by another tree - so a statement can only be replaced by a single 
    // statement.  Sometimes we want to insert a bunch of statements.  Now we
    // could insert a Block in place of a statement, but if the original statement
    // was a declaration we will have screwed up the visibility of that declaration.
    // SO we allow the translation of a statement to return a block, but if the
    // statement was not a block and now is, we insert all of the statement of the
    // new block in line.  If you really wanted a block, then wrap it doubly.
    public void visitBlock(JCBlock tree) {
        List<JCStatement> trees = (tree.stats);
        if (trees == null) return; // FIXME - I would think that we should return result=tree in this case, but that gives an Exception - FIXME
        tree.stats = expandableTranslate(trees);
        result = tree;
    }
    
    public void visitIndexed(JCArrayAccess that) {
        that.indexed = makeNullCheck(that.pos,that.indexed,NULL_ASSIGNMENT,
                inSpecExpression ? Label.UNDEFINED_NULL_DEREFERENCE : Label.POSSIBLY_NULL_DEREFERENCE);
        that.index = translate(that.index);
        // FIXME - also the array bounds check
        result = that;
    }
    
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
    
    public final static String NULL_ASSIGNMENT = "assignment of null to non_null";
    public final static String NULL_INITIALIZATION = "null initialization of non_null variable";
    public final static String LOOP_VARIANT_NEGATIVE = "loop variant is less than 0";
    public final static String NULL_SELECTION = "selecting a field of a null object";
    
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
            if (fa.sym instanceof VarSymbol) {
                VarSymbol vsym = (VarSymbol)fa.sym;
                nonnull = !vsym.type.isPrimitive() && specs.isNonNull(vsym,vsym.enclClass());
            } else {
                log.error("jml.unexpected.code.branch",fa.sym.getClass() + " " + fa);
                nonnull = false;
            }
        }
        if (nonnull) {
            that.lhs = translate(that.lhs);
            that.rhs = makeNullCheck(that.pos,that.rhs,NULL_ASSIGNMENT,
                    Label.POSSIBLY_NULL_ASSIGNMENT);
        } else {
            that.lhs = translate(that.lhs);
            that.rhs = translate(that.rhs);
        }
        
        checkAssignable(that);
        result = that;
    }
    
    protected void checkAssignable(JCAssign that) {
        if (that.lhs instanceof JCFieldAccess) checkFieldAssignable((JCFieldAccess)that.lhs,that.pos);
        else if (that.lhs instanceof JCIdent) {
            Symbol sym = ((JCIdent)that.lhs).sym;
            if (!sym.isLocal()) that.lhs = checkIdentAssignable((JCIdent)that.lhs,that.pos);
        } else if (that.lhs instanceof JCArrayAccess) {
            checkArrayAssignable((JCArrayAccess)that.lhs,that.pos);
        }
    }
    
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
    
    protected void checkFieldAssignable(JCFieldAccess assignee, int pos) {
        if (!(currentMethodDecl instanceof JmlMethodDecl)) return;
        JmlMethodSpecs mspecs = ((JmlMethodDecl)currentMethodDecl).methodSpecsCombined.cases.deSugared;
        if (mspecs == null) return;
        for (JmlSpecificationCase c: mspecs.cases) {
            JCExpression precond = trueLit;
            for (JmlMethodClause m: c.clauses) {
                if (m.token == JmlToken.REQUIRES) {
                    precond = treeutils.makeAnd(m.pos,precond,((JmlMethodClauseExpr)m).expression);
                    continue;
                }
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
                    JCExpression ee = treeutils.makeImplies(precond.pos,precond,cond);
                    ee.pos = m.pos;
                    assignee.selected = makeTrueCheck(pos,ee,assignee.selected,"assignable",Label.ASSIGNABLE);
                }
            }
        }
    }
    
    protected void checkArrayAssignable(JCArrayAccess assignee, int pos) {
        if (!(currentMethodDecl instanceof JmlMethodDecl)) return;
        JmlMethodSpecs mspecs = ((JmlMethodDecl)currentMethodDecl).methodSpecsCombined.cases.deSugared;
        if (mspecs == null) return;
        for (JmlSpecificationCase c: mspecs.cases) {
            JCExpression precond = treeutils.trueLit; // FIXME - need the assignable clauses precondition
            for (JmlMethodClause m: c.clauses) {
                if (m.token == JmlToken.REQUIRES) {
                    precond = treeutils.makeAnd(m.pos,precond,((JmlMethodClauseExpr)m).expression);
                    continue;
                }
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
    
    protected JCExpression checkIdentAssignable(JCIdent assignee, int pos) {
        JCExpression wrapped = assignee;
        if (!(currentMethodDecl instanceof JmlMethodDecl)) return wrapped;
        JmlMethodSpecs mspecs = ((JmlMethodDecl)currentMethodDecl).methodSpecsCombined.cases.deSugared;
        if (mspecs == null) return wrapped;
        for (JmlSpecificationCase c: mspecs.cases) {
            JCExpression precond = trueLit; // FIXME - need the assignable clauses precondition
            for (JmlMethodClause m: c.clauses) {
                if (m.token == JmlToken.REQUIRES) {
                    precond = treeutils.makeAnd(m.pos,precond,((JmlMethodClauseExpr)m).expression);
                    continue;
                }
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
                    e.pos = m.pos;
                    wrapped = makeTrueCheck(pos,e,wrapped,"target not assignable",Label.ASSIGNABLE);
                }
            }
        }
        return wrapped;
    }
    
    @Override
    public void visitAssignop(JCAssignOp that) {
        that.lhs = translate(that.lhs);
        if (utils.rac && (that.getTag() == JCTree.DIV_ASG || that.getTag() == JCTree.MOD_ASG)) {
            if (that.rhs instanceof JCLiteral && ((JCLiteral)that.rhs).value.equals(Integer.valueOf(0))) {
                log.noticeWriter.println("Explicit divide by zero");
                // FIXME - put in an error message?
            } else {
                that.rhs = makeZeroCheck(that.pos,that.rhs, inSpecExpression? Label.UNDEFINED_DIV0 : Label.POSSIBLY_DIV0);
            }
        } else {
            that.rhs = translate(that.rhs);
        }
        checkAssignableOp(that);
        result = that;
    }
    
    @Override
    public void visitBinary(JCBinary that) {
        that.lhs = translate(that.lhs);
        if (utils.rac && (that.getTag() == JCTree.DIV || that.getTag() == JCTree.MOD)) {
            // This translation puts in a runtime-check for divide by zero.  This test is put
            // in logically in the BasicBlocker - that ought to be moved here eventually  TODO
            if (that.rhs instanceof JCLiteral && ((JCLiteral)that.rhs).value.equals(Integer.valueOf(0))) {
                log.noticeWriter.println("Explicit divide by zero");   // FIXME
                that.rhs = makeZeroCheck(that.pos,that.rhs,inSpecExpression ? Label.UNDEFINED_DIV0 : Label.POSSIBLY_DIV0);
            } else {
                that.rhs = makeZeroCheck(that.pos,that.rhs,inSpecExpression ? Label.UNDEFINED_DIV0 : Label.POSSIBLY_DIV0);
            }
        } else {
            that.rhs = translate(that.rhs);
        }
        result = that;
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
            // log.noticeWriter.println("PACKAGE");
            return;
        }
        if (that.selected instanceof JCIdent && ((JCIdent)that.selected).sym instanceof PackageSymbol) {
            // log.noticeWriter.println("PACKAGE");
            return;
        }
//        if (that.selected instanceof JCPrimitiveTypeTree) {
//            log.noticeWriter.println("PRIM TYPE");
//            return;
//        }

        if (utils.rac) that.selected = makeNullCheck(that.pos,that.selected,NULL_SELECTION,
                inSpecExpression ? Label.UNDEFINED_NULL_DEREFERENCE : Label.POSSIBLY_NULL_DEREFERENCE);
        else that.selected = translate(that.selected);
        result = that;
    }
    
    /** We translate the JML operators into equivalent Java ones */
    @Override
    public void visitJmlBinary(JmlBinary that) {
        // The following call translates the lhs and rhs and possibly produces
        // a new JmlBinary node
        super.visitJmlBinary(that);
        that = (JmlBinary)result;
        switch (that.op) {
            case IMPLIES:
                // P ==> Q is equivalent to !P || Q (short-circuit operator)
                result = treeutils.makeOr(that.pos,treeutils.makeUnary(that.lhs.pos,JCTree.NOT,that.lhs),that.rhs);
                break;
            case REVERSE_IMPLIES:
                // P <== Q is equivalent to P || !Q (short-circuit operator)
                result = treeutils.makeOr(that.pos,that.lhs,treeutils.makeUnary(that.rhs.pos,JCTree.NOT,that.rhs));
                break;
            case EQUIVALENCE:
                // P <==> Q is equivalent to P == Q  - but we need a boolean ==
                result = treeutils.makeBinary(that.pos,JCTree.EQ,booleqSymbol,that.lhs,that.rhs);
                break;
            case INEQUIVALENCE:
                // P <=!=> Q is equivalent to P != Q  - but we need a boolean !=
                result = treeutils.makeBinary(that.pos,JCTree.NE,boolneSymbol,that.lhs,that.rhs);
                break;
            case SUBTYPE_OF:
            case JSUBTYPE_OF:
            default:
                // FIXME - what about the lock comparison operators
                //ERROR - operator not handled FIXME
                result = that;
            
        }
    }
    
    @Override
    public void visitVarDef(JCVariableDecl that) {
        if (that.init != null && !that.init.type.isPrimitive() && specs.isNonNull(that.sym,that.sym.enclClass())) {
            // FIXME _ fix this back at the declaration of $$values$...
            if (!that.getName().toString().startsWith("$$values$")) 
                that.init = makeNullCheck(that.pos,that.init,NULL_INITIALIZATION + " " + that.getName(),
                        Label.POSSIBLY_NULL_INITIALIZATION);
        } else if (that.init != null) {
            that.init = translate(that.init);
        }
        result = that;
    }
    
    @Override
    public void visitClassDef(JCClassDecl that) {
        JCClassDecl prev = currentClassDecl;
        currentClassDecl = that;
        pushSource(that.sym.sourcefile);
        try {
            super.visitClassDef(that);
        } finally {
            currentClassDecl = prev;
            popSource();
        }
    }
    
    @Override
    public void visitIdent(JCIdent that) {
        if (postState && (that.sym.owner instanceof MethodSymbol)) {
            result = factory.JmlMethodInvocation(JmlToken.BSOLD,List.<JCExpression>of(that));
            result.type = that.type;
            // If this is a method parameter
        } else {
            result = that;
        }
    }
    
    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        boolean prev = postState;
        try {
            postState = that.token == JmlToken.ENSURES || that.token == JmlToken.SIGNALS;
            super.visitJmlMethodClauseExpr(that);
        } finally {
            postState = prev;
        }
    }
    
    @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        // FIXME - do we do nothing with interfaces ?? At least translate the invariants etc.???
        if ((that.sym.flags() & Flags.INTERFACE) != 0) {
            result = that;
            return;
        }

        JCClassDecl prev = currentClassDecl;
        boolean prevSpecExpression = inSpecExpression;
        currentClassDecl = that;
        pushSource(that.sym.sourcefile);
        try {

            //visitClassDef(that);
            // Copy in the super class code (MAINTENANCE) since we need to skip
            // the JML constructs in the body and instead process the consolidated
            // collection in that.typespecs
            that.mods = translate(that.mods);
            that.typarams = translateTypeParams(that.typarams);
            that.extending = translate(that.extending);
            that.implementing = translate(that.implementing);
            //that.defs = translate(that.defs); // Inlined below to exclude obsolete JML nodes
            ListBuffer<JCTree> newlist = new ListBuffer<JCTree>();
            for (JCTree t: that.defs) {
                //            if (t == null) {log.noticeWriter.println("NULL ELEMENT IN DEFS OF CLASS " + that.name); continue; } // FIXME - this happes during JUnit tests
                if (t != null && !(t instanceof JmlTypeClause)) {
                    newlist.append(translate(t));
                }
            }

            inSpecExpression = true;
            JmlSpecs.TypeSpecs tspecs = that.typeSpecsCombined;
            if (true) {
                if (tspecs != null) {
                    ListBuffer<JmlTypeClause> nlist = new ListBuffer<JmlTypeClause>();
                    for (JmlTypeClause d : tspecs.clauses) {
                        if (d instanceof JmlTypeClauseDecl) {
                            JCTree v = ((JmlTypeClauseDecl)d).decl;
                            if (v instanceof JCVariableDecl) {
                                JCVariableDecl vv = (JCVariableDecl)translate(v);
                                newlist.append(vv);
                            } else {
                                nlist.append(translate(d));
                            }
                        } else {
                            nlist.append(translate(d));
                        }
                    }
                    tspecs.clauses = nlist;
                }
            }
            that.defs = newlist.toList();

        } finally {
            result = that;
            currentClassDecl = prev;
            inSpecExpression = prevSpecExpression;
            popSource();
        }
    }

    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        log.error("jml.internal","Should not be calling JmlTranslator.visitJmlCompilationUnit");
        result = that;
    }

    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        visitDoLoop(that);
    }

    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        // FIXME - should not care which tool is being used (or explain)
        if (utils.rac) result = that;  // FIXME - trnaslate innards
        else result = translate(that.implementation);
        //visitForeachLoop(that);
//        JmlEnhancedForLoop copy = (JmlEnhancedForLoop)result;
//        copy.loopSpecs = translate(copy.loopSpecs);
    }

    public void visitJmlForLoop(JmlForLoop that) {
        visitForLoop(that);
        JmlForLoop copy = (JmlForLoop)result;
        copy.loopSpecs = translate(copy.loopSpecs);
        result = copy;
    }

//    public void visitJmlGroupName(JmlGroupName that) {
//        result = that;
//    }
//
//    public void visitJmlImport(JmlImport that) {
//        visitImport(that);
//    }
//
//    public void visitJmlLblExpression(JmlLblExpression that) {
//        that.expression = translate(that.expression);
//        result = that;
//    }
//
//    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
//        result = that;
//    }
//
//    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
//        that.expression = translate(that.expression);
//        that.predicate = translate(that.predicate);
//        result = that;
//    }
//
//    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
//        JmlMethodClauseDecl copy = that;
//        copy.decls = translate(that.decls);
//        result = copy;
//    }
//
//    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
//        that.expression = translate(that.expression);
//        result = that;
//    }
//
//    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
//        result = that;
//    }
//
//    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
//        result = that;
//    }
//
//    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
//        result = that;
//    }
    
    @Override
    public void visitMethodDef(JCMethodDecl that) {
        JCMethodDecl prev = currentMethodDecl;
        currentMethodDecl = that;
        try {
            super.visitMethodDef(that);
        } finally {
            currentMethodDecl = prev;
        }
    }

    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        boolean prevSpecExpression = inSpecExpression;
        JCMethodDecl prev = currentMethodDecl;
        try {
            pushSource(that.source());

            visitMethodDef(that);

            inSpecExpression = true;
            currentMethodDecl = that;
            JmlSpecs.MethodSpecs mspecs = that.methodSpecsCombined;
            ListBuffer<JmlSpecificationCase> newcases = new ListBuffer<JmlSpecificationCase>();
            if (mspecs != null) { // FIXME - why would this be null
                for (JmlSpecificationCase c: mspecs.cases.cases) {
                    newcases.append(translate(c));
                }
                mspecs.cases.cases = newcases.toList();
            }
        } finally {
            currentMethodDecl = prev;
            inSpecExpression = prevSpecExpression;
            result = that;
            popSource();
        }
    }

    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        // No translation of the method, just putting in checks on
        // the arguments.
        JmlToken t = that.token;
        if (t == null) {
            visitApply(that);
            return;
        }
        // FIXME - what about these implementations
        switch (t) {
            case BSPAST:
            case BSOLD:
            case BSPRE:
//                arg = translate(tree.args.get(0));
//                int n = methodInfo.olds.size();
//                String s = "_JML$$$old_" + n;
//                Name nm = names.fromString(s);
//                JCVariableDecl v = makeVarDef(arg.type,nm,methodInfo.owner,arg);
//                methodInfo.olds.append(v);
//                JCIdent r = make.Ident(nm);
//                r.sym = v.sym;
//                r.type = v.sym.type;
//                result = r;
                break;

            case BSTYPEOF:
//                translateTypeOf(tree);
                break;

            case BSNONNULLELEMENTS :
//                translateNonnullelements(tree);
                break;

            case BSTYPELC:
                translateTypelc(that);
                return;
                //break;
            
            case BSELEMTYPE:
//                translateElemtype(tree);
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
                translate(that.args);
                break;

            default:
                JavaFileObject prev = log.useSource(source);
                log.error(that.pos, "jml.unknown.construct",t.internedName(),"JmlRac.visitApply");
            // FIXME - recovery possible?
                log.useSource(prev);
                break;
        }
        result = that;
        //that.args = translate(that.args);
        return;
    }

//    @Override
//    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
//        // No overriding needed
//    }

//    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
//        result = that;
//    }

//    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
//        JmlQuantifiedExpr copy = that;
//        // FIXME - declartion?
//        copy.range = translate(copy.range);
//        copy.value = translate(copy.value);
//        result = copy;
//    }
//

//    public void visitJmlSetComprehension(JmlSetComprehension that) {
//        JmlSetComprehension copy = that;
//        copy.predicate = translate(that.predicate);
//        // varia ble, newtype?  FIXME
//        result = copy;
//    }

    @Override
    /** This handles expression constructs with no argument list such as \\result */
    public void visitJmlSingleton(JmlSingleton that) {
        JmlToken jt = that.token;
        switch (jt) {
               
            case BSINDEX:
                result = that;
                break;
                
            case BSLOCKSET:
            case BSVALUES:
            case BSRESULT:
            case BSSAME:
            case BSNOTSPECIFIED:
            case BSNOTHING:
            case BSEVERYTHING:
                // skip
                result = that;
                break;
                
            case INFORMAL_COMMENT:
                result = trueLit;
                break;

            default:
                JavaFileObject prev = log.useSource(source);
                log.error(that.pos,"jml.unknown.type.token",that.token.internedName(),"JmlAttr.visitJmlSingleton");
                log.useSource(prev);
                result = that;
                break;
        }
    }

    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        pushSource(that.sourcefile);
        try {
            super.visitJmlSpecificationCase(that);
        } finally {
            popSource();
        }
    }

    public void visitJmlStatement(JmlStatement that) {
        boolean prev = inSpecExpression;
        inSpecExpression = true;
        switch (that.token) {
            case SET:
            case DEBUG: // FIXME - if turned on by options
                result = translate(that.statement);
                break;
            
            case HENCE_BY:
                result = factory.Skip();
                utils.notImplemented(that.pos(),"hence_by statement");
                break;
                
            default:
                // FIXME - unimplemented
                result = factory.Skip();
            	log.error("log.internal","Unexpected and unimplemented case in JmlTranslator.visitJmlStatement for token " + that.token.internedName());
        }
        inSpecExpression = prev;
    }

    public void visitJmlStatementDecls(JmlStatementDecls that) {
        // Treat this just like a declaration
        // FIXME - is this still actually a list of declarations?
        boolean prev = inSpecExpression;
        inSpecExpression = true;
        List<JCStatement> list = expandableTranslate(that.list);
        result = factory.at(that.pos).Block(0,list);
        inSpecExpression = prev;
    }

    public void visitJmlStatementExpr(JmlStatementExpr that) {
        boolean prev = inSpecExpression;
        inSpecExpression = true;
        if (that.token == JmlToken.UNREACHABLE) {
            // convert to assert
            JCExpression e = translate(that.optionalExpression);
            if (e == null) e = treeutils.makeBooleanLiteral(that.pos,false);
            JmlStatementExpr r = factory.at(that.pos).JmlExpressionStatement(JmlToken.ASSERT,Label.UNREACHABLE,e);
            r.source = that.source;
            //r.line = that.line;
            result = r;
        } else if (that.token == JmlToken.ASSERT || that.token == JmlToken.ASSUME){ // assert, assume
            // We translate the expression but leave the assert and assume statements
            that.expression = translate(that.expression);
            that.optionalExpression = translate(that.optionalExpression);
            result = that;
        } else if (that.token == JmlToken.REACHABLE) {
            result = factory.at(that.pos).Skip();
        } else {
            log.error("log.internal","Unexpected and unimplemented case in JmlTranslator.visitJmlStatementExpr for token " + that.token.internedName());
            result = that;
        }
        inSpecExpression = prev;
    }

//    public void visitJmlStatementLoop(JmlStatementLoop that) {
//        JmlStatementLoop copy = that;
//        copy.expression = translate(that.expression);
//        result = copy;
//    }
//
//    public void visitJmlStatementSpec(JmlStatementSpec that) {
//        JmlStatementSpec copy = that;
//        copy.statementSpecs = translate(that.statementSpecs);
//        result = copy;
//    }

//    @Override
//    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
//     // No overriding needed
//    }

//    @Override
//    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
//     // No overriding needed
//    }

//    @Override
//    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
//     // No overriding needed
//    }

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

    // A normal variable declaration with specs
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        pushSource(that.sourcefile);
        try {
            boolean prev = inSpecExpression;
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
            inSpecExpression = prev;
            result = saved;
        } finally {
            popSource();
        }
    }

    public void visitJmlWhileLoop(JmlWhileLoop that) {
        visitWhileLoop(that);
        JmlWhileLoop copy = (JmlWhileLoop)result;
        copy.loopSpecs = translate(copy.loopSpecs);
        result = copy;
    }
    
    public void translateTypelc(JmlMethodInvocation that) {
        // Presumes this is indeed a \type invocation and
        // that the one argument is a Type
        JCTree type = that.args.get(0);
        result = treeutils.trType(that.pos, type);
    }
    
    
}
