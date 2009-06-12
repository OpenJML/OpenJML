package org.jmlspecs.openjml;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotations.NonNull;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.Label;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.comp.Resolve;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.Token;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;

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
    
    @NonNull protected Name nonNullName;
    
    /** The factory used to create AST nodes, initialized in the constructor */
    @NonNull protected JmlTree.Maker factory;
 
    ClassSymbol utilsClass = null;
    JCIdent utilsClassIdent;
    
    protected Symbol andSymbol;
    protected Symbol orSymbol;
    protected Symbol notSymbol;
    protected Symbol objecteqSymbol;
    protected Symbol booleqSymbol;
    protected Symbol boolneSymbol;
    protected JCLiteral trueLit;
    protected JCLiteral falseLit;
    protected JCLiteral zero;
    protected JCLiteral nulllit;
    protected JCLiteral maxIntLit;

    boolean dorac;
    boolean doesc;
    boolean inSpecExpression;
    
    public JmlTranslator(Context context) {
        this.context = context;
        this.utils = Utils.instance(context);
        this.log = Log.instance(context);
        this.factory = (JmlTree.Maker)JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.utilsClass = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.utils.Utils"));
        utilsClassIdent = factory.Ident(names.fromString("org.jmlspecs.utils.Utils"));
        utilsClassIdent.type = utilsClass.type;
        utilsClassIdent.sym = utilsClassIdent.type.tsym;
        dorac = Options.instance(context).get("-rac") != null;  // FIXME - fix these - proper call and names
        doesc = Options.instance(context).get("-esc") != null;
        andSymbol = syms.predefClass.members().lookup(names.fromString("&&")).sym;
        orSymbol  = syms.predefClass.members().lookup(names.fromString("||")).sym;
        notSymbol = syms.predefClass.members().lookup(names.fromString("!")).sym;
        objecteqSymbol = findOpSymbol("==",syms.objectType);
        booleqSymbol = findOpSymbol("==",syms.booleanType);
        boolneSymbol = findOpSymbol("!=",syms.booleanType);
        trueLit = makeLit(syms.booleanType,1);
        falseLit = makeLit(syms.booleanType,0);
        zero = makeLit(syms.intType,0);
        nulllit = makeLit(syms.botType, null);
        maxIntLit = makeLit(syms.intType,Integer.MAX_VALUE);
        
    }
    
    public void translate(Env<AttrContext> env) {
        // env.tree or env.topLevel??? FIXME
        //log.noticeWriter.println((env.tree != null) + " " + (env.toplevel!= null));
        env.tree = translate(env.tree);
    }
    
    /** Visitor method: translate a list of nodes.
     */
    public <T extends JCExpression> List<T> translateNN(List<T> trees) {
        if (trees == null) return null;
        for (List<T> l = trees; l.nonEmpty(); l = l.tail)
            l.head = (T)makeNullCheck(l.head.pos,translate(l.head),
                    "ERROR",Label.UNDEFINED_NULL);
        return trees;
    }

    public Symbol findOpSymbol(String name, Type argtype) {
        Scope.Entry e = syms.predefClass.members().lookup(names.fromString(name));
        while (e != null && e.sym != null) {
            if (((MethodType)e.sym.type).argtypes.head.equals(argtype)) return e.sym;
            e = e.next();
        }
        // FIXME - throw error
        return null;
    }
    
    public JCFieldAccess findUtilsMethod(String methodName) {
        Name n = names.fromString(methodName);
        Scope.Entry e = utilsClass.members().lookup(n);
        Symbol ms = e.sym;
        JCFieldAccess m = factory.Select(utilsClassIdent,n);
        m.sym = ms;
        m.type = m.sym.type;
        return m;
    }

    
    public JCLiteral makeLiteral(boolean v, int pos) {
        JCLiteral r = factory.at(pos).Literal(TypeTags.BOOLEAN,v?1:0);
        r.type = syms.booleanType;
        return r;
    }

    public JCLiteral makeStringLiteral(String s, int pos) {
        JCLiteral r = factory.at(pos).Literal(TypeTags.CLASS,s);
        r.type = syms.stringType;
        return r;
    }

    /** Make an attributed tree representing a literal. This will be an
     *  Ident node in the case of boolean literals, a Literal node in all
     *  other cases.
     *  @param type       The literal's type.
     *  @param value      The literal's value.
     */
    JCLiteral makeLit(Type type, Object value) { // FIXME - needs pos
        return factory.Literal(type.tag, value).setType(type.constType(value));
    }

    // FIXME - can we cache the && and || operators ?
    /** Make an attributed binary expression.
     *  @param optag    The operators tree tag.
     *  @param lhs      The operator's left argument.
     *  @param rhs      The operator's right argument.
     */
    JCExpression makeBinary(int pos, int optag, Symbol opSymbol, JCExpression lhs, JCExpression rhs) {
//        if (optag == JCTree.OR && lhs == falseLit) return rhs;  // Lose position if we do this
//        if (optag == JCTree.AND && lhs == trueLit) return rhs;
        JCBinary tree = factory.at(pos).Binary(optag, lhs, rhs);
        tree.operator = opSymbol != null ? opSymbol : optag == JCTree.AND ? andSymbol : optag == JCTree.OR ? orSymbol : null; // FIXME - report error
        tree.type = tree.operator.type.getReturnType();
        return tree;
    }
    
    JCExpression makeAnd(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.AND,andSymbol,lhs,rhs);
    }

    JCExpression makeOr(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.OR,orSymbol,lhs,rhs);
    }

    JCExpression makeImplies(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.OR,orSymbol,
                makeUnary(pos,JCTree.NOT,lhs), rhs);
    }

    JCExpression makeEqObject(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.EQ,objecteqSymbol,lhs, rhs);
    }

    // FIXME - can we cache the ! operator?
    /** Make an attributed unary expression.
     *  @param optag    The operators tree tag.
     *  @param arg      The operator's argument.
     */
    JCExpression makeUnary(int pos, int optag, JCExpression arg) {
        if (arg.equals(trueLit) && optag == JCTree.NOT) return falseLit;
        if (arg.equals(falseLit) && optag == JCTree.NOT) return trueLit;
        JCUnary tree = factory.at(pos).Unary(optag, arg);
        tree.operator = optag == JCTree.NOT ? notSymbol : null; // FIXME - report error
        tree.type = tree.operator.type.getReturnType();
        return tree;
    }
    
    JCExpression makeNot(int pos, JCExpression arg) {
        return makeUnary(pos,JCTree.NOT,arg);
    }
    

//    /** Make an attributed tree representing a literal. This will be an
//     *  Ident node in the case of boolean literals, a Literal node in all
//     *  other cases.
//     *  @param type       The literal's type.
//     *  @param value      The literal's value.
//     */
//    JCLiteral makeLit(Type type, Object value) {
//        return make.Literal(type.tag, value).setType(type.constType(value));
//    }
    
 
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
                inSpecExpression ? Label.UNDEFINED_NULL : Label.POSSIBLY_NULL);
        that.index = translate(that.index);
        // FIXME - also the array bounds check
        result = that;
    }
    
    public List<JCStatement> expandableTranslate(List<JCStatement> trees) {
        for (List<JCStatement> l = trees; l.nonEmpty(); l = l.tail) {
            JCStatement r = translate(l.head);
            if (!(l.head instanceof JCBlock) && r instanceof JCBlock) {
                // insert the statements of the block, without iterating
                // over the new statements
                List<JCStatement> newtrees = ((JCBlock)r).stats;
                l.head = newtrees.head;
                newtrees = newtrees.tail;
                if (newtrees == null || newtrees.tail == null) continue;
                List<JCStatement> last = newtrees;
                while (last.tail.tail != null) last = last.tail;
                last.tail = l.tail;
                l.tail = newtrees;
                l = last;
            } else {
                l.head = r;
            }
        }
        return trees;
    }
    
    public final static String NULL_ASSIGNMENT = "assignment of null to non_null";
    public final static String NULL_INITIALIZATION = "null initialization of non_null variable";
    public final static String LOOP_VARIANT_NEGATIVE = "loop variant is less than 0";
    public final static String NULL_SELECTION = "selecting a field of a null object";
    
    public String position(JavaFileObject source, int pos) {
        JavaFileObject pr = log.currentSourceFile();
        try {
            log.useSource(source);
            return (source==null?"":source.getName() + ":" + log.currentSource().getLineNumber(pos)) + ": JML ";
        } catch (UnsupportedOperationException e) {
            return (source==null?"":source.getName() + ": ? " ) + ": JML ";
        } finally {
            log.useSource(pr);
        }
    }

    protected JCExpression makeNullCheck(int pos, JCExpression that, String msg, Label label) {
        JavaFileObject jfo = currentClassDecl.sym.sourcefile;
        String posDescription = position(jfo,pos);
        
        JCLiteral message = makeStringLiteral(posDescription + msg,pos); // end -position ??? FIXME
        JCFieldAccess m = findUtilsMethod("nonNullCheck");
        JCExpression trans = translate(that);  // Caution - translate resets the factory position
        JmlMethodInvocation newv = factory.at(pos).JmlMethodInvocation(m,List.<JCExpression>of(message,trans));
        newv.type = that.type;
        newv.label = label;
        return newv;
    }
    
    //that is presumed already translated
    protected JCExpression makeTrueCheck(int pos, JCExpression condition, JCExpression that, String msg, Label label) {
        JavaFileObject jfo = currentClassDecl.sym.sourcefile;
        String posDescription = position(jfo,pos);
        
        JCLiteral message = makeStringLiteral(posDescription + msg,pos); // end -position ??? FIXME
        JCFieldAccess m = findUtilsMethod("trueCheck");
        JCExpression tcond = translate(condition);// Caution - translate resets the factory position
        JCExpression trans = that;  
        JmlMethodInvocation newv = factory.at(pos).JmlMethodInvocation(m,List.<JCExpression>of(message,tcond,trans));
        newv.type = that.type;
        newv.label = label;
        return newv;
    }
    
    protected JCExpression makeEqCheck(int pos, JCExpression obj, JCExpression that, String msg, Label label) {
        JavaFileObject jfo = currentClassDecl.sym.sourcefile;
        String posDescription = position(jfo,pos);
        
        JCLiteral message = makeStringLiteral(posDescription + msg,pos); // end -position ??? FIXME
        JCFieldAccess m = findUtilsMethod("eqCheck");
        JmlMethodInvocation newv = factory.at(pos).JmlMethodInvocation(m,List.<JCExpression>of(message,obj,that));
        newv.type = that.type;
        newv.label = label;
        return newv;
    }
    
    protected JCExpression makeZeroCheck(int pos, JCExpression that, Label label) {
        JCLiteral message = makeStringLiteral("Divide by zero",pos); // end -position ??? FIXME
        JCExpression newv = translate(that);
//        if (that.type.tag == TypeTags.INT) {
//            JCFieldAccess m = findUtilsMethod("zeroIntCheck");
//            JmlMethodInvocation call = factory.at(pos).JmlMethodInvocation(m,List.<JCExpression>of(message,newv));
//            call.type = that.type;
        //    call.label = label;
        //newv = call;
//        } else {
//            // FIXME - no check bein done
//        }
        return newv;
    }

    public void visitAnnotation(JCAnnotation tree) {
        // FIXME - translating gets us into trouble later, but we don't need to, I think.
//        tree.annotationType = translate(tree.annotationType);
//        tree.args = translate(tree.args);
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
            //if (fa.sym instanceof VarSymbol) {
                VarSymbol vsym = (VarSymbol)fa.sym;
                nonnull = !vsym.type.isPrimitive() && specs.isNonNull(vsym,vsym.enclClass());
//            } else {
//                System.out.println("OUCH " + fa.sym.getClass() + " " + fa);
//            }
                
        }
        if (nonnull) {
            that.lhs = translate(that.lhs);
            that.rhs = makeNullCheck(that.pos,that.rhs,NULL_ASSIGNMENT,
                    inSpecExpression ? Label.UNDEFINED_NULL : Label.POSSIBLY_NULL);
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
        JmlMethodSpecs mspecs = ((JmlMethodDecl)currentMethodDecl).methodSpecsCombined.deSugared;
        if (mspecs == null) return;
        for (JmlSpecificationCase c: mspecs.cases) {
            JCExpression precond = trueLit; // FIXME - need the assignable clauses precondition
            for (JmlMethodClause m: c.clauses) {
                if (m.token == JmlToken.REQUIRES) {
                    precond = makeAnd(m.pos,precond,((JmlMethodClauseExpr)m).expression);
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
                            JCExpression ex = makeBinary(fa.pos,JCTree.EQ,objecteqSymbol,assignee.selected,fa.selected);
                            ex = makeImplies(e.pos,precond,ex);
                            cond = makeOr(e.pos,cond,ex);
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
                    JCExpression e = makeImplies(precond.pos,precond,cond);
                    assignee.selected = makeTrueCheck(pos,e,assignee.selected,"assignable",Label.ASSIGNABLE);
                }
            }
        }
    }
    
    protected void checkArrayAssignable(JCArrayAccess assignee, int pos) {
        if (!(currentMethodDecl instanceof JmlMethodDecl)) return;
        JmlMethodSpecs mspecs = ((JmlMethodDecl)currentMethodDecl).methodSpecsCombined.deSugared;
        if (mspecs == null) return;
        for (JmlSpecificationCase c: mspecs.cases) {
            JCExpression precond = trueLit; // FIXME - need the assignable clauses precondition
            for (JmlMethodClause m: c.clauses) {
                if (m.token == JmlToken.REQUIRES) {
                    precond = makeAnd(m.pos,precond,((JmlMethodClauseExpr)m).expression);
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
                        JCExpression sameArrays = makeEqObject(pos,assignee.indexed,allowed.expression);
                        if (allowed.lo == null && allowed.hi == null) {
                            // any index allowed
                        } else if (allowed.lo == allowed.hi) {
                            // require allowed.lo == assignee.index // these are ints // FIXME
                        } else if (allowed.hi == null) {
                            // requires allowed.lo <= assignee.index && assignee.index < array.length // FIXME
                        } else {
                            // requires allowed.lo <= assignee.index && assignee.index <= allowed.hi // FIXME
                        }
                        cond = makeOr(pos,cond,sameArrays);
                    } else {
                        // FIXME - bad option
                    }
                }
                if (cond != trueLit) {
                    // assert that (precond ==> cond)
                    // this does no translation
                    JCExpression e = makeImplies(precond.pos,precond,cond);
                    assignee.indexed = makeTrueCheck(pos,e,assignee.indexed,"assignable",Label.ASSIGNABLE);
                }
            }
        }
    }
    
    protected JCExpression checkIdentAssignable(JCIdent assignee, int pos) {
        JCExpression wrapped = assignee;
        if (!(currentMethodDecl instanceof JmlMethodDecl)) return wrapped;
        JmlMethodSpecs mspecs = ((JmlMethodDecl)currentMethodDecl).methodSpecsCombined.deSugared;
        if (mspecs == null) return wrapped;
        for (JmlSpecificationCase c: mspecs.cases) {
            JCExpression precond = trueLit; // FIXME - need the assignable clauses precondition
            for (JmlMethodClause m: c.clauses) {
                if (m.token == JmlToken.REQUIRES) {
                    precond = makeAnd(m.pos,precond,((JmlMethodClauseExpr)m).expression);
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
                if (cond != trueLit) {
                    // assert that (precond ==> cond)
                    // this does no translation
                    JCExpression e = makeImplies(precond.pos,precond,cond);
                    wrapped = makeTrueCheck(pos,e,wrapped,"target not assignable",Label.ASSIGNABLE);
                }
            }
        }
        return wrapped;
    }
    
    @Override
    public void visitAssignop(JCAssignOp that) {
        that.lhs = translate(that.lhs);
        if (that.getTag() == JCTree.DIV_ASG || that.getTag() == JCTree.MOD_ASG) {
            if (that.rhs instanceof JCLiteral && ((JCLiteral)that.rhs).value.equals(Integer.valueOf(0))) {
                log.noticeWriter.println("Explicit divide by zero");
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
        if (that.getTag() == JCTree.DIV || that.getTag() == JCTree.MOD) {
            if (that.rhs instanceof JCLiteral && ((JCLiteral)that.rhs).value.equals(Integer.valueOf(0))) {
                log.noticeWriter.println("Explicit divide by zero");
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
        if (that.selected instanceof JCFieldAccess) {
            if (((JCFieldAccess)that.selected).sym instanceof PackageSymbol) {
               // log.noticeWriter.println("PACKAGE");
               return;
            }
        }
//        if (that.selected instanceof JCPrimitiveTypeTree) {
//            log.noticeWriter.println("PRIM TYPE");
//            return;
//        }

        that.selected = makeNullCheck(that.pos,that.selected,NULL_SELECTION,
                inSpecExpression ? Label.UNDEFINED_NULL : Label.POSSIBLY_NULL);
        result = that;
    }
    
    /** We translate the JML operators into equivalent Java ones */
    @Override
    public void visitJmlBinary(JmlBinary that) {
        super.visitJmlBinary(that);
        switch (that.op) {
            case IMPLIES:
                // P ==> Q is equivalent to !P || Q (short-circuit operator)
                result = makeBinary(that.pos,JCTree.OR,orSymbol,makeUnary(that.lhs.pos,JCTree.NOT,that.lhs),that.rhs);
                break;
            case REVERSE_IMPLIES:
                // P <== Q is equivalent to P || !Q (short-circuit operator)
                result = makeBinary(that.pos,JCTree.OR,orSymbol,that.lhs,makeUnary(that.rhs.pos,JCTree.NOT,that.rhs));
                break;
            case EQUIVALENCE:
                // P <==> Q is equivalent to P == Q  - but we need a boolean ==
                result = makeBinary(that.pos,JCTree.EQ,booleqSymbol,that.lhs,that.rhs);
                break;
            case INEQUIVALENCE:
                // P <=!=> Q is equivalent to P != Q  - but we need a boolean !=
                result = makeBinary(that.pos,JCTree.EQ,boolneSymbol,that.lhs,that.rhs);
                break;
            case SUBTYPE_OF:
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
                        inSpecExpression ? Label.UNDEFINED_NULL : Label.POSSIBLY_NULL);
        } else if (that.init != null) {
            that.init = translate(that.init);
        }
        result = that;
    }
    
    protected JCClassDecl currentClassDecl = null;
    
    @Override
    public void visitClassDef(JCClassDecl that) {
        JCClassDecl prev = currentClassDecl;
        currentClassDecl = that;
        try {
            super.visitClassDef(that);
        } finally {
            currentClassDecl = prev;
        }
    }
    
    public void visitJmlClassDecl(JmlClassDecl that) {
        // FIXME - do we do nothing with interfaces ?? At least translate the invariants etc.???
        if ((that.sym.flags() & Flags.INTERFACE) != 0) {
            result = that;
            return;
        }
//        if (that.name.toString().equals("TestJava")) {
//            System.out.println("TestJava");
//       }

        JCClassDecl prev = currentClassDecl;
        boolean prevSpecExpression = inSpecExpression;
        currentClassDecl = that;
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
            that.defs = newlist.toList();

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
                                that.defs.append(vv);
                            }
                        } else {
                            nlist.append(translate(d));
                        }
                    }
                    tspecs.clauses = nlist;
                }
            }

        } finally {
            result = that;
            currentClassDecl = prev;
            inSpecExpression = prevSpecExpression;
        }
    }

    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        System.out.println("CANT DO THIS");
    }

    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        visitDoLoop(that);
    }

    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        // FIXME - should not care which tool si being used (or explain)
        if (dorac) result = that;  // FIXME - trnaslate innards
        else result = translate(((JmlEnhancedForLoop)that).implementation);
        //visitForeachLoop(that);
    }

    public void visitJmlForLoop(JmlForLoop that) {
        visitForLoop(that);
    }

    public void visitJmlGroupName(JmlGroupName that) {
        result = that;
    }

    public void visitJmlImport(JmlImport that) {
        visitImport(that);
    }

    public void visitJmlLblExpression(JmlLblExpression that) {
        result = that;
    }

    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
        result = that;
    }

    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        that.expression = translate(that.expression);
        that.predicate = translate(that.predicate);
        result = that;
    }

    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        result = that;
    }

    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        that.expression = translate(that.expression);
        result = that;
    }

    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        result = that;
    }

    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly that) {
        result = that;
    }

    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        result = that;
    }
    
    JCMethodDecl currentMethodDecl = null;
    
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
//        if (that.name.toString().equals("m2")) {
//            System.out.println("ZZZ");
//        }
        visitMethodDef(that);

        boolean prevSpecExpression = inSpecExpression;
        inSpecExpression = true;
        JCMethodDecl prev = currentMethodDecl;
        currentMethodDecl = that;
        try {
            JmlMethodSpecs mspecs = that.methodSpecsCombined;
            ListBuffer<JmlSpecificationCase> newcases = new ListBuffer<JmlSpecificationCase>();
            if (mspecs != null) { // FIXME - why would this be null
                for (JmlSpecificationCase c: mspecs.cases) {
                    newcases.append(translate(c));
                }
                mspecs.cases = newcases.toList();
            }
        } finally {
            currentMethodDecl = prev;  // FIXME - finally?
            inSpecExpression = prevSpecExpression;
            result = that;
        }
    }

    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        // No translation of the method, just putting in checks on
        // the arguments.
        JmlToken t = that.token;
        JCExpression arg;
        if (t == null) {
            visitApply(that);
            return;
        }
        switch (t) {
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
//                translateTypelc(tree);
                break;
            
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
                Log.instance(context).error(that.pos, "jml.unknown.construct",t.internedName(),"JmlRac.visitApply");
            // FIXME - recovery possible?
                break;
        }
        result = that;
        return;
    }

//    @Override
//    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
//        // No overriding needed
//    }

    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        result = that;
    }

    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        result = that;
    }

    public void visitJmlRefines(JmlRefines that) {
        result = that;
    }

    public void visitJmlSetComprehension(JmlSetComprehension that) {
        result = that;
    }

//    @Override
//    public void visitJmlSingleton(JmlSingleton that) {
//        // No override needed
//    }

//    @Override
//    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
//        // No override needed
//    }

    public void visitJmlStatement(JmlStatement that) {
        boolean prev = inSpecExpression;
        inSpecExpression = true;
        switch (that.token) {
            case SET:
            case DEBUG: // FIXME - if turned on by options
                result = translate(that.statement);
                break;
                
            default:
                // FIXME - unimplemented
                result = that;
        }
        inSpecExpression = prev;
    }

    public void visitJmlStatementDecls(JmlStatementDecls that) {
        // Treat this just like a declaration
        // FIXME - is this still actually a list of declarations?
        boolean prev = inSpecExpression;
        inSpecExpression = true;
        List<JCStatement> list = expandableTranslate(that.list.toList());
        result = factory.at(that.pos).Block(0,list);
        inSpecExpression = prev;
    }

    public void visitJmlStatementExpr(JmlStatementExpr that) {
        boolean prev = inSpecExpression;
        inSpecExpression = true;
        if (that.token == JmlToken.UNREACHABLE) {
            // convert to assert
            JCExpression e = translate(that.optionalExpression);
            if (e == null) e = makeLiteral(false,that.pos);
            JmlStatementExpr r = factory.at(that.pos).JmlExpressionStatement(JmlToken.ASSERT,Label.UNREACHABLE,e);
            r.source = that.source;
            r.line = that.line;
            result = r;
        } else { // assert, assume
            that.expression = translate(that.expression);
            that.optionalExpression = translate(that.optionalExpression);
            result = that;
        }
        inSpecExpression = prev;
    }

    public void visitJmlStatementLoop(JmlStatementLoop that) {
        result = that;
    }

    public void visitJmlStatementSpec(JmlStatementSpec that) {
        result = that;
    }

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

//    @Override
//    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
//        // No overriding needed
//    }

//    @Override
//    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
//        // No overriding needed
//    }

//    @Override
//    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
//          // No overriding needed
//    }

//  @Override
//    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
//      // No overriding needed
//    }

    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        result = that;
    }

//    @Override
//    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
//        // No override needed
//    }

    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        result = that;
    }

//    @Override
//    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
//        // No override needed
//    }

//    @Override
//    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
//        // No override needed
//    }

    public void visitJmlVariableDecl(JmlVariableDecl that) {
        boolean prev = inSpecExpression;
        if (utils.isJML(that.mods)) inSpecExpression = true;
        visitVarDef(that);
        inSpecExpression = true;
        if (that.fieldSpecsCombined != null) translate(that.fieldSpecsCombined.list); // FIXME - check why this is sometimes null
        if (that.fieldSpecs != null) translate(that.fieldSpecs.list); // FIXME - check why this is sometimes null
        inSpecExpression = prev;
    }

    public void visitJmlWhileLoop(JmlWhileLoop that) {
        visitWhileLoop(that);
        // FIXME - translate specs
    }
}
