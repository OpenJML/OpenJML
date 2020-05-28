/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.code.Kinds.TYP;
import static com.sun.tools.javac.code.Kinds.VAL;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.requiresClauseKind;
import static org.jmlspecs.openjml.ext.RecommendsClause.*;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.DeferredAttr.DeferredType;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.Infer;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.Attr.ResultInfo;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;

/** This class handles expression extensions that take an argument list of JCExpressions.
 * Even if there are constraints on the number of arguments, it
 * is more robust to accept all of them and then issue an error in the typechecker
 * if the number of arguments is wrong.
 * 
 * @author David Cok
 *
 */// TODO: This extension is inappropriately named at present.  However, I expect that this 
// extension will be broken into individual extensions when type checking and
// RAC and ESC translation are added.
public class FunctionLikeExpressions extends ExpressionExtension {

    protected JmlTypes jmltypes;

    public FunctionLikeExpressions(Context context) {
        super(context);
        this.jmltypes = JmlTypes.instance(context);

    }

    @Override
    public void checkParse(JmlParser parser, JmlMethodInvocation e) {
        //        checkOneArg(parser,e);
    }

    public static final String elemtypeID = "\\elemtype";
    public static final IJmlClauseKind elemtypeKind = new IJmlClauseKind.FunctionLikeExpressionKind(elemtypeID) {

        @Override
        public Type typecheck(JmlAttr attr, JCTree tr, Env<AttrContext> localEnv) {
            JmlMethodInvocation tree = (JmlMethodInvocation)tr;
            ListBuffer<Type> argtypesBuf = new ListBuffer<>();
            attr.attribArgs(tree.args, localEnv, argtypesBuf);
            //attr.attribTypes(tree.typeargs, localEnv);
            int n = tree.args.size();
            if (n != 1) {  // FIXME _ incorrect for BSOLD
                error(tree.pos(),"jml.one.arg",keyword,n);
            }
            syms = Symtab.instance(context);
            Type t = syms.errType;
            if (n > 0) {
                Type tt = tree.args.get(0).type;
                if (tt == JmlTypes.instance(context).TYPE) {
                    t = JmlTypes.instance(context).TYPE;
                } else if (tree.args.get(0).type.tsym == syms.classType.tsym) {  // FIXME - syms.classType is a parameterized type which is not equal to the argumet (particularly coming from \\typeof - using tsym works, but we ought to figure this out
                    t = syms.classType;
                } else {
                    error(tree.args.get(0).pos(),"jml.elemtype.expects.classtype",tree.args.get(0).type.toString());
                    t = JmlTypes.instance(context).TYPE;
                }
            }
            return t;
        }

        @Override
        public void checkParse(JmlParser parser, JmlMethodInvocation e) {
            checkOneArg(parser,e);
        }
    };

    public static final String typeofID = "\\typeof";
    public static final IJmlClauseKind typeofKind = new IJmlClauseKind.FunctionLikeExpressionKind(typeofID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            JmlMethodInvocation tree = (JmlMethodInvocation)expr;
            ListBuffer<Type> argtypesBuf = new ListBuffer<>();
            attr.attribArgs(VAL, tree.args, localEnv, argtypesBuf);
            return JmlTypes.instance(context).TYPE;
        }

        @Override
        public void checkParse(JmlParser parser, JmlMethodInvocation e) {
            checkOneArg(parser,e);
        }        
    };

    public static final String distinctID = "\\distinct";
    public static final IJmlClauseKind distinctKind = new IJmlClauseKind.FunctionLikeExpressionKind(distinctID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            // The result is boolean.
            // Case 1) All types are reference types
            // Case 2) Some or all are primitive - all must be convertible to
            // a common primitive type, including through unboxing
            Types types = JmlTypes.instance(attr.context);
            JmlMethodInvocation tree = (JmlMethodInvocation)expr;
            ListBuffer<Type> argtypesBuf = new ListBuffer<>();
            attr.attribArgs(VAL, tree.args, localEnv, argtypesBuf);

            boolean anyPrimitive = false;
            Type maxPrimitiveType = null;
            for (JCExpression arg : tree.args) {
                Type tt = arg.type;
                if (tt.isErroneous()) continue;
                if (tt.isPrimitive()) {
                    anyPrimitive = true;
                }
            }
            if (anyPrimitive) for (JCExpression arg : tree.args) {
                Type tt = arg.type;
                if (tt.isErroneous()) { continue; }
                if (!tt.isPrimitive()) tt = types.unboxedType(tt);
                if (tt.getTag() == TypeTag.VOID) {
                    // FIXME -error
                } else if (maxPrimitiveType == null) {
                    maxPrimitiveType = tt;
                } else if (types.isConvertible(tt,maxPrimitiveType)) {
                    // OK
                } else if (types.isConvertible(maxPrimitiveType, tt)) {
                    maxPrimitiveType = tt;
                } else {
                    // FIXME - error
                }
            }
            if (anyPrimitive) {
                for (JCExpression arg : tree.args) {
                    Type tt = arg.type;
                    if (tt.isErroneous()) continue;
                    if (!tt.isPrimitive()) tt = types.unboxedType(tt);
                    if (!types.isConvertible(tt,maxPrimitiveType)) {
                        // FIXME - ERROR
                    }
                }
            }
            return Symtab.instance(attr.context).booleanType;
        }

        @Override
        public void checkParse(JmlParser parser, JmlMethodInvocation e) {
            checkNumberArgs(parser,e, (n)->(n>0), "jml.message", "A \\distinct expression must have some arguments");
        }        
    };

    public static final String isInitializedID = "\\isInitialized";
    public static final IJmlClauseKind isInitializedKind = new IJmlClauseKind.FunctionLikeExpressionKind(isInitializedID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            // The argument is a type that is a reference type; the result is boolean
            // The argument may contain JML constructs
            JmlMethodInvocation tree = (JmlMethodInvocation)expr;
            attr.attribTypes(tree.typeargs, localEnv);
            for (JCExpression arg: tree.args) {
                Type argtype = attr.attribExpr(arg, localEnv);
                if (!argtype.isNullOrReference() && !argtype.isErroneous()) {
                    log.error(arg.pos(),"jml.ref.arg.required",keyword);
                }
            }
            return syms.booleanType;
        }

        @Override
        public void checkParse(JmlParser parser, JmlMethodInvocation e) {
            checkOneArg(parser,e);
        }        
    };

    public static class OneArgExpression extends IJmlClauseKind.FunctionLikeExpressionKind {
        public OneArgExpression(String name) { super(name); }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            JmlMethodInvocation tree = (JmlMethodInvocation)expr;
            typecheckHelper(attr, tree.args, localEnv);
            return tree.args.head.type;
        }

        @Override
        public void checkParse(JmlParser parser, JmlMethodInvocation e) {
            checkOneArg(parser,e);
        }        
    };

    public static class AnyArgExpressions extends IJmlClauseKind.FunctionLikeExpressionKind {
        public AnyArgExpressions(String name) { super(name); }
        
        // Unless overridden this returns the type of the first argument as the expression type
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            JmlMethodInvocation tree = (JmlMethodInvocation)expr;
            ListBuffer<Type> argtypes = new ListBuffer<>();
            attr.attribArgs(tree.args, localEnv, argtypes);
            com.sun.tools.javac.util.List<Type> typeargtypes = attr.attribTypes(tree.typeargs, localEnv);
            return tree.args.head != null ? argtypes.first() : null;
        }

        @Override
        public void checkParse(JmlParser parser, JmlMethodInvocation e) {
        }        
    };
    
    public static class AnyArgBooleanExpressions extends AnyArgExpressions {
        public AnyArgBooleanExpressions(String name) { super(name); }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            super.typecheck(attr, expr, localEnv);
            return Symtab.instance(context).booleanType;
        }
    }

    public static final String javaMathID = "\\java_math";
    public static final IJmlClauseKind javaMathKind = new OneArgExpression(javaMathID);
    public static final String safeMathID = "\\safe_math";
    public static final IJmlClauseKind safeMathKind = new OneArgExpression(safeMathID);
    public static final String bigintMathID = "\\bigint_math";
    public static final IJmlClauseKind bigintMathKind = new OneArgExpression(bigintMathID);

    public static final String warnopID = "\\warnop";
    public static final IJmlClauseKind warnopKind = new OneArgExpression(warnopID);
    public static final String nowarnopID = "\\nowarnop";
    public static final IJmlClauseKind nowarnopKind = new OneArgExpression(nowarnopID);
    public static final String warnID = "\\warn";
    public static final IJmlClauseKind warnKind = new OneArgExpression(warnID);
    public static final String nowarnID = "\\nowarn";
    public static final IJmlClauseKind nowarnKind = new OneArgExpression(nowarnID);

    public static final String notModifiedID = "\\not_modified";
    public static final IJmlClauseKind notModifiedKind = new AnyArgBooleanExpressions(notModifiedID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            super.typecheck(attr, tree, localEnv);
            if (!attr.postClauses.contains(attr.currentClauseType)) {
                JmlMethodInvocation expr = (JmlMethodInvocation)tree;
                log.error(tree.pos, "jml.misplaced.token", expr.kind != null ? expr.kind.name() : expr.token.internedName(), attr.currentClauseType == null ? "jml declaration" : attr.currentClauseType.name());
            }
            return Symtab.instance(context).booleanType;
        }
    };
    
    public static final String concatID = "\\concat";
    public static final IJmlClauseKind concatKind = new AnyArgExpressions(concatID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            super.typecheck(attr, tree, localEnv);
            Type stringType = attr.syms.stringType;
            for (JCExpression e: ((JmlMethodInvocation)tree).args) {
                if (!(attr.jmltypes.isSameType(e.type, stringType))) {
                    attr.log.error(e.pos, "jml.message", "The arguments of \\concat must have type String, not " + e.type);
                }
            }
            return stringType;
        }
    };
    
    public static final String erasureID = "\\erasure";
    public static final IJmlClauseKind erasureKind = new OneArgExpression(erasureID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            JmlMethodInvocation tree = (JmlMethodInvocation)expr;
            
            // Expect one argument of any array type, result type is \TYPE
            // The argument expression may contain JML constructs
            int n = tree.args.size();
            if (n != 1) {
                error(tree.pos(),"jml.one.arg",name(),n);
            } else {
                JCExpression e = tree.args.get(0);
                if (e instanceof JmlMethodInvocation && ((JmlMethodInvocation)e).kind == MiscExpressions.typelcKind) {
                    ((JmlMethodInvocation)e).javaType = true;
                }
            }
            ListBuffer<Type> argtypesBuf = new ListBuffer<>();
            attr.attribArgs(tree.args, localEnv, argtypesBuf);
            Type t = attr.syms.errType;
            if (n > 0) {
                Type tt = tree.args.get(0).type;
                if (tt == attr.jmltypes.TYPE || tt == attr.syms.classType) t = attr.syms.classType; 
            }
            return t;
        }
    };
    
    public static final String invariantForID = "\\invariant_for";
    public static final IJmlClauseKind invariantForKind = new AnyArgBooleanExpressions(invariantForID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            JmlMethodInvocation expr = (JmlMethodInvocation)tree;
            int n = expr.args.size();
            if (n != 1 && requireStrictJML()) {
                Log.instance(context).error(tree.pos(), "jml.one.arg", name(), n);
            }
            for (JCExpression arg: expr.args) {
                attr.attribTree(arg, localEnv, attr.new ResultInfo(TYP|VAL, Infer.anyPoly));
                if (arg.type.isPrimitive()) {
                    Log.instance(context).error(arg.pos(),"jml.ref.arg.required",name());
                } else if (requireStrictJML() && attr.treeutils.isATypeTree(arg)) {
                    Log.instance(context).error(arg.pos(),"jml.ref.arg.required",name());
                }
            }
            return Symtab.instance(context).booleanType;
        }
    };
    
    public static final String nonnullelementsID = "\\nonnullelements";
    public static final IJmlClauseKind nonnullelementsKind = new AnyArgBooleanExpressions(nonnullelementsID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            JmlMethodInvocation expr = (JmlMethodInvocation)tree;
            super.typecheck(attr, expr, localEnv);
            if (expr.args.size() != 1 && requireStrictJML()) Log.instance(context).error(tree.pos(),"jml.one.arg",name(),expr.args.size());
            for (JCExpression arg: expr.args) {
                Type argtype = arg.type;
                // FIXME - argtype is null when there is a DeferredType, in which case no checking is done
                if (argtype != null && !(argtype instanceof Type.ArrayType) && !argtype.isErroneous()) {
                    Log.instance(context).error(arg.pos(),"jml.arraytype.required",name(),argtype.toString(),arg.toString());
                }
            }
            return attr.syms.booleanType;
        }
    };
    
    public static final String spaceID = "\\space";
    public static final IJmlClauseKind spaceKind = new OneArgExpression(spaceID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            // The argument may be a JML spec-expression
            // Expects one argument of reference type; result is of type long
            // FIXME - there is no check that the argument is of reference type - can't this apply to primitives as well?
            JmlMethodInvocation expr = (JmlMethodInvocation)tree;
            super.typecheck(attr, expr, localEnv);
            return attr.syms.longType;
        }
    };
    
    public static final String workingspaceID = "\\working_space";
    public static final IJmlClauseKind workingspaceKind = new OneArgExpression(workingspaceID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            // The argument must be a Java expression
            // Expects one argument that is an arbitrary expression; result is of type long
            // Note: The JML reference manual puts constraints on the form of the expression; those seem to be unneeded
            // Note also: the argument is not actually evaluated (but needs to be evaluatable), 
            //   thus it may only contain Java constructs  (FIXME - there is no check on that)
            JmlMethodInvocation expr = (JmlMethodInvocation)tree;
            super.typecheck(attr, expr, localEnv);
            return attr.syms.longType;
        }
    };
    
    public static final String durationID = "\\duration";
    public static final IJmlClauseKind durationKind = new OneArgExpression(durationID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            // The argument must be a Java expression
            // Expects one argument that is an arbitrary expression; result is of type long
            // Note: The JML reference manual puts constraints on the form of the expression; those seem to be unneeded
            // Note also: the argument is not actually evaluated (but needs to be evaluatable), 
            //   thus it may only contain Java constructs  (FIXME - there is no check on that)
            JmlMethodInvocation expr = (JmlMethodInvocation)tree;
            super.typecheck(attr, expr, localEnv);
            return attr.syms.longType;
        }
    };
    
    // FIXME - reach should allow primaryTrailers
    public static final String reachID = "\\reach";
    public static final IJmlClauseKind reachKind = new OneArgExpression(reachID) {
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            super.typecheck(attr,tree,localEnv);
            return attr.JMLSetType;
        }
    };
    
    public static final String sameID = "\\same";
    public static final IJmlClauseKind sameKind = new OneArgExpression(sameID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            if (attr.currentClauseType != requiresClauseKind &&
                    attr.currentClauseType != recommendsClauseKind) {
                Log.instance(context).error(((JmlSingleton)that).pos,"jml.misplaced.same");
            }
            return Symtab.instance(context).booleanType;
        }
    };
    
    public static final String keyID = "\\key";
    public static final IJmlClauseKind keyKind = new AnyArgBooleanExpressions(keyID) {
        
        @Override
        public JCExpression parse(JCModifiers mods, String name, IJmlClauseKind kind, JmlParser parser) {
            int pos = parser.pos();
            JmlMethodInvocation expr = (JmlMethodInvocation)super.parse(mods, name, kind, parser);
            boolean value = true;
            for (JCExpression arg: expr.args) {
                if (arg instanceof JCLiteral) {
                    String key = ((JCLiteral)arg).getValue().toString();
                    value = value && Utils.instance(context).commentKeys.contains(key);
                } else if (arg instanceof JCIdent) {
                    String key = ((JCIdent)arg).name.toString();
                    value = value && Utils.instance(context).commentKeys.contains(key);
                } else {
                    error(arg.pos(), "jml.message", "An argument to \\key must be an identifier or a string literal");
                    return parser.maker().at(pos).Erroneous();
                }
            }
            return parser.maker().at(pos).Literal(value);
        }
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            attr.log.error(that.pos, "jml.message", "INTERNAL ERROR: keyKind.typecheck should not be called");
            return attr.syms.booleanType;
        }
    };
    


    public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> localEnv) {
        //        JmlMethodInvocation tree = (JmlMethodInvocation)expr;
        //        JmlTokenKind token = tree.token;
        //        
        //        switch (token) {
        //            case BSELEMTYPE:
        //                // Expect one argument of any array type, result type is \TYPE
        //                // The argument expression may contain JML constructs
        //                ListBuffer<Type> argtypesBuf = new ListBuffer<>();
        //                attr.attribArgs(tree.args, localEnv, argtypesBuf);
        //                //attr.attribTypes(tree.typeargs, localEnv);
        //                int n = tree.args.size();
        //                if (n != 1) {  // FIXME _ incorrect for BSOLD
        //                    error(tree.pos(),"jml.one.arg",token.internedName(),n);
        //                }
        //                Type t = syms.errType;
        //                if (n > 0) {
        //                    Type tt = tree.args.get(0).type;
        //                    if (tt == jmltypes.TYPE) {
        //                        t = jmltypes.TYPE;
        //                    } else if (tree.args.get(0).type.tsym == syms.classType.tsym) {  // FIXME - syms.classType is a parameterized type which is not equal to the argumet (particularly coming from \\typeof - using tsym works, but we ought to figure this out
        //                        t = syms.classType;
        //                    } else {
        //                        error(tree.args.get(0).pos(),"jml.elemtype.expects.classtype",tree.args.get(0).type.toString());
        //                        t = jmltypes.TYPE;
        //                    }
        //                }
        //                return t;
        //            case BSPOST:
        //                // FIXME - need to check types
        //                return syms.booleanType;
        //            default:
        //                error(tree.pos(), "jml.error", "Unimplemented backslash token type in ElemType.typecheck: " + token);
        //                return null;
        return null;
    }
}

