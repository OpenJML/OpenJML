/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.code.Kinds.TYP;
import static com.sun.tools.javac.code.Kinds.VAL;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.Attr.ResultInfo;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;

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
public class Elemtype extends ExpressionExtension {

    protected JmlTypes jmltypes;

    public Elemtype(Context context) {
        super(context);
        this.jmltypes = JmlTypes.instance(context);

    }

    static public JmlTokenKind[] tokens() { return new JmlTokenKind[]{
            JmlTokenKind.BSELEMTYPE, JmlTokenKind.BSTYPEOF,
            JmlTokenKind.BSOLD, JmlTokenKind.BSPAST, JmlTokenKind.BSPRE, JmlTokenKind.BSNOWARN, JmlTokenKind.BSNOWARNOP,
            JmlTokenKind.BSPOST, JmlTokenKind.BSASSIGNS,
            JmlTokenKind.BSWARN, JmlTokenKind.BSWARNOP,
            JmlTokenKind.BSBIGINT_MATH, JmlTokenKind.BSSAFEMATH, JmlTokenKind.BSJAVAMATH
    }; }

    @Override
    public IJmlClauseKind[]  clauseTypesA() { return clauseTypes(); }
    public static IJmlClauseKind[] clauseTypes() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public void checkParse(JmlParser parser, JmlMethodInvocation e) {
        //        checkOneArg(parser,e);
    }

    public static final IJmlClauseKind elemtypeKind = new IJmlClauseKind.FunctionLikeExpression("\\elemtype") {

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

    public static final IJmlClauseKind typeofKind = new IJmlClauseKind.FunctionLikeExpression("\\typeof") {
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

    public static final IJmlClauseKind distinctKind = new IJmlClauseKind.FunctionLikeExpression("\\distinct") {
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            // The result is boolean.
            // Case 1) All types are reference types
            // Case 2) Some or all are primitive - all must be convertible to
            // a common primitive type, including through unboxing
            Types types = JmlTypes.instance(context);
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
            return Symtab.instance(context).booleanType;
        }

        @Override
        public void checkParse(JmlParser parser, JmlMethodInvocation e) {
            checkNumberArgs(parser,e, (n)->(n>0), "jml.message", "A \\distinct expression must have some arguments");
        }        
    };

//    public static final IJmlClauseKind typelcKind = new IJmlClauseKind.FunctionLikeExpression("\\type") {
//        @Override
//        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
//            // Takes one argument which is a type (not an expression); the result is of type \TYPE
//            // The argument may contain JML constructs
//            JmlMethodInvocation tree = (JmlMethodInvocation)expr;
//            attr.attribTypes(tree.typeargs, localEnv);
//            int n = tree.args.size();
//            if (n != 1) {
//                log.error(tree,"jml.one.arg",keyword,n);
//            }
//            if (n > 0) {
//                JCExpression arg = tree.args.get(0);
//                attr.attribTree(arg, localEnv, attr.new ResultInfo(TYP, Type.noType));
//                if (!tree.javaType && arg.type.tsym.getTypeParameters().size() > 0 &&
//                        !arg.type.isParameterized()) {
//                    log.error(tree,"jml.invalid.erasedtype",JmlPretty.write(arg));
//                }
//                if (!tree.javaType) attr.checkForWildcards(arg,arg);
//            }
//            Type t = JmlTypes.instance(context).TYPE;
//            if (tree.javaType) t = syms.classType;
//            attr.addTodo(attr.utilsClass);
//            return t;
//        }
//
//        @Override
//        public void checkParse(JmlParser parser, JmlMethodInvocation e) {
//            checkOneArg(parser,e);
//        }        
//    };


    public static final IJmlClauseKind isInitializedKind = new IJmlClauseKind.FunctionLikeExpression("\\isInitialized") {
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

    public static class MathExpressions extends IJmlClauseKind.FunctionLikeExpression {
        public MathExpressions(String name) { super(name); }
        
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

    public static class AnyArgExpressions extends IJmlClauseKind.FunctionLikeExpression {
        public AnyArgExpressions(String name) { super(name); }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            JmlMethodInvocation tree = (JmlMethodInvocation)expr;
            attr.attribTypes(tree.typeargs, localEnv);
            return tree.args.head.type;
        }

        @Override
        public void checkParse(JmlParser parser, JmlMethodInvocation e) {
        }        
    };

    public static final IJmlClauseKind javaMathKind = new MathExpressions("\\safe_math");

    public static final IJmlClauseKind safeMathKind = new MathExpressions("\\safe_math");

    public static final IJmlClauseKind bigintMathKind = new MathExpressions("\\bigint_math");
    public static final IJmlClauseKind warnopKind = new MathExpressions("\\bigint_math");
    public static final IJmlClauseKind nowarnopKind = new MathExpressions("\\bigint_math");
    public static final IJmlClauseKind warnKind = new MathExpressions("\\bigint_math");
    public static final IJmlClauseKind nowarnKind = new MathExpressions("\\bigint_math");

    public static final IJmlClauseKind notModifiedKind = new AnyArgExpressions("\\not_modified") {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            super.typecheck(attr, expr, localEnv);
            return Symtab.instance(context).booleanType;
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

