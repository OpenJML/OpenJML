/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.code.Kinds.*;
import static com.sun.tools.javac.code.Kinds.KindSelector.*;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.requiresClauseKind;
import static org.jmlspecs.openjml.ext.RecommendsClause.*;
import static com.sun.tools.javac.parser.Tokens.TokenKind;
import static com.sun.tools.javac.parser.Tokens.TokenKind.LPAREN;
import static com.sun.tools.javac.parser.Tokens.TokenKind.RPAREN;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlOptions;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.Infer;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCErroneous;
import com.sun.tools.javac.util.*;

public class FunctionLikeExpressions extends JmlExtension {

    public static final String elemtypeID = "\\elemtype";
    public static final IJmlClauseKind elemtypeKind = new IJmlClauseKind.FunctionLikeExpressionKind(elemtypeID) {

        @Override
        public Type typecheck(JmlAttr attr, JCTree tr, Env<AttrContext> localEnv) {
            var TYPE = JmlPrimitiveTypes.TYPETypeKind.getType(attr.context);
            JmlMethodInvocation tree = (JmlMethodInvocation)tr;
            int n = tree.args.size();
            if (n != 1) {
                error(tree.pos(),"jml.one.arg",keyword,n);
            }
            Type t = attr.syms.errType;
            if (n > 0) {
            	for (var arg: tree.args) arg.type = attr.attribExpr(arg, localEnv, Type.noType);
                Type tt = tree.args.get(0).type;
            	if (tt == null) {
                	System.out.println("NULLTYPE - Unexpected null type in \\elemtype");
                } else if (tt.isErroneous()) {
                	t = tt;
                } else if (tt == TYPE) {
                    t = tt;
                } else if (tt.tsym == attr.syms.classType.tsym) {  // FIXME - syms.classType is a parameterized type which is not equal to the argumet (particularly coming from \\typeof - using tsym works, but we ought to figure this out
                    t = attr.syms.classType;
                } else {
                    error(tree.args.get(0).pos(),"jml.elemtype.expects.classtype",tt.toString());
                    t = TYPE;
                }
            }
            tree.type = t;
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
        	typecheckHelper(attr, tree.args, localEnv);
            var TYPE = JmlPrimitiveTypes.TYPETypeKind.getType(attr.context);
            expr.type = TYPE;
            return expr.type;
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
                    error(arg.pos(),"jml.ref.arg.required",keyword);
                }
            }
            return attr.syms.booleanType;
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
            int n = tree.args.size();
            if (n != 1) {
                error(tree.pos(),"jml.one.arg",keyword(),n);
            }
            if (!typecheckHelper(attr, tree.args, localEnv)) {
                expr.type = attr.syms.errType;
                return expr.type;
            }
            return tree.args.head.type;
        }

        @Override
        public void checkParse(JmlParser parser, JmlMethodInvocation e) {
            checkOneArg(parser,e);
        }        
    };

    public static class NArgExpression extends IJmlClauseKind.FunctionLikeExpressionKind {
        protected int numargs;
        public NArgExpression(String name, int numargs) { super(name); this.numargs = numargs; }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            JmlMethodInvocation tree = (JmlMethodInvocation)expr;
            int n = tree.args.size();
            if (n != numargs) {
                error(tree.pos(),"jml.message","a " + keyword() + " expression expects " + this.numargs + " arguments, not " + n); // FIXME - wrong message
            }
            if (!typecheckHelper(attr, tree.args, localEnv)) {
                expr.type = attr.syms.errType;
                return expr.type;
            }
            return tree.args.head.type;
        }

        @Override
        public void checkParse(JmlParser parser, JmlMethodInvocation e) {
            checkNumberArgs(parser,e, (n)->(n==numargs), "jml.message", "a " + keyword() + "expression expectts " + numargs + " arguments");
        }        
    };

    public static class AnyArgExpression extends IJmlClauseKind.FunctionLikeExpressionKind {
        public AnyArgExpression(String name) { super(name); }
        
        // Unless overridden this returns the type of the first argument as the expression type
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            JmlMethodInvocation tree = (JmlMethodInvocation)expr;
            if (!typecheckHelper(attr, tree.args, localEnv)) {
                expr.type = attr.syms.errType;
                return expr.type;
            }
            return tree.args.head != null ? tree.args.head.type : null;
        }

        @Override
        public void checkParse(JmlParser parser, JmlMethodInvocation e) {
        }        
    };
    
    public static class AnyArgBooleanExpression extends AnyArgExpression {
        public AnyArgBooleanExpression(String name) { super(name); }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            super.typecheck(attr, expr, localEnv);
            return attr.syms.booleanType;
        }
    }

    public static class TypeArgBooleanExpression extends AnyArgExpression {
        public TypeArgBooleanExpression(String name) { super(name); }
        
        @Override
        public JCExpression parse(JCModifiers mods, String keyword, IJmlClauseKind clauseKind, JmlParser parser) {
            init(parser);
            int start = parser.pos();
            parser.nextToken();
            int paren = parser.pos();
            if (parser.token().kind != LPAREN) {
                return parser.syntaxError(paren, List.<JCTree> nil(),
                        "jml.args.required", this.keyword());
            } else {
                parser.nextToken();
            	var args = parser.parseTypeList();
            	JmlMethodInvocation ee = toP(parser.maker().at(paren).JmlMethodInvocation(clauseKind, args));
            	ee.startpos = start;
                if (parser.token().kind != RPAREN) {
                	log.error(parser.pos(), "jml.message", "Expected a closing right parenthesis");
                } else {
                    parser.nextToken();
                }
            	return ee;
            }
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            super.typecheck(attr, expr, localEnv);
            return attr.syms.booleanType;
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
    public static final String bsnowarnID = "\\nowarn";
    public static final IJmlClauseKind nowarnKind = new OneArgExpression(bsnowarnID);

    public static final String notModifiedID = "\\not_modified";
    public static final IJmlClauseKind notModifiedKind = new AnyArgBooleanExpression(notModifiedID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            super.typecheck(attr, tree, localEnv);
            if (!attr.postClauses.contains(attr.jmlenv.currentClauseKind)) {
                JmlMethodInvocation expr = (JmlMethodInvocation)tree;
                log.error(tree.pos, "jml.misplaced.token", expr.kind != null ? expr.kind.keyword() : "?", attr.jmlenv.currentClauseKind == null ? "jml declaration" : attr.jmlenv.currentClauseKind.keyword());
            }
            return attr.syms.booleanType;
        }
    };
    
    public static final String concatID = "\\concat";
    public static final IJmlClauseKind concatKind = new AnyArgExpression(concatID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            super.typecheck(attr, tree, localEnv);
            Type stringType = attr.syms.stringType;
            for (JCExpression e: ((JmlMethodInvocation)tree).args) {
                if (!(attr.jmltypes.isSameType(e.type, stringType))) {
                    utils.error(e.pos, "jml.message", "The arguments of \\concat must have type String, not " + e.type);
                }
            }
            return stringType;
        }
    };
    
    public static final String erasureID = "\\erasure";
    public static final IJmlClauseKind erasureKind = new OneArgExpression(erasureID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            super.typecheck(attr, expr, localEnv);
            JmlMethodInvocation meth = (JmlMethodInvocation)expr;
            
            // The argument expression may contain JML constructs
            Type t = attr.syms.errType;
            int n = meth.args.size();
            if (n > 0) {
                JCExpression e = meth.args.get(0);
                if (meth.kind == MiscExpressions.typelcKind) {
                    ((JmlMethodInvocation)e).javaType = true;
                    ((JmlMethodInvocation)e).type = attr.syms.classType;
                }
                Type tt = meth.args.get(0).type;
                var TYPE = JmlPrimitiveTypes.TYPETypeKind.getType(attr.context);
                if (tt == TYPE || tt == attr.syms.classType) t = attr.syms.classType; 
            }
            return t;
        }
    };
    
    public static final String typeargID = "\\typearg";
    public static final IJmlClauseKind typeargKind = new NArgExpression(typeargID, 2) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            Type err = attr.syms.errType;
            if (super.typecheck(attr, expr, localEnv) == err) {
                return err;
            }
            JmlMethodInvocation meth = (JmlMethodInvocation)expr;
            meth.type = err;
            
            var TYPE = JmlPrimitiveTypes.TYPETypeKind.getType(attr.context);
            var arg1 = meth.args.head;
            if (!Types.instance(attr.context).isSameType(arg1.type, TYPE)) {
                utils.error(arg1, "jml.message", "first argument must have type \\TYPE, not " +arg1.type);
                return err;
            }
            var arg2 = meth.args.tail.head;
            if (!Types.instance(attr.context).isSameType(arg2.type, attr.syms.intType)) {
                utils.error(arg2, "jml.message", "second argument muat have type int, not " + arg2.type);
                return err;
            }
            meth.type = TYPE;
            return TYPE;
        }
    };
    
    public static final String typearg0ID = "\\typearg0";
    public static final IJmlClauseKind typearg0Kind = new OneArgExpression(typearg0ID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            Type err = attr.syms.errType;
            if (super.typecheck(attr, expr, localEnv) == err) {
                return err;
            }
            JmlMethodInvocation meth = (JmlMethodInvocation)expr;
            meth.type = err;
            
            var TYPE = JmlPrimitiveTypes.TYPETypeKind.getType(attr.context);
            var arg1 = meth.args.head;
            if (!Types.instance(attr.context).isSameType(arg1.type, TYPE)) {
                utils.error(arg1, "jml.message", "the argument must have type \\TYPE, not " +arg1.type);
                return err;
            }
            meth.type = TYPE;
            return TYPE;
        }
    };
    
    public static final String invariantForID = "\\invariant_for";
    public static final IJmlClauseKind invariantForKind = new AnyArgBooleanExpression(invariantForID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            JmlMethodInvocation expr = (JmlMethodInvocation)tree;
            int n = expr.args.size();
            if (n != 1 && requireStrictJML()) {
                error(tree.pos(), "jml.one.arg", keyword(), n);
            }
            for (JCExpression arg: expr.args) {
                attr.attribTree(arg, localEnv, attr.new ResultInfo(KindSelector.of(TYP,VAL), Infer.anyPoly));
                if (arg.type.isPrimitive()) {
                    error(arg.pos(),"jml.ref.arg.required",keyword());
                } else if (requireStrictJML() && attr.treeutils.isATypeTree(arg)) {
                    error(arg.pos(),"jml.ref.arg.required",keyword());
                }
            }
            return attr.syms.booleanType;
        }
        @Override public JCExpression assertionConversion(JmlAssertionAdder aa, JCExpression expr) {
            JmlMethodInvocation that = (JmlMethodInvocation)expr;
			JCExpression res = null;
			for (JCExpression arg : that.args) {
				JCExpression a = aa.treeutils.isATypeTree(arg) ? null
						: aa.convertJML(arg, aa.treeutils.trueLit, false);
				JCExpression e = aa.getInvariantAll(that, arg.type, a, true);
				res = e == null ? res : res == null ? e : aa.treeutils.makeAnd(that, res, e);
			}
			if (res == null) res = aa.treeutils.trueLit;
        	return res;
        }
    };
    
    public static final String staticInvariantForID = "\\static_invariant_for";
    public static final IJmlClauseKind staticInvariantForKind = new TypeArgBooleanExpression(staticInvariantForID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            JmlMethodInvocation expr = (JmlMethodInvocation)tree;
            int n = expr.args.size();
            if (n != 1 && requireStrictJML()) {
                error(tree.pos(), "jml.one.arg", staticInvariantForID, n);
            }
            localEnv = attr.addStatic(localEnv);
            for (JCExpression arg: expr.args) {
                attr.attribTree(arg, localEnv, attr.new ResultInfo(KindSelector.of(TYP), Infer.anyPoly));
                if (utils.isJavaOrJmlPrimitiveType(arg.type)) {
                    error(arg.pos(),"jml.ref.type.required",keyword(),arg.type);
                }
            }
            localEnv = attr.removeStatic(localEnv);
            return attr.syms.booleanType;
        }
        @Override public JCExpression assertionConversion(JmlAssertionAdder aa, JCExpression expr) {
            JmlMethodInvocation that = (JmlMethodInvocation)expr;
 			JCExpression res = null;
 			for (JCExpression arg : that.args) {
 				JCExpression e = aa.getInvariant(that, arg.type, arg.type, null, false);
 				res = e == null ? res : res == null ? e : aa.treeutils.makeAnd(that, res, e);
 			}
 			if (res == null) res = aa.treeutils.trueLit;
         	return res;
         }
    };
    
    public static final String nonnullelementsID = "\\nonnullelements";
    public static final IJmlClauseKind nonnullelementsKind = new AnyArgBooleanExpression(nonnullelementsID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            JmlMethodInvocation expr = (JmlMethodInvocation)tree;
            super.typecheck(attr, expr, localEnv);
            if (expr.args.size() != 1 && requireStrictJML()) error(tree,"jml.one.arg",keyword(),expr.args.size());
            for (JCExpression arg: expr.args) {
                Type argtype = arg.type;
                if (argtype == null || argtype.isErroneous()) {
                    // Already reported as an error
                } else if (argtype instanceof Type.ArrayType) {
                    // OK - standard array type
                } else if (JmlTypes.instance(attr.context).isSubtype(argtype, attr.syms.iterableType)) {
                    // OK - is a Java collection
                } else {
                    String s = argtype.toString(); // FIXME - check that elemtype is actually nullable
                    // FIXME - find a better way to do these tests
                    if (s.startsWith("\\seq")) {
                    } else if (s.startsWith("\\array")) { // FIXME - are we keeping array?
                    } else if (s.startsWith("\\set")) {
                    } else if (s.startsWith("\\map")) {
                    } else {
                        error(arg,"jml.arraytype.required",keyword(),argtype.toString(),arg.toString());
                    }
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
            if (attr.jmlenv.currentClauseKind != requiresClauseKind &&
                    attr.jmlenv.currentClauseKind != recommendsClauseKind) {
                error(that,"jml.misplaced.same");
            }
            return attr.syms.booleanType;
        }
    };
    
    public static final String keyID = "\\key";
    public static final IJmlClauseKind keyKind = new AnyArgBooleanExpression(keyID) {
        
        @Override
        public JCExpression parse(JCModifiers mods, String name, IJmlClauseKind kind, JmlParser parser) {
            int pos = parser.pos();
            JmlMethodInvocation expr = (JmlMethodInvocation)super.parse(mods, name, kind, parser);
            boolean value = true;
            for (JCExpression arg: expr.args) {
                if (arg instanceof JCLiteral) {
                    String key = ((JCLiteral)arg).getValue().toString();
                    value = value && JmlOptions.instance(parser.context).commentKeys.contains(key);
                } else if (arg instanceof JCIdent) {
                    String key = ((JCIdent)arg).name.toString();
                    value = value && JmlOptions.instance(parser.context).commentKeys.contains(key);
                } else {
                    utils.error(arg, "jml.message", "An argument to \\key must be an identifier or a string literal");
                    return parser.maker().at(pos).Erroneous();
                }
            }
            return parser.maker().at(pos).Literal(value);
        }
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            utils.error(that.pos, "jml.message", "INTERNAL ERROR: keyKind.typecheck should not be called");
            return attr.syms.booleanType;
        }
    };
}

