/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.code.Kinds.TYP;
import static com.sun.tools.javac.code.Kinds.VAL;
import static com.sun.tools.javac.parser.Tokens.TokenKind.LPAREN;
import static com.sun.tools.javac.parser.Tokens.TokenKind.RPAREN;
import static com.sun.tools.javac.parser.Tokens.TokenKind.VOID;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlExpression;
import org.jmlspecs.openjml.JmlTree.JmlLblExpression;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.ext.FunctionLikeExpressions.AnyArgBooleanExpressions;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.Infer;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.Attr.ResultInfo;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCErroneous;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

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
public class MiscExpressions extends ExpressionExtension {

    public MiscExpressions(Context context) {
        super(context);
    }

    @Override
    public void checkParse(JmlParser parser, JmlMethodInvocation e) {
        //        checkOneArg(parser,e);
    }

    public static final String typelcID = "\\type";
    public static final IJmlClauseKind typelcKind = new IJmlClauseKind.ExpressionKind(typelcID) {

        @Override
        public JCExpression parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            int start = parser.pos();
            parser.nextToken();
            int p = parser.pos();
            if (parser.token().kind != LPAREN) {
                return parser.syntaxError(p, List.<JCTree> nil(),
                        "jml.args.required", this.name());
            } else {
                parser.accept(TokenKind.LPAREN);
                JCExpression e;
                if (parser.token().kind == VOID) {
                    e = parser.to(parser.maker().at(parser.pos()).TypeIdent(TypeTag.VOID));
                    parser.nextToken();
                } else {
                    e = parser.parseType(); // FIXME - does not parseType() parse a void?
                }
                if (parser.token().kind != RPAREN) {
                    if (!(e instanceof JCErroneous))
                        parser.jmlerror(parser.pos(), parser.endPos(),
                                "jml.bad.bstype.expr");
                    parser.skipThroughRightParen();
                } else
                    parser.nextToken();
                // FIXME - this should be a type literal
                JmlMethodInvocation ee = toP(parser.maker().at(p).JmlMethodInvocation(typelcKind, List.of(e)));
                ee.startpos = start;
                return parser.primaryTrailers(ee, null);
            }
        }
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            JmlMethodInvocation expr = (JmlMethodInvocation)tree;    
            // Takes one argument which is a type (not an expression); the result is of type \TYPE
            // The argument may contain JML constructs
            int n = expr.args.size();
            if (n != 1) {
                attr.log.error(tree,"jml.one.arg",name(),n);
            }
            if (n > 0) {
                JCExpression arg = expr.args.get(0);
                attr.attribTree(arg, localEnv, attr.new ResultInfo(TYP, Type.noType));
                if (!expr.javaType && arg.type.tsym.getTypeParameters().size() > 0 &&
                        !arg.type.isParameterized()) {
                    attr.log.error(tree,"jml.invalid.erasedtype",JmlPretty.write(arg));
                }
                if (!expr.javaType) attr.checkForWildcards(arg,arg);
            }
            Type t = attr.jmltypes.TYPE;
            if (expr.javaType) t = syms.classType;
            attr.addTodo(attr.utilsClass);
            return t;
        }
    };

    public static final String freshID = "\\fresh";
    public static final IJmlClauseKind freshKind = new AnyArgBooleanExpressions(freshID){
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            JmlMethodInvocation expr = (JmlMethodInvocation)tree;
            int n = expr.args.size();
            if (n != 1 && n != 2) {
                Log.instance(context).error(tree.pos(),"jml.wrong.number.args",name(),"1 or 2",n);
            }
            if (n > 0) {
                if (n > 1) attr.checkLabel(expr.args.get(1));
                JCExpression arg = expr.args.get(0);
                Type tt = attr.attribExpr(arg, localEnv);
                if (tt.isPrimitive()) {
                    Log.instance(context).error(arg.pos(),"jml.ref.arg.required", name());
                }
                if (!attr.freshClauses.contains(attr.currentClauseType)) {
                    // The +1 is to fool the error reporting mechanism into 
                    // allowing other error reports about the same token
                    Log.instance(context).error(tree.pos+1, "jml.misplaced.token", name(), attr.currentClauseType == null ? "jml declaration" : attr.currentClauseType.name());
                }
            }
            return Symtab.instance(context).booleanType;
        }
    };

    public static final String allocID = "\\isAllocated";
    public static final IJmlClauseKind allocKind = new AnyArgBooleanExpressions(allocID){
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            JmlMethodInvocation expr = (JmlMethodInvocation)tree;
            int n = expr.args.size();
            if (n != 1 && n != 2) {
                Log.instance(context).error(tree.pos(),"jml.wrong.number.args",name(),"1 or 2",n);
            }
            if (n > 0) {
                if (n > 1) attr.checkLabel(expr.args.get(1));
                JCExpression arg = expr.args.get(0);
                Type tt = attr.attribExpr(arg, localEnv);
                if (tt.isPrimitive()) {
                    Log.instance(context).error(arg.pos(),"jml.ref.arg.required", name());
                }
            }
            return Symtab.instance(context).booleanType;
        }
    };

    public static final String bsmaxID = "\\max";
    public static final IJmlClauseKind bsmaxKind = new IJmlClauseKind.ExpressionKind(bsmaxID) {

        @Override
        public JCExpression parse(JCModifiers mods, String keyword, IJmlClauseKind kind, JmlParser parser) {
            init(parser);
            int startx = parser.pos();
            if (parser.getScanner().token(1).kind != LPAREN) {
                return (JCExpression)QuantifiedExpressions.qmaxKind.parse(mods,keyword,QuantifiedExpressions.qmaxKind,parser);
                //return parser.parseQuantifiedExpr(startx, QuantifiedExpressions.maxKind);
            } else {
                parser.nextToken();
                int preferred = parser.pos();
                List<JCExpression> args = parser.arguments();
                JmlMethodInvocation te = parser.maker().at(preferred).JmlMethodInvocation(
                        bsmaxKind, args);
                te.startpos = startx;
                te.kind = bsmaxKind;
                te = toP(te);
                return parser.primaryTrailers(te, null);
            }
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            JmlMethodInvocation expr = (JmlMethodInvocation)tree;    
            // Expect one argument of type JMLSetType, result type Lock
            // FIXME - this should be one argument of type JMLObjectSet, result type is Object
            // The argument expression may contain JML constructs
            ListBuffer<Type> argtypesBuf = new ListBuffer<>();
            attr.attribArgs(VAL, expr.args, localEnv, argtypesBuf);  // We can't send in Lock as the requested type because Types does not know what to do with it - FIXME: perhaps make a JmlTypes that can handle the new primitives
            int n = expr.args.size();
            if (n != 1) {
                log.error(tree.pos(),"jml.one.arg",name(),n);
            }
            Type t;
            if (n == 0) t = syms.errType;
            else {
                // FIXME - use type.sameType to compare types?
                if (!expr.args.get(0).type.equals(attr.JMLSetType)) {  // FIXME - use isSameType or check?  what about errors?
                    attr.log.error(expr.args.get(0).pos(),"jml.max.expects.lockset",attr.JMLSetType,expr.args.get(0).type.toString());
                }
                t = attr.Lock;
            }
            return t;
        }
    };

    public static class LabelExpression extends IJmlClauseKind.ExpressionKind {
        public LabelExpression(String keyword) { super(keyword); }

        @Override
        public JCExpression parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            int pos = parser.pos();
            parser.nextToken(); // skip over the keyword
            // pos is the position of the \lbl token
            int labelPos = parser.pos();
            if (parser.token().kind == TokenKind.LPAREN) {
                if (requireStrictJML()) {
                    log.warning(pos,"jml.not.strict","functional form of lbl expression");
                }
                parser.nextToken();
                List<JCExpression> args = parser.parseExpressionList();
                if (parser.token().kind != TokenKind.RPAREN) {
                    log.error(parser.pos(),"jml.message", "Expected a comma or right parenthesis here");
                } else if (args.length() != 2) {
                    log.error(labelPos, "jml.message", "Expected two arguments to a lbl experession");
                } else if (!(args.get(0) instanceof JCIdent)) {
                    log.error(args.get(0).pos, "jml.message", "The first argument of a lbl expression must be an identifier");
                } else {
                    parser.nextToken(); // skip the RPAREN
                    Name id = ((JCIdent)args.get(0)).name;
                    return toP(parser.maker().at(pos).JmlLblExpression(args.get(0).pos, this, id, args.get(1)));
                }
                return toP(parser.maker().at(labelPos).Erroneous());
            } else {
                Name n = parser.ident();
                JCExpression e = parser.parseExpression();
                e = toP(parser.maker().at(pos).JmlLblExpression(labelPos,this, n, e));
                if (this == lblanyKind ) strictCheck(parser, e);
                return e;
            }
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            JmlLblExpression expr = (JmlLblExpression)tree;    
            return expr.expression.type;
        }
    }

    public static final String lblanyID = "\\lbl";
    public static final IJmlClauseKind lblanyKind = new LabelExpression(lblanyID); 
    public static final String lblposID = "\\lblpos";
    public static final IJmlClauseKind lblposKind = new LabelExpression(lblposID); 
    public static final String lblnegID = "\\lblneg";
    public static final IJmlClauseKind lblnegKind = new LabelExpression(lblnegID); 

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

