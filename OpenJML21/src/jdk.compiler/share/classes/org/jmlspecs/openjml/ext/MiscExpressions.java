/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.code.Kinds.*;
import static com.sun.tools.javac.parser.Tokens.TokenKind.LPAREN;
import static com.sun.tools.javac.parser.Tokens.TokenKind.RPAREN;
import static com.sun.tools.javac.parser.Tokens.TokenKind.VOID;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTree.JmlLblExpression;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.ext.FunctionLikeExpressions.AnyArgBooleanExpression;

import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCErroneous;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;

public class MiscExpressions extends JmlExtension {

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
                        "jml.args.required", this.keyword());
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
                        utils.error(parser.pos(), parser.endPos(),
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
                utils.error(tree,"jml.one.arg",keyword(),n);
            }
            if (n > 0) {
                JCExpression arg = expr.args.get(0);
                attr.attribTree(arg, localEnv, attr.new ResultInfo(KindSelector.TYP, Type.noType));
                if (!expr.javaType && arg.type.tsym.getTypeParameters().size() > 0 &&
                        !arg.type.isParameterized()) {
                    utils.error(tree,"jml.invalid.erasedtype",JmlPretty.write(arg));
                }
                if (!expr.javaType) attr.checkForWildcards(arg,arg);
            }
            var TYPE = JmlPrimitiveTypes.TYPETypeKind.getType(attr.context);
            Type t = TYPE;
            if (expr.javaType) t = attr.syms.classType;
            attr.addTodo(attr.runtimeClass);
            return t;
        }
    };

    public static final String freshID = "\\fresh";
    public static final IJmlClauseKind freshKind = new AnyArgBooleanExpression(freshID){
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            JmlMethodInvocation expr = (JmlMethodInvocation)tree;
            int n = expr.args.size();
            if (n != 1 && n != 2) {
               utils.error(tree,"jml.wrong.number.args",keyword(),"1 or 2",n);
            } else {
                if (n > 1) attr.checkLabel(expr.args.get(1));
                JCExpression arg = expr.args.get(0);
                Type tt = attr.attribExpr(arg, localEnv);
                if (tt.isPrimitive()) {
                    utils.error(arg,"jml.ref.arg.required", keyword());
                }
                if (!attr.freshClauses.contains(attr.jmlenv.currentClauseKind)) {
                    // The +1 is to fool the error reporting mechanism into 
                    // allowing other error reports about the same token
                    utils.error(tree.pos+1, "jml.misplaced.token", keyword(), attr.jmlenv.currentClauseKind == null ? "jml declaration" : attr.jmlenv.currentClauseKind.keyword());
                }
            }
            expr.type = attr.syms.booleanType;
            return expr.type;
        }
    };

    public static final String allocID = "\\isAllocated";
    public static final IJmlClauseKind allocKind = new AnyArgBooleanExpression(allocID){
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            JmlMethodInvocation expr = (JmlMethodInvocation)tree;
            int n = expr.args.size();
            if (n != 1 && n != 2) {
                utils.error(tree,"jml.wrong.number.args",keyword(),"1 or 2",n);
            }
            if (n > 0) {
                if (n > 1) attr.checkLabel(expr.args.get(1));
                JCExpression arg = expr.args.get(0);
                Type tt = attr.attribExpr(arg, localEnv);
                if (tt.isPrimitive()) {
                    utils.error(arg,"jml.ref.arg.required", keyword());
                }
            }
            return attr.syms.booleanType;
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
            attr.attribArgs(Kinds.KindSelector.VAL, expr.args, localEnv, argtypesBuf);  // We can't send in Lock as the requested type because Types does not know what to do with it - FIXME: perhaps make a JmlTypes that can handle the new primitives
            int n = expr.args.size();
            if (n != 1) {
                utils.error(tree,"jml.one.arg",keyword(),n);
            }
            Type t;
            if (n == 0) t = attr.syms.errType;
            else {
                // FIXME - use type.sameType to compare types?
                if (!expr.args.get(0).type.equals(attr.JMLSetType)) {  // FIXME - use isSameType or check?  what about errors?
                    utils.error(expr.args.get(0),"jml.max.expects.lockset",attr.JMLSetType,expr.args.get(0).type.toString());
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
                    utils.warning(pos,"jml.not.strict","functional form of lbl expression");
                }
                parser.nextToken();
                List<JCExpression> args = parser.parseExpressionList();
                if (parser.token().kind != TokenKind.RPAREN) {
                    utils.error(parser.pos(),"jml.message", "Expected a comma or right parenthesis here");
                } else if (args.length() != 2) {
                    utils.error(labelPos, "jml.message", "Expected two arguments to a lbl experession");
                } else if (!(args.get(0) instanceof JCIdent)) {
                    utils.error(args.get(0).pos, "jml.message", "The first argument of a lbl expression must be an identifier");
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
}

