package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.IDENTIFIER;
import static com.sun.tools.javac.parser.Tokens.TokenKind.LPAREN;
import static com.sun.tools.javac.parser.Tokens.TokenKind.RPAREN;
import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.Extensions;
import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.Maker;

import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;

public class SignalsClauseExtension extends JmlExtension {
    
    public static final String signalsID = "signals";
    
    public void register() {
        synonym("exsures",signalsClauseKind);
        synonym("throws",signalsClauseKind);
    }
    
    public static final IJmlClauseKind signalsClauseKind = new IJmlClauseKind.MethodSpecClauseKind(signalsID) {
        @Override
        public boolean oldNoLabelAllowed() { return true; }
        @Override
        public boolean preOrOldWithLabelAllowed() { return false; }

        @Override
        public JmlMethodClause parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            if (mods != null) {
                error(mods, "jml.message", "A " + keyword + " clause may not have modifiers");
                return null;
            }
            int pp = parser.pos();
            int pe = parser.endPos();
            init(parser);
            
            
            parser.nextToken();

            JCExpression e;
            JCExpression t = null;
            Name ident = null;
            int rpos = pp;
            if (parser.token().kind != LPAREN) {
                int pos = parser.pos();
                Maker M = parser.maker().at(pos);
                parser.syntaxError(pos, null, "jml.expected.lparen.signals");
                t = parser.to(M.Ident(parser.names.fromString("java")));
                t = parser.to(M.Select(t, parser.names.fromString("lang")));
                t = parser.to(M.Select(t, parser.names.fromString("Exception")));
                e = parser.parsePredicateOrNotSpecified();
            } else {
                parser.nextToken();
                // Get type
                t = parser.parseType();
                // Get identifier (optional)
                if (parser.token().kind == IDENTIFIER) {
                    ident = parser.ident();
                }
                rpos = parser.pos();
                if (parser.token().kind != RPAREN) {
                    parser.syntaxError(rpos, null, "jml.expected.rparen.signals");
                    parser.skipToSemi();
                    e = toP(parser.maker().at(parser.pos()).Erroneous());
                } else {
                    parser.nextToken();
                    if (parser.token().kind == SEMI) {
                        e = toP(parser.maker().at(parser.pos()).Literal(TypeTag.BOOLEAN, 1)); // Boolean.TRUE));
                    } else {
                        e = parser.parsePredicateOrNotSpecified();
                    }
                }
            }
            JCTree.JCVariableDecl var = parser.maker().at(t.pos).VarDef(
                    parser.maker().at(t.pos).Modifiers(0), ident, t, null);
            parser.storeEnd(var, rpos);
            if (parser.token().kind != SEMI) {
                if (e.getKind() != Kind.ERRONEOUS)
                    parser.syntaxError(parser.pos(), null, "jml.missing.semi");
                parser.skipThroughSemi();
            } else {
                parser.nextToken();
            }
            return toP(parser.maker().at(pp).JmlMethodClauseSignals(keyword, clauseType, var, e));

        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
    
}
