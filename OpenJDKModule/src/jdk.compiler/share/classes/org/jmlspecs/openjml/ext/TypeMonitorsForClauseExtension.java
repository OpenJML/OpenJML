package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.IDENTIFIER;
import static com.sun.tools.javac.parser.Tokens.TokenKind.IF;
import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseIn;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.ITokenKind;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;

public class TypeMonitorsForClauseExtension extends JmlExtension {

    public static final String monitorsforID = "monitors_for";
    
    public static final IJmlClauseKind monitorsforClause = new IJmlClauseKind.TypeClause(monitorsforID) {
        public boolean oldNoLabelAllowed() { return false; }
        public boolean preOrOldWithLabelAllowed() { return false; }
        
        public 
        JmlTree.JmlTypeClauseMonitorsFor parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            int pp = parser.pos();
            init(parser);
            parser.nextToken();
            List<JCExpression> elist = List.<JCExpression>nil();
            Name n;
            int identPos = parser.pos();
            ITokenKind tk = parser.token().kind;
            if (tk != IDENTIFIER) {
                error(parser.pos(), parser.endPos(), "jml.expected", "an identifier");
                n = parser.names.asterisk; // place holder for an error situation
            } else {
                n = parser.ident(); // Advances to next token
                if (parser.token().kind != TokenKind.EQ && parser.jmlTokenKind() != JmlTokenKind.LEFT_ARROW) {
                    error(parser.pos(), parser.endPos(), "jml.expected",
                            "an = or <- token");
                } else {
                    parser.nextToken();
                    elist = parser.parseExpressionList();
                }
            }
            JCTree.JCIdent id = parser.to(parser.maker().at(identPos).Ident(n));
            if (parser.token().kind != SEMI) {
                parser.skipThroughSemi();
            } else {
                parser.nextToken();
            }
            return toP(parser.maker().at(pp).JmlTypeClauseMonitorsFor(mods, id, elist));
        }
        
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
}
