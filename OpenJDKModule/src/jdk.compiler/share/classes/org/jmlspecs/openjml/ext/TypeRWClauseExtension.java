package org.jmlspecs.openjml.ext;

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
import org.jmlspecs.openjml.JmlTree.Maker;

import com.sun.tools.javac.code.Type;
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
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;

public class TypeRWClauseExtension extends JmlExtension {

    public static final String readableID = "readable";
    public static final String writableID = "writable";
    
    public static final IJmlClauseKind readableClause = new RWClauseType(readableID);
    
    public static final IJmlClauseKind writableClause = new RWClauseType(writableID);

    public static class RWClauseType extends IJmlClauseKind.TypeClause {
        public RWClauseType(String keyword) { super(keyword); }
        public boolean oldNoLabelAllowed() { return false; }
        public boolean preOrOldWithLabelAllowed() { return false; }
        
        public 
        JmlTree.JmlTypeClauseConditional parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            int pp = parser.pos();
            init(parser);
            parser.nextToken(); // skip over readable/writable token; current token should now be the identifier
            Name n;
            JCExpression e;
            JCTree.JCIdent id;
            int identPos = parser.pos();
            Maker M = parser.maker();
            if (parser.token().kind != TokenKind.IDENTIFIER) {
                error(parser.pos(), parser.endPos(), "jml.expected", "an identifier");
                n = parser.names.asterisk; // place holder for an error situation
                id = parser.to(M.at(identPos).Ident(n));
                e = M.at(identPos).Erroneous();
            } else {
                n = parser.ident(); // reads name and advances scanner
                id = parser.toP(M.at(identPos).Ident(n));
                if (parser.token().kind != IF) {
                    error(parser.pos(), parser.endPos(), "jml.expected", "an if token");
                    e = M.Erroneous();
                } else {
                    parser.accept(TokenKind.IF); // check that current token is 'if' and advace scanner
                    e = parser.parseExpression(); // read expression, advancinng scanner to token after expression
                }
            }
            if (e.getTag() == JCTree.Tag.ERRONEOUS || parser.token().kind != SEMI) {
                parser.skipThroughSemi();
            } else {
                parser.accept(TokenKind.SEMI); // skip over semicolon
            }
            return toP(M.at(pp).JmlTypeClauseConditional(mods, clauseType, id, e));
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
}
