package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.IF;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.Maker;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
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
            Name nn = parser.parseOptionalName();
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
                    e = parser.parseExpression(); // read expression, advancing scanner to token after expression
                }
            }
            var t = toP(M.at(pp).JmlTypeClauseConditional(mods, clauseType, id, e));
            wrapup(t, clauseType, true, true);
            t.name = nn;
            return t;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
        	System.out.println("READABLE " + expr);
            // TODO Auto-generated method stub
            return null;
        }
    };
}
