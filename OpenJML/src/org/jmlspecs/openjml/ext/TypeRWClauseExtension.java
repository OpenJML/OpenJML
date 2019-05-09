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

public class TypeRWClauseExtension extends JmlExtension.TypeClause {

    public static final String readableID = "readable";
    public static final String writableID = "writable";
    
    public static final IJmlClauseKind readableClause = new RWClauseType() {
        public String name() { return readableID; }
    };
    
    public static final IJmlClauseKind writableClause = new RWClauseType() {
        public String name() { return writableID; }
    };

    @Override
    public IJmlClauseKind[]  clauseTypesA() { return clauseTypes(); }
    public static IJmlClauseKind[] clauseTypes() { return new IJmlClauseKind[]{
            readableClause, writableClause}; }
    

    public static class RWClauseType extends IJmlClauseKind.TypeClause {
        public boolean oldNoLabelAllowed() { return false; }
        public boolean preOrOldWithLabelAllowed() { return false; }
        
        public 
        JmlTree.JmlTypeClauseConditional parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            int pp = parser.pos();
            init(parser);
            scanner.setJmlKeyword(false);
            parser.nextToken();
            Name n;
            JCExpression e;
            int identPos = parser.pos();
            if (parser.token().kind != TokenKind.IDENTIFIER) {
                error(parser.pos(), parser.endPos(), "jml.expected", "an identifier");
                n = names.asterisk; // place holder for an error situation
                e = jmlF.Erroneous();
            } else {
                n = parser.ident();
                if (parser.token().kind != IF) {
                    error(parser.pos(), parser.endPos(), "jml.expected", "an if token");
                    e = jmlF.Erroneous();
                } else {
                    parser.accept(TokenKind.IF);
                    e = parser.parseExpression();
                }
            }
            JCTree.JCIdent id = parser.to(jmlF.at(identPos).Ident(n));
            scanner.setJmlKeyword(true);
            if (e.getTag() == JCTree.Tag.ERRONEOUS || parser.token().kind != SEMI) {
                parser.skipThroughSemi();
            } else {
                parser.nextToken();
            }
            return toP(jmlF.at(pp).JmlTypeClauseConditional(mods, clauseType, id, e));
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
}
