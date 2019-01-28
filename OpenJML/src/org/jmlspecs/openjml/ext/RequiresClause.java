package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.*;

import org.jmlspecs.openjml.IJmlClauseType;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;

public class RequiresClause extends JmlExtension.MethodClause {
    
    public static final String requiresID = "requires";
    
    public static final IJmlClauseType requiresClause = new MethodClauseExprType(requiresID) {
        public boolean isPreconditionClause() { return true; }
        
        @Override
        public 
        JmlMethodClauseExpr parse(JCModifiers mods, String keyword, IJmlClauseType clauseType, JmlParser parser) {
            if (mods != null) {
                error(mods, "jml.message", "A " + keyword + " clause may not have modifiers");
                return null;
            }
            init(parser);
            
            int pp = parser.pos();
            int pe = parser.endPos();
            
            scanner.setJmlKeyword(false);
            parser.nextToken();
            JCExpression e = parser.parsePredicateOrNotSpecified();
            scanner.setJmlKeyword(true);
            if (scanner.token().kind == ELSE) {
                parser.nextToken();
                parser.parseType();
            } 
            if (scanner.token().kind != SEMI) {
                parser.syntaxError(parser.pos(), null, "jml.invalid.expression.or.missing.semi");
                parser.skipThroughSemi();
            } else {
                parser.nextToken(); // skip SEMI
            }
            JmlMethodClauseExpr cl = jmlF.at(pp).JmlMethodClauseExpr(keyword, clauseType, e);
            return toP(cl);

        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
        

    };
    
    @Override
    public IJmlClauseType[]  clauseTypes() { return new IJmlClauseType[]{
            requiresClause}; }
    
}
