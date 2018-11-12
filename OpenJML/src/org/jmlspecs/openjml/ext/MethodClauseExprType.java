package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseType;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;

public class MethodClauseExprType extends IJmlClauseType.MethodClause {
    
    public MethodClauseExprType(String keyword) {
        this.keyword = keyword;
    }

    @Override
    public boolean oldNoLabelAllowed() { return false; }
    @Override
    public boolean preOrOldWithLabelAllowed() { return false; }

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
    
}