package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.IF;
import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseType;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseConditional;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;

public class MethodConditionalClauseExtension implements JmlExtension.MethodClause {

    public static final String durationID = "duration";
    public static final String workingspaceID = "working_space";
    public static final String measuredbyID = "measured_by";
    
    public static final IJmlClauseType durationClause = new MethodConditionalClauseType() {
        public String name() { return durationID; }
        public boolean oldNoLabelAllowed() { return false; }
        public boolean preOrOldWithLabelAllowed() { return false; }
    };
    
    public static final IJmlClauseType workingspaceClause = new MethodConditionalClauseType() {
        public String name() { return workingspaceID; }
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return false; }
    };
    
    public static final IJmlClauseType measuredbyClause = new MethodConditionalClauseType() {
        public String name() { return measuredbyID; }
    };
    
    @Override
    public IJmlClauseType[]  clauseTypes() { return new IJmlClauseType[]{
            durationClause, measuredbyClause, workingspaceClause}; }
    
    public static class MethodConditionalClauseType extends IJmlClauseType.MethodClause {
 
        @Override
        public boolean oldNoLabelAllowed() { return false; }
        @Override
        public boolean preOrOldWithLabelAllowed() { return false; }

        @Override
        public 
        JmlMethodClauseConditional parse(JCModifiers mods, String keyword, IJmlClauseType clauseType, JmlParser parser) {
            init(parser);

            int pp = parser.pos();
            int pe = parser.endPos();

            scanner.setJmlKeyword(false);
            parser.nextToken();
            JCExpression p = null;
            JCExpression e = parser.parsePredicateOrNotSpecified();
            if (parser.token().kind == IF) { // The if is not allowed if the
                // expression is not_specified, but we test that
                // during type checking
                parser.nextToken();
                p = parser.parseExpression();
            }
            JmlMethodClauseConditional res = parser.to(jmlF.at(pp)
                    .JmlMethodClauseConditional(keyword, clauseType, e, p));
            scanner.setJmlKeyword(true);
            if (parser.token().kind == SEMI) {
                parser.nextToken();
            } else {
                parser.jmlerror(parser.pos(), parser.endPos(), "jml.bad.construct",
                        keyword + " specification");
                parser.skipThroughSemi();
            }
            return res;

        }

        @Override
        public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    }
}
