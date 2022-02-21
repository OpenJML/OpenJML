package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.IF;
import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseConditional;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;

public class MethodResourceClauseExtension extends JmlExtension {

    public static final String durationID = "duration";
    public static final String workingspaceID = "working_space";
    public static final String measuredbyID = "measured_by";
    
    public static final IJmlClauseKind durationClause = new MethodConditionalClauseType(durationID) {
        public boolean oldNoLabelAllowed() { return false; }
        public boolean preOrOldWithLabelAllowed() { return false; }
    };
    
    public static final IJmlClauseKind workingspaceClause = new MethodConditionalClauseType(workingspaceID) {
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return false; }
    };
    
    public static final IJmlClauseKind measuredbyClause = new MethodConditionalClauseType(measuredbyID) {
    };

    
    public static class MethodConditionalClauseType extends IJmlClauseKind.MethodSpecClauseKind {
        public MethodConditionalClauseType(String keyword) { super(keyword); }

        @Override
        public boolean oldNoLabelAllowed() { return false; }
        @Override
        public boolean preOrOldWithLabelAllowed() { return false; }

        @Override
        public 
        JmlMethodClauseConditional parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);

            int pp = parser.pos();

            parser.nextToken();
            var n = parser.parseOptionalName();
            JCExpression p = null;
            JCExpression e = parser.parseExpression();
            if (parser.token().kind == IF) {
                parser.nextToken();
               p = parser.parseExpression();
            }
            JmlMethodClauseConditional res = parser.to(parser.maker().at(pp)
                    .JmlMethodClauseConditional(keyword, clauseType, e, p));
            wrapup(res, clauseType, true, true);
            res.name = n;
            return res;

        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    }
}
