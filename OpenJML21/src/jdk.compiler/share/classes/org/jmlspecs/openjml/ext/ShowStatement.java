/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;
import org.jmlspecs.openjml.JmlTree.JmlStatementShow;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.ListBuffer;

public class ShowStatement extends JmlExtension {

    public static final String showID = "show";
    
    public static final IJmlClauseKind showClause = new JmlStatementType(showID);

    public static class JmlStatementType extends IJmlClauseKind.Statement {
        public JmlStatementType(String keyword) { super(keyword); }
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }

        public JmlAbstractStatement parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            int pp = parser.pos();
            int pe = parser.endPos();
            init(parser);
            if (JmlOption.langJML.equals(JmlOption.value(parser.context, JmlOption.LANG))) {
                utils.warning(pp,"jml.not.strict","show statement");
            }
            
            parser.nextToken();

            ListBuffer<JCExpression> expressions = new ListBuffer<>();
            if (parser.token().kind != TokenKind.SEMI && !parser.isEndJml()) {
            	do {
            		int n = log.nerrors;
            		JCExpression t = parser.parseExpression();
            		if (n != log.nerrors) {
            			parser.skipToSemi();
            			break;
            		}
            		expressions.add(t);
                } while (parser.acceptIf(TokenKind.COMMA));
            }
            JmlStatementShow st = toP(parser.maker().at(pp).JmlStatementShow(showClause,expressions.toList()));
            wrapup(st, clauseType, true, true);
            return st;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    }
}
