/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static org.jmlspecs.openjml.JmlTokenKind.ENDJMLCOMMENT;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.IJmlLoop;
import org.jmlspecs.openjml.JmlTree.JmlIfStatement;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlSwitchStatement;
import org.jmlspecs.openjml.JmlTreeUtils;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;

/** This class handles expression extensions that take an argument list of JCExpressions.
 * Even if there are constraints on the number of arguments, it
 * is more robust to accept all of them and then issue an error in the typechecker
 * if the number of arguments is wrong.
 * 
 * @author David Cok
 *
 */
public class ReachableStatement extends JmlExtension {

    public static final String reachableID = "reachable";
    public static final String unreachableID = "unreachable";
    public static final String splitID = "split";
    public static final String haltID = "halt";
    
    public static final IJmlClauseKind reachableClause = new ExprStatementType(reachableID);

    public static final IJmlClauseKind unreachableClause = new ExprStatementType(unreachableID);

    public static final IJmlClauseKind splitClause = new ExprStatementType(splitID);

    public static final IJmlClauseKind haltClause = new ExprStatementType(haltID);

    public static class ExprStatementType extends IJmlClauseKind.Statement {
        public ExprStatementType(String keyword) { super(keyword); }
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
        // allowed forms:
        //   reachable ;
        //   reachable <expr> ;
        //   reachable <expr> : <expr> ; // The first <epxr> is a String literal, used as a message or identifier
        // FIXME - string literal is not used
        @Override
        public JCTree parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            int pp = parser.pos();
            int pe = parser.endPos();
            int p = scanner.currentPos();
            boolean noExpression = keyword.equals(splitID) || keyword.equals(haltID);
            boolean semiWarning = !noExpression && JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG));
            parser.nextToken();
            JmlStatementExpr st = parser.maker().at(pp).JmlExpressionStatement(keyword,clauseType,null,null);
            if (!noExpression) st.expression = JmlTreeUtils.instance(context).makeBooleanLiteral(pp,true);
            if (parser.token().kind == TokenKind.SEMI) {
                parser.nextToken();
            } else if (parser.token().ikind == JmlTokenKind.ENDJMLCOMMENT) {
                if (semiWarning) parser.jmlwarning(p-1, "jml.missing.semi", keyword);
            } else {
                JCExpression opt = null;
                JCExpression e = parser.parseExpression();
                if (e == null) return null;
                if (parser.token().kind == TokenKind.COLON) {
                    opt = parser.parseExpression();
                    st.optionalExpression = e;
                    st.expression = opt;
                } else {
                    st.expression = e;
                }

                if (parser.token().ikind == JmlTokenKind.ENDJMLCOMMENT) {
                    if (semiWarning) parser.jmlwarning(p-2, "jml.missing.semi", keyword);
                } else if (parser.token().kind != TokenKind.SEMI) {
                    parser.jmlerror(p, "jml.missing.semi", keyword);
                } else {
                    parser.nextToken(); // skip over semicolon
                }
            }
            JCTree tree = st;
            if (keyword.equals(splitID) && st.expression == null) {
                while (parser.jmlTokenClauseKind() == Operators.endjmlcommentKind) parser.nextToken();
                JCStatement stt = parser.blockStatement().head;
                if (stt instanceof JmlIfStatement) {
                    ((JmlIfStatement)stt).split = true;
                } else if (stt instanceof JmlSwitchStatement) {
                    ((JmlSwitchStatement)stt).split = true;
                } else if (stt instanceof IJmlLoop) {
                    ((IJmlLoop)stt).setSplit(true);
                } else {
                    log.warning(st, "jml.message", "Ignoring out of place split statement");
                }
                tree = stt;
            }
            return tree;
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    }
    
}
