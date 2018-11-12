/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static org.jmlspecs.openjml.JmlTokenKind.ENDJMLCOMMENT;

import org.jmlspecs.openjml.IJmlClauseType;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
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
public class ReachableStatement implements JmlExtension.Statement {

    public static final String reachableID = "reachable";
    public static final String unreachableID = "unreachable";
    
    public static final IJmlClauseType reachableClause = new ExprStatementType() {
        public String name() { return reachableID; }
    };

    public static final IJmlClauseType unreachableClause = new ExprStatementType() {
        public String name() { return unreachableID; }
    };

    public IJmlClauseType[]  clauseTypes() { return new IJmlClauseType[]{
            reachableClause, unreachableClause }; }
    
    public static class ExprStatementType extends IJmlClauseType.Statement {
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
        // allowed forms:
        //   reachable ;
        //   reachable <expr> ;
        //   reachable <expr> : <expr> ; // The first <epxr> is a String literal, used as a message or identifier
        // FIXME - string literal is not used
        @Override
        public JmlStatementExpr parse(JCModifiers mods, String keyword, IJmlClauseType clauseType, JmlParser parser) {
            init(parser);
            int pp = parser.pos();
            int pe = parser.endPos();
            int p = scanner.currentPos();
            parser.nextToken();
            JmlStatementExpr st = jmlF.at(p).JmlExpressionStatement(keyword,clauseType,null,jmlF.Literal(TypeTag.BOOLEAN,1));
            if (parser.token().kind == TokenKind.SEMI) {
                return st;
            } else {
                JCExpression opt = null;
                JCExpression e = parser.parseExpression();
                if (e == null) return null;
                if (parser.token().kind == TokenKind.COLON) {
                    opt = parser.parseExpression();
                }

                if (parser.token().ikind == JmlTokenKind.ENDJMLCOMMENT) {
                    parser.jmlwarning(p-2, "jml.missing.semi", keyword);
                } else if (parser.token().kind != TokenKind.SEMI) {
                    parser.jmlerror(p, "jml.missing.semi", keyword);
                }
                st.optionalExpression = e;
                return st;
                //return jmlF.at(p).JmlExpressionStatement(keyword,clauseType,null,e);
            }

        }

        @Override
        public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    }
    
}
