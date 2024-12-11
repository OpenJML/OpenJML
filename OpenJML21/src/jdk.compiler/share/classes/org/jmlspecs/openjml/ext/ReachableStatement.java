/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.JmlTreeUtils;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;

public class ReachableStatement extends JmlExtension {

    public static final String reachableID = "reachable";
    public static final String unreachableID = "unreachable";
    public static final String haltID = "halt";
    
    // FIXME - combine this with StatementExprType
    public static final IJmlClauseKind reachableClause = new ExprStatementType(reachableID);

    public static final IJmlClauseKind unreachableClause = new ExprStatementType(unreachableID);

    public static final IJmlClauseKind haltClause = new ExprStatementType(haltID);

    public static class ExprStatementType extends IJmlClauseKind.Statement {
        public ExprStatementType(String keyword) { super(keyword); }
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
        // allowed forms:
        //   unreachable
        //   unreachable;
        //   reachable ;
        //   reachable <expr> ;
        //   reachable <expr> : <expr> ; // The first <epxr> is a String literal, used as a message or identifier
        // FIXME - string literal is not used
        // FIXME - is a missing semicolon ever warned about? Are expressions ever used?
        @Override
        public JCTree parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            int pp = parser.pos();
            int p = parser.getScanner().currentPos(); // FIXME - why do we get this position from the scanner?
            boolean noExpression = keyword.equals(haltID) || keyword.equals(reachableID) || keyword.equals(unreachableID);
            boolean semiWarning = !noExpression && JmlOption.langJML.equals(JmlOption.value(parser.context, JmlOption.LANG));
            parser.nextToken();
            JmlStatementExpr st = parser.maker().at(pp).JmlExpressionStatement(keyword,clauseType,null,null);
            if (!noExpression) st.expression = JmlTreeUtils.instance(parser.context).makeBooleanLiteral(pp,true);
            if (parser.token().kind == TokenKind.SEMI) {
                parser.nextToken();
            } else if (parser.isEndJml()) {
                if (semiWarning) utils.warning(p-1, "jml.missing.semi", keyword);
            } else if (noExpression) {
                // continue
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

                if (parser.isEndJml()) {
                    if (semiWarning) utils.warning(p-2, "jml.missing.semi", keyword);
                } else if (parser.token().kind != TokenKind.SEMI) {
                    utils.error(p, "jml.missing.semi", keyword);
                } else {
                    parser.nextToken(); // skip over semicolon
                }
                // FIXME - use wrapup
            }
            return st;
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> env) {
        	JmlTree.JmlStatementExpr clause = (JmlTree.JmlStatementExpr)tree;
        	boolean prevAllowJML = attr.jmlresolve.setAllowJML(true);
        	attr.jmlenv = attr.jmlenv.pushCopy();
        	attr.jmlenv.inPureEnvironment = true;
        	attr.jmlenv.currentClauseKind = clause.clauseType;
        	// unreachable statements have a null expression
	        if (clause.expression != null) attr.attribExpr(clause.expression,env,attr.syms.booleanType);
        	if (clause.optionalExpression != null) attr.attribExpr(clause.optionalExpression,env,Type.noType);
        	attr.jmlenv = attr.jmlenv.pop();
        	attr.jmlresolve.setAllowJML(prevAllowJML);
        	return null; // No type returned for the clause
        }
    }
    
}
