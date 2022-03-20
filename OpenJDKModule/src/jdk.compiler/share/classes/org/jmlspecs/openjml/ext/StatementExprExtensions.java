package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.COLON;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;
import org.jmlspecs.openjml.esc.Label;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;

public class StatementExprExtensions extends JmlExtension {
    
    public static final String assertID = "assert";
    public static final String checkID = "check";
    public static final String assumeID = "assume";
    public static final String commentID = "comment";
    public static final String useID = "use";
    public static final String loopinvariantID = "loop_invariant";
    public static final String loopdecreasesID = "loop_decreases";
    
    public static final IJmlClauseKind assertClause = new StatementExprType(assertID);
    public static final IJmlClauseKind checkClause = new StatementExprType(checkID);
    public static final IJmlClauseKind assumeClause = new StatementExprType(assumeID);
    public static final IJmlClauseKind commentClause = new StatementExprType(commentID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree t, Env<AttrContext> env) {
        	// Do nothing for a comment clause -- just contains text
        	return null;
        }
    };
    
    public static final IJmlClauseKind useClause = new StatementExprType(useID);
    public static final IJmlClauseKind loopinvariantClause = new StatementExprType(loopinvariantID);
    public static final IJmlClauseKind loopdecreasesClause = new StatementExprType(loopdecreasesID);
    
    static {
        synonym("decreases",loopdecreasesClause);
        synonym("decreasing",loopdecreasesClause);
        synonym("maintaining",loopinvariantClause);
    }
    
    public static class StatementExprType extends IJmlClauseKind.Statement {
        
        public StatementExprType(String keyword) { super(keyword); }
        
        @Override
        public JmlAbstractStatement parse(JCModifiers mods, String id, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            int pp = parser.pos();

            parser.nextToken(); // skip over the keyword
            var n = parser.parseOptionalName();

            JCExpression t = parser.parseExpression();
            if (t instanceof JCTree.JCErroneous) parser.skipToSemi();
            String nm = clauseType.keyword();
            JmlAbstractStatement ste;
            //if (t instanceof JCTree.JCErroneous) t = JmlTreeUtils.instance(context).trueLit;
            if (clauseType == StatementExprExtensions.loopinvariantClause ||
                    clauseType == StatementExprExtensions.loopdecreasesClause) {
                JmlTree.JmlStatementLoopExpr st = parser.maker()
                        .at(pp)
                        .JmlStatementLoopExpr(
                                clauseType,
                                    t);
                ste = st;
            } else {
                JmlTree.JmlStatementExpr st = parser.maker()
                        .at(pp)
                        .JmlExpressionStatement(
                                nm,
                                clauseType,
                                nm.equals("assume") ? Label.EXPLICIT_ASSUME :
                                    Label.EXPLICIT_ASSERT,  // FIXME?
                                    t);
                st.keyword = id;
                Token tk = parser.token();
                if (tk.kind == COLON) {
                    parser.nextToken();
                    st.optionalExpression = parser.parseExpression();
                }
                ste = st;
            }
            wrapup(ste,clauseType,true);
            return ste;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree t, Env<AttrContext> env) {
        	JmlTree.JmlStatementExpr tree = (JmlTree.JmlStatementExpr)t;
            boolean isUse = tree.clauseType == useClause;
            boolean prevAllowJML = attr.jmlresolve.setAllowJML(true);
            attr.jmlenv = attr.jmlenv.pushCopy();
            attr.jmlenv.inPureEnvironment = true;
            attr.jmlenv.currentClauseKind = tree.clauseType;
            Type expectedType = tree.clauseType == loopdecreasesClause ? JmlTypes.instance(attr.context).BIGINT : isUse ? Type.noType : attr.syms.booleanType; 
            // unreachable statements have a null expression
            if (tree.expression != null) {
            	var ty = attr.attribExpr(tree.expression,env,expectedType);
            	tree.expression.type = ty != attr.syms.errType ? ty : expectedType;
            }
            if (tree.optionalExpression != null) attr.attribExpr(tree.optionalExpression,env,Type.noType);
            attr.jmlenv = attr.jmlenv.pop();
            attr.jmlresolve.setAllowJML(prevAllowJML);
            return null; // No type returned
        }
    }
    
}
