package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.COLON;
import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.IJmlLoop;
import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;
import org.jmlspecs.openjml.JmlTree.JmlIfStatement;
import org.jmlspecs.openjml.JmlTree.JmlSwitchStatement;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.ext.ReachableStatement.ExprStatementType;

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
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCLiteral;

public class StatementExprExtensions extends JmlExtension {
    
    public static final String assertID = "assert";
    public static final String checkID = "check";
    public static final String assumeID = "assume";
    public static final String commentID = "comment";
    public static final String useID = "use";
    public static final String loopinvariantID = "loop_invariant";
    public static final String loopdecreasesID = "loop_decreases";
    public static final String splitID = "split";

    
    public static final IJmlClauseKind assertClause = new StatementExprType(assertID);
    public static final IJmlClauseKind checkClause = new StatementExprType(checkID);
    public static final IJmlClauseKind assumeClause = new StatementExprType(assumeID);
    public static final IJmlClauseKind commentClause = new StatementExprType(commentID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree t, Env<AttrContext> env) {
            var type = super.typecheck(attr,  t,  env);
            if (t instanceof JmlTree.JmlStatementExpr tree && !(tree.expression instanceof JCLiteral lit)) {
                utils.error(tree.expression != null ? tree.expression : tree,
                        "jml.message", "A comment statement may only contain a string literal");
            }
            return type;
        }
    };
    
    public static final IJmlClauseKind splitClause = new StatementExprType(splitID);
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
        public JCTree parse(JCModifiers mods, String id, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            int pp = parser.pos();

            parser.nextToken(); // skip over the keyword
            var n = parser.parseOptionalName();

            JCExpression t;
            if ((parser.token().kind == SEMI || parser.isEndJml()) && clauseType == splitClause) {
                // expression is optional in split statement
                t = null;
            } else {
                t = parser.parseExpression();
            }
            if (t instanceof JCTree.JCErroneous) parser.skipToSemi();
            String nm = clauseType.keyword();
            JmlAbstractStatement ste;
            JmlTree.JmlStatementExpr st = null;
            if (clauseType == StatementExprExtensions.loopinvariantClause ||
                    clauseType == StatementExprExtensions.loopdecreasesClause) {
                ste = parser.maker()
                        .at(pp)
                        .JmlStatementLoopExpr(
                                clauseType,
                                    t);
            } else {
                st = parser.maker()
                        .at(pp)
                        .JmlExpressionStatement(
                                nm,
                                clauseType,
                                nm == assumeID ? Label.EXPLICIT_ASSUME :
                                    Label.EXPLICIT_ASSERT,  // FIXME?
                                    t);
                st.keyword = id;
                Token tk = parser.token();
                if (tk.kind == COLON) {
                    if (clauseType == assertClause || clauseType == assumeClause) {
                        parser.nextToken();
                        st.optionalExpression = parser.parseExpression();
                    } else {
                        utils.error(tk.pos, "jml.message", "A secondary expression is only permitted for assert or assume statements");
                        parser.skipToSemi();
                    }
                }
                ste = st;
            }
            wrapup(ste,clauseType,true, clauseType != splitClause);
            if (clauseType == splitClause && st.expression == null) {
                while (parser.jmlTokenClauseKind() == Operators.endjmlcommentKind) parser.nextToken();
                JCStatement stt = parser.blockStatement().head;
                if (stt instanceof JmlIfStatement stif) {
                    stif.split = true;
                    while (stif.elsepart instanceof JmlIfStatement stiff) {
                        stiff.split = true;
                        stif = stiff;
                    }
                } else if (stt instanceof JmlSwitchStatement) {
                    ((JmlSwitchStatement)stt).split = true;
                } else if (stt instanceof IJmlLoop) {
                    ((IJmlLoop)stt).setSplit(true);
                } else {
                    utils.warning(ste, "jml.message", "Ignoring out of place split statement");
                }
                return stt;
            }
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
            Type expectedType = tree.clauseType == loopdecreasesClause ? JmlPrimitiveTypes.bigintTypeKind.getType(attr.context)
                : isUse ? Type.noType
                : tree.clauseType == commentClause ? attr.syms.stringType
                : attr.syms.booleanType; 
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
