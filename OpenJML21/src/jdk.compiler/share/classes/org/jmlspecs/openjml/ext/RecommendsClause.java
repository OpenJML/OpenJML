package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.*;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.visitors.IJmlVisitor;
import org.jmlspecs.openjml.visitors.JmlTreeVisitor;

import com.sun.source.tree.TreeVisitor;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;

public class RecommendsClause extends JmlExtension {
    
    public static final String recommendsID = "recommends";
    
    public static final IJmlClauseKind recommendsClauseKind = new MethodClauseExprType(recommendsID) {
        
        public boolean isPreconditionClause() { return true; }
        
        @Override
        public 
        JmlMethodClauseExpr parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            if (mods != null) {
                error(mods, "jml.message", "A " + keyword + " clause may not have modifiers");
                return null;
            }
            init(parser);
            
            int pp = parser.pos();
            parser.nextToken();
            JCExpression e = parser.parseExpression();
            JCExpression ex = null;
            if (parser.token().kind == ELSE) {
                parser.nextToken();
                ex = parser.parseType();
            } else {
                parser.syntaxError(parser.pos(), null, "jml.message", "A recommends clause must include an exception (recommends <expr> else <exception>;");
                parser.skipToSemi();
            }
            Node cl = new Node(pp, e, ex);
            cl.exception = ex;
            wrapup(cl, clauseType, true, true);
            return cl;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree clause, Env<AttrContext> env) {
            if (!(clause instanceof Node)) throw new RuntimeException(); // FIXME - a better exception and message
            Node that = (Node)clause;
            Type t = attr.attribExpr(that.expression, env, attr.syms.booleanType);
            if (that.exceptionType != null) {
                t = attr.attribType(that.exceptionType, env);
                that.exceptionType.type = t;
                // t has to be an exception type
            }
            return null;
        }
    };
    
    public static class Node extends JmlTree.JmlMethodClauseExpr {

        //@ nullable
        public JCExpression exceptionType;

        protected Node(int pos, JCExpression expression, JCExpression exceptionType) {
            super(pos, recommendsID, recommendsClauseKind, expression);
            this.exceptionType = exceptionType;
        }
        
        public Node copy() {
            Node n = new Node(pos, expression, exceptionType);
            n.type = type;
            n.keyword = keyword;
            return n;
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodClauseExpr(this); 
            } else {
                //System.out.println("A JmlMethodClauseExpr expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodClauseExpr(this, d);
            } else {
                System.out.println("A JmlMethodClauseExpr expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
}
