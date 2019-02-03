package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.*;

import org.jmlspecs.openjml.IJmlClauseType;
import org.jmlspecs.openjml.IJmlVisitor;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeVisitor;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;

import com.sun.source.tree.TreeVisitor;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.Visitor;

public class RequiresClause extends JmlExtension.MethodClause {
    
    public static final String requiresID = "requires";
    
    public static final IJmlClauseType requiresClause = new MethodClauseExprType(requiresID) {
        
        public boolean isPreconditionClause() { return true; }
        
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
            JCExpression ex = null;
            if (scanner.token().kind == ELSE) {
                parser.nextToken();
                ex = parser.parseType();
            } 
            if (scanner.token().kind != SEMI) {
                parser.syntaxError(parser.pos(), null, "jml.invalid.expression.or.missing.semi");
                parser.skipThroughSemi();
            } else {
                parser.nextToken(); // skip SEMI
            }
            Node cl = new Node(pp, e, ex);
            return toP(cl);

        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree clause, Env<AttrContext> env) {
            if (!(clause instanceof Node)) throw new RuntimeException(); // FIXME - a better exception and message
            Node that = (Node)clause;
            Type t = attr.attribExpr(that.expression, env, syms.booleanType);
            if (that.exceptionType != null) {
                t = attr.attribType(that.exceptionType, env);
                that.exceptionType.type = t;
                // t has to be an exception type
            }
            return null;
        }
        

    };
    
    @Override
    public IJmlClauseType[]  clauseTypes() { return new IJmlClauseType[]{
            requiresClause}; }
    
    public static class Node extends JmlTree.JmlMethodClauseExpr {

        //@ nullable
        public JCExpression exceptionType;

        protected Node(int pos, JCExpression expression, JCExpression exceptionType) {
            super(pos, requiresID, requiresClause, expression);
            this.exceptionType = exceptionType;
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
