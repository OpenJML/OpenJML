package org.jmlspecs.openjml.loopinvariantinference;

import org.jmlspecs.openjml.JmlTree;

import com.sun.source.tree.TreeVisitor;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Name;

public class JmlRapidTree extends JmlTree {

    public static class JmlReturn extends JCTree.JCReturn {
        protected JmlReturn(JCExpression expr) {
            super(expr);
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlRapidVisitor) {
                ((IJmlRapidVisitor)v).visitJmlReturn(this);
            } else {
                //System.out.println("A JmlStatementSpec expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }
    }
    
    public static class JmlRapidParens extends JCParens {

        protected JmlRapidParens(JCExpression expr) {
            super(expr);
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlRapidVisitor) {
                ((IJmlRapidVisitor)v).visitJmlRapidParen(this); 
            } else {
                super.accept(v);
            }
        }
    }
    
    public static class JmlRapidBinary extends JCBinary {

        protected JmlRapidBinary(Tag opcode, JCExpression lhs, JCExpression rhs,
                Symbol operator) {
            super(opcode, lhs, rhs, operator);
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlRapidVisitor) {
                ((IJmlRapidVisitor)v).visitJmlRapidBinary(this); 
            } else {
                super.accept(v);
            }
        }
    }
    
    public static class JmlRapidFieldAccess extends JCFieldAccess {

        protected JmlRapidFieldAccess(JCExpression selected, Name name,
                Symbol sym) {
            super(selected, name, sym);
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlRapidVisitor) {
                ((IJmlRapidVisitor)v).visitJmlRapidFieldAccess(this); 
            } else {
                super.accept(v);
            }
        }
    }
    
    public static class JmlRapidUnary extends JCUnary {

        protected JmlRapidUnary(Tag opcode, JCExpression arg) {
            super(opcode, arg);
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlRapidVisitor) {
                ((IJmlRapidVisitor)v).visitJmlRapidUnary(this); 
            } else {
                super.accept(v);
            }
        }
    }
    
    public static class JmlRapidReturn extends JCReturn {

        protected JmlRapidReturn(JCExpression expr) {
            super(expr);
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlRapidVisitor) {
                ((IJmlRapidVisitor)v).visitJmlRapidReturn(this); 
            } else {
                super.accept(v);
            }
        }
    }
}
