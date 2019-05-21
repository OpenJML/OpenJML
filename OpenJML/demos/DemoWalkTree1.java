// DemoWalkTree1.java
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import com.sun.tools.javac.tree.JCTree;

public class DemoWalkTree1 {

    static class Walker extends JmlTreeScanner {

        int nodes = 0;
        int jmlopcount = 0;
        int allopcount = 0;
        
        @Override
        public void scan(JCTree node) {
            if (node != null) System.out.println("Node: " + node.getClass());
            if (node != null) nodes++;
            super.scan(node);
        }
        
        @Override
        public void visitJmlBinary(JmlTree.JmlBinary that) {
            jmlopcount++;
            allopcount++;
            super.visitJmlBinary(that);
        }

        @Override
        public void visitBinary(JCTree.JCBinary that) {
            allopcount++;
            super.visitBinary(that);
        }

    }
    public static void main(String[] argv) {
        try {
            IAPI m = Factory.makeAPI();
            Walker visitor = new Walker();
            JCTree.JCExpression expr = m.parseExpression("(a+b)*c", false);
            visitor.scan(expr);
            System.out.println("Counts: " + visitor.nodes + " " + 
                visitor.allopcount + " " + visitor.jmlopcount);
            expr = m.parseExpression("a <==> \\result", true);
            visitor.scan(expr);
            System.out.println("Counts: " + visitor.nodes + " " + 
                visitor.allopcount + " " + visitor.jmlopcount);

        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}
