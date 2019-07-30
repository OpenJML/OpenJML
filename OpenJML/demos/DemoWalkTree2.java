// DemoWalkTree2.java
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import com.sun.tools.javac.tree.JCTree;

public class DemoWalkTree2 {

    static class Walker extends JmlTreeScanner {

        public Walker(int mode) {
            super(mode);
        }

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
            java.io.File f = new java.io.File("src/demo/A.java");
            IAPI m = Factory.makeAPI("-specspath","specs","-sourcepath","src","-noPurityCheck");
            JmlTree.JmlCompilationUnit expr = m.parseFiles(f).get(0);
            Walker visitor = new Walker(Walker.AST_JAVA_MODE);
            visitor.scan(expr);
            System.out.println("Counts: " + visitor.nodes + " " + 
                visitor.allopcount + " " + visitor.jmlopcount);
            visitor = new Walker(Walker.AST_JML_MODE);
            visitor.scan(expr);
            System.out.println("Counts: " + visitor.nodes + " " + 
                visitor.allopcount + " " + visitor.jmlopcount);
            try {
                visitor = new Walker(Walker.AST_SPEC_MODE);
                visitor.scan(expr);
                System.out.println("Counts: " + visitor.nodes + " " + 
                    visitor.allopcount + " " + visitor.jmlopcount);
            } catch (Exception e) {
                System.out.println("EXCEPTION: "  + e);
            }
            m.typecheck(expr);
            visitor = new Walker(Walker.AST_SPEC_MODE);
            visitor.scan(expr);
            System.out.println("Counts: " + visitor.nodes + " " + 
                visitor.allopcount + " " + visitor.jmlopcount);

        } catch (Exception e) {
            System.out.println(e);         
        }
    }
}
