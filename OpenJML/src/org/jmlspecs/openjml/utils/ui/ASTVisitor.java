package org.jmlspecs.openjml.utils.ui;

import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeScanner;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.util.List;

public class ASTVisitor extends TreeScanner {

    public ASTTreeNode root = new ASTTreeNode();
    
    public ASTVisitor(){
        root.setRoot(root);
    }
    
    /** Visitor method: Scan a single node.
     */
    public void scan(JCTree tree) {
        if(tree!=null) tree.accept(this);
    }

    /** Visitor method: scan a list of nodes.
     */
    public void scan(List<? extends JCTree> trees) {
        if (trees != null)
        for (List<? extends JCTree> l = trees; l.nonEmpty(); l = l.tail)
            scan(l.head);
    }
    
    public void visitClassDef(JCClassDecl tree) {
        
        ASTTreeNode previousRoot = root.getRoot();
        ASTTreeNode newRoot = new ASTTreeNode(tree);
            
        // add me to the previous root's children
        root.addChild(newRoot);
        
        // and make me the new root.
        newRoot.setRoot(root.getRoot());
        root.setRoot(newRoot);
        
        root.refine(tree.mods);
        root.refine(tree.typarams);
        root.refine(tree.extending);
        root.refine(tree.implementing);
        
        // scan(tree.mods);
        // scan(tree.typarams);
        // scan(tree.extending);
        // scan(tree.implementing);
        scan(tree.defs);
        
        root.setRoot(previousRoot);
    }
    
    public void visitMethodDef(JCMethodDecl tree) {
        
        ASTTreeNode previousRoot = root.getRoot();
        
        ASTTreeNode newRoot = new ASTTreeNode(tree);
        root.addChild(newRoot);
        newRoot.setRoot(root.getRoot());
        root.setRoot(newRoot);
        
        root.refine(tree.mods);
        root.refine(tree.restype);
        root.refine(tree.typarams);
        root.refine(tree.params);
        root.refine(tree.thrown);
        root.refine(tree.defaultValue);
        root.refine(tree.sym);
        
        
//        scan(tree.mods);
//        scan(tree.restype);
//        scan(tree.typarams);
//        scan(tree.params);
//        scan(tree.thrown);
//        scan(tree.defaultValue);
        scan(tree.body);
        
        root.setRoot(previousRoot);
    }

    public void visitBlock(JCBlock tree) {
        scan(tree.stats);
    }
    
    public void visitExec(JCExpressionStatement tree) {
        // each expression statement gets a new node as a child
        ASTTreeNode previousRoot = root.getRoot();
        
        ASTTreeNode newRoot = new ASTTreeNode(tree);
        root.addChild(newRoot);
        newRoot.setRoot(root.getRoot());

        root.setRoot(newRoot);
        
        scan(tree.expr);
        
        root.setRoot(previousRoot);        
    }
    
    public void visitExpression(JCExpression tree) {
        root.addChild(new ASTTreeNode(tree));
    }
    
}
