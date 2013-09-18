package org.jmlspecs.openjml.flowspecs;

import org.jmlspecs.openjml.JmlTree.JmlMethodClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTreeScanner;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCIf;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;

/**
 * A JML TreeScanner that uses the "enter" / "exit" pattern in the visitor. 
 * 
 * Notes:
 * - That this walker only implements a certain type of traversal relevant to type checking. We should probably generalize this pattern fully and make it available to developers.
 * - We are interested in JmlTreeScanner rather than just a tree scanner because we need to extract the method specifications 
 * to check declassification. 
 * 
 * @author JLS
 *
 */
public abstract class JmlEETreeScanner extends JmlTreeScanner {
    
    public JmlEETreeScanner() {
        super(AST_JML_MODE);
    }
    
    public void scan(JCTree tree){
        if (tree == null) return;
        super.scan(tree);
    }
    
//    @Override
//    public void visitJmlBinary(JmlTree.JmlBinary that) {
//        super.visitJmlBinary(that);
//    }

//    @Override
//    public void visitBinary(JCBinary that) {
//        super.visitBinary(that);
//    }
//
    @Override
    public void visitExec(JCExpressionStatement tree){
        enterExec(tree);
        super.visitExec(tree);
        exitExec(tree);
    }
    
    public abstract void enterExec(JCExpressionStatement tree);
    public abstract void exitExec(JCExpressionStatement tree);
    
    @Override
    public void visitIdent(JCIdent tree){
        enterIdent(tree);
        super.visitIdent(tree);
        exitIdent(tree);
    }
    
    public abstract void enterIdent(JCIdent tree);
    public abstract void exitIdent(JCIdent tree);
    
    @Override
    public void visitBlock(JCBlock tree)
    {
        enterBlock(tree);
        super.visitBlock(tree);
        exitBlock(tree);
    }

    public abstract void enterBlock(JCBlock tree);
    public abstract void exitBlock(JCBlock tree);
    
    @Override
    public void visitVarDef(JCVariableDecl tree){
        enterVarDef(tree);
        super.visitVarDef(tree);
        exitVarDef(tree);
    }
    
    public abstract void enterVarDef(JCVariableDecl tree);
    public abstract void exitVarDef(JCVariableDecl tree);
    
    @Override
    public void visitTopLevel(JCCompilationUnit tree){
        enterTopLevel(tree);
        exitTopLevel(tree);
        
        
    }
    
    public abstract void enterTopLevel(JCCompilationUnit tree);
    public abstract void exitTopLevel(JCCompilationUnit tree);

    @Override
    public void visitJmlMethodDecl(JmlMethodDecl tree){
        enterJmlMethodDecl(tree);
        super.visitJmlMethodDecl(tree);
        exitJmlMethodDecl(tree);
    }
    
    public abstract void enterJmlMethodDecl(JmlMethodDecl tree);
    public abstract void exitJmlMethodDecl(JmlMethodDecl tree);

    @Override
    public void visitIf(JCIf tree){
        enterIf(tree);
        super.visitIf(tree);
        exitIf(tree);
    }
    
    public abstract void enterIf(JCIf tree);
    public abstract void exitIf(JCIf tree);

    
    @Override
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl tree){
        enterJmlMethodClauseDecl(tree);
        exitJmlMethodClauseDecl(tree);
    }
    
    public abstract void enterJmlMethodClauseDecl(JmlMethodClauseDecl tree);
    public abstract void exitJmlMethodClauseDecl(JmlMethodClauseDecl tree);

    @Override
    public void visitAssign(JCAssign tree){
        enterAssign(tree);
        exitAssign(tree);
    }

    public abstract void enterAssign(JCAssign tree);
    public abstract void exitAssign(JCAssign tree);
    
}
