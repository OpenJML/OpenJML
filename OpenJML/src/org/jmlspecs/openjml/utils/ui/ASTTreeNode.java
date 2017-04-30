package org.jmlspecs.openjml.utils.ui;

import java.util.ArrayList;
import java.util.List;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;

public class ASTTreeNode {
    
    private ASTTreeNode  root;
    public List<JCTree> data = new ArrayList<JCTree>();
    private MethodSymbol       sym;
    
    public ASTTreeNode(){
        this.data = null;
    }
    public ASTTreeNode(JCTree data){
        this.data.add(data);
    }
    
    public ASTTreeNode(List<? extends JCTree> data){
        this.data.addAll(data);
    }
    
    public List<ASTTreeNode> children = new ArrayList<ASTTreeNode>();
    
    public void setRoot(ASTTreeNode n){
        this.root = n;
    }
    
    public ASTTreeNode getRoot(){
        return this.root;
    }
    
    public void addChild(ASTTreeNode n){
        this.getRoot().children.add(n);
    }
    
    public void refine(JCTree n){
        this.getRoot().data.add(n);
    }
    public void refine(MethodSymbol s){
        this.getRoot().sym = s;
    }
    
    public void refine(List<? extends JCTree> ns){
        this.getRoot().data.addAll(ns);
    }

    public String getNodeRep(boolean detail){ 
        
        JCTree tree = data.get(0);
        
        if(tree instanceof JCClassDecl){
            JCClassDecl n = (JCClassDecl) tree;
            return String.format("%s : %s", n.name, n.getClass().getSimpleName());
        }else if(tree instanceof JCMethodDecl){
            JCMethodDecl n = (JCMethodDecl) tree;
            
            String resType = (n.restype==null) ? "N/A" : n.restype.getClass().getSimpleName();
            String sym = (n.sym==null) ? "N/A" : n.sym.getClass().getSimpleName();
            String type = (n.type==null) ? "N/A" : n.type.getClass().getSimpleName();
                    
            if(detail)
                return String.format("%s [%s] %s() [%s] [[restype=%s, sym=%s, type=%s]]", n.mods.toString(), n.mods.getClass().getSimpleName(), n.name, n.getClass().getSimpleName(), resType, sym, type);
            else
                return String.format("%s() [%s]", n.name, n.getClass().getSimpleName());
            
        }else if(tree instanceof JCExpressionStatement){
            JCExpressionStatement n = (JCExpressionStatement) tree;

            if(detail)
                return String.format("%s [%s] (%s)", n.toString(), n.getClass().getSimpleName(),  n.expr.getClass().getSimpleName());
            else
                return String.format("%s [%s]", n.toString(), n.getClass().getSimpleName());
                
        }
            return "xxx" + tree.getClass().getSimpleName() + "xxx";
    }
        
    
    public String toString(){
        return getNodeRep(true);
    }
    
}
