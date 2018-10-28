package org.jmlspecs.openjml.utils.ui;

import java.awt.BorderLayout;
import java.awt.Dialog;
import java.awt.Window;

import javax.swing.BoxLayout;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JTabbedPane;

import com.sun.tools.javac.tree.JCTree;

public class ASTViewer {
    
    public enum ViewType {DIALOG, FRAME};
    
    private static ASTViewer lastViewer;

    private ASTPanel astPanel;
    private ASTTreeNode root;
    private Window container;
    private JTabbedPane tabs;
    private ViewType type;
    
    public ASTViewer(ViewType type){
        this.type = type;
        
        if(this.type==ViewType.FRAME){
            initAsFrame();
        }else{
            initAsDialog();
        }
    }
    
    private void show(){
        if(this.type==ViewType.FRAME){
            container.pack();
            container.setVisible(true);
        }else{
            container.pack();
            container.setVisible(true);
        }
        
    }
    
    private void initAsDialog(){
        container = new JDialog(null, "AST Viewer", Dialog.ModalityType.DOCUMENT_MODAL);
        
        JDialog c = (JDialog)container;
        
        c.setLayout(new BorderLayout());
        
        // add the tabs
        tabs = new JTabbedPane();
        c.getContentPane().add(tabs, BorderLayout.CENTER);
    }
    
    private void initAsFrame(){
        container = new JFrame();
        JFrame c = (JFrame)container;

        c.setTitle("AST Viewer");
        c.setLayout(new BorderLayout());
        
        // add the tabs
        tabs = new JTabbedPane();
        c.getContentPane().add(tabs, BorderLayout.CENTER);
    }
    
   
    
    private void add(String title, JCTree root){
        tabs.addTab(title, new ASTView(title, root));
    }
    
    
    public static void addView(String title, JCTree root, ViewType t){
        
        if(lastViewer==null){
            lastViewer = new ASTViewer(t);
        }
        
        lastViewer.add(title, root);
        lastViewer.show();
    }
    
    public static void addView(String title, JCTree root){
        addView(title, root, ViewType.FRAME);
    }
    
    
    public static void view(String title, JCTree root, ViewType t){
        ASTViewer v = new ASTViewer(t);
        v.add(title, root);
        
        v.show();
    }
    
    public static void view(String title, JCTree root){
        view(title, root, ViewType.FRAME);
    }
    
    
    public static void main(String args[]){
        ASTViewer.addView("test", null);
       
        //System.exit(0);
    }
      

}
