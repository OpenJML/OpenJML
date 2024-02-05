package org.jmlspecs.openjml;

import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.JmlTree.*;

public class JmlAstPrinter extends JmlTreeScanner {

    public static String print(JCTree tree, Context context) {
        var p = new JmlAstPrinter(context);
        //p.builder.append("AST FOR " + tree).append("\n");
        p.scan(tree);
        return p.builder.toString();
    }
    
    public JmlAstPrinter(Context context) {
        super(context);
    }
    
    public StringBuilder builder = new StringBuilder();
    
    int nindent = 0;
    String indent;
    String[] indents = new String[1000];
    {
        String s = "";
        for (int i = 0; i < indents.length; i++) { indents[i] = s; s = s + "  "; }
        indent = indents[nindent];
    }
    public void in() { indent = indents[++nindent]; }
    public void out() { indent = indents[--nindent]; }
    
    public String shortName(JCTree tree) {
        String cl = tree.getClass().toString();
        int k = cl.indexOf("JCTree$");
        if (k != -1) cl = cl.substring(k+7);
        else {
            k = cl.indexOf("JmlTree$");
            if (k != -1) cl = cl.substring(k+8);
        }
        return cl;
    }
    
    public void start(JCTree tree) {
        builder.append(indent).append(shortName(tree));
    }
    
    public void visitTree(JCTree tree) {
        start(tree);
        builder.append(" ?????\n");
        in();
//        super.visitTree(tree);
        out();
    }
    
    public void visitTopLevel(JCCompilationUnit tree) {
        start(tree);
        builder.append("\n");
        in();
        super.visitTopLevel(tree);
        out();
    }
    
    public void visitImport(JCImport tree) {
        start(tree);
        if (tree instanceof JmlImport i && i.isModel) builder.append(" model"); 
        if (tree.isStatic()) builder.append(" static"); 
        builder.append("\n");
        in();
        super.visitImport(tree);
        out();
    }
    
    public void visitClassDef(JCClassDecl tree) {
        start(tree);
        builder.append(": ").append(tree.name.toString());
        builder.append("\n");
        in();
        super.visitClassDef(tree);
        out();
        
    }
    
    public void visitMethodDef(JCMethodDecl tree) {
        start(tree);
        builder.append(": ").append(tree.name.toString());
        builder.append("\n");
        in();
        super.visitMethodDef(tree);
        out();
        
    }
    
    public void visitVarDef(JCVariableDecl tree) {
        start(tree);
        builder.append(": ").append(tree.name.toString());
        builder.append("\n");
        in();
        super.visitVarDef(tree);
        out();
        
    }
    
    public void visitAnnotatedType(JCAnnotatedType tree) {
        start(tree);
        builder.append("\n");
        in();
        super.visitAnnotatedType(tree);
        out();
    }
    
    public void visitAnnotation(JmlAnnotation tree) {
        start(tree);
        builder.append("\n");
        in();
        super.visitAnnotation(tree);
        out();
    }
    
    public void visitExpression(JCExpression tree) {
        start(tree);
        if (tree.type != null) builder.append(": ").append(String.valueOf(tree.type));
        builder.append(" ").append(tree.toString());
        builder.append("\n");
        in();
        super.visitTree(tree);
        out();
    }
    
    public void visitIdent(JCIdent tree) {
        start(tree);
        builder.append(": ").append(tree.name.toString());
        if (tree.type != null) builder.append(" ").append(String.valueOf(tree.type));
        builder.append("\n");
        in();
        super.visitIdent(tree);
        out();
    }
    
    public void visitSelect(JCFieldAccess tree) {
        start(tree);
        builder.append(": ").append(tree.name.toString());
        if (tree.type != null) builder.append(" ").append(String.valueOf(tree.type));
        builder.append(" ").append(tree.toString());
        builder.append("\n");
        in();
        super.visitSelect(tree);
        out();
    }
}
