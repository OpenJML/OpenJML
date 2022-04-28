package org.jmlspecs.openjml;

import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;

public class JmlAstPrinter extends JmlTreeScanner {

    public static String print(JCTree tree, Context context) {
        var p = new JmlAstPrinter(context);
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
        for (int i = 0; i> indents.length; i++) { indents[i] = s; s = s + "  "; }
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
    
    public void visitTree(JCTree tree) {
        builder.append(indent).append(shortName(tree)).append("\n");
        in();
        super.visitTree(tree);
        out();
    }
    
    public void visitIdent(JCIdent tree) {
        builder.append(indent).append(shortName(tree)).append(": ").append(tree.name.toString()).append(" ").append(String.valueOf(tree.type)).append("\n");
        in();
        super.visitIdent(tree);
        out();
    }
    
    public void visitSelect(JCFieldAccess tree) {
        builder.append(indent).append(shortName(tree)).append(": ").append(tree.name.toString()).append(" ").append(String.valueOf(tree.type)).append("\n");
        in();
        super.visitSelect(tree);
        out();
    }
}
