package org.jmlspecs.openjml;

import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.JmlTree.*;

public class JmlAstPrinter extends JmlTreeScanner {

    /** Use this method to emit a String containing a tree representation of 
     * an AST created in the given context. This representation is for debugging
     * purposes.
     */
    public static String print(JCTree tree, Context context) {
        var p = new JmlAstPrinter(context);
        //p.builder.append("AST FOR " + tree).append(eol);
        p.scan(tree);
        return p.builder.toString();
    }
    
    /** Creates the tree visitor used by 'print' above. */
    public JmlAstPrinter(Context context) {
        super(context);
    }
    
    /** The StringBuilder that accumulates the output String */
    public StringBuilder builder = new StringBuilder();
    
    /** The amount of a single indentation step */
    public static final String singleIndent = "  ";// Two-character indent set here
    
    public static final String sp = " ";
    public static final String eol = "\n";
    
    /** Current indentation level */
    int nindent = 0;
    /** Current indentation string */
    String indent;
    /** An array that holds indentation strings. It needs to be sized big enough as it is not expanded as needed. */
    String[] indents = new String[1000];
    {
        String s = "";
        for (int i = 0; i < indents.length; i++) { indents[i] = s; s = s + singleIndent; } 
        indent = indents[nindent];
    }
    /** Adds a level of indentation */
    public void in() { indent = indents[++nindent]; }
    /** Removes a level of indentation */
    public void out() { indent = indents[--nindent]; }
    
    /** Initiates a walk of the given AST */
    public void scan(JCTree t) { if (t != null) t.accept(this); }
    
    /** Abbreviated name of the class of the JCTree node */
    public String shortName(Object tree) {
        if (tree == null) return "<null>";
        String key = "JCTree$";
        String key2 = "JmlTree$";
        String cl = tree.getClass().toString();
        int k = cl.indexOf(key);
        if (k != -1) cl = cl.substring(k+key.length());
        else {
            k = cl.indexOf(key2);
            if (k != -1) cl = cl.substring(k+key2.length());
        }
        return cl;
    }
    
    public void start(JCTree tree) {
        String cvalue = (tree.type != null && tree.type.constValue() != null) ? "[" + (tree.type.toString().equals("boolean") ? (((Number)tree.type.constValue()).intValue()!=0)  : tree.type.constValue().toString() ) + "]" : "";
        builder.append(indent).append(shortName(tree)).append(sp).append(tree.getTag()).append(": ");
        if (tree instanceof JCExpression) builder.append(type(tree)).append(cvalue).append(" : ");
    }
    
    public String type(JCTree tree) {
        if (tree.type == null) return "?";
        return tree.type.toString();
    }
    
    /** Called for any trees with visit methods that are not implemented */
    public void visitTree(JCTree tree) {
        start(tree);
        
        builder.append(" ?????").append(eol);
        in();
//        super.visitTree(tree);
        out();
    }
    
    public void visitTopLevel(JCCompilationUnit tree) { // FIXME JmlCompilationUnit
        start(tree);
        builder.append(tree.packge).append(sp).append(tree.modle).append(sp).append(tree.sourcefile).append(eol);
        in();
        super.visitTopLevel(tree);
        out();
    }
    
    public void visitPackageDef(JCPackageDecl tree) {
        start(tree);
        builder.append(tree.packge).append(sp).append(tree.annotations).append(eol); // FIXME test annotations
        in();
        super.visitPackageDef(tree);
        out();
    }
    
    public void visitImport(JCImport tree) {
        start(tree);
        if (tree instanceof JmlImport i && i.isModel) builder.append("model").append(sp); 
        if (tree.isStatic()) builder.append("static"); 
        builder.append(eol);
        in();
        super.visitImport(tree);
        out();
    }
    
    public void visitClassDef(JCClassDecl tree) {  // FIXME JmlClassDecl - and more stuff
        start(tree);
        builder.append(tree.name.toString()).append(eol);
        in();
        super.visitClassDef(tree);
        out();
        
    }
    
    public void visitMethodDef(JCMethodDecl tree) {  // FIXME JmlMethodDecl - and more stuff
        start(tree);
        builder.append(tree.name.toString()).append(eol);
        in();
        super.visitMethodDef(tree);
        out();
        
    }
    
    public void visitBlock(JCBlock tree) { // FIXME - test patternMatchingCatch
        start(tree);
        builder.append(tree.flags).append(sp).append(com.sun.tools.javac.code.Flags.toString(tree.flags)).append(eol);
        in();
        super.visitBlock(tree);
        out();
        
    }
    
    public void visitVarDef(JCVariableDecl tree) { // FIXME JmlVarDef -- more fields
        start(tree);
        builder.append(tree.name.toString()).append(sp).append(tree.sym).append(sp).append(tree.mods).append(eol);
        in();
        super.visitVarDef(tree);
        out();
        
    }
    
    public void visitAnnotatedType(JCAnnotatedType tree) {
        start(tree);
        builder.append(eol);
        in();
        super.visitAnnotatedType(tree);
        out();
    }
    
    public void visitAnnotation(JmlAnnotation tree) {
        start(tree);
        builder.append(tree.kind.toString()).append(sp).append(tree.token).append(sp).append(tree.sourcefile).append(eol);
        in();
        super.visitAnnotation(tree);
        out();
    }
    
    public void visitExpression(JCExpression tree) { // FIXME - is this ever called?
        start(tree);
        builder.append(tree.toString()).append(eol);
        in();
        super.visitTree(tree);
        out();
    }
    
    public void visitIdent(JCIdent tree) {
        start(tree);
        builder.append(tree.name.toString()).append(eol);
        in();
        super.visitIdent(tree);
        out();
    }
    
    public void visitLiteral(JCLiteral tree) {
        start(tree);
        builder.append(tree.getValue()).append(sp).append(tree.typetag).append(sp).append(shortName(tree.getValue())).append(eol);
    }
    
    public void visitBinary(JCBinary tree) {
        start(tree);
        builder.append(tree.opcode).append(sp).append(tree.operator).append(eol);
        in();
        tree.lhs.accept(this);
        tree.rhs.accept(this);
        out();
    }
    
    public void visitJmlBinary(JmlBinary tree) {
        start(tree);
        builder.append(tree.op).append(eol);
        in();
        tree.lhs.accept(this);
        tree.rhs.accept(this);
        out();
    }
    
    public void visitUnary(JCUnary tree) { // FIXME JmlUnary
        start(tree);
        builder.append(tree.opcode).append(sp).append(tree.operator).append(eol);
        in();
        tree.arg.accept(this);
        out();
    }
    
    public void visitConditional(JCConditional tree) {
        start(tree);
        builder.append(eol);
        in();
        super.visitConditional(tree);
        out();
    }
    
    public void visitSelect(JCFieldAccess tree) {
        start(tree);
        builder.append(tree.name == null ? "*" : tree.name.toString());
        builder.append(sp).append(tree.sym).append(sp).append(tree.toString());
        builder.append(eol);
        in();
        super.visitSelect(tree);
        out();
    }
    
    public void visitApply(JCMethodInvocation tree) { // FIXME JmlMethodInvocation and more fields
        start(tree);
//        builder.append(tree.name.toString());
//        if (tree.type != null) builder.append(sp).append(String.valueOf(tree.type));
//        builder.append(sp).append(tree.toString());
        builder.append(eol);
        in();
        super.visitApply(tree);
        out();
    }
    
    public void visitTypeCast(JCTypeCast tree) {
        start(tree);
        builder.append(eol);
        in();
        super.visitTypeCast(tree);
        out();
    }
    
    public void visitTypeTest(JCInstanceOf tree) {
        start(tree);
        builder.append(tree.allowNull).append(eol);
        in();
        super.visitTypeTest(tree);
        out();
    }
}
