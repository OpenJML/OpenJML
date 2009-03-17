package org.jmlspecs.openjml;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;

import org.jmlspecs.annotations.*;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCImport;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;

public class JmlPretty extends Pretty implements IJmlVisitor {

    // Pretty was not originally a registered tool.  In order to be able to
    // slide in JmlPretty, I added a registration mechanism, but see the comments
    // in Pretty: it does not depend on context (so compiler options are not
    // available).
    public static void preRegister(final Context context) {
        cachedInstance = new JmlPretty(null,false); 
    }

    protected JmlPretty inst(Writer out, boolean sourceOutput) {
        return new JmlPretty(out,sourceOutput);
    }

    
    /** The Writer to which this pretty printer prints, initialized in the
     * constructor
     */
    /*@ non_null*/ protected Writer out;
    
    protected boolean sourceOutput;
    
    public boolean useJMLComments;
        
    /** Instantiates a pretty-printer for Jml nodes with default indentation
     * @param out the Write to which output is to be put
     * @param sourceOutput whether to produce output that is equivalent to source code
     *   (if false, there may be additional, uncompilable, information)
     */
    public JmlPretty(/*@non_null*/Writer out, boolean sourceOutput) {
        super(out, sourceOutput);
        this.out = out;
        this.width = 2;
        this.sourceOutput = sourceOutput;
        this.useJMLComments = sourceOutput;
    }
    
    /** Writes out a tree in pretty-printed fashion, with two-character indentation
     * 
     * @param tree the tree to print
     * @return the resulting text
     */
    static public @NonNull String write(@NonNull JCTree tree) {
        StringWriter sw = new StringWriter();
        JmlPretty p = new JmlPretty(sw,true);
        p.width = 2;
        tree.accept(p);
        return sw.toString();
        //return write("","  ",tree);
    }
    
    /** A method used for those pretty-printing methods that are not yet
     * implemented; it just prints the class type.
     * @param that a non-null AST node
     * @throws IOException if there is a problem writing to the writer
     */
    protected void notImpl(/*@non_null*/JCTree that) throws IOException {
            out.write("<");
            out.write(that.getClass().toString());
            out.write(">");
    }
    
    /** A method used to report exceptions that happen on writing to the writer
     * 
     * @param that a non-null AST node
     * @param e the exception that is being reported
     */
    protected void perr(/*@ non_null*/JCTree that, /*@ non_null*/Exception e) {
        System.err.println(e.getClass() + " error in JMLPretty: " + that.getClass());
    }
    
    // FIXME _ needs to fix parentheses??? Like JCBInary does???
    public void visitJmlBinary(JmlBinary that) {
        try {
            out.write("(");
            that.lhs.accept(this);
            out.write(" ");
            out.write(that.op.internedName());
            out.write(" ");
            that.rhs.accept(this);
            out.write(")");
        } catch (IOException e) { perr(that,e); }
    }
    
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        try {
            print(that.token.internedName());
            print("(");
            printExprs(that.args);
            print(")");
        } catch (IOException e) { perr(that,e); }
    }


    public void visitJmlLblExpression(JmlLblExpression that) {
        try { 
            out.write("(");
            out.write(that.token.internedName());
            out.write(" ");
            out.write(that.label.toString());
            out.write(" ");
            that.expression.accept(this);
            out.write(")");
        } catch (IOException e) { perr(that,e); }
    }
    
    public void visitJmlRefines(JmlRefines that) {
        try { 
            out.write("//@ refines \"");
            out.write(that.filename);
            out.write("\";");
            println();
        } catch (IOException e) { perr(that,e); }
    }
    
    public void visitJmlImport(JmlImport that) {
        try {
            if (that.isModel) out.write("//@ model ");
            print("import ");
            if (that.staticImport) print("static ");
            printExpr(that.qualid);
            print(";");
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        try {
            if (that.cases.size() == 1) {
                that.cases.get(0).accept(this);
            } else {  // FIXME - handle indenting properly
                out.write("         {|");
                boolean first = true;
                for (JmlSpecificationCase t: that.cases) {
                    if (first) first = false;
                    else out.write("         also");
                    t.accept(this);
                }
                out.write("         |}");
            }
            
        } catch (IOException e) { perr(that,e); }
    }
    

    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        try { 
            for (JCTree.JCStatement s: that.stats) {
                out.write("         ");
                out.write(that.token.internedName());
                out.write(" ");
                s.accept(this);
                out.write(";");
                println();
            }
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        try { 
            out.write("         ");
            out.write(that.token.internedName());
            out.write(" ");
            that.expression.accept(this);
            out.write(";");
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        try { 
            out.write("         ");
            out.write(that.token.internedName());
            out.write(" ");
            that.expression.accept(this);
            if (that.predicate != null) {
                out.write(" if ");
                that.predicate.accept(this);
            }
            out.write(";");
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly that) {
        try { 
            out.write("         ");
            out.write(that.token.internedName());
            out.write(" ");
            for (JCExpression item: that.list) item.accept(this);
            out.write(";");
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseAssignable(JmlMethodClauseAssignable that) {
        try { 
            out.write("         ");
            out.write(that.token.internedName());
            out.write(" ");
            for (JCTree item: that.list) item.accept(this);
            out.write(";");
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        try { 
            out.write("         ");
            out.write(that.token.internedName());
            out.write(" (");
            if (that.vardef != null) {
                that.vardef.vartype.accept(this);
                out.write(" ");
                out.write(that.vardef.name.toString());
            }
            out.write(") ");
            that.expression.accept(this);
            out.write(";");
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        try { 
            if (useJMLComments) out.write("    /*@"); println();
            for (JmlSpecificationCase c: that.cases) {
                c.accept(this);
            }
            if (useJMLComments) out.write("    */"); println();
        } catch (Exception e) { perr(that,e); }
        
    }

    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        try { 
            out.write("(");
            out.write(that.op.internedName());
            out.write(" ");
            for (JCTree.JCVariableDecl n: that.decls) {
                out.write(n.toString());
                out.write(",");  // FIXME - one too many commas
            }
            out.write(";");
            if (that.range != null) that.range.accept(this);
            out.write(";");
            that.predicate.accept(this);
            out.write(")");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlSetComprehension(JmlSetComprehension that) {
        try { notImpl(that);  // FIXME
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlSingleton(JmlSingleton that) {
        try {
            out.write(that.toString());
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        try { 
            if (that.token == null) {
                // lightweight
            } else {
                out.write("      ");
                out.write(that.token.internedName());
                println();
            }
            for (JmlMethodClause c: that.clauses) {
                c.accept(this);
                //s.append(c.toString(indent2));
            }
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlStatement(JmlStatement that) {
        that.statement.accept(this);
    }

    public void visitJmlStatementLoop(JmlStatementLoop that) {
        try { 
            print("         ");
            if (useJMLComments) print("  //@ ");
            print(that.token.internedName());
            print(" ");
            that.expression.accept(this);
            print(";");
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlStatementSpec(JmlStatementSpec that) {
        that.statementSpecs.accept(this);
    }

    public void visitJmlStatementExpr(JmlStatementExpr that) {
        try { 
            if (useJMLComments) print ("/*@ ");  // FIXME - this is needed in lots more places
            print(that.token.internedName());
            print(" ");
            if (that.label != null && !sourceOutput) {
                print(that.label);
                print(" ");
            }
            printExpr(that.expression); 
            print(";");
            if (useJMLComments) print("*/");
            println();
        } catch (IOException e) { perr(that,e); }
        
    }

    public void visitJmlStatementDecls(JmlStatementDecls that) {
        try { notImpl(that);  // FIXME
        } catch (IOException e) { perr(that,e); }
        
    }

    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        try { 
            if (useJMLComments) print("  //@ ");
            printFlags(that.modifiers.flags);
            print(that.token.internedName());
            print(" ");
            printExpr(that.expression);
            print(";");
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        try { 
            print(that.decl);
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        try { 
            print(that.token.internedName());
            for (JmlGroupName g: that.list) {
                print(" ");
                print(g.selection);
            }
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        try {
            print(that.token.internedName());
            print(" ");
            print(that.expression);
            print(" \\into");
            for (JmlGroupName g: that.list) {
                print(" ");
                print(g.selection);
            }
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlGroupName(JmlGroupName that) {
        try { notImpl(that); } // FIXME
        catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        try { 
            that.specs.accept(this);
            print(that.token.internedName());
            print(" {}");
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        try {
            if (useJMLComments) print("  //@ ");
            printFlags(that.modifiers.flags);
            print(that.token.internedName());
            print(" ");
            that.expression.accept(this);
            if (that.sigs != null && !that.sigs.isEmpty()) {
                print(" for SIGNATURES"); // FIXME
            }
            out.write(";");
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        try { 
            if (useJMLComments) print("  //@ ");
            printFlags(that.modifiers.flags);
            out.write(that.token.internedName());
            out.write(" ");
            that.ident.accept(this);
            out.write(" = ");
            that.expression.accept(this);
            out.write(";");
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        try { notImpl(that); 
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        try { notImpl(that); 
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        try { out.write(that.token.internedName()); 
        } catch (IOException e) { perr(that,e); }
        
    }

    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        try {
            that.expression.accept(this);
            out.write('[');
            if (that.lo == null) {
                out.write('*');
            } else if (that.hi == that.lo) {
                that.lo.accept(this);
            } else if (that.hi == null) {
                that.lo.accept(this);
                out.write(" .. *");
            } else {
                that.lo.accept(this);
                out.write(" .. ");
                that.hi.accept(this);
            }
        } catch (IOException e) { perr(that,e); }
    }

//    @Override
//    public void visitJmlStoreRefField(JmlStoreRefField that) {
//        try {
//            that.expression.accept(this);
//            out.write('.');
//            out.write(that.ident.toString());
//        } catch (Exception e) {}
//    }
//
//    @Override
//    public void visitJmlStoreRefIdent(JmlStoreRefIdent that) {
//        try {
//            if (that.ident != null) that.ident.accept(this);
//            if (that.token != null) out.write(that.token.toString());
//        } catch (Exception e) {}
//    }

    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        try { 
            out.write(that.token.internedName()); 
        } catch (IOException e) { perr(that,e); }
    }
    
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        try { notImpl(that);         
        } catch (IOException e) { perr(that,e); }

    }


    static final String prefix = "org.jmlspecs.annotations";
    @Override
    public void visitAnnotation(JCAnnotation tree) {
        try {
            String s = tree.annotationType.toString();
            if (s.startsWith(prefix)) {
                s = s.substring(prefix.length());
                print("@");
                print(s);
            } else {
                super.visitAnnotation(tree);
            }
        } catch (IOException e) {
            //throw e;
        }
    }
    
    @Override
    public void printAnnotations(List<JCAnnotation> trees) throws IOException {
        for (List<JCAnnotation> l = trees; l.nonEmpty(); l = l.tail) {
            printStat(l.head);
            print(" ");
        }
        println();
        align();
    }

    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        for (JmlStatementLoop s: that.loopSpecs) {
            s.accept(this);
        }
        super.visitDoLoop(that);
        
    }

    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        for (JmlStatementLoop s: that.loopSpecs) {
            s.accept(this);
        }
        super.visitForeachLoop(that);
    }

    public void visitJmlForLoop(JmlForLoop that) {
        if (that.loopSpecs != null) for (JmlStatementLoop s: that.loopSpecs) {
            s.accept(this);
        }
        super.visitForLoop(that);
    }

    public void visitJmlWhileLoop(JmlWhileLoop that) {
        if (that.loopSpecs != null) for (JmlStatementLoop s: that.loopSpecs) {
            s.accept(this);
        }
        super.visitWhileLoop(that);
    }

    public void visitJmlClassDecl(JmlClassDecl that) {
        // FIXME - does this print the class specs?
        visitClassDef(that);
    }
    
    boolean inSequence = false;

    public void visitJmlCompilationUnit(JmlCompilationUnit tree) {
        // Duplicated from the super class in order to insert printing the refines statement - MAINTENANCE
        try {
            printDocComment(tree);
            if (tree.pid != null) {
                print("package ");
                printExpr(tree.pid);
                print(";");
                println();
            }
            if (tree.refinesClause != null) {
                tree.refinesClause.accept(this);
            }
            boolean firstImport = true;
            for (List<JCTree> l = tree.defs; l.nonEmpty(); l = l.tail) {
                if (l.head.getTag() == JCTree.IMPORT) {
                    JCImport imp = (JCImport)l.head;
                    if (true) {
                        if (firstImport) {
                            firstImport = false;
                            println();
                        }
                        printStat(imp);
                    }
                } else {
                    printStat(l.head);
                }
            }
            if (!inSequence && tree.specsSequence != null) {
                inSequence = true;
                println();
                print("// Refinement Sequence:");
                for (JmlCompilationUnit jcu : tree.specsSequence) {
                    print(" ");
                    print(jcu.sourcefile);
                }
                println();
                for (JmlCompilationUnit jcu : tree.specsSequence) {
                    print("// Specification file: " + jcu.sourcefile); 
                    println();
                    jcu.accept(this);
                    println();
                }
                inSequence = false;
            }
        } catch (IOException e) {
            perr(tree,e);
        }
    }

    public void visitJmlMethodDecl(JmlMethodDecl that) {
        if (that.methodSpecs != null) that.methodSpecs.accept(this);
        visitMethodDef(that);
    }

    //@ xxxx
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        visitVarDef(that);  // FIXME - print field specs
    }
    
    public void visitLiteral(JCLiteral that) {
        if (that.value instanceof Type) {
            try {
                print(that.value.toString());
            } catch (IOException e) {
                perr(that,e);
            }
        } else {
            super.visitLiteral(that);
        }
    }

}
