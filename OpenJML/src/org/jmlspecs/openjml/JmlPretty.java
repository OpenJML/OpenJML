package org.jmlspecs.openjml;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;

import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.BasicProgram.AuxVarDSA;
import org.jmlspecs.openjml.esc.BasicProgram.ProgVarDSA;

import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;

public class JmlPretty extends Pretty implements IJmlVisitor {

//    public static void preRegister(final Context context) {
//        context.put(prettyKey, new Context.Factory<Pretty>() {
//            public Pretty make() {
//                return new JmlPretty(context); 
//            }
//        });
//    }
    
    /** The Writer to which this pretty printer prints, initialized in the
     * constructor
     */
    /*@ non_null*/ Writer out;
    
    /** The character string that is the leading part of each line*/
    /*@ non_null*/ public String indentAmount;
    
    /** The character string that is the additional indent */
    /*@ non_null*/ public String indentExtra;
    
    /** The current indent string, only used internally; this should be
     * indentAmount + zero or more copies of indentExtra
     */
    ///*@ non_null*/ protected String currentIndent;
    
    // TODO - and what about the indents?
    public JmlPretty(/*@non_null*/Writer out, boolean sourceOutput) {
        super(out, sourceOutput);
        this.out = out;
    }
    
    // TODO
    public JmlPretty(/*@non_null*/String indentAmount, /*@non_null*/String indentExtra) {
        this(new StringWriter(),true);
        this.indentAmount = indentAmount;
        this.indentExtra = indentExtra;
    }
    
    // TODO
    static String write(String in, String ad, JCTree tree) {
        StringWriter sw = new StringWriter();
        JmlPretty p = new JmlPretty(sw,true);
        p.indentAmount = in;
        p.indentExtra = ad;
        tree.accept(p);
        return sw.toString();
    }
    
    /** A method used for those pretty-printing methods that are not yet
     * implemented; it just prints the class type.
     * @param that a non-null AST node
     * @throws IOException if there is a problem writing to the writer
     */
    public void notImpl(/*@non_null*/JCTree that) throws IOException {
            out.write("<");
            out.write(that.getClass().toString());
            out.write(">");
    }
    
    /** A method used to report exceptions that happen on writing to the writer
     * 
     * @param that a non-null AST node
     * @param e the exception that is being reported
     */
    public void perr(/*@ non_null*/JCTree that, /*@ non_null*/Exception e) {
        System.err.println(e.getClass() + " error in JMLPretty: " + that.getClass());
    }

    public void visitJmlBinary(JmlBinary that) {
        try {
            that.lhs.accept(this);
            out.write(that.op.internedName());
            that.rhs.accept(this);
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlLblExpression(JmlLblExpression that) {
        try { notImpl(that); } // FIXME
        catch (IOException e) { perr(that,e); }
    }
    
    public void visitJmlRefines(JmlRefines that) {
        try { 
            out.write(that.toString());
        } catch (IOException e) { perr(that,e); }
    }
    
    public void visitJmlImport(JmlImport that) {
        // FIXME - print model
        visitImport(that);
    }

    public void visitJmlFunction(JmlFunction that) {
        try { 
            out.write(that.token.internedName());
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {
        // FIXME
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
        try { notImpl(that); // FIXME
        } catch (IOException e) { perr(that,e); } 
    }

    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly that) {
        try { notImpl(that);  // FIXME
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseAssignable(JmlMethodClauseAssignable that) {
        try { notImpl(that);  // FIXME
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        try { notImpl(that);  // FIXME
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        try { 
            for (JmlSpecificationCase c: that.cases) {
                c.accept(this);
            }
        } catch (Exception e) { perr(that,e); }
        
    }

    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        try { notImpl(that);  // FIXME
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
            out.write("      ");
            //String indent2 = indent + "  ";  // FIXME - indenting?
            out.write(that.token == null ? "<lightweight>" : that.token.internedName());
            println();
            for (JmlMethodClause c: that.clauses) {
                c.accept(this);
                //s.append(c.toString(indent2));
            }
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlStatement(JmlStatement that) {
        try { notImpl(that);  // FIXME
        } catch (IOException e) { perr(that,e); }
        
    }

    public void visitJmlStatementLoop(JmlStatementLoop that) {
        try { notImpl(that);  // FIXME
        } catch (IOException e) { perr(that,e); }
        
    }

    public void visitJmlStatementSpec(JmlStatementSpec that) {
        try { notImpl(that);  // FIXME
        } catch (IOException e) { perr(that,e); }
        
    }

    public void visitJmlStatementExpr(JmlStatementExpr that) {
        try { 
            print(that.token.internedName());
            print(" ");
            if (that.label != null) {
                print(that.label);
                print(" ");
            }
            printExpr(that.expression); 
            print(";");
            println();
        } catch (IOException e) { perr(that,e); }
        
    }

    public void visitJmlStatementDecls(JmlStatementDecls that) {
        try { notImpl(that);  // FIXME
        } catch (IOException e) { perr(that,e); }
        
    }

    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        try { 
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
            print(" ");
            print("?????"); // FIXME
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        try { notImpl(that); }  // FIXME
        catch (IOException e) { perr(that,e); }
    }

    public void visitJmlGroupName(JmlGroupName that) {
        try { notImpl(that); } // FIXME
        catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        try { 
            out.write(that.token.internedName());  // FIXME - indent, eol
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        try { notImpl(that); 
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        try { notImpl(that); 
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
        } catch (Exception e) {}
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
        super.visitDoLoop(that);
        // TODO Auto-generated method stub
        
    }

    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        super.visitForeachLoop(that);
        // TODO Auto-generated method stub
        
    }

    public void visitJmlForLoop(JmlForLoop that) {
        super.visitForLoop(that);
        // TODO Auto-generated method stub
        
    }

    public void visitJmlWhileLoop(JmlWhileLoop that) {
        super.visitWhileLoop(that);
        // TODO Auto-generated method stub
        
    }

    public void visitJmlClassDecl(JmlClassDecl that) {
        visitClassDef(that);  // FIXME
    }

    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        visitTopLevel(that);  // FIXME
    }

    public void visitJmlMethodDecl(JmlMethodDecl that) {
        visitMethodDef(that);  // FIXME
    }

    public void visitJmlVariableDecl(JmlVariableDecl that) {
        visitVarDef(that);  // FIXME
    }

    @Override
    public void visitAuxVarDSA(AuxVarDSA that) {
        try {
            out.write(that.toString());
        } catch(IOException e) {}
    }

    @Override
    public void visitProgVarDSA(ProgVarDSA that) {
        try {
            out.write(that.toString());
        } catch(IOException e) {}
    }

}
