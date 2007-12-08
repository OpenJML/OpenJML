package org.jmlspecs.openjml;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;

import org.jmlspecs.openjml.JmlTree.*;

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
    
    Writer out;
    public String indentAmount;
    public String indentExtra;
    protected String currentIndent;
    
    public JmlPretty(Writer out, boolean sourceOutput) {
        super(out, sourceOutput);
        this.out = out;
    }
    
    public JmlPretty(String indentAmount, String indentExtra) {
        this(new StringWriter(),true);
        this.indentAmount = indentAmount;
        this.indentExtra = indentExtra;
    }
    
    static String write(String in, String ad, JCTree tree) {
        StringWriter sw = new StringWriter();
        JmlPretty p = new JmlPretty(sw,true);
        p.indentAmount = in;
        p.indentExtra = ad;
        tree.accept(p);
        return sw.toString();
    }
    
    public void notImpl(JCTree that) {
        try {
            out.write("<");
            out.write(that.getClass().toString());
            out.write(">");
            } catch (Exception e) { } // ignore - too much trouble to fix just for printing
    }

    @Override
    public void visitJmlBinary(JmlBinary that) {
        try {
            that.lhs.accept(this);
            out.write(that.op.internedName());
            that.rhs.accept(this);
        } catch (Exception e) {}
    }

    @Override
    public void visitJmlLblExpression(JmlLblExpression that) {
        try { notImpl(that); } catch (Exception e) {}
        
    }
    
    @Override
    public void visitJmlRefines(JmlRefines that) {
        try { 
            out.write(that.toString());
        } catch (Exception e) {}
    }
    
    @Override
    public void visitJmlImport(JmlImport that) {
        // FIXME - print model
        visitImport(that);
    }

    @Override
    public void visitJmlFunction(JmlFunction that) {
        try { 
            out.write(that.token.internedName());
        } catch (Exception e) {}
        
    }

    @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {
        // FIXME
    }
    

    @Override
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
        } catch (Exception e) {}
    }

    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        try { 
            out.write("         ");
            out.write(that.token.internedName());
            out.write(" ");
            that.expression.accept(this);
            out.write(";");
            println();
        } catch (Exception e) {}
    }

    @Override
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        try { notImpl(that); } catch (Exception e) {}
        
    }

    @Override
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly that) {
        try { notImpl(that); } catch (Exception e) {}
        
    }

    @Override
    public void visitJmlMethodClauseAssignable(JmlMethodClauseAssignable that) {
        try { notImpl(that); } catch (Exception e) {}
        
    }

    @Override
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        try { notImpl(that); } catch (Exception e) {}
        
    }

    @Override
    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        try { 
            for (JmlSpecificationCase c: that.cases) {
                c.accept(this);
            }
        } catch (Exception e) {}
        
    }

    @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        try { notImpl(that); } catch (Exception e) {}
        
    }

    @Override
    public void visitJmlSetComprehension(JmlSetComprehension that) {
        try { notImpl(that); } catch (Exception e) {}
        
    }

    @Override
    public void visitJmlSingleton(JmlSingleton that) {
        try {
            out.write(that.toString());
        } catch (Exception e) {}
    }

    @Override
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
        } catch (Exception e) {}
        
    }

    @Override
    public void visitJmlStatement(JmlStatement that) {
        try { notImpl(that); } catch (Exception e) {}
        
    }

    @Override
    public void visitJmlStatementLoop(JmlStatementLoop that) {
        try { notImpl(that); } catch (Exception e) {}
        
    }

    @Override
    public void visitJmlStatementSpec(JmlStatementSpec that) {
        try { notImpl(that); } catch (Exception e) {}
        
    }

    @Override
    public void visitJmlStatementExpr(JmlStatementExpr that) {
        try { notImpl(that); } catch (Exception e) {}
        
    }

    @Override
    public void visitJmlStatementDecls(JmlStatementDecls that) {
        try { notImpl(that); } catch (Exception e) {}
        
    }

    @Override
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        try { 
            printFlags(that.modifiers.flags);
            print(that.token.internedName());
            print(" ");
            printExpr(that.expression);
            print(";");
            println();
        } catch (Exception e) {}
    }

    @Override
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        try { 
            print(that.decl);
        } catch (Exception e) {}
    }

    @Override
    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        try { 
            print(that.token.internedName());
            print(" ");
            print("?????"); // FIXME
            println();
        } catch (Exception e) {}
    }

    @Override
    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        try { notImpl(that); } catch (Exception e) {}
    }

    @Override
    public void visitJmlGroupName(JmlGroupName that) {
        try { notImpl(that); } catch (Exception e) {}
    }

    @Override
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        try { 
            out.write(that.token.internedName());  // FIXME - indent, eol
        } catch (Exception e) {}
    }

    @Override
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        try { notImpl(that); } catch (Exception e) {}
    }

    @Override
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        try { notImpl(that); } catch (Exception e) {}
    }

    @Override
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        try { notImpl(that); } catch (Exception e) {}
    }

    @Override
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        try { notImpl(that); } catch (Exception e) {}
    }

    @Override
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        try { out.write(that.token.internedName()); } catch (Exception e) {}
        
    }

    @Override
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

    @Override
    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        try { out.write(that.token.internedName()); } catch (Exception e) {}
    }
    
    @Override
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        try { notImpl(that); } catch (Exception e) {}
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

    @Override
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        super.visitDoLoop(that);
        // TODO Auto-generated method stub
        
    }

    @Override
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        super.visitForeachLoop(that);
        // TODO Auto-generated method stub
        
    }

    @Override
    public void visitJmlForLoop(JmlForLoop that) {
        super.visitForLoop(that);
        // TODO Auto-generated method stub
        
    }

    @Override
    public void visitJmlWhileLoop(JmlWhileLoop that) {
        super.visitWhileLoop(that);
        // TODO Auto-generated method stub
        
    }

    @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        visitClassDef(that);  // FIXME
    }

    @Override
    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        visitTopLevel(that);  // FIXME
    }

    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        visitMethodDef(that);  // FIXME
    }

    @Override
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        visitVarDef(that);  // FIXME
    }

}
