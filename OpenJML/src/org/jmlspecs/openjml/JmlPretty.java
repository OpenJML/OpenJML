package org.jmlspecs.openjml;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCImport;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCNewClass;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;

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

    
//    /** The Writer to which this pretty printer prints, initialized in the
//     * constructor
//     */
//    /*@ non_null*/ protected Writer out;
    
//    protected boolean sourceOutput;
    
    /** If true, then wrap JML statements in JML comments */
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
        this.useJMLComments = sourceOutput;
    }
    
    /** Writes out a tree in pretty-printed fashion, with two-character indentation
     * 
     * @param tree the tree to print
     * @return the resulting text
     */
    static public @NonNull String write(@NonNull JCTree tree) {
        return write(tree,true);
    }
    
    /** Writes out a tree in pretty-printed fashion, with two-character indentation
     * 
     * @param tree the tree to print
     * @param source if true then put out compilable source
     * @return the resulting text
     */
    static public @NonNull String write(@NonNull JCTree tree, boolean source) {
        StringWriter sw = new StringWriter();
        JmlPretty p = new JmlPretty(sw,source);
        p.width = 2;
        tree.accept(p);
        return sw.toString();
    }
    
    /** Writes out a tree in pretty-printed fashion, with two-character indentation,
     * but ignoring any JML.
     * 
     * @param tree the tree to print
     * @param source if true then put out compilable source
     * @return the resulting text
     */
    static public String writeJava(JCTree tree, boolean source) {
        try { 
            // Here we use the Pretty constructor because we specifically
            // want only Java, not any JML
            StringWriter sw = new StringWriter();
            tree.accept(new Pretty(sw,true)); 
            return sw.toString();
        } catch(Exception e) {}
        return "<Exception>";
    }
    
    protected void indentAndPrint() throws IOException {
        indent();
        for (int i=width; i>0; --i) print(" ");
    }
    
    /** A method used for those pretty-printing methods that are not yet
     * implemented; it just prints the class type.
     * @param that a non-null AST node
     * @throws IOException if there is a problem writing to the writer
     */
    protected void notImpl(/*@non_null*/JCTree that) throws IOException {
            print("<");
            print(that.getClass());
            print(">");
    }
    
    /** A method used to report exceptions that happen on writing to the writer
     * 
     * @param that a non-null AST node
     * @param e the exception that is being reported
     */
    protected void perr(/*@ non_null*/JCTree that, /*@ non_null*/Exception e) {
        System.err.println(e.getClass() + " error in JMLPretty: " + that.getClass());
        e.printStackTrace(System.err);
    }
    
    //-------------- VISITOR METHODS -------------------------------------------
    
    public void visitJmlBinary(JmlBinary that) {
        try {
            that.lhs.accept(this);
            print(" ");
            print(that.op.internedName());
            print(" ");
            that.rhs.accept(this);
        } catch (IOException e) { perr(that,e); }
    }
    
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        try {
            if (that.token == null) {
                visitApply(that);
            } else {
                print(that.token.internedName());
                print("(");
                printExprs(that.args);
                print(")");
            }
        } catch (IOException e) { perr(that,e); }
    }


    public void visitJmlLblExpression(JmlLblExpression that) {
        try { 
            // NOTE: JML requires that a lbl expression be in parentheses.
            // In this parser the outer parentheses are a JCParens expression.
            print(that.token.internedName());
            print(" ");
            print(that.label.toString());
            print(" ");
            that.expression.accept(this);
        } catch (IOException e) { perr(that,e); }
    }
    
    public void visitJmlRefines(JmlRefines that) {
        try { 
            if (useJMLComments) print("//@ ");
            print("refines \"");
            print(that.filename);
            print("\";");
            println();
        } catch (IOException e) { perr(that,e); }
    }
    
    public void visitJmlImport(JmlImport that) {
        try {
            if (useJMLComments && that.isModel) print("//@ ");
            if (that.isModel) print("model ");
            print("import ");
            if (that.staticImport) print("static ");
            printExpr(that.qualid);
            print(";");
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        // Presumes already aligned; does not call println at end
        try {
            if (that.cases.size() == 1) {
                that.cases.get(0).accept(this);
            } else {
                print("{|"); println();
                // Internal specification cases are always 'lightweight'
                // and so have an automatic indentation
                boolean first = true;
                for (JmlSpecificationCase t: that.cases) {
                    if (first) first = false;
                    else {
                        align(); print("also"); println();
                    }
                    align();
                    t.accept(this);  // indents and undents itself for lightweight clauses
                    println();
                }
                align(); print("|}");
            }
        } catch (IOException e) { perr(that,e); }
    }
    

    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        try { 
            for (JCTree.JCVariableDecl s: that.decls) {
                print(that.token.internedName());
                print(" ");
                s.accept(this);
                print(";");
            }
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        try { 
            print(that.token.internedName());
            print(" ");
            that.expression.accept(this);
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        try { 
            print(that.token.internedName());
            print(" ");
            that.expression.accept(this);
            if (that.predicate != null) {
                print(" if ");
                that.predicate.accept(this);
            }
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
        try { 
            print(that.token.internedName());
            print(" ");
            if (that.list.isEmpty()) {
                print("\\nothing");
            } else {
                boolean first = true;
                for (JCExpression item: that.list) {
                    if (first) first = false; else print(", ");
                    item.accept(this);
                }
            }
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
        try { 
            print(that.token.internedName());
            print(" ");
            boolean first = true;
            for (JCTree item: that.list) {
                if (first) first = false; else print(", ");
                item.accept(this);
            }
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        try { 
            print(that.token.internedName());
            print(" (");
            if (that.vardef != null) {
                that.vardef.vartype.accept(this);
                if (that.vardef.name != null) {
                    String s = that.vardef.name.toString();
                    if (!JmlAttr.syntheticExceptionID.equals(s)) {
                        print(" ");
                        print(that.vardef.name.toString());
                    }
                }
            }
            print(") ");
            that.expression.accept(this);
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        if (that.cases.isEmpty()) return;
        try {
            if (useJMLComments) { align(); print("/*@"); println(); }
            try { 
                indent();
                for (JmlSpecificationCase c: that.cases) {
                    align();
                    c.accept(this);  // presumes already aligned; does not end with println
                    println();
                }
            } finally { 
                undent();
            }
            if (useJMLComments) { align(); print(" */"); println(); }
        } catch (Exception e) { 
            perr(that,e);
        }
    }

    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        try { 
            // FIXME - it appears that the enclosing parentheses are parsed as a Parens
            // expression - is this really right?
            print(that.op.internedName());
            print(" ");
            boolean first = true;
            for (JCTree.JCVariableDecl n: that.decls) {
                if (!first) print(", ");
                else first = false;
                n.accept(this);
            }
            print("; ");
            if (that.range != null) that.range.accept(this);
            print("; ");
            that.value.accept(this);
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlSetComprehension(JmlSetComprehension that) {
        int oldprec = prec;
        prec = 0;
        try { 
                print("new ");
                that.newtype.accept(this);
                print(" { ");
                that.variable.accept(this);
                print(" | ");
                that.predicate.accept(this);
                print(" }");
        } 
        catch (IOException e) { perr(that,e); }
        finally {
            prec = oldprec;
        }
    }

    public void visitJmlSingleton(JmlSingleton that) {
        try {
            if (that.token == JmlToken.INFORMAL_COMMENT) {
                print("(*");
                print(that.info);
                print("*)");
            } else {
                print(that);
            }
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        // Presumes the output is already aligned before the call
        // Presumes the caller does any needed println() afterwards
        try { 
            if (that.modifiers != null &&
                    (that.modifiers.flags != 0 || that.modifiers.annotations != null)) {
                that.modifiers.accept(this); // presumes that this call adds a trailing space
            }
            if (that.code) {
                print(JmlToken.CODE.internedName());
                print(" ");
            }
            if (that.token == JmlToken.MODEL_PROGRAM) {
                print(that.token.internedName());
                print(" ");
                that.block.accept(this);
                return;
            }
            if (that.token == null) {
                // lightweight
            } else {
                print(that.token.internedName());
                println();
                align();
            }
            try {
                // Note - the output is already aligned, so we have to bump up the alignment
                indentAndPrint();
                boolean first = true;
                for (JmlMethodClause c: that.clauses) {
                    if (first) first = false; else { println(); align(); }
                    c.accept(this);
                }
            } finally {
                undent();
            }
        } catch (IOException e) { perr(that,e); }
    }

    /** debug and set statements */
    public void visitJmlStatement(JmlStatement that) {
        try { 
            if (useJMLComments) print ("/*@ ");
            print(that.token.internedName());
            print(" ");
            that.statement.accept(this);
            if (useJMLComments) print("*/");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlStatementLoop(JmlStatementLoop that) {
        try { 
            if (useJMLComments) print("//@ ");
            print(that.token.internedName());
            print(" ");
            that.expression.accept(this);
            print(";");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlStatementSpec(JmlStatementSpec that) {
        that.statementSpecs.accept(this);
    }

    public void visitJmlStatementExpr(JmlStatementExpr that) {
        try { 
            if (that.token == JmlToken.COMMENT) {
                print("// ");
                print(((JCLiteral)that.expression).value);
            } else {
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
                //println();
            }
        } catch (IOException e) { perr(that,e); }
        
    }

    public void visitJmlStatementDecls(JmlStatementDecls that) {
        try { notImpl(that);  // FIXME
        } catch (IOException e) { perr(that,e); }
        
    }

    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        try { 
            if (useJMLComments) print("//@ ");
            if (that.modifiers != null) that.modifiers.accept(this);  // trailing space if non-empty
            print(that.token.internedName());
            print(" ");
            printExpr(that.expression);
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        that.decl.accept(this);
    }

    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        try { 
            print(that.token.internedName());
            for (JmlGroupName g: that.list) {
                print(" ");
                g.selection.accept(this);
            }
            print("; ");
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
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlGroupName(JmlGroupName that) {
        try { notImpl(that); } // FIXME
        catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        try { // FIXME - modifiers?
            if (that.specs != null) that.specs.accept(this);
            align();
            print(that.token.internedName());
            print(" {}");
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        try {
            if (useJMLComments) print("//@ ");
            if (that.modifiers != null) that.modifiers.accept(this);  // trailing space if non-empty
            print(that.token.internedName());
            print(" ");
            that.expression.accept(this);
            if (that.sigs != null && !that.sigs.isEmpty()) {
                print(" for SIGNATURES"); // FIXME
            }
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        try { 
            if (useJMLComments) print("//@ ");
            if (that.modifiers != null) that.modifiers.accept(this);  // trailing space if non-empty
            print(that.token.internedName());
            print(" ");
            that.ident.accept(this);
            print(" = ");
            that.expression.accept(this);
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        try { 
            if (that.modifiers != null) that.modifiers.accept(this);  // trailing space if non-empty
            print(that.token.internedName());
            print(" ");
            that.identifier.accept(this);
            print(" if ");
            that.expression.accept(this);
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        try { 
            if (that.modifiers != null) that.modifiers.accept(this);  // trailing space if non-empty
            print(that.token.internedName());
            print(" ");
            that.identifier.accept(this);
            print(" = ");
            boolean first = true;
            for (JCExpression item: that.list) {
                if (first) first = false; else print(", ");
                item.accept(this);
            }
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        try { print(that.token.internedName()); 
        } catch (IOException e) { perr(that,e); }
        
    }

    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        try {
            that.expression.accept(this);
            print('[');
            if (that.lo == null) {
                print('*');
            } else if (that.hi == that.lo) {
                that.lo.accept(this);
            } else if (that.hi == null) {
                that.lo.accept(this);
                print(" .. *");
            } else {
                that.lo.accept(this);
                print(" .. ");
                that.hi.accept(this);
            }
            print(']');
        } catch (IOException e) { perr(that,e); }
    }

//    @Override
//    public void visitJmlStoreRefField(JmlStoreRefField that) {
//        try {
//            that.expression.accept(this);
//            print('.');
//            print(that.ident);
//        } catch (Exception e) {}
//    }
//
//    @Override
//    public void visitJmlStoreRefIdent(JmlStoreRefIdent that) {
//        try {
//            if (that.ident != null) that.ident.accept(this);
//            if (that.token != null) print(that.token);
//        } catch (Exception e) {}
//    }

    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        try { 
            print(that.token.internedName()); 
        } catch (IOException e) { perr(that,e); }
    }
    
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        try { 
            print(that.token.internedName());
            print('(');
            boolean first = true;
            for (JCTree expr : that.list) {
                if (first) first = false; else print(',');
                expr.accept(this);
            }
            print(')');
        } catch (IOException e) { perr(that,e); }

    }


    /** This is the package name (including a terminating period) of the 
     * package that contains the JML annotation types (e.g. NonNull).
     */
    static final String prefix = "org.jmlspecs.annotation.";
    
    /** This is overridden simply to exclude the package name from JML annotations,
     * in order to conserve space. [FIXME - this will actually create illegal
     * source if there is no import statement for the annotations. ]
     */
    @Override
    public void visitAnnotation(JCAnnotation tree) {
        try {
            // We prefer to use tree.type since it will be the fully resolved
            // type name, including the package, even if the use of the annotation
            // itself does not use the package name.  However, if types have not
            // yet been attributed (e.g. this is a pure parse tree), then 
            // tree.type is null.
            String s = (tree.type != null) ? tree.type.toString() :
                tree.annotationType.toString();
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
        if (!trees.isEmpty()) { // This test is needed for example in quantified expressions
            println();
            align();
        }
    }

    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        for (JmlStatementLoop s: that.loopSpecs) {
            s.accept(this);
        }
        super.visitDoLoop(that);
        
    }

    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        try {
            if (that.loopSpecs != null) for (JmlStatementLoop s: that.loopSpecs) {
                s.accept(this);
                println();
                align();
            }
            super.visitForeachLoop(that);
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlForLoop(JmlForLoop that) {
        try {
            if (that.loopSpecs != null) {
                for (JmlStatementLoop s: that.loopSpecs) {
                    s.accept(this);
                    println();
                    align();
                }
            }
            super.visitForLoop(that);
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlWhileLoop(JmlWhileLoop that) {
        try {
            if (that.loopSpecs != null) {
                for (JmlStatementLoop s: that.loopSpecs) {
                    s.accept(this);
                    println();
                    align();
                }
            }
            super.visitWhileLoop(that);
        } catch (IOException e) { perr(that,e); }
    }

    JmlSpecs.TypeSpecs specsToPrint = null;
    
    public void visitJmlClassDecl(JmlClassDecl that) {
        if (that.typeSpecsCombined != null) {
            specsToPrint = that.typeSpecsCombined;
        } else if (that.typeSpecs != null) {
            specsToPrint = that.typeSpecs;
        }

        visitClassDef(that);
    }
    
    public void printStats(List<? extends JCTree> stats) throws IOException {
        JmlSpecs.TypeSpecs toPrint = specsToPrint;
        specsToPrint = null;
        super.printStats(stats);
        if (toPrint != null && !toPrint.clauses.isEmpty()) {
            align(); print("// JML specifications"); println();
            for (JmlTypeClause t: toPrint.clauses) {
                align();
                t.accept(this);
                println();
            }
        }
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
        if (that.methodSpecsCombined != null) {
            that.methodSpecsCombined.cases.accept(this);
        }
        else if (that.cases != null) that.cases.accept(this);
        // FIXME - visitMethodDef will print the Java modifiers
        // and annotations that are on the Java declaration
        // We need the following to get the combined annotations
        // but we don't want both?
        // if (that.methodSpecsCombined != null) that.methodSpecsCombined.mods.accept(this);
        visitMethodDef(that);
    }

    public void visitJmlVariableDecl(JmlVariableDecl that) {
        visitVarDef(that);
    }
    
    public void visitVarDef(JmlVariableDecl that) {
        super.visitVarDef(that);
        if (that.fieldSpecsCombined != null) printFieldSpecs(that.fieldSpecsCombined);
        else if (that.fieldSpecs != null) printFieldSpecs(that.fieldSpecs);
    }
    
    public void printFieldSpecs(JmlSpecs.FieldSpecs fspecs) {
        // FIXME - may need to add a println at the beginning and omit one at the end
        indent();
        for (JmlTypeClause t: fspecs.list) {
            try {
                if (t.token == JmlToken.IN || t.token == JmlToken.MAPS) {
                    align(); t.accept(this); println();
                }
            } catch (IOException e) {
                perr(t,e);
            }
        }
        for (JmlTypeClause t: fspecs.list) {
            try{
                if (t.token == JmlToken.IN || t.token == JmlToken.MAPS) continue;
                align(); t.accept(this); println();
            } catch (IOException e) {
                perr(t,e);
            }
        }
        undent();
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

    /** Overridden in order to handle the case of a null selection field - this
     * means a * in a store-ref expression.
     */
    @Override
    public void visitSelect(JCFieldAccess tree) {
        try {
            printExpr(tree.selected, TreeInfo.postfixPrec);
            if (tree.name == null) print(".*");
            else print("." + tree.name);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /** Overridden to try to cleanup a little bit the printing of an anonymous
     * class expression.
     */
    @Override
    public void visitNewClass(JCNewClass tree) {
        indent(); indent(); indent(); indent();  // indent
        super.visitNewClass(tree);
        undent(); undent(); undent(); undent();  // indent
    }

    public void visitJmlConstraintMethodSig(JmlConstraintMethodSig that) {
        try { notImpl(that);  // FIXME
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
        try { notImpl(that);  // FIXME
        } catch (IOException e) { perr(that,e); }
    }
}
