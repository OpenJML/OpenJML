/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import static com.sun.tools.javac.tree.JCTree.Tag.PARENS;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.Iterator;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.IJmlClauseKind.ModifierKind;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.ext.FunctionLikeExpressions;
import org.jmlspecs.openjml.ext.MethodSimpleClauseExtensions;
import org.jmlspecs.openjml.ext.MiscExpressions;
import org.jmlspecs.openjml.ext.Operators;
import org.jmlspecs.openjml.ext.RecommendsClause;
import org.jmlspecs.openjml.ext.SingletonExpressions;
import org.jmlspecs.openjml.vistors.IJmlVisitor;

import static org.jmlspecs.openjml.ext.EndStatement.*;
import static org.jmlspecs.openjml.ext.StatementExprExtensions.*;
import static org.jmlspecs.openjml.ext.TypeInClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeMapsClauseExtension.*;
import static org.jmlspecs.openjml.ext.InlinedLoopStatement.*;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.Pretty.UncheckedIOException;
//import com.sun.tools.javac.tree.Pretty.UncheckedIOException;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Pair;

/** This class does pretty-printing of JML ASTs. */
public class JmlPretty extends Pretty implements IJmlVisitor {

    // Pretty was not originally a registered tool.  In order to be able to
    // slide in JmlPretty, I added a registration mechanism, but see the comments
    // in Pretty: it does not depend on context (so compiler options are not
    // available).
    public static void preRegister(final Context context) {
        cachedInstance = new JmlPretty(null,false); 
    }

    /** Returns a new pretty printer of the dynamic type of the receiver.
     * @param out the writer to pretty print to
     * @param sourceOutput if true, writes out compilable source code
     *   (if false, there may be additional, uncompilable, information)
     *  */
    @Override
    protected JmlPretty inst(Writer out, boolean sourceOutput) {
        return new JmlPretty(out,sourceOutput);
    }

    /** If true, then wrap JML statements in JML comments */
    public boolean useJMLComments;
    
    /** If true, special rules for things that will only appear in specs **/
    public boolean specOnly = false;
    
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
        if(tree!=null)
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
    static public String writeJava(JCTree tree, boolean source) { // FIXME - source is ignored
        try { 
            // Here we use the Pretty constructor because we specifically
            // want only Java, not any JML
            StringWriter sw = new StringWriter();
            tree.accept(new Pretty(sw,true)); 
            return sw.toString();
        } catch(Exception e) {}
        return "<Exception>";
    }

    /** Flush the output Writer */
    public void flush() throws IOException {
        out.flush();
    }
    
    /** Adds to the indentation amount and realigns the indentation;
     * call this when increasing the indentation after align() has already been called.
     * @throws IOException
     */
    public void indentAndRealign() throws IOException {
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
            int ownprec = JmlParser.jmlPrecedence(that.op); // FIXME - This needs a bit more testing
            int p = ownprec;
            if (ownprec == -2) {
                if (that.op == Operators.equivalenceKind || that.op == Operators.inequivalenceKind) p = TreeInfo.orPrec - 2;
                else p = TreeInfo.orPrec - 1;
            }
            open(prec, p);
            printExpr(that.lhs, p);
            print(Strings.space);
            print(that.op.name());
            print(Strings.space);
            printExpr(that.rhs, p + 1);
            close(prec, p);
        } catch (IOException e) { perr(that,e); }
    }
    
    public void visitJmlChained(JmlChained that) {
        try {
            JCTree.Tag tag = that.conjuncts.head.getTag();
            int ownprec = TreeInfo.opPrec(tag);

            printExpr(that.conjuncts.head.lhs, ownprec);
            for (JCBinary b: that.conjuncts) {
                String opname = operatorName(b.getTag());
                open(prec, ownprec);
                print(Strings.space);
                print(opname);
                print(Strings.space);
                printExpr(b.rhs, ownprec);
                close(prec, ownprec);
            }
        } catch (IOException e) { perr(that,e); }
    }
    
    public void visitJmlBlock(JmlBlock that) {
        
        if(that.type==null && specOnly){
            return;
        }
        
        visitBlock(that);
    }
    
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        try {
            if (that.kind != null) {
                print(that.kind.name());
                if (that.javaType && 
                        (that.kind == MiscExpressions.typelcKind || that.kind == FunctionLikeExpressions.typeofKind)
                        ) print("j");
                print("(");
                printExprs(that.args);
                print(")");
            } else if (that.token != null) {
                print(that.token.internedName());
                if (that.javaType && 
                        (that.kind == MiscExpressions.typelcKind || that.kind == FunctionLikeExpressions.typeofKind)
                        ) print("j");
                print("(");
                printExprs(that.args);
                print(")");
            } else if (that.name != null) {
                print(that.name);
                print("(");
                printExprs(that.args);
                print(")");
            } else {
                visitApply(that);
            }
        } catch (IOException e) { perr(that,e); }
    }
    
    public void visitLambda(JCLambda that) {
        try {
            if (that instanceof JmlLambda) {
                JmlLambda jthat = (JmlLambda)that;
                if (jthat.jmlType != null) {
                    print("/*@{ ");
                    (jthat.jmlType).accept(this);
                    print(" }@*/");
                }
                if (jthat.literal != null) {
                    jthat.literal.accept(this);
                } else {
                    super.visitLambda(that);
                }
            } else {
                super.visitLambda(that);
            }
        } catch (IOException e) {
            perr(that,e);
        }
    }

    public void visitJmlLabeledStatement(JmlLabeledStatement that) {
        try {
            printStats(that.extraStatements.toList());
            print(that.label + ":");
            printStat(that.body);
        } catch (IOException e) {
            perr(that,e);
        }
    }
    

    public void visitJmlLblExpression(JmlLblExpression that) {
        try { 
            // NOTE: JML requires that a lbl expression be in parentheses.
            // In this parser the outer parentheses are a JCParens expression.
            print(that.kind.name());
            print(" ");
            print(that.label.toString());
            print(" ");
            printExpr(that.expression);
        } catch (IOException e) { perr(that,e); }
    }
    
    public void visitJmlNewClass(JmlNewClass that) {
        visitNewClass(that);
    }

    public void visitJmlMatchExpression(JmlMatchExpression that) {
        try { 
            // NOTE: JML requires that a lbl expression be in parentheses.
            // In this parser the outer parentheses are a JCParens expression.
            print("match (");
            printExpr(that.expression);
            print(") {");
            indent();
            println();
            for (JmlMatchExpression.MatchCase c: that.cases) {
                align();
                printExpr(c.caseExpression);
                print(" -> ");
                printExpr(c.value);
                println();
            }
            undent();
            align();
            print("}");
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
            if(that.cases==null){
                return;
            }
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
                    t.accept(this);  // indents and outdents itself for lightweight clauses
                    println();
                }
                align(); print("|}");
            }
        } catch (IOException e) { perr(that,e); }
    }
    

    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        try {
            for (JCTree.JCVariableDecl s: that.decls) {
                print(useCanonicalName ? that.clauseKind.name() : that.keyword);
                print(" ");
                s.accept(this);
                // The declaration has its own closing semicolon
            }
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        try { 
            print(useCanonicalName ? that.clauseKind.name() : that.keyword);
            print(" ");
            printExpr(that.expression);  // noPrec
            if (that instanceof RecommendsClause.Node) {
                RecommendsClause.Node rc = (RecommendsClause.Node)that;
                if (rc.exceptionType != null) {
                    print(" else ");
                    printExpr(rc.exceptionType);
                }
            }
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that) {
        try { 
            print(useCanonicalName ? that.clauseKind.name() : that.keyword);
            print(" ");
            if (that.keyword != null) {
                that.keyword.accept(this);
            } else {
                Iterator<JmlMethodSig> iter = that.methodSignatures.iterator();
                iter.next().accept(this);
                while (iter.hasNext()) {
                    print(", ");
                    iter.next().accept(this);// FIXME printExpr?
                }
            }
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        try { 
            print(useCanonicalName ? that.clauseKind.name() : that.keyword);
            print(" ");
            that.expression.accept(this);
            if (that.predicate != null) {
                print(" if ");
                printExpr(that.predicate);
;
            }
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
        try { 
            print(useCanonicalName ? that.clauseKind.name() : that.keyword);
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
            print(useCanonicalName ? that.clauseKind.name() : that.keyword);
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
            print(useCanonicalName ? that.clauseKind.name() : that.keyword);
            print(" (");
            if (that.vardef != null) {
                that.vardef.vartype.accept(this);
                if (that.vardef.name != null) {
                    String s = that.vardef.name.toString();
                    if (!Strings.syntheticExceptionID.equals(s)) {
                        print(" ");
                        print(that.vardef.name.toString());
                    }
                }
            }
            print(") ");
            printExpr(that.expression);
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        if (that.cases.isEmpty()) return;
        try {
            if (useJMLComments) { align(); print("/*@"); println(); }
            boolean first = true;
            for (JmlSpecificationCase c: that.cases) {
            	if (first) first = false;
            	else {
            		print("also"); //$NON-NLS-1$
            		println();
            	}
            	indent();
            	align();
            	c.accept(this);  // presumes already aligned; does not end with println
            	println();
            	undent();
            }
            if (that.feasible != null) {
                print("also feasible"); println();
                indent();
                for (JmlMethodClause cl: that.feasible) {
                    cl.accept(this);
                }
                undent();
            }
            if (useJMLComments) { align(); print(" */"); println(); }
        } catch (Exception e) { 
            perr(that,e);
        }
    }

    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        int savedPrec = prec;
        prec = TreeInfo.noPrec;
        try { 
            // FIXME - it appears that the enclosing parentheses are parsed as a Parens
            // expression - is this really right?
            print(that.kind.name());
            print(" "); //$NON-NLS-1$
            boolean first = true;
            for (JCTree.JCVariableDecl n: that.decls) {
                if (!first) print(", "); //$NON-NLS-1$
                else first = false;
                n.accept(this);
            }
            print("; "); //$NON-NLS-1$
            if (that.range != null) printExpr(that.range);

            print("; "); //$NON-NLS-1$
            if (that.value != null) printExpr(that.value);
            else print("????:"); //$NON-NLS-1$
            
            if (that.triggers != null) {
                print( " : ");
                printExprs(that.triggers);
            }
        } catch (IOException e) { 
        	perr(that,e); 
        } finally {
        	prec = savedPrec;
        }
    }

    public void visitJmlSetComprehension(JmlSetComprehension that) {
        int oldprec = prec;
        prec = 0;
        try { 
                print("new "); //$NON-NLS-1$
                that.newtype.accept(this);
                print(" { ");
                that.variable.accept(this);
                print(" | ");
                printExpr(that.predicate);
                print(" }");
        } 
        catch (IOException e) { perr(that,e); }
        finally {
            prec = oldprec;
        }
    }

    public void visitJmlSingleton(JmlSingleton that) {
        try {
            if (that.kind == SingletonExpressions.informalCommentKind) {
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
            boolean modOrCodeOrBehavior = false;
            if (that.modifiers != null &&
                    (that.modifiers.flags != 0 || (that.modifiers.annotations != null && !that.modifiers.annotations.isEmpty()))) {
                that.modifiers.accept(this); // presumes that this call adds a trailing space
                modOrCodeOrBehavior = true;
            }
            if (that.code) {
                print(MethodSimpleClauseExtensions.codeID);
                print(" ");
                modOrCodeOrBehavior = true;
            }
            if (that.token == MethodSimpleClauseExtensions.modelprogramClause) {
                print(MethodSimpleClauseExtensions.modelprogramID);
                print(" ");
                that.block.accept(this);
                return;
            }
            if (that.token == null) {
                // lightweight
            } else {
                print(that.token.keyword);
                if (that.name != null) {
                    print(" ");
                    print(that.name);
                    print(": ");
                }
                modOrCodeOrBehavior = true;
            }
            if (modOrCodeOrBehavior) {
                println();
                align();
            }
            try {
                // Note - the output is already aligned, so we have to bump up the alignment
                indentAndRealign();
                boolean first = true;
                if(that.clauses!=null){
                    for (JmlMethodClause c: that.clauses) {
                        if (first) first = false; else { println(); align(); }
                        c.accept(this);
                    }
                }
                if (that.block != null) {
                    println();
                    align();
                    that.block.accept(this);
                }
            } finally {
                undent();
            }
        } catch (IOException e) { perr(that,e); }
    }

    /** debug and set and end statements */
    public void visitJmlStatement(JmlStatement that) {
        try { 
            if (useJMLComments) print ("/*@ ");
            print(useCanonicalName ? that.clauseType.name() : that.keyword);
            print(" ");
            if (that.statement == null) print(": "); // FIXME - why the colon?
            else that.statement.accept(this);
            if (useJMLComments) print("*/");
        } catch (IOException e) { perr(that,e); }
    }

    /** inlined_loop statement */
    public void visitJmlInlinedLoop(JmlInlinedLoop that) {
        try {
            if (that.loopSpecs != null) {
                for (JmlStatementLoop s: that.loopSpecs) {
                    s.accept(this);
                    println();
                    align();
                }
            }
            if (useJMLComments) print ("/*@ ");
            print(inlinedLoopStatement.name());
            //print(useCanonicalName ? that.clauseType.name() : that.keyword);
            print(";");
            if (useJMLComments) print("*/");
        } catch (IOException e) { perr(that,e); }
    }

    /** show statement */
    public void visitJmlStatementShow(JmlStatementShow that) {
        try { 
            if (useJMLComments) print ("/*@ ");
            print(that.clauseType.name());
            boolean first = true;
            for (JCExpression e: that.expressions) {
                if (!first) print(",");
                else first = false;
                print(" ");
                e.accept(this);
            }
            print(";");
            if (useJMLComments) print("*/");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlStatementLoopExpr(JmlStatementLoopExpr that) {
        try { 
            if (useJMLComments) print("//@ ");
            print(that.clauseType.name());
            print(" ");
            printExpr(that.expression); // noPrecÍP
            print(";");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlStatementLoopModifies(JmlStatementLoopModifies that) {
        try { 
            if (useJMLComments) print ("//@ ");
            print(that.clauseType.name());

            print(" ");
            boolean first = true;
            for (JCTree item: that.storerefs) {
                if (first) first = false; else print(", ");
                item.accept(this); // FISXME - printExpr?
            }
            print(";");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlStatementSpec(JmlStatementSpec that) {
        that.statementSpecs.accept(this);  // FIXME - need to print exports
        if (that.statements != null) {
            try {
                printStats(that.statements);
            } catch (IOException e) {
                perr(that,e); 
            }
        }
    }

    public void visitJmlStatementExpr(JmlStatementExpr that) {
        try { 
            if (that.clauseType == commentClause) {
                print("// ");
                if (that.expression != null) print(((JCLiteral)that.expression).value); // FIXME - can the comment span more than one line?
                else {
                    print("[ERROR: NULL COMMENT EXPRESSION]");
                }
            } else {
                if (useJMLComments) print ("/*@ ");  // FIXME - this is needed in lots more places
                print(useCanonicalName ? that.clauseType.name() : that.keyword);
                print(" ");
                if (that.label != null && !sourceOutput) {
                    print(that.label);
                    print(" ");
                }
                printExpr(that.expression); 
                if (that.optionalExpression != null) {
                    print(" : ");
                    printExpr(that.optionalExpression);
                }
                print(";");
                if (useJMLComments) print("*/");
                //println();
            }
        } catch (IOException e) { perr(that,e); }
        
    }

    public void visitJmlStatementHavoc(JmlStatementHavoc that) {
        try { 
            if (useJMLComments) print ("//@ ");
            print(that.clauseType.name());

            print(" ");
            boolean first = true;
            for (JCTree item: that.storerefs) {
                if (first) first = false; else print(", ");
                item.accept(this); // FISXME - printExpr?
            }
            print("; ");
        } catch (IOException e) { perr(that,e); }
        
    }

    public void visitJmlStatementDecls(JmlStatementDecls that) {
        try { notImpl(that);  // FIXME
        } catch (IOException e) { perr(that,e); }
        
    }

    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        try { 
            if (useJMLComments) print("//@ ");
            if (that.modifiers != null) that.modifiers.accept(this);  // includes trailing space if non-empty
            print(useCanonicalName ? that.clauseType.name() : that.keyword);
            print(" ");
            printExpr(that.expression); // TreeInfo.noPrec
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        that.decl.accept(this); // FIXME - //@?
    }
    
    public boolean useCanonicalName = true;
    
    
    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        try {
            if (useJMLComments) print("//@ ");
            print(useCanonicalName ? that.clauseType.name() : that.keyword);
            Iterator<JmlGroupName> g = that.list.iterator();
            print(" ");
            g.next().accept(this);
            while(g.hasNext()) {
                print(", ");
                g.next().accept(this);
            }
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        try {
            if (useJMLComments) print("//@ ");
            print(useCanonicalName ? that.clauseType.name() : that.keyword);
            print(" ");
            print(that.expression);
            print(" \\into");
            Iterator<JmlGroupName> g = that.list.iterator();
            print(" ");
            g.next().accept(this);
            while(g.hasNext()) {
                print(", ");
                g.next().accept(this);
            }
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlGroupName(JmlGroupName that) {
//        try { 
//        	// FIXME - this was changed - is it right?
//            if (that.selection != null) {
                that.selection.accept(this); 
//                print(".");
//            }
//            print(that.sym);
//        }
//        catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        try {
            if (that.specs != null) that.specs.accept(this);
            align();
            if (that.modifiers != null) that.modifiers.accept(this);
            print(useCanonicalName ? that.clauseType.name() : that.keyword);
            print(" {}");
            println();
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        try {
            if (useJMLComments) print("//@ ");
            if (that.modifiers != null) that.modifiers.accept(this);  // includes trailing space if non-empty
            print(useCanonicalName ? that.clauseType.name() : that.keyword);
            print(" ");
            printExpr(that.expression);
            if (that.sigs != null && !that.sigs.isEmpty()) {
                print(" for ");
                if (that.notlist) print("! "); 
                if (that.sigs.isEmpty()) print(" \\nothing");
                else {
                    boolean first = true;
                    for (JmlMethodSig sig: that.sigs) {
                        if (first) first = false; else print(", ");
                        sig.accept(this);
                    }
                }
            }
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        try { 
            if (useJMLComments) print("//@ ");
            if (that.modifiers != null) that.modifiers.accept(this);  // trailing space if non-empty
            print(useCanonicalName ? that.clauseType.name() : that.keyword);
            print(" ");
            that.ident.accept(this);
            print(" = ");
            printExpr(that.expression);
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        try {
            if (useJMLComments) print("//@ ");
            if (that.modifiers != null) that.modifiers.accept(this);  // trailing space if non-empty
            print(useCanonicalName ? that.clauseType.name() : that.keyword);
            print(" ");
            that.identifier.accept(this);
            if (that.expression != null) {
                print(" if ");
                printExpr(that.expression);
            }
            print("; ");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        try {
            if (useJMLComments) print("//@ ");
            if (that.modifiers != null) that.modifiers.accept(this);  // trailing space if non-empty
            print(useCanonicalName ? that.clauseType.name() : that.keyword);
            print(" ");
            that.identifier.accept(this);
            print(" = ");
            boolean first = true;
            for (JCExpression item: that.list) {
                if (first) first = false; else print(", ");
                printExpr(item);
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
            printExpr(that.expression);
            print('[');
            if (that.lo == null) {
                print('*');
            } else if (that.hi == that.lo) {
                printExpr(that.lo);   // FIXME - what is the precedence of ..
            } else if (that.hi == null) {
                printExpr(that.lo);
                print(" .. *");
            } else {
            	printExpr(that.lo);
                print(" .. ");
                printExpr(that.hi);
            }
            print(']');
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        try { 
            print(that.kind.name()); 
        } catch (IOException e) { perr(that,e); }
    }
    
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        try { 
            print(that.token.internedName());
            print('(');
            boolean first = true;
            for (JCTree expr : that.list) {
                if (first) first = false; else print(',');
                printExpr(expr);
            }
            print(')');
        } catch (IOException e) { perr(that,e); }

    }

    public void visitJmlTuple(JmlTuple that) {
        try { 
            print('(');
            boolean first = true;
            for (JCExpression expr : that.values) {
                if (first) first = false; else print(',');
                printExpr(expr);
            }
            print(')');
        } catch (IOException e) { perr(that,e); }

    }

    /** This is overridden simply to exclude the package name from JML annotations,
     * in order to conserve space. [FIXME - this will actually create illegal
     * source if there is no import statement for the annotations. ]
     */
    static public boolean useFullAnnotationTypeName = true;
    static public boolean useJmlModifier = true;
    
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
            boolean isJml = s.startsWith(Strings.jmlAnnotationPackage);
            if (useJmlModifier && isJml) {
                for (IJmlClauseKind k : Extensions.allKinds.values()) {
                    if (k instanceof ModifierKind && ((ModifierKind)k).fullAnnotation.equals(s)) {
                        print("/*@ " + ((ModifierKind)k).keyword + " */");
                        return;
                    }
                }
//                for (JmlTokenKind t: JmlTokenKind.values()) {
//                    if (t.annotationType != null && t.annotationType.toString().substring("interface ".length()).equals(s)) {
//                        print("/*@ " + t.internedName() + " */");
//                        return;
//                    }
//                }
                super.visitAnnotation(tree);
            } else if (!useFullAnnotationTypeName && isJml) {
                    s = s.substring(Strings.jmlAnnotationPackage.length()+1); // +1 for the extra period
                    print("@");
                    print(s);
            } else {
                super.visitAnnotation(tree);
            }
        } catch (IOException e) { perr(tree,e); }
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
    
    public void printStatementSpecs(List<JmlStatementLoop> loopspecs) throws IOException {
        if (loopspecs != null) {
            for (List<? extends JCTree> l = loopspecs; l.nonEmpty(); l = l.tail) {
                printStat(l.head);
                println();
                align();
            }
        }
    }

    // Fixes some formatting problems in super.visitDoLoop
    @Override
    public void visitDoLoop(JCDoWhileLoop tree) {
        try {
            print("do ");
            printStat(tree.body);
            //align();
            print(" while ");
            if (tree.cond.hasTag(PARENS)) {
                printExpr(tree.cond);
            } else {
                print("(");
                printExpr(tree.cond);
                print(")");
            }
            print(";");
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        try {
            if (that.loopSpecs != null) {
                printStatementSpecs(that.loopSpecs);
            }
            visitDoLoop(that);
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        try {
            if (that.loopSpecs != null) {
                printStatementSpecs(that.loopSpecs);
            }
            super.visitForeachLoop(that);
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlForLoop(JmlForLoop that) {
        try {
            if (that.loopSpecs != null) {
                printStatementSpecs(that.loopSpecs);
            }
            super.visitForLoop(that);
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlWhileLoop(JmlWhileLoop that) {
        try {
            if (that.loopSpecs != null) {
                printStatementSpecs(that.loopSpecs);
            }
            super.visitWhileLoop(that);
        } catch (IOException e) { perr(that,e); }
    }
    
    public void visitJmlChoose(JmlChoose that) {
        try { // FIXME - this needs testing
            align();
            boolean save = useJMLComments;
            if (useJMLComments) print ("/*@ ");
            useJMLComments = false;
            print(that.keyword);
            println();
            indent();
            Iterator<JCBlock> iter = that.orBlocks.iterator();
            align();
            iter.next().accept(this);
            while (iter.hasNext()) {
                println();
                align();
                print("or");
                println();
                align();
                iter.next().accept(this);
            }
            println();
            align();
            if (that.elseBlock != null) {
                print("else");
                println();
                align();
                that.elseBlock.accept(this);
            }
            if (save) print (" */");
            useJMLComments = save;
            println();
            undent();
        
        } catch (IOException e) { perr(that,e); }
    }

    // FIXME - clean this up
    JmlSpecs.TypeSpecs specsToPrint = null;
    
    public void visitJmlClassDecl(JmlClassDecl that) {
        if (that.typeSpecs != null) {
            specsToPrint = that.typeSpecs;
        }
        if (that instanceof org.jmlspecs.openjml.ext.DatatypeExt.JmlDatatypeDecl) {
            org.jmlspecs.openjml.ext.DatatypeExt.JmlDatatypeDecl d = (org.jmlspecs.openjml.ext.DatatypeExt.JmlDatatypeDecl)that;
            try {
                print("datatype " + that.name.toString() + " {"); 
                indent();
                boolean first = true;
                for (Pair<Name,List<JCTree.JCVariableDecl>> p: d.constructors) {
                    if (!first) print(","); else first = false;
                    println();
                    align();
                    print(p.fst.toString());
                    print("(");
                    print(p.snd.toString());
                    print(")");
                    // FIXME - commas, semicolon, methods
                }
                undent();
                println();
                align();
                print("}"); println();
                visitClassDef(that);
            } catch (IOException e) {
                perr(that,e);
            }
        } else {
            visitClassDef(that);
        }
    }
    
    @Override
    public void printEnumBody(List<JCTree> stats) throws IOException {
        if(specOnly){
            print("{}");
            return;
        }
    }
    
   
    
    public void printStats(List<? extends JCTree> stats) throws IOException {
        JmlSpecs.TypeSpecs toPrint = specsToPrint;
        specsToPrint = null;
        super.printStats(stats);
        if (toPrint != null && (!toPrint.clauses.isEmpty() || !toPrint.decls.isEmpty())) {
            align(); print("// JML specifications"); println();
            for (JmlTypeClause t: toPrint.clauses) {
                align();
                t.accept(this);
                println();
            }
            for (JmlTypeClause t: toPrint.decls) {
                align();
                t.accept(this);
                println();
            }
        }
    }
    
    // FIXME - document
    protected boolean inSequence = false;

    public void visitJmlCompilationUnit(JmlCompilationUnit tree) {
        // FIXME - can we call Pretty.printUnit - or do we not get model imports then
        // FIXME - review this for sourceOutput true and false
        try {
            printDocComment(tree);
            if (tree.pid != null) {
                print("package ");
                printExpr(tree.pid);
                print(";");
                println();
            }
            boolean firstImport = true;
            for (List<JCTree> l = tree.defs; l.nonEmpty(); l = l.tail) {
                if (l.head.getTag() == JCTree.Tag.IMPORT) {
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
            if (!inSequence && tree.specsCompilationUnit != null && !useJMLComments) {
                boolean prevInSequence = inSequence; // should always be false, since we don't call this more than one level deep
                inSequence = true;
                try {
                    println();
                    print("// Specifications: ");
                    print(tree.specsCompilationUnit.sourcefile.getName());
                    println();
                    JmlCompilationUnit jcu = tree.specsCompilationUnit;
                    print("// Specification file: " + jcu.sourcefile.getName()); 
                    println();
                    jcu.accept(this);
                    println();
                } finally {
                    inSequence = prevInSequence;
                }
            }
        } catch (IOException e) {
            perr(tree,e);
        }
    }

    public void visitJmlMethodDecl(JmlMethodDecl that) {
        // FIXME //@? model?
        if (that.methodSpecsCombined != null) {
            that.methodSpecsCombined.cases.accept(this);
        }
        else if (that.cases != null) that.cases.accept(this);
        // FIXME - visitMethodDef will print the Java modifiers
        // and annotations that are on the Java declaration
        // We need the following to get the combined annotations
        // but we don't want both?
        // if (that.methodSpecsCombined != null) that.methodSpecsCombined.mods.accept(this);
        
        // Do some shenanigans with sourceOuput to get default constructors printed
        boolean wasSourceOutput = sourceOutput;
        if (that.name == that.name.table.names.init &&
                sourceOutput) sourceOutput = false;

        visitMethodDef(that);
        sourceOutput = wasSourceOutput;
    }

    public void visitJmlVariableDecl(JmlVariableDecl that) {
        // FIXME //@?
        visitVarDef(that);
    }
    
    @Override
    public void visitVarDef(JCVariableDecl that) {
        super.visitVarDef(that);
        if (!(that instanceof JmlVariableDecl)) return;
        JmlVariableDecl jmlthat = (JmlVariableDecl)that;
        if (jmlthat.fieldSpecsCombined != null) printFieldSpecs(jmlthat.fieldSpecsCombined);
        else if (jmlthat.fieldSpecs != null) printFieldSpecs(jmlthat.fieldSpecs);
    }
    
    public void printFieldSpecs(JmlSpecs.FieldSpecs fspecs) {
        // FIXME - may need to add a println at the beginning and omit one at the end
        // FIXME //@?
        indent();
        for (JmlTypeClause t: fspecs.list) {
            try {
                if (t.clauseType == inClause|| t.clauseType == mapsClause) {
                    align(); t.accept(this); println();
                }
            } catch (IOException e) {
                perr(t,e);
            }
        }
        for (JmlTypeClause t: fspecs.list) {
            try{
                if (t.clauseType == inClause || t.clauseType == mapsClause) continue;
                align(); t.accept(this); println(); // FIXME - what might theses be?
            } catch (IOException e) {
                perr(t,e);
            }
        }
        undent();
    }

    @Override
    public void visitLiteral(JCLiteral that) {
        try {
            if (that.value instanceof Type) {
                print(that.value.toString());
            } else if (that.value instanceof Long) {
                print(that.value.toString() + "L");
            } else {
                super.visitLiteral(that);
            }
        } catch (IOException e) {
            perr(that,e);
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
            else {
                // This special case is here because of a bug in JDK that 
                // put a parent with an empty name before each package name.
                // We also put a fix in TreeMaker.QualIdent, but am not sure it
                // is correct or will be kept.
                if(tree.selected instanceof JCIdent 
                        && ((JCIdent)(tree.selected)).name!=null 
                        && ((JCIdent)(tree.selected)).name.isEmpty())
                    print(tree.name);
                else print("." + tree.name);
            }
        } catch (IOException e) {
            perr(tree,e);
        }
    }

    /** Overridden to try to cleanup a little bit the printing of an anonymous
     * class expression.
     */
    @Override
    public void visitNewClass(JCNewClass tree) { // FIXME - review
        indent(); indent(); indent(); indent();  // indent
        super.visitNewClass(tree);
        undent(); undent(); undent(); undent();  // indent
    }

    public void visitJmlMethodSig(JmlMethodSig that) {
        try { 
            printExpr(that.expression);
            print("(");
            boolean first = true;
            for (JCExpression t: that.argtypes) {
                if (first) first = false; else print(",");
                printExpr(t);
            }
            print(")");
        } catch (IOException e) { perr(that,e); }
    }

    public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
        that.item.accept(this);
    }
    
    // Enables printing of things like:             
    //
    // [jmlrac:../demos/Test.java:1]\t %line
    // 
    // This makes reading the -show output easier. 

    public static String toFancyLineFormat(String file, JmlPrettyFormatter fmt, String old)
    {
        String pieces [] = old.split(System.getProperty("line.separator"));
        
        StringBuffer sb = new StringBuffer();
        
        int line=1;
        for(String p : pieces){
            sb.append(fmt.formatLine(file, line, p)).append(System.getProperty("line.separator"));
            line++;
        }

        return sb.toString();
    }
    
    public static String toFancyLineFormat(String file, JmlPrettyFormatter fmt, String prefix, String old)
    {
        return toFancyLineFormat(file, fmt, prefix + System.getProperty("line.separator") + old );
    }
    
    public static JmlPrettyFormatter racFormatter;
    
    interface JmlPrettyFormatter {
        default public String formatLine(String file, int lineNumber, String line) {
            return line;
        }
    }
    
    static {
        racFormatter = new JmlPrettyFormatter() {
//            @Override
//            public String formatLine(String file, int lineNumber, String line) {
//                return String.format("[jmlrac:%s:%d]    %s", file, lineNumber, line);
//            }
        };

    }
    
    
    
    
}
