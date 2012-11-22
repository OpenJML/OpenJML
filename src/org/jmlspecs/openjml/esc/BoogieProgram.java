/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.List;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Pure;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.esc.BasicBlockProgram.BlockParent;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.util.Context;

/**
 * A BasicProgram is an equivalent representation of a method:
 * <UL>
 * <LI>it expresses the program as a DAG of basic blocks
 * <LI>each block represents a non-branching set of code
 * <LI>DSA has been applied
 * <LI>all statements have been converted to assumptions and assertions
 * <LI>the AST used for expressions is simplified
 * </UL>
 * The BasicBlocks are allowed to have regular Java/JML statements (as an 
 * interim state) but are then
 * massaged (by the BasicBlocker) into the official BasicProgram form.  This 
 * class just holds the data and does not provide transforming functionality.
 * 
 * @author David Cok
 */
// Note: everything declared protected is intended for use just in this class
// and any future derived classes - not in the containing package
public class BoogieProgram extends BasicBlockProgram<BoogieProgram.BoogieBlock>{
    
    public BoogieProgram(Context context) {
        super(context);
    }

    /** Factory method to create a new block. */
    @Override
    protected BasicBlockProgram.BlockParent<BoogieBlock> newBlock(JCIdent id) { return new BoogieBlock(id); }
        
    /** A list of (global) variable declarations; that is - variables that are used in
     * more than one block. They may or may not have an initial value.
     */
    protected List<JCIdent> declarations = new ArrayList<JCIdent>();
    
    /** A list of background assertions that are needed to support the functions
     * and constants used in the program.
     */
    protected List<JCExpression> background = new ArrayList<JCExpression>();

    /** Returns the (mutable) list of background assertions that are part of this program
     * @return the program's definitions
     */
    @Pure
    public List<JCExpression> background() {
        return background;
    }
    
    
    public String trType(Type t) {
        if (t == syms.booleanType) return "bool";
        if (t == syms.intType) return "int"; // FIXME - 
        return "REF";
    }
    /** Writes out the BasicProgram to the given Writer (e.g. log.noticeWriter) for diagnostics */
    public void write(Writer w) {
        try {
            //w.append("START = " + startId + "\n");
            JmlPretty pw = new BoogiePrinter(w);
            pw.print("type REF; ");
            pw.println();
            pw.print("const unique null : REF ;");
            pw.println();
            
            pw.print("procedure ");
            pw.print(methodDecl.name);
            boolean first = true;
            for (JCVariableDecl p : methodDecl.params) {
                if (first) { first = false; pw.print("("); } else pw.print(",");
                pw.print(p.name.toString() + "__" + p.pos);
                pw.print(" : ");
                pw.print(trType(p.type));
            }
            pw.print(") returns ()");  // FIXME - needs  return type
            pw.println();
            // FIXME - needs the spec
            pw.print("{");
            pw.println();
            for (JCIdent e: declarations) {
                pw.print("var ");
                pw.print(e.name.toString());
                pw.print(" : ");
                pw.print(trType(e.type));
                pw.print(" ;");
                pw.println();
                w.flush();
            }
            for (JCExpression e: background) {
                e.accept(pw);
                pw.println();
                w.flush();
            }
            for (BoogieProgram.BoogieBlock b: this.blocks) {
                b.write(w);
            }
            pw.print("}");
            pw.println();
        } catch (java.io.IOException e) {
            System.out.println("EXCEPTION: " + e);
            e.printStackTrace(System.out);
        }
    }

    /** Writes the BasicProgram to a string with the given initial string */
    public String write(String header) {
        StringWriter sw = new StringWriter();
        sw.append(header);
        write(sw);
        return sw.toString();
    }

    /** This class holds a basic block (a sequence of non-branching
     * statements, expressions have no embedded calls or side-effects such
     * as assignments).
     * The expressions in a BasicBlock use JCTree nodes.
     * Note that a BasicBlock becomes basic as a process of evolution.
     * @author David Cok
     *
     */
    static public class BoogieBlock extends BasicBlockProgram.BlockParent<BoogieBlock> {
        
        /** A constructor creating an empty block with a name 
         * 
         * @param id the name of the block
         */
        BoogieBlock(/*@ non_null*/JCIdent id) { 
            super(id);
        }
        
        /** A constructor creating an empty block with a given name; the
         * newly created block becomes the block that precedes the blocks
         * that previously succeeded the argument. 
         * @param id the identifier of the new block
         * @param b the block donating its followers
         */
        // BEFORE  b.succeeding -> List
        // AFTER   b.succeeding -> NONE; this.succeeding -> List
        protected BoogieBlock(@NonNull JCIdent id, @NonNull BoogieBlock b) {
            this(id);
            List<BoogieBlock> s = succeeding; // empty, just don't create a new empty list
            succeeding = b.succeeding;
            b.succeeding = s;
            for (BoogieBlock f: succeeding) {
                f.preceding.remove(b);
                f.preceding.add(this);
            }
        }
        
        /** Writes out the basic block to the given Writer
         * 
         * @param w where to put a String representation of the block
         */
        public void write(Writer w) {
            try {
                // The 'false' argument allows non-compilable output and avoids
                // putting JML comment symbols everywhere
                JmlPretty pw = new BoogiePrinter(w);
                w.write(id+":\n");
                w.flush();
                for (JCTree t: statements) {
                    w.write("    "); // FIXME - use JMLPretty indentation?
                    t.accept(pw);
                    w.write("\n");
                    w.flush();
                }
                if (succeeding.isEmpty()) {
                    w.write("    return;\n"); // FIXME - replace all the \n
                } else {
                    w.write("    goto");
                    boolean first = true;
                    for (BoogieBlock ss: succeeding) {
                        if (first) first = false; else w.write(",");
                        w.write(" ");
                        w.write((ss).id.toString()); // FIXME _ can this be done without a cast
                    }
                    w.write(";\n");
                }
                w.flush();
            } catch (java.io.IOException e) {
                System.out.println("EXCEPTION: " + e);
            }
        }

        
    }
    
    public static class BoogiePrinter extends JmlPretty {
        public BoogiePrinter(Writer out) { super(out,false); }
        
        public void visitJmlStatementExpr(JmlStatementExpr that) {
            try { 
                if (that.token == JmlToken.COMMENT) {
                    // SKIP
                    //print("// ");
                    //print(((JCLiteral)that.expression).value); // FIXME - can the comment span more than one line?
                } else {
                    print(that.token.internedName());
                    print(" ");
                    if (that.label != null) {
                        print("{ :reason \"");
                        print(that.label);
                        print("\"} ");
                    }
                    print("{ :pos ");
                    print(that.pos);
                    print("} ");
                    printExpr(that.expression); 
                    print(";");
                    //println();
                }
            } catch (IOException e) { perr(that,e); }
        }

        @Override
        public void visitExec(JCExpressionStatement tree) {
            try {
                printExpr(tree.expr);
                println();
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
        }
        @Override
        public void visitAssign(JCAssign tree) {
            try {
                open(prec, TreeInfo.assignPrec);
                printExpr(tree.lhs, TreeInfo.assignPrec + 1);
                print(" := ");
                printExpr(tree.rhs, TreeInfo.assignPrec);
                print(" ;");
                close(prec, TreeInfo.assignPrec);
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
        }


    }
    
}
