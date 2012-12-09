/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Pure;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAssignment;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAssignment;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.esc.BasicBlockProgram.BlockParent;
import org.smtlib.IExpr;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
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
    
    protected int style = 0;
    protected final int HEAP_STYLE = 1;
    protected final int SEP_STYLE = 0;
    
    public BoogieProgram(Context context) {
        super(context);
    }

    public Map<String,JmlStatementExpr> assertMap = new HashMap<String,JmlStatementExpr>();
    
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
            pw.print("type Arrays a = [REF][int] a; ");
            pw.println();
            pw.print("var arrays_int: Arrays int ;");
            pw.println();
            pw.print("var arrays_REF: Arrays REF; ");
            pw.println();
            pw.print("const unique null : REF ;");
            pw.println();
            pw.print("const unique this__0 : REF ;");
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
            pw.print("    modifies arrays_int;");
            pw.println();
            // FIXME - needs the spec
            pw.print("{");
            pw.println();
            for (JCIdent e: declarations) {
                if (e.sym != null && e.sym.owner != null &&
                        !e.sym.isStatic() &&
                        e.sym.owner instanceof Symbol.ClassSymbol) {
                    if (style == SEP_STYLE) {
                        pw.print("var ");
                        pw.print(e.name.toString());
                        pw.print(" : [REF]");
                        pw.print(trType(e.type));
                    }
                } else {
                    pw.print("var ");
                    pw.print(e.name.toString());
                    pw.print(" : ");
                    pw.print(trType(e.type));
                }
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
                b.write(w,pw);
            }
            pw.print("}");
            pw.println();
        } catch (java.io.IOException e) {
            System.out.println("EXCEPTION: " + e); // FIXME
            e.printStackTrace(System.out); // FIXME
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
        public void write(Writer w, JmlPretty bp) {
            try {
                // The 'false' argument allows non-compilable output and avoids
                // putting JML comment symbols everywhere
                JmlPretty pw = bp;
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
                System.out.println("EXCEPTION: " + e); // FIXME
            }
        }

        
    }
    
    public class BoogiePrinter extends JmlPretty {
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
                    print("{ :id ");
                    print(that.pos);
                    print("} ");
                    printExpr(that.expression); 
                    print(";");
                    assertMap.put(Integer.toString(that.pos), that);
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
        public void visitVarDef(JCVariableDecl tree) {
//            try {
//                print("var ");
//                print(tree.name.toString());
//                print(" : ");
//                print(trType(tree.type));
//                print(" ;");
//                println();
//            } catch (IOException e) {
//                throw new UncheckedIOException(e);
//            }
        }
        
        @Override
        public void visitAssign(JCAssign tree) {
            try {
                open(prec, TreeInfo.assignPrec);
                if (tree.lhs instanceof JCIdent) {
                    printExpr(tree.lhs, TreeInfo.assignPrec + 1);
                    print(" := ");
                    printExpr(tree.rhs, TreeInfo.assignPrec);
                    print(" ;");
                } else if (tree.lhs instanceof JCFieldAccess) {
                    JCFieldAccess fa = (JCFieldAccess)tree.lhs;
                    if (style == SEP_STYLE) {
                        // f := f[o := expr ]
                        print(fa.name);
                        print(" := ");
                        print(fa.name);
                        print("[");
                        printExpr(fa.selected);
                        print(" := ");
                        printExpr(tree.rhs);
                        print("];");
                    } else {
                        throw new RuntimeException("Unimplemented in BoogiePrinter.visitAssign " + tree.getClass());
                    }
                } else if (tree.lhs instanceof JCArrayAccess) {
                    JCArrayAccess fa = (JCArrayAccess)tree.lhs;
                    if (style == SEP_STYLE) {
                        // arrays_T := arrays_T[indexed := arrays_T[indexed][index := value] ]
                        print("arrays_int");
                        print(" := ");
                        print("arrays_int");
                        print("[");
                        printExpr(fa.indexed);
                        print(" := ");
                        print("arrays_int");
                        print("[");
                        printExpr(fa.indexed);
                        print("][");
                        printExpr(fa.index);
                        print(" := ");
                        printExpr(tree.rhs);
                        print("]];");
                    } else {
                        throw new RuntimeException("Unimplemented in BoogiePrinter.visitAssign " + tree.getClass());
                    }
                } else {
                    throw new RuntimeException("Unimplemented in BoogiePrinter.visitAssign " + tree.getClass());
                }
                close(prec, TreeInfo.assignPrec);
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
        }
        
        @Override
        public void visitSelect(JCFieldAccess tree) {
            try {
                if (style == SEP_STYLE) {
                    print(tree.name);
                    print("[");
                    printExpr(tree.selected);
                    print("]");
                } else {
                    throw new RuntimeException("Unimplemented in BoogiePrinter.visitSelect " + style);
                }
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }

        }

        @Override
        public void visitIndexed(JCArrayAccess tree) {
            try {
                if (style == SEP_STYLE) {
                    print("arrays_int");
                    print("[");
                    print(tree.indexed);
                    print("]");
                    print("[");
                    printExpr(tree.index);
                    print("]");
                } else {
                    throw new RuntimeException("Unimplemented in BoogiePrinter.visitSelect " + style);
                }
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }

        }

        @Override
        public void visitApply(JCMethodInvocation tree) {
            try {
            JCExpression m = tree.meth;
            if (m instanceof JCIdent) {
//                if (((JCIdent)m).name.toString().equals(BasicBlocker2.STOREString)) {
//                    result = F.fcn(F.symbol("store"),
//                            convertExpr(tree.args.get(0)),
//                            convertExpr(tree.args.get(1)),
//                            convertExpr(tree.args.get(2))
//                            );
//                    return;
//                }
            } else if (m == null) {
                if (tree instanceof JmlBBFieldAssignment) {
                    JCTree name = tree.args.get(1);
                    JCTree obj = tree.args.get(2);
                    JCTree value = tree.args.get(3);
                    if (style == SEP_STYLE) {
                        // f := f[o := expr ]
                        print(name.toString());
                        print(" := ");
                        print(name.toString());
                        print("[");
                        printExpr(obj);
                        print(" := ");
                        printExpr(value);
                        print("]");
                        return;
                    } else {
                        throw new RuntimeException("Unimplemented in BoogiePrinter.visitAssign " + tree.getClass());
                    }
                }
                else if (tree instanceof JmlBBArrayAssignment) {
                    // [0] = store([1],[2], store(select([1],[2]),[3],[4]))
//                    IExpr.IFcnExpr sel = F.fcn(F.symbol("select"),
//                            convertExpr(tree.args.get(1)),
//                            convertExpr(tree.args.get(2))
//                            );
//                    IExpr.IFcnExpr newarray = F.fcn(F.symbol("store"),
//                                    sel,
//                                    convertExpr(tree.args.get(3)),
//                                    convertExpr(tree.args.get(4))
//                                    );
//
//                    IExpr.IFcnExpr right = F.fcn(F.symbol("store"),
//                            convertExpr(tree.args.get(1)),
//                            convertExpr(tree.args.get(2)),
//                            newarray
//                            );
//                    result = F.fcn(F.symbol("="), convertExpr(tree.args.get(0)),right);
//                    return;
                }
            }
            notImpl(tree);
            super.visitApply(tree);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        }


    }
    
}
