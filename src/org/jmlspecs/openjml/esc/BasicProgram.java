/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.io.StringWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Pure;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTree;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCStatement;
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
public class BasicProgram {
    
    /** The method declaration generating this program */
    protected JCMethodDecl methodDecl;
    
    /** The id of the starting block */
    //@ non_null
    protected JCIdent startId;
    
    /** This class represents a definition
     * <UL>
     * <LI>id: the identifier being defined
     * <LI>value: the defined value for the identifier
     * <LI>expr: an expression that is (id == value)
     * <LI>pos: a character position for the definition
     * </UL>
     */
    static public class Definition {
        /** The character position for the definition */
    	public int pos;
    	/** The identifier being defined */
        public JCIdent id;
        /** The defined value of the identifier */
        public JCExpression value;
        /** An expression representing (id == value) */
        private JCExpression expr;
        
        /** Constructor for a new definition */
        public Definition(int pos, JCIdent id, JCExpression value) {
        	this.pos = pos;
            this.id = id;
            this.value = value;
            this.expr = null;
        }
        
        /** Returns the lazily created equality for the definition */
        public JCExpression expr(Context context) {
            if (expr != null) return expr;
            expr = JmlTree.Maker.instance(context).Binary(JCTree.EQ,id,value); // use treeutils?
            expr.pos = id.pos;  // FIXME _ end position not set, do we need it?
            expr.type = Symtab.instance(context).booleanType;
            return expr;
        }
    }
    
    /** A list of (global) variable declarations; that is - variables that are used in
     * more than one block. They may or may not have an initial value.
     */
    protected List<JCIdent> declarations = new ArrayList<JCIdent>();

    /** A list of logical assertions (e.g. equalities that are definitions)
     *  used in the block equations but are not block equations themselves.
     */
    protected List<Definition> definitions = new ArrayList<Definition>();
    
    // FIXME - and what are these?
    protected List<JCExpression> pdefinitions = new ArrayList<JCExpression>();

    /** A map of expressions and ids that are the assumptions to be checked for vacuity. */
    //@ non_null
    public List<Map.Entry<JCExpression,String>> assumptionsToCheck = new LinkedList<Map.Entry<JCExpression,String>>();
    
    /** Returns the (mutable) list of definitions that are part of this program
     * @return the program's definitions
     */
    @Pure
    public List<Definition> definitions() {
        return definitions;
    }
    
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
    
    /** A list of blocks that constitute this BasicProgram. */
    //@ non_null
    protected ArrayList<BasicBlock> blocks = new ArrayList<BasicBlock>();
    
    /** Returns this program's list of blocks 
     * @return this program's blocks
     */
    @Pure @NonNull
    public List<BasicBlock> blocks() { return blocks; }
    
    // FIXME - document
    public Map<JCTree,JCTree> toLogicalForm = null;
    
    // FIXME -document
    public JCIdent assumeCheckVar;
    
    /** The identifier for the starting block - must match one of the blocks. */
    @Pure @NonNull
    public JCIdent startId() {
        return startId;
    }
    
    /** The starting block */
    @Pure @NonNull
    public BasicBlock startBlock() {
        // Almost always the first one, but just in case, we
        // start with the first but check them all
        for (BasicBlock b: blocks) {
            if (b.id == startId) return b;
        }
        throw new RuntimeException("INTERNAL ERROR - A BasicProgram does not contain its own start block"); // FIXME - what exception to use
    }
    
    /** Writes out the BasicProgram to the given Writer (e.g. log.noticeWriter) for diagnostics */
    public void write(Writer w) {
        try {
            w.append("START = " + startId + "\n");
            JmlPretty pw = new JmlPretty(w,true);
            pw.useJMLComments = false;
            for (JCExpression e: background) {
                e.accept(pw);
                pw.println();
                w.flush();
            }
            for (JCIdent e: declarations) {
                pw.print(e.name.toString());
                pw.print(" : ");
                pw.print(e.type.toString());
                pw.println();
                w.flush();
            }
            for (Definition e: definitions) {
                e.id.accept(pw);
                pw.print(" ::: ");
                e.value.accept(pw);
                pw.println();
                w.flush();
            }
            for (JCExpression e: pdefinitions) { // FIXME - get rid of this
                e.accept(pw);
                pw.println();
                w.flush();
            }
            for (BasicProgram.BasicBlock b: this.blocks) {
                b.write(w,this);
            }
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

    /** Writes the program to a String, returning it. */
    @Override
    public String toString() {
        return write("");
    }
    
    /** This class holds a basic block (a sequence of non-branching
     * statements, expressions have no embedded calls or side-effects such
     * as assignments).
     * The expressions in a BasicBlock use JCTree nodes.
     * Note that a BasicBlock becomes basic as a process of evolution.
     * @author David Cok
     *
     */
    static public class BasicBlock {
        
        /** A constructor creating an empty block with a name 
         * 
         * @param id the name of the block
         */
        BasicBlock(/*@ non_null*/JCIdent id) { 
            this.id = id;
        }
        
        /** A constructor creating an empty block with a given name; the
         * newly created block becomes the block that precedes the blocks
         * that previously succeeded the argument. 
         * @param id the identifier of the new block
         * @param b the block donating its followers
         */
        // BEFORE  b.succeeding -> List
        // AFTER   b.succeeding -> NONE; this.succeeding -> List
        protected BasicBlock(@NonNull JCIdent id, @NonNull BasicBlock b) {
            this(id);
            List<BasicBlock> s = succeeding; // empty, just don't create a new empty list
            succeeding = b.succeeding;
            b.succeeding = s;
            for (BasicBlock f: succeeding) {
                f.preceding.remove(b);
                f.preceding.add(this);
            }
        }
        
        /** The identifier of the block */
        /*@ non_null*/protected JCIdent id;
        
        /** Returns the id of the block
         * @return the block's id
         */
        @Pure @NonNull
        public JCIdent id() { return id; }
        
        /** The ordered list of statements in the block */
        @NonNull protected List<JCStatement> statements = new LinkedList<JCStatement>();
        
        /** Returns the block's statements
         * @return the block's statements
         */
        @Pure @NonNull
        public List<JCStatement> statements() { return statements; }
        
        /** The set of blocks that succeed this one */
        @NonNull protected List<BasicBlock> succeeding = new ArrayList<BasicBlock>();
        
        /** Returns the block's followers
         * @return the block's followers
         */
        @Pure @NonNull
        public List<BasicBlock> succeeding() { return succeeding; }
        
        /** The set of blocks that precede this one */ // FIXME - is this ever needed?
        /*@ non_null*/List<BasicBlock> preceding = new ArrayList<BasicBlock>();
        
        /** Generates a human-readable String representation of the block */
        @Override // @NonNull
        public String toString() {
            java.io.StringWriter s = new java.io.StringWriter();
            write(s,null);
            return s.toString();
        }
        
        /** Writes out the basic block to the given Writer
         * 
         * @param w where to put a String representation of the block
         */
        public void write(Writer w, BasicProgram program) {
            try {
                // The 'false' argument allows non-compilable output and avoids
                // putting JML comment symbols everywhere
                JmlPretty pw = new JmlPretty(w,false);
                w.write(id+":\n");
                w.write("    follows");
                for (BasicBlock ss: preceding) {
                    w.write(" ");
                    w.write(ss.id.toString());
                }
                w.write("\n");
                w.flush();
                for (JCTree t: statements) {
                    w.write("    "); // FIXME - use JMLPretty indentation?
                    t.accept(pw);
                    if (program != null && t instanceof JmlTree.JmlStatementExpr && ((JmlTree.JmlStatementExpr)t).expression instanceof JCIdent) {
                        JCIdent i = (JCIdent)((JmlTree.JmlStatementExpr)t).expression;
                        for (Definition def : program.definitions) {
                            if (def.id.name.equals(i.name)) {
                                JCExpression rhs = def.value;
                                w.write("    [ ");
                                rhs.accept(pw);
                                w.write(" ]");
                                break;
                            }
                        }
                        // TODO - I don't think the conditional in this loop is ever triggered
//                        for (JCExpression e : program.pdefinitions) {
//                            if (e instanceof JCBinary && ((JCBinary)e).lhs instanceof JCIdent 
//                                    && ((JCIdent)((JCBinary)e).lhs ).name.equals(i.name)) {
//                                JCExpression rhs = ((JCBinary)e).rhs;
//                                w.write("    [ ");
//                                rhs.accept(pw);
//                                w.write(" ]");
//                                break;
//                            }
//                        }
                    }
                    w.write("\n");
                    w.flush();
                }
                w.write("    goto");
                for (BasicBlock ss: succeeding) {
                    w.write(" ");
                    w.write(ss.id.toString());
                }
                w.write("\n");
                w.flush();
            } catch (java.io.IOException e) {
                System.out.println("EXCEPTION: " + e);
            }
        }
    }
    
}
