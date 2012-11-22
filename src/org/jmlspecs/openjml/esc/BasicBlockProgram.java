/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.io.Writer;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Pure;
import org.jmlspecs.openjml.JmlPretty;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
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
abstract public class BasicBlockProgram<T extends BasicBlockProgram.BlockParent<?>> {
    
    public BasicBlockProgram(Context context) {
        syms = Symtab.instance(context);
        blocks = new ArrayList<T>();
    }

    @NonNull final public Symtab syms;
    
    /** The method declaration generating this program */
    protected JCMethodDecl methodDecl;
    
    /** Factory method to create a new block. */
    abstract protected BlockParent<T> newBlock(JCIdent id);
    
    /** A list of blocks that constitute this BasicProgram. */
    //@ non_null
    protected ArrayList<T> blocks;
    
    /** Returns this program's list of blocks 
     * @return this program's blocks
     */
    @Pure @NonNull
    public List<T> blocks() { return blocks; }
    
    /** Writes out the BasicProgram to the given Writer (e.g. log.noticeWriter) for diagnostics */
    abstract public void write(Writer w);
    
    /** Writes the BasicProgram to a string with the given initial string */
    abstract public String write(String header);

    /** Writes the program to a String, returning it. */
    @Override
    public String toString() {
        return write("");
    }
    
    static public class BlockParent<T> {
        /** The identifier of the block */
        /*@ non_null*/protected JCIdent id;
        
        public BlockParent(JCIdent id) {
            this.id = id;
        }
        
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
        @NonNull protected List<T> succeeding = new ArrayList<T>();
        
        /** Returns the block's followers
         * @return the block's followers
         */
        @Pure @NonNull
        public List<T> succeeding() { return succeeding; }
        
        /** The set of blocks that precede this one */ // FIXME - is this ever needed?
        /*@ non_null*/List<T> preceding = new ArrayList<T>();
        
        /** Generates a human-readable String representation of the block */
        @Override // @NonNull
        public String toString() {
            java.io.StringWriter s = new java.io.StringWriter();
            write(s);
            return s.toString();
        }

        /** Writes out the basic block to the given Writer
         * 
         * @param w where to put a String representation of the block
         */
        public void write(Writer w) {
            try {
                // The 'false' argument allows non-compilable output and avoids
                // putting JML comment symbols everywhere
                JmlPretty pw = new JmlPretty(w,false);
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
                    for (T ss: succeeding) {
                        if (first) first = false; else w.write(",");
                        w.write(" ");
                        w.write(((BlockParent<T>)ss).id.toString()); // FIXME _ can this be done without a cast
                    }
                    w.write(";\n");
                }
                w.flush();
            } catch (java.io.IOException e) {
                System.out.println("EXCEPTION: " + e);
            }
        }

    }
    
    /** This class holds a basic block (a sequence of non-branching
     * statements, expressions have no embedded calls or side-effects such
     * as assignments).
     * The expressions in a BasicBlock use JCTree nodes.
     * Note that a BasicBlock becomes basic as a process of evolution.
     * @author David Cok
     *
     */
    static public class Block extends BlockParent<Block> {
        
        /** A constructor creating an empty block with a name 
         * 
         * @param id the name of the block
         */
        Block(/*@ non_null*/JCIdent id) { 
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
        protected Block(@NonNull JCIdent id, @NonNull Block b) {
            this(id);
            List<Block> s = succeeding; // empty, just don't create a new empty list
            succeeding = b.succeeding;
            b.succeeding = s;
            for (Block f: succeeding) {
                f.preceding.remove(b);
                f.preceding.add(this);
            }
        }
        
        
    }
    
}
