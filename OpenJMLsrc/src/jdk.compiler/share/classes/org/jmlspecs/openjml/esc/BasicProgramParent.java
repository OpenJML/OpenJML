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


import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;

/**
 * A BasicProgram is an equivalent representation of a method:
 * <UL>
 * <LI>it expresses the program as a DAG of basic blocks
 * <LI>each block represents a non-branching set of code
 * </UL>
 * The BasicBlocks are allowed to contain regular Java/JML statements but derived
 * classes may make additional transformation and have restrictions on the
 * kinds of statements allowed.  This 
 * class just holds the data and does not provide transforming functionality.
 * 
 * @typeparam T the type of Block used by the program
 * @author David Cok
 */
// Note: everything declared protected is intended for use just in this class
// and any future derived classes - not in the containing package
abstract public class BasicProgramParent<T extends BasicProgramParent.BlockParent<T>> {

    /** Cached value of the symbol table */
    /*@non_null*/ final public Symtab syms;

    /** Parent class constructor */
    public BasicProgramParent(Context context) {
        //super(context);
        blocks = new ArrayList<T>();
        syms = Symtab.instance(context);
    }

    /** Factory method to create a new block. */
    abstract protected T newBlock(JCIdent id);
    
    /** A list of blocks that constitute this BasicProgram. */
    //@ non_null
    protected List<T> blocks;
    
    /** A list of variables that will need to be declared at the beginning of
     * a basic block program. Boogie requires all declarations at the beginning
     * of the implementation.
     */
    protected List<JCIdent> declarations = new ArrayList<JCIdent>();

    /** Returns this program's list of blocks 
     * @return this program's blocks
     */
    /*@pure*/ /*@non_null*/
    public List<T> blocks() { return blocks; }

    /** The method declaration generating this program */
    protected JCMethodDecl methodDecl;
    
    /** Writes out the BasicProgram to the given Writer (e.g. log.noticeWriter) for diagnostics */
    abstract public void write(Writer w);
    
    /** Writes the program to a String, returning it. */
    @Override
    public String toString() {
        StringWriter sw = new StringWriter();
        write(sw);
        return sw.toString();
    }

    /** The base class for basic blocks; the type argument is derived Block class */
    static abstract public class BlockParent<T extends BasicProgramParent.BlockParent<T>> {
        /** The identifier of the block */
        /*@ non_null*/protected JCIdent id;
        protected int unique;
        JCIdent sourceId;
        
        /** Constructs a block with the given id. The id is used both for its
         * name, which is an identifier of the block, and its position, which
         * indicates the location or statement in the program that begins
         * the block.
         * 
         * @param id
         */
        public BlockParent(JCIdent id) {
            this.id = id;
            this.unique = -1;
        }
        
        /** Returns the id of the block
         * @return the block's id
         */
        /*@pure*/ /*@non_null*/
        public JCIdent id() { return id; }
        
        /** The ordered list of statements in the block */
        /*@non_null*/ protected List<JCStatement> statements = new LinkedList<JCStatement>();
        
        /** Returns the block's statements
         * @return the block's statements
         */
        /*@pure*/ /*@non_null*/
        public List<JCStatement> statements() { return statements; }
        
        /** The set of blocks that succeed this one */
        /*@non_null*/ protected List<T> followers = new ArrayList<T>();
        
        /** Returns the block's followers
         * @return the block's followers
         */
        /*@pure*/ /*@non_null*/
        public List<T> followers() { return followers; }
        
        /** The set of blocks that precede this one */
        /*@non_null*/ protected List<T> preceders = new ArrayList<T>();
        
        /** Returns the block's preceders
         * @return the block's preceders
         */
        /*@pure*/ /*@non_null*/
        public List<T> preceders() { return preceders; }
        
        /** Generates a human-readable String representation of the block */
        @Override // /*@non_null*/
        public String toString() {
            java.io.StringWriter s = new java.io.StringWriter();
            write(s);
            return s.toString();
        }

        /** Writes out the basic block to the given Writer
         * 
         * @param w where to put a String representation of the block
         */
        abstract public void write(Writer w);
    }
}
