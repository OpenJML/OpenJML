package org.jmlspecs.openjml.esc;  // FIXME - change package

import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.annotations.*;
import org.jmlspecs.openjml.IJmlVisitor;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTreeVisitor;

import com.sun.source.tree.TreeVisitor;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Name;

/**
 * A BasicProgram is an equivalent representation of a method. There are three
 * forms of BasicProgram:
 * <ol>
 * <li>in formation - in this form the statements may be any JCTree
 * statements,</li>
 * <li>preDSA - in this form, the statements may be assignments with pure
 * RHS, simple method calls (including an assignment of the result of a method
 * call), assume statements and assert statements, and</li>
 * <li>postDSA - in this form, all assigned variables are unique (in DSA
 * form), and all assignments are converted into assumptions.</li>
 * </ul>
 * 
 * @author David Cok
 */
public class BasicProgram {

    /** A List of declarations of variables
     * that are used in this BasicProgram; note that these identifiers
     * have encoded names that are different than the declared name,
     * because of DSA renaming.
     */
    //@ non_null
    protected Collection<JCIdent> declarations = new ArrayList<JCIdent>();
    
    /** Returns the declarations in this program
     * 
     * @return the declarations of variables in this program
     */
    public Collection<JCIdent> declarations() { return declarations; }
    
    /** The name of the starting block */
    //@ non_null
    String startId;
    
    /** A list of equalities that are definitions used in the block equations
     *  but are not block equations themselves.
     */
    List<JCExpression> definitions;

    /** Returns the definitions that are part of this program
     * @return the program's definitions
     */
    @Pure
    public List<JCExpression> definitions() {
        return definitions;
    }
    
    /** A list of blocks that constitute this BasicProgram. */
    //@ non_null
    ArrayList<BasicBlock> blocks = new ArrayList<BasicBlock>();
    
    /** Returns this programs list of blocks 
     * @return this programs blocks
     */
    @Pure @NonNull
    public List<BasicBlock> blocks() { return blocks; }
    
    public JCIdent assumeCheckVar;
    
    // FIXME
    @Pure @NonNull
    public String startId() {
        return startId;
    }
    
    @Pure @NonNull
    public BasicBlock startBlock() {
        return blocks.get(0); // FIXME - is it always the first one?
    }
    
    /** Writes out the BasicProgram to System.out for diagnostics */
    public void write() {
        System.out.println("START = " + startId);
        try {
            Writer w = new OutputStreamWriter(System.out);
            JmlPretty pw = new JmlPretty(w,true);
            pw.useJMLComments = false;
            for (JCExpression e: definitions) {
                e.accept(pw);
                pw.println();
                w.flush();
            }
            for (BasicProgram.BasicBlock b: this.blocks) {
                b.write();
            }
        } catch (java.io.IOException e) {
            System.out.println("EXCEPTION: " + e);
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
    static public class BasicBlock {
        /** A constructor creating an empty block with a name 
         * 
         * @param name the name of the block
         */
        BasicBlock(/*@ non_null*/String name) { 
            this.name = name;
        }
        
        /** A constructor creating an empty block with a given name; the
         * newly created block becomes the block that precedes the blocks
         * that previously succeeding the argument. 
         * @param name the name of the new block
         * @param b the block donating its followers
         */
        // BEFORE  b.succeeding -> List
        // AFTER   b.succeeding -> NONE; this.succeeding -> List
        BasicBlock(@NonNull String name, @NonNull BasicBlock b) {
            this(name);
            List<BasicBlock> s = succeeding;
            succeeding = b.succeeding;
            b.succeeding = s;
            for (BasicBlock f: succeeding) {
                f.preceding.remove(b);
                f.preceding.add(this);
            }
        }
        
        /** The name of the block */
        /*@ non_null*/String name;
        
        /** Returns the name of the block
         * @return the block's name
         */
        @Pure @NonNull
        public String name() { return name; }
        
        /** The ordered list of statements in the block */
        /*@ non_null*/List<JCStatement> statements = new LinkedList<JCStatement>();
        
        /** Returns the block's statements
         * @return the block's statements
         */
        @Pure @NonNull
        public List<JCStatement> statements() { return statements; }
        
        /** The set of blocks that succeed this one */
        @NonNull List<BasicBlock> succeeding = new ArrayList<BasicBlock>();
        
        /** Returns the block's followers
         * @return the block's followers
         */
        @Pure @NonNull
        public List<BasicBlock> succeeding() { return succeeding; }
        
        /** The set of blocks that precede this one */ // FIXME - is this ever needed?
        /*@ non_null*/List<BasicBlock> preceding = new ArrayList<BasicBlock>();
        
        /** Writes out the block to System.out, for diagnostic purposes */
        public void write() {
            write(new OutputStreamWriter(System.out));
        }
        
        public String toString() {
            java.io.StringWriter s = new java.io.StringWriter();
            write(s);
            return s.toString();
        }
        
        public void write(Writer w) {
            try {
                JmlPretty pw = new JmlPretty(w,false);
                w.write(name+":\n");
                w.write("    follows");
                for (BasicBlock ss: preceding) {
                    w.write(" ");
                    w.write(ss.name);
                }
                w.write("\n");
                w.flush();
                for (JCTree t: statements) {
                    w.write("    "); // FIXME - use JMLPretty indentation?
                    t.accept(pw);
                    w.write("\n");
                    w.flush();
                }
                w.write("    goto");
                for (BasicBlock ss: succeeding) {
                    w.write(" ");
                    w.write(ss.name);
                }
                w.write("\n");
                w.flush();
            } catch (java.io.IOException e) {
                System.out.println("EXCEPTION: " + e);
            }
        }
    }
    
}
