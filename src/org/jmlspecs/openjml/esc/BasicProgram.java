package org.jmlspecs.openjml.esc;  // FIXME - change package

import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.ArrayList;
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

    /** A List of declarations of variables (program or auxiliary variables)
     * that are used in this BasicProgram.
     */
    //@ non_null
    protected List<VarDSA> declarations = new ArrayList<VarDSA>();
    
    /** Returns the declarations in this program
     * 
     * @return the declarations of variables in this program
     */
    public List<VarDSA> declarations() { return declarations; }
    
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
    
    public AuxVarDSA assumeCheckVar;
    
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
        JmlPretty p = new JmlPretty("  ", "  ");
        System.out.println("START = " + startId);
        try {
            System.out.print("Decls: ");
            for (VarDSA d: declarations) {
                System.out.print(d.sym.type);
                System.out.print(" ");
                System.out.print(d.toString());
                System.out.print("; ");
            }
            System.out.println();
            Writer w = new OutputStreamWriter(System.out);
            JmlPretty pw = new JmlPretty(w,true);
            for (JCExpression e: definitions) {
                pw.printExpr(e); pw.println();
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
            try {
                Writer w = new OutputStreamWriter(System.out);
                JmlPretty pw = new JmlPretty(w,true);
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
                    if (t instanceof JCTree.JCExpressionStatement) w.write("\n");
                    w.flush(); // FIXME - we should not need explicit newline after assignments?
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
    
    /** A parent class of Basic program variables - either those
     * representing program variables or those that are helper
     * auxiliary variables.
     * @author avid Cok
     *
     */ // TODO - finish documentation
    public static abstract class VarDSA extends JCTree.JCExpression {
        public VarSymbol sym;
        
        public VarDSA(VarSymbol sym) {
            this.sym = sym;
        }

       public Kind getKind() {
           // TODO Auto-generated method stub
           return null;
       }

       @Override
       public int getTag() {
           // TODO Auto-generated method stub
           return 0;
       }
       public int hashCode() {
           return toString().hashCode();
       }
       
       public boolean equals(Object o) {
           if (!(o instanceof VarDSA)) return false;
           return toString().equals(o.toString());
       }
   }
   
   public static class ProgVarDSA extends VarDSA{
       public ProgVarDSA(VarSymbol s, int usePos) {
           super(s);
           this.pos = usePos;
           this.incarnation = 0;
       }
       private ProgVarDSA(VarSymbol s, int incarnation, int usePos) {
           this(s,usePos);
           this.incarnation = incarnation;
       }
       int incarnation;
       
       public String toString() {
           return sym + "$" + sym.pos + "$" + incarnation;
       }

       public String root() {
           return sym + "$" + sym.pos + "$";
       }

       @Override
       public void accept(Visitor v) { 
           ((IJmlVisitor)v).visitProgVarDSA(this); 
       }

       @Override
       public <R,D> R accept(TreeVisitor<R,D> v, D d) {
           return ((JmlTreeVisitor<R,D>)v).visitProgVarDSA(this, d);
       }
       
       public ProgVarDSA copy() {
           return new ProgVarDSA(sym,incarnation,pos);
       }
}
   
   public static class AuxVarDSA extends VarDSA {
       public AuxVarDSA(Name root, Type type, JCExpression def) {
           super(null);
           this.root = root;
           super.sym = new VarSymbol(0,root,type,null);
           this.definition = def;
       }
       
       public Name root;
       
       public JCExpression definition;

       public String toString() {
           return root.toString();
       }

       @Override
       public void accept(Visitor v) { ((IJmlVisitor)v).visitAuxVarDSA(this); }

       @Override
       public <R,D> R accept(TreeVisitor<R,D> v, D d) {
           return ((JmlTreeVisitor<R,D>)v).visitAuxVarDSA(this, d);
       }
       public AuxVarDSA copy() {
           return new AuxVarDSA(root,sym.type,definition); // FIXME - use the same type?
       }
       
   }


}
