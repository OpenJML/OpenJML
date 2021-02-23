/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.io.Writer;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTree;

import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.util.Context;

// FIXME - needs review - do we need all the fields of BasicProgram

/**
 * An instantiation of BasicProgramParent with a specific kind of BasicBlock.
 * 
 * @author David Cok
 */
// Note: everything declared protected is intended for use just in this class
// and any future derived classes - not in the containing package
public class BasicProgram extends BasicProgramParent<BasicProgram.BasicBlock> {
    
    /** Constructor of an empty program */
    public BasicProgram(Context context) {
        super(context);
    }

    /** Factory method to create a new block. */
    @Override
    protected BasicBlock newBlock(JCIdent id) { 
        return new BasicBlock(id); 
    }
        
    /** The id of the starting block; the pos of the block indicates where
     * in the original program the block starts */
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
            expr = JmlTree.Maker.instance(context).Binary(JCTree.Tag.EQ,id,value); // use treeutils?
            expr.pos = id.pos;  // FIXME _ end position not set, do we need it?
            expr.type = Symtab.instance(context).booleanType;
            return expr;
        }
    }
    
    /** A list of logical assertions (e.g. equalities that are definitions)
     *  used in the block equations but are not block equations themselves.
     */
    protected List<Definition> definitions = new ArrayList<Definition>();
    
//    /** Axioms - that is, assertions that do not rely on declarations within the basic block program */
//    protected List<JCExpression> pdefinitions = new ArrayList<JCExpression>();

    /** A map of expressions and ids that are the assumptions to be checked for vacuity. */
    //@ non_null
    public List<Map.Entry<JCExpression,String>> assumptionsToCheck = new LinkedList<Map.Entry<JCExpression,String>>();
    
    /** Returns the (mutable) list of definitions that are part of this program
     * @return the program's definitions
     */
    /*@pure*/
    public List<Definition> definitions() {
        return definitions;
    }
    
    /** A list of background assertions that are needed to support the functions
     * and constants used in the program.
     */
    protected List<JCExpression> background = new ArrayList<JCExpression>();

    /** Returns the (mutable) list of background assertions that are part of this program
     * @return the program's background assertions
     */
    /*@pure*/
    public List<JCExpression> background() {
        return background;
    }
    
    
    // FIXME -document
    public JCIdent assumeCheckVar;
    
    /** The identifier for the starting block - must match one of the blocks. */
    /*@pure*/ /*@non_null*/
    public JCIdent startId() {
        return startId;
    }
    
    /** The starting block */
    /*@pure*/ /*@non_null*/
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
                pw.print(e.name);
                pw.print(" : ");
                pw.print(e.type);
                pw.println();
                w.flush();
            }
            for (Definition e: definitions) {
                e.id.accept(pw);
                pw.print(" ::: ");
                if (e.value != null) e.value.accept(pw);
                pw.println();
                w.flush();
            }
            for (BasicProgram.BasicBlock b: this.blocks) {
                b.write(w,this);
            }
        } catch (java.io.IOException e) {
            // FIXME - create an error of some sort
            System.out.println("EXCEPTION: " + e);
            e.printStackTrace(System.out);
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
    static public class BasicBlock extends BasicProgramParent.BlockParent<BasicBlock> {
        
        /** A constructor creating an empty block with a name 
         * 
         * @param id the name of the block
         */
        BasicBlock(/*@ non_null*/JCIdent id) { 
            super(id);
        }
        
        public static class MethodInfo {
            JCExpression meth;
            JCExpression path;
            public MethodInfo(JCExpression meth, JCExpression path) {
                this.meth = meth;
                this.path = path;
            }
        }
        
        /*@ nullable */ Map<MethodSymbol,List<MethodInfo>> methodInfoMap = null;
        
       
        /** Writes out the basic block to the given Writer
         * 
         * @param w where to put a String representation of the block
         */
        public void write(Writer w, BasicProgram program) {
            // The 'false' argument allows non-compilable output and avoids
            // putting JML comment symbols everywhere
            JmlPretty pw = new JmlPretty(w,false);
            try {
                pw.print(id+":"+JmlPretty.lineSep);
                pw.print("    follows");
                for (BasicBlock ss: preceders()) {
                    pw.print(" ");
                    pw.print(ss.id.toString());
                }
                pw.print(JmlPretty.lineSep);
                pw.flush();
                //pw.indentAndPrint(); // FIXME - can't we use indenting?
                for (JCTree t: statements) {
                    pw.print("    ");
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
                    }
                    pw.print(JmlPretty.lineSep);
                    pw.flush();
                }
                if (followers.isEmpty()) {
                    pw.print("    <no continuation>;");
                } else {
                    pw.print("    goto");
                    boolean first = true;
                    for (BasicBlock ss: followers) {
                        if (first) first = false; else pw.print(",");
                        pw.print(" ");
                        pw.print(ss.id.toString());
                    }
                    pw.print(";");
                }
                //pw.undent(); // FIXME - check that this undents in the right place
                pw.print(JmlPretty.lineSep);
                pw.flush();
            } catch (java.io.IOException e) {
                try {
                    pw.print("EXCEPTION while pretty printing: " + e);
                } catch (java.io.IOException ee) {
                    // Give up
                }
            }
        }
        
        @Override
        public void write(Writer w) {
            write(w,null);
        }
    }
    
}
