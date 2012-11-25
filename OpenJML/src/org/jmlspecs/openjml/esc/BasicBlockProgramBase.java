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
abstract public class BasicBlockProgramBase {
    
    public BasicBlockProgramBase(Context context) {
        syms = Symtab.instance(context);
    }

    @NonNull final public Symtab syms;
    
    /** The method declaration generating this program */
    protected JCMethodDecl methodDecl;
    
    /** Writes out the BasicProgram to the given Writer (e.g. log.noticeWriter) for diagnostics */
    abstract public void write(Writer w);
    
    /** Writes the BasicProgram to a string with the given initial string */
    abstract public String write(String header);

    /** Writes the program to a String, returning it. */
    @Override
    public String toString() {
        return write("");
    }
    
}
