package com.sun.tools.javac.parser;

import java.io.PrintStream;

import org.jmlspecs.openjml.JmlTreeScanner;

import com.sun.tools.javac.tree.JCTree;

/** This class walks a JML AST printing debug information about each node.
 * Note that it needs a reference to the parser in order to get position information.
 * @author David Cok
 */
public class TreePrinter extends JmlTreeScanner {
    
    /** The current indentation level */
    String indent = "";
    
    /** The output stream */
    PrintStream out;
    
    /** The parser supplying end position information */
    EndPosParser parser;
    
    /** A constructor for the tree
     * @param out where to write the output information
     * @param p the parser with the position information
     */
    public TreePrinter(PrintStream out, EndPosParser p) {
        this.out = out;
        parser = p;
    }
    
    // FIXME - what AST walking mode should be used
    
    /** Implements the superclass scan method to print out a line of information about
     * argument and then proceed to scan its children
     */
    public void scan(JCTree t) {
        if (t == null) return;
        out.println(indent + t.getClass() 
                + " " + t.getTag() 
                + " " + t.getStartPosition() 
                + " " + (parser==null?"":String.valueOf(parser.getEndPos(t))));
        String oldindent = indent;
        indent = indent + "  ";
        super.scan(t);
        indent = oldindent;
    }
}