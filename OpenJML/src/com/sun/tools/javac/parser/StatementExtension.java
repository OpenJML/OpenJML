/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.parser;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;

/* FIXME - do more to implement extensions */

/* TODO - needs documentation */
abstract public class StatementExtension {
    protected static final Context.Key<StatementExtension> statementExtensionsKey =
            new Context.Key<StatementExtension>();

    /** The compilation context, set when derived classes are instantiated */
    protected /*@ non_null */ Context context;

    /** The parser in use, set when derived classes are instantiated */
    protected /*@ non_null */ JmlParser parser;
    
    /** The scanner in use, set when derived classes are instantiated */
    protected /*@ non_null */ JmlScanner scanner;
    
    /** The node factory in use, set when derived classes are instantiated */
    protected /*@ non_null */ JmlTree.Maker jmlF;

    /** The symbol table, set when the context is set */
    protected Symtab syms;
    
    /** The Utils instance */
    protected Utils utils;
    
    //@ public constraint context == \old(context);
    
    
    /** A constructor needed by derived classes; this class should not be
     * instantiated directly by users.
     */
    protected StatementExtension(Context context) {
        this.context = context;
        this.syms = Symtab.instance(context);
        this.utils = Utils.instance(context);
    }
    
    /** Writes an error message to the log, using the given DiagnosticPosition
     * (typically gotten from tree.pos()), 
     * a key (as in the file org.jmlspecs.openjml.messages.properties)
     * and arguments for that key
     * @param pos the DiagnosticPosition used to identify the relevant location in the source file
     * @param key the resource key holding the error message
     * @param args (non-null) arguments for the key - there must be at least as many arguments as there are place-holders in the key string
     */
    public void error(DiagnosticPosition pos, String key, Object ... args) {
        Log.instance(context).error(pos,key,args);
    }
    
    /** Writes a warning message to the log, using the given DiagnosticPosition
     * (typically gotten from tree.pos()), a key (as in the file org.jmlspecs.openjml.messages.resources)
     * and arguments for that key
     * @param pos the DiagnosticPosition used to identify the relevant location in the source file
     * @param key the resource key holding the error message
     * @param args (non-null) arguments for the key - there must be at least as many arguments as there are place-holders in the key string
     */
    public void warning(DiagnosticPosition pos, String key, Object ... args) {
        Log.instance(context).warning(pos,key,args);
    }
    
    /** Writes an informational message to the log's noticeWriter (as with
     * println).  To be used for informational or debugging information.
     * @param msg the String to write
     */
    public void info(@NonNull String msg) {
        Log.instance(context).getWriter(WriterKind.NOTICE).println(msg);
    }
    
    /** Sets the end position of the given tree node to be the end position of
     * the previously scanned token.
     * @param <T> the type of the node being set
     * @param tree the node whose end position is being set
     * @return returns the same node
     */
    public <T extends JCTree> T toP(T tree) {
        return parser.toP(tree);
    }
    
    /** Called by JmlParser when it sees the initial token for this extension.
     * The derived class implementation is responsible to scan tokens using
     * the scanner (JmlParser.getScanner()) and return a JCExpression parse
     * tree.  When called, the current scanner token is the JmlToken itself;
     * this method is responsible to scan the end of the expression (e.g. the
     * terminating parenthesis) and no more.  If an error occurs because of
     * badly formed input, the method is required to return null and to 
     * recover as best it can.  [ FIXME - return JCErroneous?]
     * <BR>Useful methods:
     * <BR>JmlParser.getScanner() - returns the current JmlScanner
     * <BR>JmlScanner.token() - the current Java token, or CUSTOM if a JML token
     * <BR>JmlScanner.jmlToken() - the current JML token (null if a Java token)
     * <BR>JmlScanner.nextToken() - scans the next token
     * <BR>JmlScanner.pos() - the current character position, used for error reporting
     * <BR>JmlParser.syntaxError(...) - to report a parsing error
     * <BR>TODO: warning and error and informational messages
     * <BR>TODO: maker(), at(), primarySuffix, toP(), arguments(), others
     * 
     * @param parser the JmlParser for this compilation unit and compilation context
     * @param typeArgs any type arguments already seen (may be null)
     * @return the AST for the expression
     */
    abstract public JCStatement parse(JmlParser parser);
    
    protected void init(JmlParser parser) {
        this.parser = parser;
        this.scanner = parser.getScanner();
        this.jmlF = parser.maker();
    }
    
    // TODO: document
    abstract public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env);
    
}
