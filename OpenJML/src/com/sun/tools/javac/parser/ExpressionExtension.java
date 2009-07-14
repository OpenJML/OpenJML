package com.sun.tools.javac.parser;

import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Map;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.ext.Elemtype;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

public abstract class ExpressionExtension {

    /** The compilation context, set when derived classes are instantiated */
    protected /*@ non_null */ Context context;

    /** The parser in use, set when derived classes are instantiated */
    protected /*@ non_null */ JmlParser parser;
    
    /** The scanner in use, set when derived classes are instantiated */
    protected /*@ non_null */ JmlScanner scanner;
    
    //@ public constraint context == \old(context);
    
    /** A constructor needed by derived classes; this class should not be
     * instantiated directly by users.
     */
    protected ExpressionExtension() {}
    
    /** Sets the compilation context - called by the infrastructure when a
     * derived instance is instantiated.
     * @param context the compilation context
     */
    //@ ensures this.context == context;
    public void setContext(JmlParser parser) {
        this.context = parser.context;
        this.parser = parser;
        this.scanner = parser.getScanner();
    }
    
    /** Returns a (derived instance of) ExpressionExtension if there is one associated
     * with the given token; sets its context.  Returns null if there is no
     * extension for the given token.
     * @param token the extension token
     * @param context the compilation context
     * @return an instance of a ExpressionExtension object, or null
     */
    static public @Nullable ExpressionExtension find(int pos, JmlToken token, Context context, JmlParser parser) {
        Class<?> c = extensions.get(token);
        if (c == null) return null;
        try {
            ExpressionExtension e = (ExpressionExtension)c.newInstance();
            e.setContext(parser);
            return e;
        } catch (Exception ee) {
            Log.instance(context).error(pos,"jml.failure.to.create.ExpressionExtension",token.internedName());
            return null;
        }
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
        Log.instance(context).noticeWriter.println(msg);
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
    
    /** Called by JmlParser when it sees the token for this extension.
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
    abstract public JCExpression parse(JmlParser parser, @Nullable List<JCExpression> typeArgs);
    
    // FIXME - I thought that here we could use Class<? extends ExpressionExtension>
    // avoiding the cast of the result of newInstance above.
    static protected Map<JmlToken,Class<?>> extensions = new HashMap<JmlToken,Class<?>>();
    
    static Class<?>[] extensionClasses = { Elemtype.class };
    static {
        JmlToken[] tokens;
        for (Class<?> c: extensionClasses) {
            try {
                Method m = c.getMethod("tokens");
                tokens = (JmlToken[])m.invoke(null);
            } catch (Exception e) {
                continue;
            }
            for (JmlToken t: tokens) extensions.put(t,c);
        }
    }
    
}
