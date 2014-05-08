/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.parser;

import java.lang.reflect.Constructor;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.ext.Arithmetic.Safe;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

/* FIXME - do more to implement extensions */

/* TODO - needs documentation */
abstract public class ExpressionExtension {
    protected static final Context.Key<ExpressionExtension> exprExtensionsKey =
            new Context.Key<ExpressionExtension>();

    /** The compilation context, set when derived classes are instantiated */
    protected /*@ non_null */ Context context;

    /** The parser in use, set when derived classes are instantiated */
    protected /*@ non_null */ JmlParser parser;
    
    /** The scanner in use, set when derived classes are instantiated */
    protected /*@ non_null */ JmlScanner scanner;
    
    /** The symbol table, set when the context is set */
    protected Symtab syms;
    
    /** The Utils instance */
    protected Utils utils;
    
    //@ public constraint context == \old(context);

    public static void register(Context context) {}
    
    /** A constructor needed by derived classes; this class should not be
     * instantiated directly by users.
     */
    protected ExpressionExtension(Context context) {
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
    public JCExpression parse(JmlParser parser,
            @Nullable List<JCExpression> typeArgs) {
        // TODO Auto-generated method stub
        this.parser = parser;
        this.scanner = parser.getScanner();
        JmlToken jt = scanner.jmlToken();
        int p = scanner.pos();
        scanner.nextToken();
        if (scanner.token() != Token.LPAREN) {
            return parser.syntaxError(p, null, "jml.args.required", jt.internedName());
        } else if (typeArgs != null && !typeArgs.isEmpty()) {
            return parser.syntaxError(p, null, "jml.no.typeargs.allowed", jt.internedName());
        } else {
            int pp = scanner.pos();
            List<JCExpression> args = parser.arguments();
            JmlMethodInvocation t = toP(parser.maker().at(pp).JmlMethodInvocation(jt, args));
            t.startpos = p;
            checkParse(parser,t);
            return parser.primarySuffix(t, typeArgs);
        }
    }
    
    abstract public void checkParse(JmlParser parser, JmlMethodInvocation e);

    public void checkOneArg(JmlParser parser, JmlMethodInvocation e) {
        if (e.args.size() != 1) {
            parser.jmlerror(e.pos, e.getEndPosition(parser.endPositions()), "jml.one.arg", e.token.internedName());
        }
    }

    
    // TODO: document
    abstract public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env);

    public static <T> T instance(Context context, Class<T> key) {
        T s = context.get(key);
        if (s == null) {
            try {
                Constructor<T> c = key.getConstructor(Context.class);
                s = c.newInstance(context);
                context.put(key, s);
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        }
        return s;
    }

}
