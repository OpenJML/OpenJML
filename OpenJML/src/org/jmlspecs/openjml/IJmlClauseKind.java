package org.jmlspecs.openjml;

import static com.sun.tools.javac.parser.Tokens.TokenKind.IDENTIFIER;
import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;
import static org.jmlspecs.openjml.JmlTokenKind.ENDJMLCOMMENT;

import java.lang.reflect.Constructor;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;
import org.jmlspecs.openjml.JmlTree.JmlSource;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.JmlToken;
import com.sun.tools.javac.parser.JmlTokenizer;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.Log.WriterKind;

/** Objects of this type represents kinds of JML clauses and statements, for example,
 *  requires clauses or the \old expression. Instances represent kinds of clauses,
 *  not instances of clauses. These objects also contain behavior of the clause kinds,
 *  namely how to parse and typecheck instances of these clauses. Instances of clauses
 *  are usually instances of derived types of JmlTree.
 * @author davidcok
 *
 */
public abstract class IJmlClauseKind {
    
    public static abstract class MethodClause extends IJmlClauseKind {
        public boolean preAllowed() { return !isPreconditionClause(); }
        public boolean isPreconditionClause() { return false; }
    }
    public static abstract class Statement extends IJmlClauseKind{
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
        public boolean preAllowed() { return true; }
    }
    
    /** The kind of line annotations */
    public static abstract class LineAnnotationKind extends IJmlClauseKind {

        @Override
        public JCTree parse(JCModifiers mods, String keyword,
                IJmlClauseKind clauseType, JmlParser parser) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            throw new UnsupportedOperationException();
        }

        abstract public void scan(int keywordPos, String keyword, IJmlClauseKind clauseKind, JmlTokenizer tokenizer);

        /** A class that is a record of an instance of a line annotation.
         * A line annotation is captured by the scanner, not the parser,
         * and so is a bit of a different animal. */
        public static abstract class LineAnnotation {
            public int line;
            public int keywordPos;
            public IJmlClauseKind clauseKind;
            public IJmlClauseKind clauseKind() { return clauseKind; }
            abstract public java.util.List<JCExpression> exprs();
            abstract public Type typecheck(JmlAttr attr, Env<AttrContext> env);
        }
    }
    public static abstract class TypeClause extends IJmlClauseKind {
    }
    public static abstract class Expression extends IJmlClauseKind {
    }
    public static abstract class Modifier extends IJmlClauseKind {
    }

    // These fields and methods give behavior of JML clauses of the given kind.

    protected String keyword;
    public String name() { return keyword; }
    
    public String toString() { return name(); }
    
    /** If true, is a method or type spec clause types in which \old without a label can be used
    */
    public boolean oldNoLabelAllowed() { return false; }
    
    /** If true, is a clause in which \pre and \old with a label can be used (e.g. asst)
     */
    public boolean preOrOldWithLabelAllowed() { return false; }
    
    public boolean preAllowed() { return false; }

    /** If true, is a method clause type in which these tokens may appear:
     *  \not_assigned \only_assigned \only_captured \only_accessible \not_modified */
    public boolean postClauseAllowed() { return false; }
    
    /** If true, is a method clause type in which the \result token may appear 
     * (and \not_assigned \only_assigned \only_captured \only_accessible \not_modified) */
    public boolean resultExpressionAllowed() { return false; }

    /** If true, is a method clause type in which the \exception token may appear 
     */
    public boolean exceptionExpressionAllowed() { return false; }

    /** If true, is a method clause type in which the \fresh token may appear 
     */
    public boolean freshExpressionAllowed() { return false; }
    
    // The following fields are initialized on demand when parsing or typechecking
    
    /** The compilation context, set when derived classes are instantiated */
    static protected /*@ non_null */ Context context;
    //@ public constraint context == \old(context);

    /** The parser in use, set when derived classes are instantiated */
    protected /*@ non_null */ JmlParser parser;
    
    /** The scanner in use, set when derived classes are instantiated */
    protected /*@ non_null */ JmlScanner scanner;
    
    /** The node factory in use, set when derived classes are instantiated */
    protected /*@ non_null */ JmlTree.Maker jmlF;

    /** The symbol table, set when the context is set */
    protected Symtab syms;
    
    /** The names table, set when the context is set */
    protected Names names;
    
    /** The Utils instance */
    protected Utils utils;
    
    protected Log log;
    
    /** Writes an error message to the log, using the given DiagnosticPosition
     * (typically gotten from tree.pos()), 
     * a key (as in the file org.jmlspecs.openjml.messages.properties)
     * and arguments for that key
     * @param pos the DiagnosticPosition used to identify the relevant location in the source file
     * @param key the resource key holding the error message
     * @param args (non-null) arguments for the key - there must be at least as many arguments as there are place-holders in the key string
     */
    public void error(DiagnosticPosition pos, String key, Object ... args) {
        log.error(pos,key,args);
    }
    
    /**
     * Creates an error message for which the source is a range of characters,
     * from begin up to and not including end; the identified line is that of
     * the begin position.
     */
    public void error(int begin, int end, String key, Object... args) {
        log.error(new JmlTokenizer.DiagnosticPositionSE(begin, end - 1), key,
                args); // TODO - not unicode friendly
    }

    /** Writes a warning message to the log, using the given DiagnosticPosition
     * (typically gotten from tree.pos()), a key (as in the file org.jmlspecs.openjml.messages.resources)
     * and arguments for that key
     * @param pos the DiagnosticPosition used to identify the relevant location in the source file
     * @param key the resource key holding the error message
     * @param args (non-null) arguments for the key - there must be at least as many arguments as there are place-holders in the key string
     */
    public void warning(DiagnosticPosition pos, String key, Object ... args) {
        log.warning(pos,key,args);
    }
    
    /**
     * Creates a warning message for which the source is a range of characters,
     * from begin up to and not including end; the identified line is that of
     * the begin position.
     */
    public void warning(int begin, int end, String key, Object... args) {
        log.warning(new JmlTokenizer.DiagnosticPositionSE(begin, end - 1), key,
                args); // TODO - not unicode friendly
    }

    /** Writes an informational message to the log's noticeWriter (as with
     * println).  To be used for informational or debugging information.
     * @param msg the String to write
     */
    public void info(@NonNull String msg) {
        log.getWriter(WriterKind.NOTICE).println(msg);
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
    abstract public JCTree parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser);
    
    protected void init(JmlParser parser) {
        Context c = this.context = parser.context;
        this.names = Names.instance(c);
        this.syms = Symtab.instance(c);
        this.utils = Utils.instance(c);
        this.log = Log.instance(c);
        this.parser = parser;
        this.scanner = parser.getScanner();
        this.jmlF = parser.maker();
        this.scanner.setJmlKeyword(false);
    }
    
    protected void wrapup(JCTree statement, IJmlClauseKind clauseType, boolean parseSemicolon) {
        parser.toP(statement);
        if (statement instanceof JmlSource) {
            ((JmlSource)statement).setSource(Log.instance(context).currentSourceFile());
        }
        //ste.line = log.currentSource().getLineNumber(pos);
        scanner.setJmlKeyword(true);
        if (!parseSemicolon) {
            // If we do not need a semicolon yet (e.g. because we already
            // parsed it or because the statement does not end with one,
            // then the scanner has already scanned the next symbol,
            // with setJmlKeyword having been (potentially) false.
            // So we need to do the following conversion.
            if (parser.token().kind == IDENTIFIER && scanner.jml()) {
                JmlTokenKind tt = JmlTokenKind.allTokens.get(scanner.chars());
                if (tt != null) {
                    scanner.setToken(new JmlToken(tt, null, parser.pos(), parser.endPos()));
                }
            }
        } else if (parser.token().ikind == ENDJMLCOMMENT) {
            // FIXME - why -2 here
            log.warning(parser.pos()-2, "jml.missing.semi", clauseType.name());
        } else if (parser.token().kind != SEMI) {
            error(parser.pos(), parser.endPos(), "jml.bad.construct", clauseType.name() + " statement");
            parser.skipThroughSemi();
        } else {
            parser.nextToken(); // advance to the token after the semi
        }

    }
    
    // TODO: document
    abstract public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env);
    

}
