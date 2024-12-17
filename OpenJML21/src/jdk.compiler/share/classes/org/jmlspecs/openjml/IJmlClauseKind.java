package org.jmlspecs.openjml;

import static com.sun.tools.javac.parser.Tokens.TokenKind.COMMA;
import static com.sun.tools.javac.parser.Tokens.TokenKind.DOT;
import static com.sun.tools.javac.parser.Tokens.TokenKind.IDENTIFIER;
import static com.sun.tools.javac.parser.Tokens.TokenKind.LPAREN;
import static com.sun.tools.javac.parser.Tokens.TokenKind.NEW;
import static com.sun.tools.javac.parser.Tokens.TokenKind.RPAREN;
import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;
import static com.sun.tools.javac.parser.Tokens.TokenKind.STAR;
import static com.sun.tools.javac.parser.Tokens.TokenKind.SUPER;
import static com.sun.tools.javac.parser.Tokens.TokenKind.THIS;

import com.sun.tools.javac.parser.*;
import java.lang.reflect.Constructor;
import java.util.function.Function;

import org.jmlspecs.openjml.Extensions;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlMethodSig;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;

import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlMethodSig;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.JmlTree.JmlSource;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;

import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Kinds.KindSelector;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.Attr;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlToken;
import com.sun.tools.javac.parser.JmlTokenizer;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.Log.WriterKind;

import javax.tools.JavaFileObject;


/** Objects of this type represents kinds of JML clauses and statements, for example,
 *  requires clauses or the \old expression. Instances represent kinds of clauses,
 *  not instances of clauses. These objects also contain behavior of the clause kinds,
 *  namely how to parse and typecheck instances of these clauses. There should be just
 *  a singleton object for each kind of clause. Clause kinds include standalone
 *  keywords, such as normal-behavior. 
 *  Instances of clauses are usually instances of derived types of JmlTree.
 * @author davidcok
 *
 */
public abstract class IJmlClauseKind {

    public IJmlClauseKind(String keyword) {
        this.keyword = keyword;
        Extensions.allKinds.put(keyword, this);
    }
    
    // These fields and methods give behavior of JML clauses of the given kind.

    public String keyword = null;

    public String keyword() { return keyword; }
    
    public String toString() { return keyword(); }
    
    /** If true, is a method or type spec clause kind within which \old without a label can be used (e.g. ensures)
    */
    public boolean oldNoLabelAllowed() { return false; }
    
    /** If true, is a kind of clause in which \pre and \old with a label can be used (e.g. assert)
     */
    public boolean preOrOldWithLabelAllowed() { return false; }
    
    public boolean preAllowed() { return false; }

    /** If true, is a method clause kind within which these tokens may appear:
     *  \not_assigned \only_assigned \only_captured \only_accessible \not_modified */
    public boolean postClauseAllowed() { return false; }
    
    /** If true, is a method clause kind in which the \result token may appear 
     * (and \not_assigned \only_assigned \only_captured \only_accessible \not_modified) */
    public boolean resultExpressionAllowed() { return false; }

    /** If true, is a method clause kind in which the \exception token may appear 
     */
    public boolean exceptionExpressionAllowed() { return false; }

    /** If true, is a method clause kind in which the \fresh token may appear 
     */
    public boolean freshExpressionAllowed() { return false; }
    
    // The following fields are initialized on demand when parsing or typechecking
    // They are not necessarily available when an instanceof IJmlClauseKind is created
    
    /** The compilation context */
    private /*@ non_null */ Context context;

    /** The parser in use, set when parsing is requested; note that there is a new parser created for each file parsed */
    protected /*@ non_null */ JmlParser parser;
    
//    /** The scanner in use, set when parsing is requested; note that there is a new parser created for each file parsed */
//    protected /*@ non_null */ JmlScanner scanner;
    
//    /** The symbol table, set when the context is set */
//    protected Symtab syms;
    
    /** Set when the context is set */
    protected Log log;
    
    /** Set when the context is set */
    protected JCDiagnostic.Factory diagFactory;
    
    /** Set when the context is set */
    protected Utils utils;
    
    public com.sun.tools.javac.util.JCDiagnostic.Error errorKey(String key, Object ... args) {
    	return diagFactory.errorKey(key,args);
    }
    
    public com.sun.tools.javac.util.JCDiagnostic.Warning warningKey(String key, Object ... args) {
    	return diagFactory.warningKey(key,args);
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
        utils.error(pos, key, args);
    }
    
    public void error(JavaFileObject sourcefile, DiagnosticPosition pos, String key, Object ... args) {
        utils.error(sourcefile, pos, key, args);
    }
    
    /**
     * Creates an error message for which the source is a range of characters,
     * from begin up to and not including end; the identified line is that of
     * the begin position.
     */
    public void error(int begin, int end, String key, Object... args) {
        utils.error(begin, end, key, args);
    }

    /** Writes a warning message to the log, using the given DiagnosticPosition
     * (typically gotten from tree.pos()), a key (as in the file org.jmlspecs.openjml.messages.resources)
     * and arguments for that key
     * @param pos the DiagnosticPosition used to identify the relevant location in the source file
     * @param key the resource key holding the error message
     * @param args (non-null) arguments for the key - there must be at least as many arguments as there are place-holders in the key string
     */
    public void warning(DiagnosticPosition pos, String key, Object ... args) {
        utils.warning(pos, key, args);
    }
    
    /**
     * Creates a warning message for which the source is a range of characters,
     * from begin up to and not including end; the identified line is that of
     * the begin position.
     */
    public void warning(int begin, int end, String key, Object... args) {
        utils.warning(begin, end, key, args);
    }

    /** Writes an informational message to the log's noticeWriter (as with
     * println).  To be used for informational or debugging information.
     * @param msg the String to write
     */
    public void info(/*@non_null*/ String msg) {
        utils.noPrefix(msg);
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
     * the scanner (JmlParser.getScanner()) and return a JCTree parse
     * tree.  When called, the current scanner token is the JmlToken itself;
     * this method is responsible to scan the end of the expression (e.g. the
     * terminating parenthesis) and no more.  If an error occurs because of
     * badly formed input, the method is required to return null and to 
     * recover as best it can.  [ FIXME - return JCErroneous?]
     */
    abstract public JCTree parse(JCModifiers mods, String keyword, IJmlClauseKind clauseKind, JmlParser parser);

    public JCExpression assertionConversion(JmlAssertionAdder aa, JCExpression expr) { return null; }

    protected void init(JmlParser parser) {
        Context c = context = parser.context ;
        //this.syms = Symtab.instance(c);
        this.log = Log.instance(c);
        this.parser = parser;
        //this.scanner = parser.getScanner();
        this.utils = Utils.instance(c);
        this.diagFactory = JCDiagnostic.Factory.instance(c);
    }

    protected void wrapup(JCTree statement, IJmlClauseKind clauseType, boolean parseSemicolon) {
        wrapup(statement,clauseType,parseSemicolon, true);
    }
    
    protected void wrapup(JCTree statement, IJmlClauseKind clauseType, boolean parseSemicolon, boolean requireSemicolon) {
        if (statement instanceof JmlSource) {
            ((JmlSource)statement).setSource(log.currentSourceFile());
        }
        //ste.line = log.currentSource().getLineNumber(pos);
        if (!parseSemicolon) {
            // If we do not need a semicolon yet (e.g. because we already
            // parsed it or because the statement does not end with one,
            // then the scanner has already scanned the next symbol --
        	// either the end-of-jml or the start of the next JML clause/statement
        } else if (parser.isEndJml()) {
            // FIXME - was -2 here, why?
            if (requireSemicolon) warning(parser.pos(), parser.endPos(), "jml.missing.semi", clauseType.keyword());
        } else if (parser.token().kind != SEMI && parser.token().kind == TokenKind.IDENTIFIER && Extensions.findKeyword(parser.token().name()) != null) {
        	int p = parser.pos();
        	var t = parser.getScanner().prevToken();
        	p = t.endPos;
            error(p, p, "jml.bad.construct.missing.semi", clauseType.keyword() + " statement");
        } else if (parser.token().kind != SEMI) {
            error(parser.pos(), parser.endPos(), "jml.bad.construct", clauseType.keyword() + " statement");
            parser.skipThroughSemi();
        } else {
            parser.nextToken(); // advance to the token after the semi
        }
        parser.toP(statement);
        parser.acceptEndJML(); // accepts any end-jml-comment tokens, if present
    }
    
    /** Derived classes implement this method to do any typechecking of the tree, which should have
     * a dynamic type corresponding to the kind of the tree; returns the type of the result, or Type.noType.
     */
    abstract public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> env);
    
    /** returns true if strict adherence to JML is required (language option is jml) */
    public boolean requireStrictJML() {
        return JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG));
    }
    
    /** Issue warning if strictness is required -- e.g. call this if an extension is being used */
    public void strictCheck(JmlParser parser, JCTree e) {
        if (requireStrictJML()) {
            utils.warning(e,"jml.not.strict",keyword());
        }
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////////////////// 
    
    /** Base class for kinds of clauses in method specifications, both 
        clauses with content (MethodSpecClauseKind) and simple keywords (MethodKeywordClause)
      */
    public static abstract class MethodClauseKind extends IJmlClauseKind {
        public MethodClauseKind(String keyword) { super(keyword); }
        public boolean preAllowed() { return !isPreconditionClause(); }
        public boolean isPreconditionClause() { return false; }
        @Override
        public void init(JmlParser parser) {
            super.init(parser);
        }
    }
    
    /** Base class for kinds of clauses in method specifications (e.g. requires) */
    public static abstract class MethodSpecClauseKind extends MethodClauseKind {
        public MethodSpecClauseKind(String keyword) { super(keyword); }
    }
    
    public static interface IStatementKind {}
    
    /** Base class for kinds of clauses that are statements (e.g. assert) */
    public static abstract class Statement extends IJmlClauseKind implements IStatementKind {
        public Statement(String keyword) { super(keyword); }
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
        public boolean preAllowed() { return true; }
        @Override
        public void init(JmlParser parser) {
            super.init(parser);
        }
    }
    
    /** The kind of line annotations */
    public static abstract class LineAnnotationKind extends IJmlClauseKind {
        public LineAnnotationKind(String keyword) { super(keyword); }

        @Override
        public JCTree parse(JCModifiers mods, String keyword,
                IJmlClauseKind clauseType, JmlParser parser) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            throw new UnsupportedOperationException();
        }

        abstract public void scan(int keywordPos, String keyword, IJmlClauseKind clauseKind, JmlScanner scanner);

        /** A class that is a record of an instance of a line annotation.
         * A line annotation is captured by the scanner, not the parser,
         * and so is a bit of a different animal. */
        public static abstract class LineAnnotation {
        	protected LineAnnotation() {}
            public int line;
            public int keywordPos;
            public IJmlClauseKind clauseKind;
            public IJmlClauseKind clauseKind() { return clauseKind; }
            abstract public java.util.List<JCExpression> exprs();
            abstract public Type typecheck(JmlAttr attr, Env<AttrContext> env);
        }
    }
    
    /** The base class for the kind of type clauses (e.g. invariant) */
    public static abstract class TypeClause extends IJmlClauseKind {
        public TypeClause(String keyword) { super(keyword); }
        @Override
        public void init(JmlParser parser) {
            super.init(parser);
        }
    }

    /** A base class for JML extensions that do not fit into other categories */
    public static abstract class Misc extends IJmlClauseKind {
        public Misc(String keyword) { super(keyword); }
        abstract public JCTree parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser);
    }
    
    /** A base class for JML extensions that are kinds of expressions */
    public static abstract class ExpressionKind extends IJmlClauseKind {
        public ExpressionKind(String keyword) { super(keyword); }
        abstract public JCExpression parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser);
        public JCExpression assertionConversion(JmlAssertionAdder aa, JCExpression expr) { return null; }
    }
    
    /** This class is used for JML expressions that have a standard function-call
     * form: a keyword followed by a parenthesized comma-separated list of expressions
     */
    public static abstract class FunctionLikeExpressionKind extends ExpressionKind {
        public FunctionLikeExpressionKind(String keyword) { super(keyword); }
        
        /** This implementation of parse() parses a keyword + 
         * parenthesized comma-separated list of expressions,
         * producing a JmlMethodInvocation node. Derived classes
         * must implement checkParse(), to do any additional checking,
         * such as that the number of arguments is correct.
         */
        public JCExpression parse(JCModifiers mods, String name, IJmlClauseKind kind, JmlParser parser) {
            init(parser);
            int startx = parser.pos();
            var jt = parser.jmlTokenClauseKind();
            parser.nextToken();
            if (parser.token().kind != TokenKind.LPAREN) {
                return parser.syntaxError(startx, null, "jml.args.required", jt.keyword());
            } else {
                int preferredPos = parser.pos(); // points at the left-paren
                List<JCExpression> args = parser.arguments();
                JmlMethodInvocation t = toP(parser.maker().at(preferredPos).JmlMethodInvocation(this, args));
                t.startpos = startx;
                t.kind = jt;
                checkParse(parser,t);
                return parser.primaryTrailers(t, null); // FIXME - was primarySuffix
            }
        }
        
        abstract public void checkParse(JmlParser parser, JmlMethodInvocation e);

        /** A helper method that can be called in a derived class's implementation
         * of checkParse() -- this method applies the given function to the number of
         * arguments and emits an error message if the function returns false.
         */
        public void checkNumberArgs(JmlParser parser, JmlMethodInvocation e, Function<Integer,Boolean> f, String key, Object ... messageArgs) {
            if (!f.apply(e.args.size())) {
                error(e.pos, parser.getEndPos(e), key, messageArgs);
            }
        }

        /** A helper method that can be called in a derived class's implementation
         * of checkParse() -- for the case of exactly one argument.
         */
        public void checkOneArg(JmlParser parser, JmlMethodInvocation e) {
            checkNumberArgs(parser, e, (n)->(n==1), "jml.one.arg", e.kind.keyword());
        }
        
        public boolean typecheckHelper(JmlAttr attr, List<JCExpression> args, Env<AttrContext> localEnv) {
            boolean ok = true;
            for (JCExpression e: args) {
                //System.out.println("TCH " + e + " " + e.getClass());
                Attr.ResultInfo resultInfo = attr.new ResultInfo(KindSelector.VAL, Type.noType );
                Type t = attr.attribExpr(e, localEnv);
                t = attr.check(e, t, KindSelector.VAL, resultInfo );
                if (t.isErroneous()) ok = false;
                if (e.type == null) Utils.dumpStack("Type not set for " + e + " " + args);
              //  System.out.println("  ATTRIB " + t + " " + e.type);
            }
            return ok;
//            ListBuffer<Type> argTypes = new ListBuffer<>();
//            for (JCExpression e: args) {
//                Attr.ResultInfo resultInfo = attr.new ResultInfo(KindSelector.VAL, Type.noType );
//                Type t = attr.attribExpr(e, localEnv);
//                t = attr.check(e, t, KindSelector.VAL, resultInfo );
//                argTypes.add(t);
//            }
        }
       
    }
    
    /** This class is used for JML items that are just a keyword but
     * are not expressions or other categories themselves.
     */
    public static abstract class SingletonKind extends IJmlClauseKind.Misc {
        
        public SingletonKind(String name) { super(name); }
        
        @Override
        public JCTree parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            IJmlClauseKind jt = parser.jmlTokenClauseKind();
            int p = parser.pos();
            String stringRep = parser.getScanner().chars();
            parser.nextToken();
            if (parser.token().kind == TokenKind.LPAREN) {
                return parser.syntaxError(p, null, "jml.no.args.allowed", jt.keyword());
            } else {
                JmlSingleton e = toP(parser.maker().at(p).JmlSingleton(jt));
                e.kind = this;
                checkParse(parser,e,stringRep);
                return e;
            }
        }
        
        /** A method meant to be overridden in derived classes to do any
         * additional checking -- typically none for a singleton.
         */
        public void checkParse(JmlParser parser, JmlSingleton e, String rep) {}

    }
    /** This class is used for kinds of JML expressions that are just a keyword with
     * no parenthesized argument list
     */
    public static abstract class SingletonExpressionKind extends ExpressionKind {
        
        public SingletonExpressionKind(String name) { super(name); }
        
        @Override
        public JCExpression parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            IJmlClauseKind jt = parser.jmlTokenClauseKind();
            int p = parser.pos();
            String stringRep = keyword;
            parser.nextToken();
            if (parser.token().kind == TokenKind.LPAREN) {
                return parser.syntaxError(p, null, "jml.no.args.allowed", jt.keyword());
            } else {
                JmlSingleton e = toP(parser.maker().at(p).JmlSingleton(jt));
                e.kind = this;
                checkParse(parser,e,stringRep);
                return e;
            }
        }
        
        /** A method meant to be overridden in derived classes to do any
         * additional checking -- typically none for a singleton.
         */
        public void checkParse(JmlParser parser, JmlSingleton e, String rep) {}

    }
    
    @SuppressWarnings("unchecked")
    public static class ModifierKind extends IJmlClauseKind {
        public String fullAnnotation;
        public com.sun.tools.javac.code.Symbol.ClassSymbol annotationSym = null;
        public boolean strict;
        public Class<? extends java.lang.annotation.Annotation> clazz;
        
        public boolean isTypeAnnotation() {
            return false;
        }
        
        public boolean isNormalModifier() {
            return !isTypeAnnotation();
        }
        
        public ModifierKind(String keyword, boolean strict) {
            super(keyword);
            this.strict = strict;
            String annotation = keyword;
            while (true) {
                int i = annotation.indexOf("_");
                if (i < 0 || i >= annotation.length()-1) break;
                char c = annotation.charAt(i+1);
                char uc = Character.toUpperCase(c);
                annotation = annotation.substring(0,i) + String.valueOf(uc) + annotation.substring(i+2);
            }
            char c = annotation.charAt(0);
            this.fullAnnotation = "org.jmlspecs.annotation." + Character.toUpperCase(c) + annotation.substring(1);
            try {
            	this.clazz = (Class<? extends java.lang.annotation.Annotation>)Class.forName(this.fullAnnotation);
            } catch (Exception e) {
            	Main.uninitializedLog().error("jml.message","Failed to find annotation class for " + this.fullAnnotation);
            	this.clazz = null;
            }
        }
        
        public ModifierKind(String keyword, boolean strict, String annotation) { 
            super(keyword); 
            this.strict = strict;
            this.fullAnnotation = annotation.contains(".") ? annotation : ("org.jmlspecs.annotation." + annotation);
            try {
            	this.clazz = (Class<? extends java.lang.annotation.Annotation>)Class.forName(this.fullAnnotation); // unchecked cast
            } catch (Exception e) {
            	Main.uninitializedLog().error("jml.message","Failed to find annotation class for " + this.fullAnnotation);
            	this.clazz = null;
            }
        }

        @Override
        public JCTree parse(JCModifiers mods, String keyword,
                IJmlClauseKind clauseKind, JmlParser parser) {
            return null;
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> env) {
            return null;
        }
    }

    public static class TypeAnnotationKind extends ModifierKind {
    	public TypeAnnotationKind(String keyword, boolean strict) {
    		super(keyword,strict);
    	}
        public boolean isTypeAnnotation() {
            return true;
        }
    }

    
    public static abstract class ClassLikeKind extends IJmlClauseKind {
        public ClassLikeKind(String keyword) { super(keyword); }
    }
    
    /**
     * Parses a list of method-name; returns a possibly empty list; does not
     * parse the terminating semicolon
     */
    public List<JmlMethodSig> parseMethodNameList() {
        ListBuffer<JmlMethodSig> sigs = new ListBuffer<JmlMethodSig>();
        while (true) {
            JmlMethodSig m = parseMethodName();
            if (m == null) {
                parser.skipToCommaOrParenOrSemi();
            } else {
                sigs.append(m);
            }
            toP(m);
            if (parser.token().kind != COMMA) break;
            parser.nextToken();
        }
        return sigs.toList();
    }

    /** Parses a method-name */
    public JmlMethodSig parseMethodName() {
        int initpos = parser.pos();
        int p = initpos;
        Name n = null;
        JCTree newType = null;
        TokenKind tk = parser.token().kind;
        if (tk == NEW) {
            newType = parser.parseType();
            // FIXME - check that it is a reference type
        } else if (tk == IDENTIFIER) {
            n = parser.ident();
        } else if (tk == THIS) {
            n = parser.names._this;
            parser.nextToken();
        } else if (tk == SUPER) {
            n = parser.names._super;
            parser.nextToken();
        } else {
            utils.error(parser.pos(), parser.endPos(), "jml.bad.construct",
                    "constraint method");
            return null;
        }
        JCExpression id = null;
        if (newType == null) {
            id = parser.jmlF.at(p).Ident(n);
            boolean first = true;
            tk = parser.token().kind;
            while (tk == DOT) {
                parser.nextToken();
                tk = parser.token().kind;
                p = parser.pos();
                if (tk == IDENTIFIER) {
                    n = parser.ident();
                } else if (tk == THIS) {
                    n = parser.names._this;
                    parser.nextToken();
                } else if (tk == STAR) {
                    // * may only be the only thing after any dot, if it is
                    // present
                    if (!first) {
                        utils.error(parser.pos(), parser.endPos(), "jml.expected",
                                "identifier or this, since a * may only be used after the first dot");
                    }
                    n = parser.names.asterisk;
                    parser.nextToken();
                    if (parser.token().kind == DOT) {
                        utils.error(parser.pos(), parser.endPos(), "jml.expected",
                                "no dot, since a dot may not be used after a *");
                    }
                } else {
                    utils.error(parser.pos(), parser.endPos(), "jml.expected",
                            "identifier or this");
                    break;
                }
                id = parser.jmlF.at(p).Select(id, n);
                first = false;
                if (n == parser.names.asterisk) {
                    return parser.jmlF.at(initpos).JmlConstraintMethodSig(id, null);
                }
            }
        }
        ListBuffer<JCExpression> args = null;
        if (parser.token().kind == LPAREN) {
            args = new ListBuffer<JCExpression>();
            parser.nextToken();
            if (parser.token().kind != RPAREN) {
                JCExpression arg = parser.parseType();
                args.append(arg);
                while (parser.token().kind == COMMA) {
                    parser.nextToken();
                    arg = parser.parseType();
                    args.append(arg);
                }
                if (parser.token().kind != RPAREN) {
                    utils.error(parser.pos(), parser.endPos(), "jml.expected",
                            "comma or right parenthesis");
                } else {
                    parser.nextToken();
                }
            } else {
                parser.nextToken(); // consume the RPAREN
            }
        }
        return parser.jmlF.at(initpos).JmlConstraintMethodSig(id,
                args == null ? null : args.toList());
    }
}
