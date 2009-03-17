package com.sun.tools.javac.parser;

import static com.sun.tools.javac.parser.Token.*;
import static com.sun.tools.javac.util.ListBuffer.lb;
import static org.jmlspecs.openjml.JmlToken.*;

import java.io.PrintStream;
import java.util.EnumSet;
import java.util.Set;

import org.jmlspecs.openjml.JmlInternalError;
import org.jmlspecs.openjml.JmlOptionName;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.Label;

import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCErroneous;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Position;

/** This class extends the javac parser to parse JML constructs as well. */
public class JmlParser extends EndPosParser {

    /** The context this parser was created for */
    //@ non_null
    protected Context context;
    
    /** The scanner associated with the parser */
    //@ non_null
    protected JmlScanner S;
    
    /** The node factory to use */
    //@ non_null
    protected JmlTree.Maker jmlF;
    
    /** The table of identifiers */
    //@ non_null
    protected Name.Table names;
    
    /** A constructor for a new parser, but you should get new instances of the
     * parser from the parser factory, that is, by JmlParser.instance(context).newParser(...).
     * @param fac the node factory to use to create parse trees
     * @param S  the scanner to produce tokens for the parser to ask for
     * @param keepDocComments whether to keep javadoc comments
     */
    protected JmlParser(Parser.Factory fac, Lexer S, boolean keepDocComments) {
        super(fac, S, keepDocComments);
        if (!(S instanceof JmlScanner)) {
            log.error("jml.internal","S expected to be a JmlScanner in JmlParser");
            throw new JmlInternalError();
        }
        if (!(F instanceof JmlTree.Maker)) {
            log.error("jml.internal","F expected to be a JmlTree.Maker in JmlParser");
            throw new JmlInternalError();
        }
        this.S = (JmlScanner)S; 
        this.jmlF = (JmlTree.Maker)F; 
    }

    /** This class extends the Java Parser factory class to be able to produce
     * JML ast nodes as well.  There is just one factory per context, but there
     * may be multiple instances of parsers.
     * @author David Cok
     */
    public static class JmlFactory extends Parser.Factory {
        
        /** The context key for the parser factory. */
        protected static final Context.Key<JmlFactory> jmlparserFactoryKey =
            new Context.Key<JmlFactory>();

        
        /** The constructor for the factory.
         * @param context the Context for which this is the factory
         */
        protected JmlFactory(Context context) {
            super(context);
            this.context = context;
        }
        
        /** The context in which this factory works */
        protected Context context;
        
        /** A static call that registers an instance of JmlFactory as the
         * factory to use for this context.
         * @param context the context in which to register the factory
         */
        public static void preRegister(final Context context) {
            context.put(parserFactoryKey, new Context.Factory<Parser.Factory>() {
                public Parser.Factory make() {
                    return new JmlParser.JmlFactory(context);
                }
            });
        }
        
        /** Creates a new parser from the factory, given a lexer and flags as
         * to whether to keep javadoc comments and whether to generate end
         * position information.
         */
        //@ requires S != null;
        //@ ensures this.S != null && this.context != null;
        //@ ensures this.names != null && this.jmlF != null;
        @Override
        public Parser newParser(Lexer S, boolean keepDocComments, boolean genEndPos) {
            JmlParser p = new JmlParser(this,S,keepDocComments || true);  // FIXME - really just want the doc comments when doing jmldoc
            p.names = Name.Table.instance(context);
            p.context = context;
            return p;
        }
        
    }
    
    /** Parses a compilation unit using tokens from the scanner - generally the
     * entry point used to parse a Java/JML file.
     */
    @Override
    public JCTree.JCCompilationUnit compilationUnit() {
        JCTree.JCCompilationUnit u =  super.compilationUnit();
        if (u instanceof JmlCompilationUnit) {
            JmlCompilationUnit jmlcu = (JmlCompilationUnit)u;
            jmlcu.refinesClause = refinesClause;
            refinesClause = null;
            // sort the sheep from the goats
            ListBuffer<JCTree> list = new ListBuffer<JCTree>();
            for (JCTree t: u.defs) {
                if (t instanceof JmlClassDecl &&
                        Utils.isJML(((JmlClassDecl)t).mods)) {
                    jmlcu.parsedTopLevelModelTypes.add((JmlClassDecl)t);
                } else if (t != null) { // screens out the null from parsing refines
                    list.append(t);
                }
            }
            jmlcu.defs = list.toList();
        } else {
            log.error("jml.internal",
                    "JmlParser.compilationUnit expects to receive objects of type JmlCompilationUnit, but it found a " 
                    + u.getClass() + " instead, for source " + u.getSourceFile().toUri().getPath());
        }
        return u;
    }
    
    /** Used to make sure a refines declaration is before any imports */
    protected boolean alreadyHaveImports = false;

    /** The Java AST does not know about refines clauses, so we hang onto it here
     * until the JmlCompilationUnit is formed. */
    //@ nullable
    public JmlRefines refinesClause = null;
    
    /** Overrides the super class importDeclaration in order to recognize
     * refines statements and model import statements.
     * @return null or a JCImport node
     */
    //@ ensures \result == null || \result instanceof JCTree.JCImport;
    @Override //@ nullable
    protected JCTree importDeclaration() {
        if (S.jmlToken() == JmlToken.REFINES) {
            int p = S.pos();
            String filename = null;
            if (alreadyHaveImports) {
                log.error(S.pos(),"jml.refines.before.imports");
            }
            S.nextToken(); // refines token
            if (S.token() != Token.STRINGLITERAL) {
                log.error(S.pos(),"jml.refines.missing.string");
                skipThroughSemi();
            } else {
                filename = S.stringVal();
                S.nextToken();
                if (S.token() == Token.SEMI) S.nextToken();
                else {
                    log.error(S.pos(),"jml.refines.missing.semicolon");
                    skipThroughSemi();
                }
                if (Utils.jmldebug) System.out.println("REFINES " + filename);
            }
            if (filename != null) {
                if (refinesClause != null) {
                    log.error(p,"jml.two.refines.clauses");
                } else {
                    refinesClause = toP(jmlF.at(p).JmlRefines(filename));
                }
            }
            if (S.jmlToken() == ENDJMLCOMMENT) S.nextToken();
            return null; // This puts a null in the compilation unit's def list
        } else {
            int p = S.pos();
            boolean modelImport = S.jmlToken() == JmlToken.MODEL;
            JCTree t = super.importDeclaration();
            ((JmlImport)t).isModel = modelImport;
            t.setPos(p);
            alreadyHaveImports = true;
            if (S.jmlToken() == JmlToken.ENDJMLCOMMENT) {
                S.nextToken();
            }
            return t;
        }
    }
    
    @Override
    protected JCStatement classOrInterfaceOrEnumDeclaration(JCModifiers mods, String dc) {
        boolean prevInJmlDeclaration = inJmlDeclaration;
        if (S.jml) {
            if (mods == null) {
                mods = jmlF.at(Position.NOPOS).Modifiers(0);
                storeEnd(mods,Position.NOPOS);
            }
            if (!inJmlDeclaration) Utils.setJML(mods);
            inJmlDeclaration = true;
        }
        JCStatement s = super.classOrInterfaceOrEnumDeclaration(mods, dc);
        inJmlDeclaration = prevInJmlDeclaration;
        return s;
    }

    @Override
    public List<JCStatement> blockStatements() {
        ListBuffer<JCStatement> list = new ListBuffer<JCStatement>();
        int pos = -1;
        JCModifiers mods = null;
        while (S.token() != Token.RBRACE && S.token() != EOF) {
            if (S._pos == pos) break;
            pos = S._pos;
            if (S.token() == CUSTOM) {
                mods = modifiersOpt();
            }
            if (S.token() == CUSTOM) {
                JCStatement st = (statement());
                list.append(st);
            } else {
                pushBackModifiers = mods;
                mods = null;
                if (S.jml) {
                    boolean prevInJmlDeclaration = inJmlDeclaration;
                    inJmlDeclaration = true;
                    List<JCTree.JCStatement> dlist = super.blockStatements();
                    inJmlDeclaration = prevInJmlDeclaration;
                    if (inJmlDeclaration) {
                        // In this case we are in the body of a model method.
                        // Within the body we don't mark any local variables
                        // or classes as ghost or model (with setJML).
                        list.appendList(dlist);
                    } else {
                        for (JCTree.JCStatement t: dlist) {
                            if (t instanceof JmlVariableDecl) {
                                JmlVariableDecl d = (JmlVariableDecl)t;
                                Utils.setJML(d.mods);
                            } else if (t instanceof JmlClassDecl) {
                                JmlClassDecl d = (JmlClassDecl)t;
                                Utils.setJML(d.mods);
                            } else if (t instanceof JCTree.JCSkip) {
                                // An empty statement is not really allowed within
                                // a JML annotation, but it is common to find one 
                                // after a local class declaration, so we won't
                                // complain.
                            } else {
                                log.error(t.pos,"jml.expected.decl.or.jml");                                
                            }
                            list.append(t);
                        }
                    }
                } else {
                    list.appendList(super.blockStatements());
                }
            }
        }
        // Run through the list to combine any loop statements
        ListBuffer<JCStatement> newlist = new ListBuffer<JCStatement>();
        ListBuffer<JmlStatementLoop> loops = new ListBuffer<JmlStatementLoop>();
        for (JCStatement s : list) {
            if (s instanceof JmlStatementLoop) {
                loops.append((JmlStatementLoop)s);
                continue;
            } else if (s instanceof JmlForLoop) {
                ((JmlForLoop)s).loopSpecs = loops.toList();
                loops = new ListBuffer<JmlStatementLoop>();
            } else if (s instanceof JmlEnhancedForLoop) {
                ((JmlEnhancedForLoop)s).loopSpecs = loops.toList();
                loops = new ListBuffer<JmlStatementLoop>();
            } else if (s instanceof JmlWhileLoop) {
                ((JmlWhileLoop)s).loopSpecs = loops.toList();
                loops = new ListBuffer<JmlStatementLoop>();
            } else if (s instanceof JmlDoWhileLoop) {
                ((JmlDoWhileLoop)s).loopSpecs = loops.toList();
                loops = new ListBuffer<JmlStatementLoop>();
            } else {
                if (loops.size() != 0) {
                    log.error(loops.first().pos(),"jml.loop.spec.misplaced");
                    loops = new ListBuffer<JmlStatementLoop>();
                }
            }
            newlist.append(s);
        }
        if (loops.size() != 0) {
            log.error(loops.first().pos(),"jml.loop.spec.misplaced");
        }
        return newlist.toList();
    }
    
    /** Set to true when parsing statements within a model program */
    protected boolean inModelProgram = false;
    
    /** Overridden to parse JML statements */
    public JCStatement statement() {
        JCStatement st;
        String reason = null;
        if (S.token() == Token.CUSTOM) { // Note that declarations may start with a non-JML keyword, even if they are ghost
            if (S.jmlToken() == JmlToken.STARTJMLCOMMENT) {
                S.nextToken();
            }
            if (S.jmlToken() != JmlToken.ENDJMLCOMMENT) {
                int pos = S.pos();
                JmlToken jtoken = S.jmlToken();
                if (jtoken != null) reason = jtoken.internedName() + " statement";
                if (jtoken == JmlToken.ASSUME || jtoken == JmlToken.ASSERT) {
                    S.setJmlKeyword(false);
                    S.nextToken();
                    JCExpression t = null;
                    t = expression();
                    JmlTree.JmlStatementExpr ste = to(jmlF.at(pos).JmlExpressionStatement(jtoken,
                            jtoken == JmlToken.ASSUME ? Label.EXPLICIT_ASSUME : Label.EXPLICIT_ASSERT, t));
                    if (S.token() == Token.COLON) {
                        S.nextToken();
                        ste.optionalExpression = expression();
                    }
                    ste.source = log.currentSource();
                    ste.line = log.getLineNumber(pos);
                    st = ste;
                } else if (jtoken == HENCE_BY || jtoken == UNREACHABLE) {
                    S.setJmlKeyword(false);
                    S.nextToken();
                    JCExpression t = null;
                    if (jtoken != UNREACHABLE) t = expression();
                    JmlTree.JmlStatementExpr ste = to(jmlF.at(pos).JmlExpressionStatement(jtoken,Label.UNREACHABLE,t));
                    ste.source = log.currentSource();
                    ste.line = log.getLineNumber(pos);
                    st = ste;
                } else if (jtoken == DECREASES || jtoken == LOOP_INVARIANT) {
                    S.setJmlKeyword(false);
                    S.nextToken();
                    JCExpression t = expression();
                    JmlStatementLoop ste = to(jmlF.at(pos).JmlStatementLoop(jtoken,t));
                    ste.source = log.currentSource();
                    ste.line = log.getLineNumber(pos);
                    st = ste;
                } else if (jtoken == JmlToken.SET || jtoken == JmlToken.DEBUG) {
                    S.setJmlKeyword(false);
                    S.nextToken();
                    JCStatement t = super.statement();
                    st = toP(jmlF.at(pos).JmlStatement(jtoken,t));
                    S.setJmlKeyword(true); // This comes a token too late.
                        // So we need to do the following conversion.
                    if (S.token() == Token.IDENTIFIER && S.jml) {
                        JmlToken tt = JmlToken.allTokens.get(S.name().toString());
                        if (tt != null) {
                            S.token(CUSTOM);
                            S.jmlToken = tt;
                        }
                    }
                    if (S.jmlToken() == JmlToken.ENDJMLCOMMENT) S.nextToken();
                    return st;
                    
                    // FIXME - add in model-program specific statements
                    
                } else if (jtoken == JmlToken.REFINING) {// FIXME - implement
                    log.warning(S.pos(),"jml.unimplemented.construct","refining statement","JmlParser");
                    st = to(F.at(pos).Skip());
                    S.nextToken();
                } else {
                    log.error(S.pos(),"jml.unknown.statement",jtoken.internedName());
                    skipToSemi();
                    st = jmlF.at(S.pos()).Skip();
                }
            } else {
                S.nextToken(); // swallows the ENDJMLCOMMENT
                return super.statement();
            }
            S.setJmlKeyword(true);
            if (S.token() != Token.SEMI) {
                log.error(S.pos(),"jml.bad.construct",reason);
                skipThroughSemi();
            } else {
                S.nextToken();
            }
            if (S.jmlToken() == JmlToken.ENDJMLCOMMENT) S.nextToken();
            return st;
        }
        JCStatement stt = super.statement();
        return stt;
    }
    
    /** Prints an AST using TreePrinter
     * @param t the tree to print
     * @param out the PrintStream on which to write the output
     */
    void printTree(JCTree t, PrintStream out) {
        new TreePrinter(out,this).scan(t);
    }
    
    protected boolean inJmlDeclaration = false; // when true we are parsing declarations within a model method or class, 
                                    // so the individual declarations are not themselves model even though they are in JML
    
    @Override
    protected List<JCTree> classOrInterfaceBodyDeclaration(Name className, boolean isInterface) {

        if (S.jmlToken() == STARTJMLCOMMENT) S.nextToken();
       
        ListBuffer<JCTree> list = new ListBuffer<JCTree>();
        loop: while (true) {
            while (S.jmlToken() == ENDJMLCOMMENT) {
                S.nextToken(); // swallows the ENDJMLCOMMENT
                if (S.jmlToken() != STARTJMLCOMMENT) {
                    break loop;
                }
                S.nextToken(); // swallow the STARTJMLTOKEN
            }
            if (S.jml) S.setJmlKeyword(true);
            JCModifiers mods = modifiersOpt(); // Gets anything in that is in pushBackModifiers
            int pos = S.pos();
            JmlToken jt = S.jmlToken();
            if (jt == null || jt == BSTYPEUC || jt == BSREAL || jt == BSBIGINT) {
                pushBackModifiers = mods; // This is used to pass the modifiers into super.classOrInterfaceBodyDeclaration
                mods = null;
                boolean startsInJml = S.jml;
                if (startsInJml) {
                    boolean prevInJmlDeclaration = inJmlDeclaration;
                    inJmlDeclaration = true;
                    List<JCTree> t = super.classOrInterfaceBodyDeclaration(className,isInterface);
                    inJmlDeclaration = prevInJmlDeclaration;
                    if (!inJmlDeclaration) {
                        for (JCTree tr: t) { 
                            JCTree ttr = tr;
                            if (tr instanceof JmlClassDecl) {
                                JmlClassDecl d = (JmlClassDecl)tr;
                                Utils.setJML(d.mods);
                                d.sourcefile = log.currentSource();
                                ttr = toP(jmlF.at(pos).JmlTypeClauseDecl(d));
                            } else if (tr instanceof JmlMethodDecl) {
                                JmlMethodDecl d = (JmlMethodDecl)tr;
                                Utils.setJML(d.mods);
                                d.sourcefile = log.currentSource();
                                ttr = toP(jmlF.at(pos).JmlTypeClauseDecl(d));
                            } else if (tr instanceof JmlVariableDecl) {
                                JmlVariableDecl d = (JmlVariableDecl)tr;
                                Utils.setJML(d.mods);
                                d.sourcefile = log.currentSource();
                                ttr = toP(jmlF.at(pos).JmlTypeClauseDecl(d));
                            }
                            list.append(ttr);
                        }
                    } else {
                        list.appendList(t);
                    }
                } else {
                    // no longer in JML
                    List<JCTree> t = super.classOrInterfaceBodyDeclaration(className,isInterface);
                    list.appendList(t);
                }
                break;
            } else if (jt == INVARIANT || jt == INITIALLY || jt == AXIOM) {
                parseInvariantInitiallyAxiom(mods,list);
            } else if (jt == CONSTRAINT) {
                parseConstraint(mods,list);
            } else if (jt == REPRESENTS) {
                parseRepresents(mods,list);
            } else if (methodClauseTokens.contains(jt) || specCaseTokens.contains(jt)) {
                list.append(parseMethodSpecs(mods));
                // getMethodSpecs may have already parsed some modifiers.
                // They will be in pushBackModifiers
            } else if (jt == IN) {
                list.append(parseIn(pos,mods));                    
            } else if (jt == MAPS) {
                parseMaps(pos,mods,list);
            } else if (jt == READABLE || jt == WRITABLE) {
                parseReadableWritable(mods,jt,list);
            } else if (jt == MONITORS_FOR) {
                parseMonitorsFor(mods,list);
            } else if (jt == INITIALIZER || jt == STATIC_INITIALIZER) {
                list.append(to(jmlF.at(S.pos()).JmlTypeClauseInitializer(jt)));
                S.nextToken();
            } else {
                log.error(S.pos(),"jml.illegal.token.for.declaration",jt.internedName());
                skipThroughSemi();
                break;
            }
        }
        return list.toList();
    }
    
    public void parseMaps(int pos, JCModifiers mods, ListBuffer<JCTree> list) {
        if (!isNone(mods)) log.error(pos,"jml.no.mods.allowed",JmlToken.MAPS.internedName());
        S.setJmlKeyword(false);
        S.nextToken(); // skip over the maps token
        JCExpression e = parseMapsTarget();
        if (e.getTag() == JCTree.ERRONEOUS) return; // presumes already advanced to SEMI
        ListBuffer<JmlGroupName> glist;
        if (S.jmlToken() != JmlToken.BSINTO) {
            log.error(S.pos(),"log.expected","an \\into token here, or the maps target is ill-formed");
            glist = new ListBuffer<JmlGroupName>();
            S.setJmlKeyword(true);
            skipThroughSemi();
        } else {
            S.nextToken();
            glist = parseGroupNameList();
            S.setJmlKeyword(true);
            if (S.token() != Token.SEMI) {
                log.error(S.pos(),"jml.bad.construct","maps clause");
                skipThroughSemi();
            } else {
                S.nextToken();
            }
        }
        list.append( toP(jmlF.at(pos).JmlTypeClauseMaps(e,glist.toList())) );
    }
    
    public JCExpression parseMapsTarget() {
        int p = S.pos();
        if (S.token() != Token.IDENTIFIER) {
            log.error(S.pos(),"jml.expected","an identifier");
            skipThroughSemi();
            return toP(jmlF.at(p).Erroneous());
        }
        Name n = ident();
        JCExpression result = to(jmlF.at(p).Ident(n));
        if (S.token() == Token.LBRACKET) {
            result = parseArrayRangeExpr(result,false); 
        }
        if (S.token() == Token.DOT) {
            S.nextToken();
            if (S.token() == Token.STAR) {
                S.nextToken();
                n = null;
            } else if (S.token() == Token.IDENTIFIER) {
                n = ident();
            } else {
                log.error(S.pos(),"jml.ident.or.star.after.dot");
                skipThroughSemi();
                return toP(jmlF.at(p).Erroneous());
            }
            // Caution: Java will not expect n to be null
            // It is null to denote a wildcard selector
            result = to(jmlF.at(p).Select(result,n));
        } else if (!(result instanceof JmlStoreRefArrayRange)) {
            log.error(S.pos(),"jml.expected","a . to select a field");
            skipThroughSemi();
            return to(jmlF.at(p).Erroneous());
        }
        return result;
    }
    
    public JmlTypeClauseIn parseIn(int pos, JCModifiers mods) {
        if (!isNone(mods)) log.error(pos,"jml.no.mods.allowed",JmlToken.IN.internedName());
        S.setJmlKeyword(false);
        S.nextToken(); // skip over the in token
        ListBuffer<JmlGroupName> list = parseGroupNameList();
        S.setJmlKeyword(true);
        accept(SEMI);
        return toP(jmlF.at(pos).JmlTypeClauseIn(list.toList()));
    }
    
    public void parseInvariantInitiallyAxiom(JCModifiers mods, ListBuffer<JCTree> list) {
        int pos = S.pos();
        JmlToken jt = S.jmlToken();
        S.setJmlKeyword(false);
        S.nextToken();
        JCExpression e = expression();
        S.setJmlKeyword(true);
        if (S.token() != SEMI) {
            log.error(S.pos(),"jml.bad.construct",jt.internedName() + " declaration");
            skipThroughSemi();
        } else {
            JmlTypeClauseExpr tcl = to(jmlF.at(pos).JmlTypeClauseExpr(mods,jt,e));
            tcl.source = log.currentSource();
            list.append(tcl);
            S.nextToken();
        }
    }
    
    public void parseRepresents(JCModifiers mods, ListBuffer<JCTree> list) {
        S.setJmlKeyword(false);
        int pos = S.pos();
        S.nextToken();
        JCExpression id = (JCExpression)parseStoreRef(true);
        boolean suchThat;
        JCExpression e;
        if (S.token() == Token.EQ || S.jmlToken() == JmlToken.LEFT_ARROW) {
            suchThat = false;
            S.nextToken();
            e = expression();
        } else if (S.jmlToken() == JmlToken.BSSUCHTHAT) {
            suchThat = true;
            S.nextToken();
            e = expression();
        } else {
            log.error(S.pos(),"jml.bad.represents.token");
            e = null;
            skipThroughSemi();
            suchThat = false;
        }
        S.setJmlKeyword(true);
        if (e == null) { // skip
        } else if (S.token() != Token.SEMI) {
            log.error(S.pos(),"jml.invalid.expression.or.missing.semi");
            skipThroughSemi();
        } else {
            JmlTypeClause tcl;
            list.append(tcl=to(jmlF.at(pos).JmlTypeClauseRepresents(mods, id, suchThat, e)));
            tcl.source = log.currentSource();
            S.nextToken();
        }
    }
    
    public void parseConstraint(JCModifiers mods, ListBuffer<JCTree> list) {
        int pos = S.pos();
        S.setJmlKeyword(false);
        S.nextToken();
        JCExpression e = expression();
        S.setJmlKeyword(true);
        ListBuffer<JmlConstraintMethodSig> sigs = new ListBuffer<JmlConstraintMethodSig>();
        if (S.token() == Token.FOR) {
            S.nextToken();
            if (S.jmlToken == JmlToken.BSEVERYTHING) {
                S.nextToken();
                // This is the default, so we just set the sigs to null
                sigs = null;
            } else {
                while (true) {
                    JmlConstraintMethodSig m = parseConstraintMethod();
                    if (m == null) break;
                    sigs.append(m);
                    if (S.token() != COMMA) break;
                    S.nextToken();
                }
            }
        }
        JmlTypeClause tcl=to(jmlF.at(pos).JmlTypeClauseConstraint(mods,e,sigs==null?null:sigs.toList()));
        tcl.source = log.currentSource();
        list.append(tcl);
        if (S.token() != SEMI) {
            log.error(S.pos(),"jml.bad.construct","constraint declaration");
            skipThroughSemi();
        } else {
            S.nextToken();
        }
    }
    
    // FIXME - check and fix this - also gets used for callable so change name?
    public JmlConstraintMethodSig parseConstraintMethod() {
        Token t = S.token();
        if (t != Token.IDENTIFIER && t != Token.THIS && t != Token.SUPER) return null;
        int initpos = S.pos();
        int p = initpos;
        Name n;
        if (S.token() == Token.IDENTIFIER) {
            n = ident();
        } else if (S.token() == Token.THIS) {
            n = names._this;
            S.nextToken();
        } else if (S.token() == Token.SUPER) {
            n = names._super;
            S.nextToken();
        } else {
            n = null;
        }
        JCExpression id = jmlF.at(p).Ident(n);
        do {
            if (S.token() != Token.DOT) break;
            S.nextToken();
            p = S.pos();
            if (S.token() == Token.IDENTIFIER) {
                n = ident();
            } else if (S.token() == Token.THIS) {
                n = names._this;
                S.nextToken();
            } else if (S.token() == Token.SUPER) {
                n = names._super;
                S.nextToken();
            } else {
                /// FIXME -error
            }
            id = jmlF.at(p).Select(id,n);
        } while (true);
        ListBuffer<JCExpression> args = null;
        if (S.token() == Token.LPAREN) {
            args = new ListBuffer<JCExpression>();S.nextToken();
            if (S.token() != Token.RPAREN) {
                JCExpression arg = type();
                args.append(arg);
                while (S.token() == Token.COMMA) {
                    S.nextToken();
                    arg = type();
                    args.append(arg);
                }
                if (S.token() != RPAREN) {
                    // ERROR
                } else {
                    S.nextToken();
                }
            } else {
                S.nextToken();
            }
        }
        return jmlF.at(initpos).JmlConstraintMethodSig(id,args==null?null:args.toList());
    }
    
    public void parseReadableWritable(JCModifiers mods, JmlToken token, ListBuffer<JCTree> list) {
        int p = S.pos();
        S.setJmlKeyword(false);
        S.nextToken();
        if (S.token() != Token.IDENTIFIER) {
            log.error(S.pos(),"jml.expected","an identifier");
            S.setJmlKeyword(true);
            skipThroughSemi();
            return;
        }
        Name n = ident();
        JCTree.JCIdent id = to(jmlF.at(S.pos()).Ident(n));
        if (S.token() != Token.IF) {
            log.error(S.pos(),"jml.expected","an if token");
            S.setJmlKeyword(true);
            skipThroughSemi();
            return;
        }
        accept(Token.IF);
        JCExpression e = expression();
        S.setJmlKeyword(true);
        if (e.getTag() == JCTree.ERRONEOUS || S.token() != SEMI) {
            skipThroughSemi();
        } else {
            S.nextToken();
        }
        list.append( toP(jmlF.at(p).JmlTypeClauseConditional(mods,token,id,e)) );
    }
    
    public void parseMonitorsFor(JCModifiers mods, ListBuffer<JCTree> list) {
        int p = S.pos();
        S.setJmlKeyword(false);
        S.nextToken();
        if (S.token() != Token.IDENTIFIER) {
            log.error(S.pos(),"jml.expected","an identifier");
            S.setJmlKeyword(true);
            skipThroughSemi();
            return;
        }
        Name n = ident();
        JCTree.JCIdent id = to(jmlF.at(S.pos()).Ident(n));
        if (S.token() != Token.EQ && S.jmlToken() != JmlToken.LEFT_ARROW) {
            log.error(S.pos(),"jml.expected","an = or <- token");
            S.setJmlKeyword(true);
            skipThroughSemi();
            return;
        }
        S.nextToken();
        ListBuffer<JCExpression> elist = expressionList();
        S.setJmlKeyword(true);
        if (S.token() != SEMI) {
            skipThroughSemi();
        } else {
            S.nextToken();
        }
        list.append( toP(jmlF.at(p).JmlTypeClauseMonitorsFor(mods,id,elist)) );
    }
    
    public ListBuffer<JCExpression> expressionList() {
        ListBuffer<JCExpression> args = lb();
        args.append(expression());
        while (S.token() == COMMA) {
            S.nextToken();
            JCExpression e = expression();
            args.append(e); // e might be a JCErroneous
        }
        return args;
    }
    
    public JCExpression parseNotAssigned() {
        int p = S.pos();
        JmlToken jt = S.jmlToken();
        S.nextToken();
        accept(LPAREN);
        ListBuffer<JCTree> list = parseStoreRefList(false);
        if (S.token() != RPAREN) {
            log.error(S.pos(),"log.expected","right parenthesis");
            skipThroughRightParen();
        } else {
            S.nextToken();
        }
        return toP(jmlF.at(p).JmlStoreRefListExpression(jt,list));
    }
    
    
    public JmlMethodSpecs parseMethodSpecs(JCModifiers mods) {
        // Method specifications are a sequence of specification cases
        ListBuffer<JmlSpecificationCase> cases = new ListBuffer<JmlSpecificationCase>();
        JmlSpecificationCase c;
        JmlToken t;
        int pos = S.pos();
        while ((c=parseSpecificationCase(mods,false)) != null) {
            cases.append(c);
            mods = modifiersOpt();
        }
        JmlMethodSpecs sp = jmlF.at(pos).JmlMethodSpecs(cases.toList());  // end position set below
        if ((t=S.jmlToken()) == JmlToken.IMPLIES_THAT) {
            if (!isNone(mods)) log.error(S.pos(),"jml.no.mods.allowed",t.internedName());
            S.nextToken();
            mods = modifiersOpt();
            cases = new ListBuffer<JmlSpecificationCase>();
            while ((c=parseSpecificationCase(mods,false)) != null) {
                cases.append(c);
                mods = modifiersOpt();
            }
            if (cases.size() > 0) cases.first().also = t;
            sp.impliesThatCases = cases.toList();
        }
        if ((t=S.jmlToken()) == JmlToken.FOR_EXAMPLE) {
            if (!isNone(mods)) log.error(S.pos(),"jml.no.mods.allowed",t.internedName());
            S.nextToken();
            mods = modifiersOpt();
            cases = new ListBuffer<JmlSpecificationCase>();
            while ((c=parseSpecificationCase(mods,true)) != null) {
                cases.append(c);
                mods = modifiersOpt();
            }
            if (cases.size() > 0) cases.first().also = t;
            sp.forExampleCases = cases.toList();
        }
        storeEnd(sp,S.prevEndPos());
        // We may have parsed some modifiers and then found out that we are not
        // at the beginning of a spec case (perhaps at the beginning of a method
        // declaration for example).  So we have to preserve the modifiers that
        // have already been parsed.
        pushBackModifiers = mods;
        // It is possible that a problem in parsing results in
        // an empty set of specification cases.  That would not be legal
        // JML, but I expect that a message has been logged about it already.
        return sp;
    }
    
    /** Tokens that can end a model program (until we parse it properly) */
    public final static Set<JmlToken> stops = EnumSet.of(ALSO,IMPLIES_THAT,FOR_EXAMPLE,ENDJMLCOMMENT);
    
    /** Returns true if no modifiers or annotations (of any kind) have been set
     * @param mods the modifiers structure to check
     * @return true if any flags or annotations are set
     */
    public boolean isNone(JCModifiers mods) {
        return mods == null || ((mods.flags&Flags.StandardFlags) == 0 && (mods.annotations == null || mods.annotations.isEmpty()));
    }
    
    // [ also ] [ modifiers ] [ | behavior | normal_behavior | exceptional_behavior ] [ clause ]*
    public JmlSpecificationCase parseSpecificationCase(JCModifiers mods, boolean exampleSection) {
        JmlToken also = null;
        JmlToken ijt = S.jmlToken();
        if (ijt == ALSO) {
            if (!isNone(mods)) {
                log.error(S.pos(),"jml.no.mods.allowed",ijt.internedName());
                mods = null;
            }
            S.nextToken();
            also = ijt;
            // get any modifiers
            mods = modifiersOpt();
        }
        boolean code = false;
        int codePos = 0;
        if (S.jmlToken() == JmlToken.CODE) {
            codePos = S.pos();
            code = true;
            S.nextToken();
        }

        JmlToken jt = S.jmlToken();
        int pos = S.pos();
        if (jt == JmlToken.BEHAVIOR || jt == JmlToken.NORMAL_BEHAVIOR ||
                jt == JmlToken.EXCEPTIONAL_BEHAVIOR) {
            if (exampleSection) {
                log.warning(S.pos(),"jml.example.keyword","must not",jt.internedName());
            }
            S.nextToken();
        } else if (jt == JmlToken.EXAMPLE || jt == JmlToken.NORMAL_EXAMPLE ||
                    jt == JmlToken.EXCEPTIONAL_EXAMPLE) {
            if (!exampleSection) {
                log.warning(S.pos(),"jml.example.keyword","must",jt.internedName());
            }
            S.nextToken();
        } else if (jt == MODEL_PROGRAM) {
            return parseModelProgram(mods,code,also);
        } else {
            jt = null;
            if (code) log.warning(codePos,"jml.misplaced.code");
            // lightweight
        }
        
        ListBuffer<JmlMethodClause> clauses = new ListBuffer<JmlMethodClause>();
        JmlMethodClause e;
        while (S.token() == CUSTOM && (e=getClause()) != null) {
            clauses.append(e);
        }
        
        if (clauses.size() == 0) {
            if (jt != null) {
                log.error(pos,"jml.empty.specification.case");
            }
            if (also == null && !code) return null;
        }
        if (jt == null && code) code = false; // Already warned about this
        JmlSpecificationCase j = toP(jmlF.at(pos).JmlSpecificationCase(mods,code,jt,also,clauses.toList()));
        j.sourcefile = log.currentSource();
        return j;
    }
    
    public JmlSpecificationCase parseModelProgram(JCModifiers mods, boolean code, JmlToken also) {
        JmlToken jt = S.jmlToken();
        int pos = S.pos();
        
        // skip the whole model program - FIXME parse it someday
        // skip up to ALSO/IMPLIES_THAT_FOR_EXAMPLE or ENDJMLCOMMENT or EOF
        
        if (JmlOptionName.isOption(context, JmlOptionName.SHOW_NOT_IMPLEMENTED)) 
            log.warning(pos, "jml.unimplemented.construct", "model program", "JmlParser.getSpecificationCase()");

        int count = 0;
        do {
            S.nextToken();
            jt = S.jmlToken();
            if (S.token() == LBRACE) count++;
            else if (S.token() == RBRACE) count--;
        } while (S.token() != EOF && count != 0);
        JmlSpecificationCase spc = toP(jmlF.at(pos).JmlSpecificationCase(mods,code,MODEL_PROGRAM,also,List.<JmlMethodClause>nil()));
        if (jt == ENDJMLCOMMENT || S.token() == RBRACE) S.nextToken();
        return spc;
    }
    
    /** Parses an entire specification group; the current token must be the
     * SPEC_GROUP_START and upon return the SPEC_GROUP_END will have been 
     * consumed.
     * @return a JMLMethodClauseGroup AST node
     */
    public JmlMethodClauseGroup getSpecificationGroup() {
        int p = S.pos();
        ListBuffer<JmlSpecificationCase> list = new ListBuffer<JmlSpecificationCase>();
        S.nextToken();
        do {
            JmlSpecificationCase g = parseSpecificationCase(null,false);
            list.append(g);
        } while (S.jmlToken == ALSO);
        if (S.jmlToken != SPEC_GROUP_END) {
            log.error(S.pos(),"jml.invalid.spec.group.end");
            while (S.jmlToken() != JmlToken.ENDJMLCOMMENT && S.token() != EOF) S.nextToken();
            if (S.token() != EOF) S.nextToken();
        } else {
            S.nextToken();
        }
        return toP(jmlF.at(p).JmlMethodClauseGroup(list.toList()));
    }

    /** Parses a method specification clause; the current token must be the
     * token indication the kind of clause; upon return the terminating semicolon
     * will have been consumed.  It is also legal for the current token to be
     * ENDJMLCOMMENT, in which case it is consumed.  If the next token is not
     * a STARTJMLCOMMENT, null is returned; if the next token is STARTJMLCOMMENT,
     * it is consumed, and the method attempts to read another clause.  The 
     * method returns null when no more clauses are recognized.
     * @return a JmlMethodClause AST node, or null if there is no clause recognized
     */
    public JmlMethodClause getClause() {
        JCExpression e ;
        if (S.jmlToken() == ENDJMLCOMMENT) {
            S.nextToken();
            if (S.jmlToken() != STARTJMLCOMMENT) return null;
            S.nextToken();
        }
        JmlToken jt = S.jmlToken();
        int pos = S.pos();
        S.setJmlKeyword(false);
        JmlMethodClause res = null;
        if (jt != null) switch (jt) {

            // The cases have to include all clause types.
            
            case REQUIRES:
            case ENSURES:
            case DIVERGES:
            case WHEN:
                res = parseRequires();
                break;
                
            case SIGNALS: // signals (Exception e) expression ;
                res = parseSignals();
                break;
            
            case SIGNALS_ONLY:
                res = parseSignalsOnly();
                break;
                
            case ASSIGNABLE:
                res = parseAssignable();
                break;
                
            case FORALL:
            case OLD:
                res = parseForallOld();
                break;

            case WORKING_SPACE:
            case MEASURED_BY:
            case DURATION:
                res = parseDurationEtc();
                break;

            case ACCESSIBLE:
            case CAPTURES:
            case CALLABLE:
                if (JmlOptionName.isOption(context, JmlOptionName.SHOW_NOT_IMPLEMENTED)) 
                    log.warning(S.pos(), "jml.unimplemented.construct", jt.internedName(), "JmlParser.getClause()");
                S.nextToken();
                S.setJmlKeyword(true);
                skipThroughSemi();  // FIXME - needs implementation
                e = toP(jmlF.at(S.pos()).Erroneous());
                res = toP(jmlF.at(pos).JmlMethodClauseExpr(jt, e));  // just so something is returned, for now, since null means end of input
                break;
            
            case SPEC_GROUP_START:
                S.setJmlKeyword(true);
                res = getSpecificationGroup();
                break;
                
            default:
                // For any other token we just exit this loop,
                // WITHOUT HAVING CALLED nextToken()!!!!
                break;

        }
        if (res != null) res.sourcefile = log.currentSource();
        S.setJmlKeyword(true);  // Just in case, but it is too late, since the
                        // token after the semicolon is already read
        return res;
    }
    
    protected JCExpression expressionOrNotSpecified() {
        if (S.jmlToken() == BSNOTSPECIFIED) {
            S.nextToken();
            return toP(jmlF.at(S.pos()).JmlSingleton(BSNOTSPECIFIED));
        } else {
            return expression();
        }
    }
    
    /** Parses a requires method specification clause
     * @return the parsed JmlMethodClause
     */
    protected JmlMethodClause parseRequires() {
        JmlToken jt = S.jmlToken();
        int pos = S.pos();
        S.nextToken();
        JCExpression e = expressionOrNotSpecified();
        S.setJmlKeyword(true);
        if (S.token() != Token.SEMI) {
            syntaxError(S.pos(),null,"jml.invalid.expression.or.missing.semi");
            skipThroughSemi();
        } else {
            S.nextToken(); // skip SEMI
        }
        return toP(jmlF.at(pos).JmlMethodClauseExpr(jt, e));
    }

    /** Parses a signals method specification clause
     * @return the parsed JmlMethodClause
     */
    protected JmlMethodClause parseSignals() {
        JmlToken jt = S.jmlToken();
        int pos = S.pos();
        JCExpression e;
        S.nextToken();
        JCExpression t = null;
        Name ident = null;
        int rpos = pos;
        if (S.token() != Token.LPAREN) {
            syntaxError(S.pos(),null,"jml.expected.lparen.signals");
            t = to(jmlF.at(S.pos()).Ident(names.fromString("java")));
            t = to(jmlF.at(S.pos()).Select(t,names.fromString("lang")));
            t = to(jmlF.at(S.pos()).Select(t,names.fromString("Exception")));
            e = expression();
        } else {
            S.nextToken();
            // Get type
            t = type();
            // Get identifier (optional)
            if (S.token() == IDENTIFIER) {
                ident = ident();
            }
            rpos = S.pos();
            if (S.token() != Token.RPAREN) {
                syntaxError(S.pos(),null,"jml.expected.rparen.signals");
                skipToSemi();
                e = toP(jmlF.at(S.pos()).Erroneous());
            } else {
                S.nextToken();
                if (S.token() == Token.SEMI) {
                    e = toP(jmlF.at(S.pos()).Literal(TypeTags.BOOLEAN,Boolean.TRUE));
                } else {
                    e = expression();
                }
            }
        }
        S.setJmlKeyword(true);
        JCTree.JCVariableDecl var = jmlF.at(t.pos).VarDef(
                jmlF.at(t.pos).Modifiers(0),ident,t,null);
        storeEnd(var,rpos);
        if (S.token() != Token.SEMI) {
            if (e.getKind() != Kind.ERRONEOUS) syntaxError(S.pos(),null,"jml.missing.semi");
            skipThroughSemi();
        } else {
            S.nextToken();
        }
        return toP(jmlF.at(pos).JmlMethodClauseSignals(jt,var,e));
    }
    
    /** Parses a signals_only clause.  The current token must be the signals_only
     * token; upon return the terminating semicolon will have been parsed.
     * @return a JmlMethodClauseSigOnly AST node
     */
    protected JmlMethodClauseSigOnly parseSignalsOnly() {
        JmlToken jt = S.jmlToken();
        int pos = S.pos();
        S.nextToken();
        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
        
        if (S.jmlToken() == BSNOTHING) {  // FIXME - can have multiple nothing and everything
            S.setJmlKeyword(true);
            S.nextToken();
            if (S.token() != SEMI) {
                syntaxError(S.pos(),null,"jml.expected.semi.after.nothing");
                skipThroughSemi();
            } else {
                S.nextToken();
            }
        } else if (S.token() == SEMI) {
            S.setJmlKeyword(true);
            syntaxError(S.pos(),null,"jml.use.nothing",jt.internedName());
            S.nextToken();
        } else {
            while (true) {
                JCExpression typ = type(); // if this fails, a JCErroneous is returned
                list.append(typ);
                if (S.token() == SEMI) {
                    S.setJmlKeyword(true);
                    S.nextToken();
                    break;
                } else if (S.token() == COMMA) {
                    S.nextToken();
                    continue;
                } else if (S.jmlToken() == ENDJMLCOMMENT) {
                    syntaxError(S.pos(),null,"jml.missing.semi"); 
                } else {
                    syntaxError(S.pos(),null,"jml.missing.comma"); 
                }
                // error 
                S.setJmlKeyword(true);
                skipThroughSemi();
                break;
            }
        }  
        return toP(jmlF.at(pos).JmlMethodClauseSignalsOnly(jt,list.toList()));
    }
    
    protected JmlMethodClauseDecl parseForallOld() {
        int pos = S.pos();
        JmlToken jt = S.jmlToken();
        S.nextToken();
        // non_null and nullable and perhaps other type modifiers in the
        // future are allowed
        JCModifiers mods = modifiersOpt();
        JCExpression t = type();
        boolean prev = inJmlDeclaration;
        inJmlDeclaration = true; // allows non-ghost declarations
        ListBuffer<JCTree.JCStatement> stats = variableDeclarators(mods, t,new ListBuffer<JCStatement>());
        inJmlDeclaration = prev;
        JmlMethodClauseDecl res = to(jmlF.at(pos).JmlMethodClauseDecl(jt,t,stats));
        S.setJmlKeyword(true);
        if (S.token() == Token.SEMI) {
            S.nextToken();
        } else {
            log.error(S.pos(),"jml.bad.construct",jt.internedName() + " specification");
            skipThroughSemi();
        }
        return res;
    }
    
    /** Parses (duration|working_space|?) (<expression>|"\\not_specified") [ "if" <expression> ] ";" */
    protected JmlMethodClauseConditional parseDurationEtc() {
        int pos = S.pos();
        JmlToken jt = S.jmlToken();
        JCExpression p = null;
        S.nextToken();
        JCExpression e = expressionOrNotSpecified();
        if (S.token() == Token.IF) { // The if is not allowed if the
                    // expression is not_specified, but we test that 
                    // during type checking
            S.nextToken();
            p = expression();
        }
        JmlMethodClauseConditional res = to(jmlF.at(pos).JmlMethodClauseConditional(jt,e,p));
        S.setJmlKeyword(true);
        if (S.token() == Token.SEMI) {
            S.nextToken();
        } else {
            log.error(S.pos(),"jml.bad.construct",jt.internedName() + " specification");
            skipThroughSemi();
        }
        return res;
    }
    
    /** Parses "assignable" <store-ref-list> ";" */
    protected JmlMethodClauseAssignable parseAssignable() {
        JmlToken jt = S.jmlToken();
        int pos = S.pos();
        ListBuffer<JCTree> list = new ListBuffer<JCTree>();
        S.nextToken(); // skip over the assignable token
        if (S.token() == SEMI) {
            syntaxError(S.pos(),null,"jml.use.nothing.assignable");
            S.setJmlKeyword(true);
            S.nextToken(); // skip over the SEMI
        } else {
            list = parseStoreRefList(false);
            if (S.token() == SEMI) {
                // OK, go on
            } else if (S.jmlToken() == ENDJMLCOMMENT) {
                syntaxError(S.pos(),null,"jml.missing.semi"); 
            }
            S.setJmlKeyword(true);
            if (S.token() != SEMI) {
                // error already reported
                skipThroughSemi();
            } else {
                if (list.isEmpty()) {
                    syntaxError(S.pos(),null,"jml.use.nothing.assignable");
                }
                S.nextToken();
            }
        }
        return toP(jmlF.at(pos).JmlMethodClauseAssignable(jt, list.toList()));
    }
    
    /** Parses ("\|nothing"|"\\everything"|"\\not_specified"| <store-ref> [ "," <store-ref> ]* ) ";" 
     * <BR>
     * a store-ref
     *  is a JCIdent, a JCSelect (potentially with a null field), or a JmlStoreRefArrayRange;
     *  there may be more than one use of a JmlStoreRefArrayRange, e.g. a[2..3][4..5] or
     *  a.f[4..5].g[6..7]
     * @param strictId if true, keywords and wildcards are not allowed
     * @return list of zero or more store-refs or a list of one store-ref-keyword; 
     */
    protected ListBuffer<JCTree> parseStoreRefList(boolean strictId) {
        JmlToken jt = S.jmlToken();
        int p = S.pos();
        ListBuffer<JCTree> list = new ListBuffer<JCTree>();
        if (!strictId && (jt == BSNOTHING || jt == BSEVERYTHING|| jt == BSNOTSPECIFIED)) {
            JCTree s = to(jmlF.at(p).JmlStoreRefKeyword(jt));
            S.nextToken();
            list.append(s);
            return list;
        }
        while (true) {
            JCTree r = parseStoreRef(false);
            if (r != null) list.append(r);
            if (S.token() == COMMA) {
                S.nextToken();
                continue;
            } else if (S.token() == SEMI) {
                return list;
            } else if (S.jmlToken == ENDJMLCOMMENT) {
                // The missing semi-colon is reported by the caller
                return list;
            } else {
                syntaxError(S.pos(),null,"jml.missing.comma"); 
                if (r==null) return list;
            }
        }
    }
    
    /** Parses (<informal-comment>| (<identifier>|"this"|"super") [ "." "*" | "." <identifier> | <array-range-expr> ]* )
     * except that "this" or "super" must have something following them.
     * @param strictId if true, no informal comments or wildcards are allowed
     * @return a JCExpression or JmlStoreRefKeyword
     */
    protected /*@ nullable */ JCTree parseStoreRef(boolean strictId) {
        JCTree ss = parseStoreRefInit(strictId);
        if (ss instanceof JmlStoreRefKeyword) return ss;
        if (ss instanceof JCExpression) {
            JCExpression e = (JCExpression)ss;
            while (true) {
                if (S.token() == Token.DOT) {
                    int dotpos = S.pos();
                    S.nextToken();
                    if (!strictId && S.token() == Token.STAR) {
                        S.nextToken();
                        // Caution: Java will not expect the field selector to be null
                        e = toP(jmlF.at(dotpos).Select(e,(Name)null));
                        if (S.token() != Token.COMMA && S.token() != Token.SEMI) {
                            log.error(S.pos(),"jml.not.after.star");
                            skipToCommaOrSemi();
                        }
                        break;
                    } else if (S.token() == Token.IDENTIFIER) {
                        Name n = ident();
                        e = to(jmlF.at(dotpos).Select(e,n));
                        continue;
                    } else {
                        if (strictId) log.error(S.pos(),"jml.expected.id");
                        else log.error(S.pos(),"jml.ident.or.star.after.dot");
                        skipToCommaOrSemi();
                        break;
                    }

                } else if (S.token() == Token.LBRACKET) {
                    e = parseArrayRangeExpr(e,strictId);
                } else {
                    break;
                }
            }
            if (e instanceof JCIdent) {
                if (((JCIdent)e).name == names._this || ((JCIdent)e).name == names._super) {
                    log.error(e.pos(),"jml.naked.this.super");
                    // A standalone this or super is not allowed.  We state the
                    // error but the parse tree is this.* or super.*
                    e = to(jmlF.at(e.pos).Select(e,(Name)null));
                }
            }
            ss = e;
        } else {
            if (ss != null) log.error(S.pos(), "jml.internal", "Code branch thought to be infeasable in JmlParser.parseStoreRef: " + ss.getClass());
        }
        return ss;
    }
    
    /** Parses the initial part of a store-ref: (<informal-comment>|<identifier>|"this"|"super")
     * @param strictId when true, only store-refs that start with identifiers,
     *  this, or super are allowed
     * @return
     */
    //@ ensures \result == null || \result instanceof JmlStoreRefKeyword || \result instanceof JCIdent;
    protected JCTree parseStoreRefInit(boolean strictId) {
        JmlToken jt = S.jmlToken;
        int p = S.pos();
        if (!strictId&&(jt == INFORMAL_COMMENT)) {
            JCTree s = to(jmlF.at(p).JmlStoreRefKeyword(jt));
            S.nextToken();
            return s;
        } else if (S.token() == Token.IDENTIFIER){
            Name n = ident();
            JCTree.JCIdent id = to(jmlF.at(p).Ident(n));
            return id;
        } else if (S.token() == Token.SUPER) {
            S.nextToken(); // skip over the this or super
            JCTree.JCIdent id = toP(jmlF.at(p).Ident(names._super));
            return id;
        } else if (S.token() == Token.THIS) {
            S.nextToken(); // skip over the this or super
            JCTree.JCIdent id = toP(jmlF.at(p).Ident(names._this));
            return id;
        }
        log.error(p,"jml.bad.store.ref");
        skipToCommaOrSemi();
        return null;
    }
    
    /** Parses [ "[" ( "*" | <expression> | <expression> ".." "*" | <expression> ".." | <expression> ".." <expression> ) "]" ]*
     * @param t the leading expression for which the array index or range is a suffix
     * @param strictId if true, no wildcards or ranges are allowed
     * @return
     */
    protected JCExpression parseArrayRangeExpr(JCExpression t, boolean strictId) {
        while (S.token() == Token.LBRACKET) {
            S.nextToken();  // move past the LBRACKET
            if (!strictId && S.token() == Token.STAR) {
                S.nextToken();
                if (S.token() == Token.RBRACKET) {
                    S.nextToken();
                    t = toP(jmlF.at(t.pos).JmlStoreRefArrayRange(t,null,null));
                    continue;
                } else {
                    log.error(S.pos(),"jml.expected.rbracket.star");
                    skipToCommaOrSemi();
                    break;
                }
            } else {
                JCExpression lo = expression();
                if (S.token() == Token.RBRACKET) {
                    t = to(jmlF.at(t.pos).JmlStoreRefArrayRange(t,lo,lo));
                    S.nextToken();
                    continue;
                } else if (!strictId && S.jmlToken() == DOT_DOT) {
                    S.nextToken();
                    JCExpression hi = null;
                    if (S.token() == STAR) {
                        S.nextToken();
                    } else if (S.token() == Token.RBRACKET) {
                        // OK
                    } else {
                        hi = expression();
                    }
                    if (S.token() == Token.RBRACKET) {
                        t = to(jmlF.at(t.pos).JmlStoreRefArrayRange(t,lo,hi));
                        S.nextToken();
                    } else {
                        log.error(S.pos(),"jml.expected.rbracket");
                        skipToCommaOrSemi();
                        break;
                    }
                    continue;
//                } else if (!strictId && S.token() == STAR) {
//                    t = to(jmlF.at(t.pos).JmlStoreRefArrayRange(t,lo,null));
//                    continue;
                } else {
                    log.error(S.pos(),"jml.invalid.expression.succeeding.token");
                    skipToCommaOrSemi();
                    break;
                }
            }
        }
        return t;
    }

    protected JCModifiers pushBackModifiers = null;
    
    /** Overridden so that anything in 'pushBackModifiers' is incorporated into
     * the result of the call
     * @return combination of 'pushBackModifiers' and any modifiers that are
     * next in the token string
     */
    @Override
    protected JCModifiers modifiersOpt() {
        JCModifiers partial = pushBackModifiers;
        pushBackModifiers = null;
        return modifiersOpt(partial);
    }

    /** Combines 'pushBackModifiers', the argument and any modifiers that are
     * next in the token string (including JML modifiers)
     * the result of the call
     * @return combination of 'pushBackModifiers' and any modifiers that are
     * next in the token string
     */
    @Override
    protected JCModifiers modifiersOpt(JCModifiers partial) {
        if (partial == null) {
            partial = pushBackModifiers;
            pushBackModifiers = null;
        } else if (pushBackModifiers != null) {
            log.error(S.pos(),"jml.internal.nosobad","This code branch in modifiersOpt() is not expected to be executed and is not fully implemented - please report with code samples");
            // I don't think this is ever executed.  If it is we need to check that
            // there is no duplication of modifiers.
            long flags = partial.flags | pushBackModifiers.flags;
            //long same = (partial.flags & pushBackModifiers.flags);
            ListBuffer<JCAnnotation> annotations = new ListBuffer<JCAnnotation>();
            annotations.appendList(pushBackModifiers.annotations);
            annotations.appendList(partial.annotations);
            partial = jmlF.at(pushBackModifiers.pos()).Modifiers(flags,annotations.toList());
            pushBackModifiers = null;
        }
        partial = super.modifiersOpt(partial);
        while (S.token() == Token.CUSTOM) {
            partial = jmlModifiersOpt(partial);
            if (S.token() == Token.CUSTOM) break;
            partial = super.modifiersOpt(partial);
        }
        return partial;
    }
    
    /** Converts a token to an annotation expression, or to null if there is no
     * corresponding annotation.
     * @param jt the input token
     * @param position the character position
     * @return the annotation expression
     */
    protected /*@ nullable */ JCAnnotation tokenToAnnotationAST(JmlToken jt, int position) {
        Class<?> c = jt.annotationType;
        if (c == null) return null;
        JCExpression t = to(F.at(position).Ident(names.fromString("org")));
        t = to(F.at(position).Select(t, names.fromString("jmlspecs")));
        t = to(F.at(position).Select(t, names.fromString("annotations")));
        t = to(F.at(position).Select(t, names.fromString(c.getSimpleName())));
        JCAnnotation ann = to(F.at(position).Annotation(t, List.<JCExpression>nil()));
        return ann;
    }
    
    /** Reads any JML modifiers, combining them with the input to produce a new
     * JCModifiers object
     * @param partial input modifiers and annotations
     * @return combined modifiers and annotations
     */
    protected JCModifiers jmlModifiersOpt(JCModifiers partial) {
        ListBuffer<JCAnnotation> annotations = new ListBuffer<JCAnnotation>();
        if (partial != null) annotations.appendList(partial.annotations);
        int pos = Position.NOPOS;
        if (partial != null) pos = partial.pos;
        while (S.token() == Token.CUSTOM) {
            JmlToken j = S.jmlToken();
            if (JmlToken.modifiers.contains(j)) {
                JCAnnotation a = tokenToAnnotationAST(j,S._pos);
                if (a != null) annotations.append(a);
                // a is null if no annotation is defined for the modifier;
                // we just silently ignore that situation
                // (this is true at the moment for math annotations, but could
                // also be true for a modifier someone forgot)
            } else if (j == STARTJMLCOMMENT) {
                // skip over
            } else if (j == ENDJMLCOMMENT) {
                // skip over
            } else if (j == CONSTRUCTOR || j == FIELD || j == METHOD) {
                // FIXME - do we want to save this anywhere; check that it matches the declaration; check that it is not used on something other than a declaration?
                S.setJmlKeyword(false);
            } else {
                // Not a modifier
                break;
            }
            S.nextToken();
        }
        JCModifiers mods = F.at(pos).Modifiers(partial==null?0:partial.flags, annotations.toList());
        storeEnd(mods, pos == Position.NOPOS ? pos: S.prevEndPos());
        return mods;
    }
    
    /** Parses a type expression */
    @Override
    public JCExpression type() {
        JCExpression t = super.type();
        boolean start = false;
        if (S.jmlToken == STARTJMLCOMMENT) { S.nextToken(); start = true; }
        if (S.jmlToken == WEAKLY) S.nextToken();  // FIXME - we completely ignore weakly, and also allow it many places where it may not be.
        if (start && S.jmlToken == ENDJMLCOMMENT) S.nextToken();
        return t;
    }
    
    // Have to replicate this method because we cannot just add the JML operators
    // into the token set for the Java operators.
    @Override
    protected JCExpression term1() {
        JCExpression t = term2Equiv();
        if ((mode & EXPR) != 0 && S.token() == QUES) {
            mode = EXPR;
            return term1Rest(t);
        } else {
            return t;
        }
    }
    
    protected JCExpression term1Rest(JCExpression t) {
        return super.term1Rest(term2EquivRest(term2ImpRest(t)));
    }


    protected JCExpression term2Equiv() {
        JCExpression t = term2Imp();
        if ((mode & EXPR) != 0 && (S.jmlToken() == JmlToken.EQUIVALENCE ||
                                S.jmlToken() == JmlToken.INEQUIVALENCE)) {
            mode = EXPR;
            return term2EquivRest(t);
        } else {
            return t;
        }
    }
    
    protected JCExpression term2EquivRest(JCExpression t) {
        JmlToken jt = S.jmlToken();
        while (jt == JmlToken.EQUIVALENCE || jt == JmlToken.INEQUIVALENCE) {
            int ppos = S.pos(); // position of the operator
            S.nextToken();
            JCExpression tt = term2Imp();
            t = toP(jmlF.at(ppos).JmlBinary(jt, t, tt));
            jt = S.jmlToken();
        }
        return t;
    }
    
    protected JCExpression term2Imp() {
        JCExpression t = term2();
        if ((mode & EXPR) != 0 && (S.jmlToken() == JmlToken.IMPLIES || S.jmlToken() == JmlToken.REVERSE_IMPLIES )) {
            mode = EXPR;
            return term2ImpRest(t);
        } else {
            return t;
        }
    }
    
    protected JCExpression term2ImpRest(JCExpression t) {
        JmlToken jt = S.jmlToken();
        if (jt == JmlToken.IMPLIES) {
            // For IMPLIES we need to associate to the right
            int ppos = S.pos(); // position of the operator
            S.nextToken();
            JCExpression tt = term2ImpRestX();
            t = toP(jmlF.at(ppos).JmlBinary(jt, t, tt));
            if (S.jmlToken == JmlToken.REVERSE_IMPLIES) {
                syntaxError(S.pos(),null,"jml.mixed.implies");
                skipToSemi();
            }
        } else if (jt == JmlToken.REVERSE_IMPLIES) {
            // For REVERSE_IMPLIES we do the conventional association to the left
            do { 
                int ppos = S.pos(); // position of the operator
                S.nextToken();
                JCExpression tt = term2();
                t = toP(jmlF.at(ppos).JmlBinary(jt, t, tt));
                jt = S.jmlToken();
            } while (jt == JmlToken.REVERSE_IMPLIES );
            if (jt == JmlToken.IMPLIES) {
                syntaxError(S.pos(),null,"jml.mixed.implies");
                skipToSemi();
            }
        }
        return t;
    }
    
    /** A local call so we can use recursion to do the association to the right */
    protected JCExpression term2ImpRestX() {
        JCExpression t = term2();
        JmlToken jt = S.jmlToken();
        if (jt != JmlToken.IMPLIES) return t;
        int ppos = S.pos();
        S.nextToken();
        JCExpression tt = term2ImpRestX();
        return toP(jmlF.at(ppos).JmlBinary(jt, t, tt));
    }
        
    @Override 
    protected JCExpression term3() {
        List<JCExpression> typeArgs = null;
        // No JML function expects type arguments.  If they did we would parse them here (before seeing
        // the JML token).  But we can't do that just to check, because super.term3() down below 
        // expects to parse them itself.  So if someone does write type arguments for a JML function
        // the code will fall into the super.term3() call and the token will not be recognized -
        // no chance for a nice error message.
        if (S.token() == Token.CUSTOM) {
            JCExpression t;
            JmlToken jt = S.jmlToken();
            int p = S.pos(); // Position of the keyword
            
            switch (jt) {
                case BSTYPEUC:
                case BSREAL:
                case BSBIGINT:
                    t = to(jmlF.at(p).JmlPrimitiveTypeTree(jt));
                    S.nextToken();
                    t = bracketsSuffix(bracketsOpt(t));
                    return t;
                    
                case BSRESULT :
                case BSINDEX :
                case BSVALUES :
                case BSLOCKSET : // FIXME - what can follow this?
                    t = to(jmlF.at(p).JmlSingleton(jt));
                    S.nextToken();
                    if (S.token() == Token.LPAREN) {
                        JCExpression res = syntaxError(S.pos(),null,"jml.no.args.allowed",jt.internedName());
                        primarySuffix(t,typeArgs); // Parse arguments and ignore, both to do as much
                                    // type checking as possible and to skip valid constructs to avoid
                                    // extra errors
                        return res;
                    } else {
                        return primarySuffix(t,typeArgs);
                    }
                    
                case BSSAME:
                case INFORMAL_COMMENT:
                    t = to(jmlF.at(p).JmlSingleton(jt));
                    S.nextToken();
                    return t;

                case BSTYPELC :
                    S.nextToken();
                    // FIXME - check that typeargs is null
                    if (S.token() != Token.LPAREN) {
                        return syntaxError(p,null,"jml.args.required",jt.internedName());
                    } else {
                        accept(Token.LPAREN);
                        JCExpression e;
                        if (S.token() == Token.VOID) {
                            e = to(F.at(S.pos()).TypeIdent(TypeTags.VOID));
                            S.nextToken();
                        } else {
                            e = type();
                        }
                        if (S.token() != Token.RPAREN) {
                            if (!(e instanceof JCErroneous)) log.error(S.pos(),"jml.bad.bstype.expr");
                            skipThroughRightParen();
                        }
                        else S.nextToken();
                        // FIXME - this should be a type literal
                        return toP(jmlF.at(p).JmlMethodInvocation(jt, List.of(e)));
                    }
                    
                case BSNONNULLELEMENTS :
                case BSMAX :
                case BSFRESH :
                case BSREACH :
                case BSSPACE :
                case BSWORKINGSPACE :
                case BSDURATION :
                case BSISINITIALIZED :
                case BSINVARIANTFOR :
                    S.nextToken();
                    if (S.token() != Token.LPAREN) {
                        if (jt == BSMAX) {
                            return parseQuantifiedExpr(p,jt);
                        }
                        return syntaxError(p,null,"jml.args.required",jt.internedName());
                    } else {
                        // FIXME - check no typeargs
                        int pp = S._pos;
                        List<JCExpression> args = arguments();
                        return toP(jmlF.at(pp).JmlMethodInvocation(jt,args));
                    }
                    
                case BSOLD :
                case BSPRE :
                case BSTYPEOF :
                case BSELEMTYPE :
                case BSNOWARN:
                case BSNOWARNOP:
                case BSWARN:
                case BSWARNOP:
                case BSBIGINT_MATH:
                case BSSAFEMATH:
                case BSJAVAMATH:
                    S.nextToken();
                    if (S.token() != Token.LPAREN) {
                        if (jt == BSMAX) {
                            return parseQuantifiedExpr(p,jt);
                        }
                        return syntaxError(p,null,"jml.args.required",jt.internedName());
                    } else {
                        // FIXME - check no typeargs
                        int pp = S._pos;
                        List<JCExpression> args = arguments();
                        t = toP(jmlF.at(pp).JmlMethodInvocation(jt,args));
                        return primarySuffix(t,typeArgs);
                    }
                    
                case BSNOTMODIFIED:
                    S.nextToken();
                    // FIXME - check no typeargs
                    int pp = S._pos;
                    List<JCExpression> args = arguments();
                    return toP(jmlF.at(pp).JmlMethodInvocation(jt,args));

                case BSNOTASSIGNED:
                case BSONLYACCESSED:
                case BSONLYCAPTURED:
                case BSONLYASSIGNED:
                    return parseNotAssigned();

                case BSFORALL:
                case BSEXISTS:
                case BSPRODUCT:
                case BSSUM:
                case BSNUMOF:
                case BSMIN:
                    S.nextToken();
                    return parseQuantifiedExpr(p,jt);
                    
                case BSPEER:
                case NONNULL:
                case NULLABLE:
                case BSREADONLY:
                case BSREP:
                case READONLY:
                    S.nextToken();
                    if (JmlOptionName.isOption(context, JmlOptionName.SHOW_NOT_IMPLEMENTED)) 
                        log.warning(S.pos(), "jml.unimplemented.construct", jt.internedName(), "JmlParser.term3(), as type modifiers");

                    // FIXME - ignoring these type modifiers for now
                    return term3();
                
                case BSLBLANY:
                case BSLBLNEG:
                case BSLBLPOS:
                    S.nextToken();
                    return parseLblExpr(p,jt);
                    
                case BSONLYCALLED:
                    // FIXME - needs implementation
                    if (JmlOptionName.isOption(context, JmlOptionName.SHOW_NOT_IMPLEMENTED)) 
                        log.warning(S.pos(), "jml.unimplemented.construct", jt.internedName(), "JmlParser.term3(), as type modifiers");
                    S.nextToken();
                    skipThroughRightParen();
                    return toP(jmlF.at(p).Erroneous());
                    
                default:
                    log.error(p,"jml.bad.type.expression","( token " + jt.internedName() + " in JmlParser.term3())");
                    return toP(jmlF.at(p).Erroneous());
            }
        }
        return super.term3();
    }
    
    protected boolean inCreator = false;
        
    public JCExpression parseQuantifiedExpr(int pos, JmlToken jt) {
        JCModifiers mods = modifiersOpt();
        JCExpression t = type();
        if (t.getTag() == JCTree.ERRONEOUS) return t;
        if (mods.pos == -1) mods.pos = t.pos; // set the beginning of the modifiers
                                        // to the beginning of the type, if there
                                        // are no modifiers
        ListBuffer<JCVariableDecl> decls = new ListBuffer<JCVariableDecl>();
        int idpos = S.pos();
        Name id = ident(); // FIXME  JML allows dimensions after the ident
        decls.append(jmlF.at(idpos).VarDef(mods,id,t,null));
        while (S.token() == COMMA) {
            S.nextToken();
            idpos = S.pos();
            id = ident(); // FIXME  JML allows dimensions after the ident
            decls.append(jmlF.at(idpos).VarDef(mods,id,t,null));
        }
        if (S.token() != SEMI) {
            log.error(S.pos(),"jml.expected.semicolon.quantified");
            int p = S.pos();
            skipThroughRightParen();
            return toP(jmlF.at(p).Erroneous());
        }
        S.nextToken();
        JCExpression range = null;
        JCExpression pred = null;
        if (S.token() == SEMI) {
            // type id ; ; predicate
            // two consecutive semicolons is allowed, and means the
            // range is null - continue
            S.nextToken();
            pred = expression();
        } else {
            range = expression();
            if (S.token() == SEMI) {
                // type id ; range ; predicate
                S.nextToken();
                pred = expression();
            } else if (S.token() == RPAREN) {
                // type id ; predicate
                pred = range;
                range = null;
            } else {
                log.error(S.pos(),"jml.expected.semicolon.quantified");
                int p = S.pos();
                skipThroughRightParen();
                return toP(jmlF.at(p).Erroneous());
            }
        }
        return toP(jmlF.at(pos).JmlQuantifiedExpr(jt,decls,range,pred));
    }

    // MAINTENANCE ISSUE:
    // This is a copy from Parser, so we can add in parseSetComprehension
    JCExpression creator(int newpos, List<JCExpression> typeArgs) {
        switch (S.token()) {
            case BYTE: case SHORT: case CHAR: case INT: case LONG: case FLOAT:
            case DOUBLE: case BOOLEAN:
                if (typeArgs == null)
                    return arrayCreatorRest(newpos, basicType());
                break;
            default:
        }
        JCExpression t = qualident();
        int oldmode = mode;
        mode = TYPE;
        if (S.token() == LT) {
            checkGenerics();
            t = typeArguments(t);
        }
        while (S.token() == DOT) {
            int pos = S.pos();
            S.nextToken();
            t = toP(F.at(pos).Select(t, ident()));
            if (S.token() == LT) {
                checkGenerics();
                t = typeArguments(t);
            }
        }
        mode = oldmode;
        if (S.token() == LBRACKET) {
            JCExpression e = arrayCreatorRest(newpos, t);
            if (typeArgs != null) {
                int pos = newpos;
                if (!typeArgs.isEmpty() && typeArgs.head.pos != Position.NOPOS) {
                    // note: this should always happen but we should
                    // not rely on this as the parser is continuously
                    // modified to improve error recovery.
                    pos = typeArgs.head.pos;
                }
                syntaxError(pos, null,"cannot.create.array.with.type.arguments");
                return toP(F.at(newpos).Erroneous(typeArgs.prepend(e)));
            }
            return e;
        } else if (S.token() == LPAREN) {
            return classCreatorRest(newpos, null, typeArgs, t);
        } else if (S.token() == LBRACE) {
            return parseSetComprehension(t);
        } else {
            // recovery? FIXME
            syntaxError(S.pos(), null, "expected3",
                    "\'(\'","\'{\'",
            "\'[\'");
            t = toP(F.at(newpos).NewClass(null, typeArgs, t, List.<JCExpression>nil(), null));
            return toP(F.at(newpos).Erroneous(List.<JCTree>of(t)));
        }
    }
    
    /** Parses: <identifier> <expression> 
     * @param pos character position of the lbl token
     * @param jmlToken either the LBLPOS or LBLNEG token
     * @return a JmlLblExpression
     */
    protected JCExpression parseLblExpr(int pos, JmlToken jmlToken) {
        // The JML token is already scanned
        Name n = ident();
        JCExpression e = expression();
        return toP(jmlF.at(pos).JmlLblExpression(jmlToken,n,e));
    }
    
    /** Parses: "{" [ <modifiers> ] <type> <identifier> "|" <expression> "}" */
    protected JCExpression parseSetComprehension(JCExpression type) {
        // FIXME - the following will parse error-free input.  Need to be robust
        // against errors
        int begin = S.pos();
        accept(LBRACE);
        JCModifiers mods = modifiersOpt();
        int tpos = S.pos();
        JCTree.JCExpression t = type();
        Name n = ident();
        JCTree.JCVariableDecl v = toP(jmlF.at(tpos).VarDef(mods,n,t,null));
        accept(BAR);
        JCExpression predicate = expression();
        accept(RBRACE);
        JmlSetComprehension sc = toP(jmlF.at(begin).JmlSetComprehension(type,v,predicate));
        return sc;
    }
    
    /** Parses: <groupName> [ "," <groupName> ]* */
    protected ListBuffer<JmlGroupName> parseGroupNameList() {
        ListBuffer<JmlGroupName> list = new ListBuffer<JmlGroupName>();
        JmlGroupName g = parseGroupName();
        list.append(g);
        while (S.token() == Token.COMMA) {
            S.nextToken();
            g = parseGroupName();
            list.append(g);
        }
        return list;
    }
    
    /** Parses: [ "this" "." | "super" "." ] <identifier>  */
    protected JmlGroupName parseGroupName() {
        JCExpression t = null;
        int p = S.pos();
        if (S.token() == Token.THIS) {
            t = to(jmlF.at(p).Ident(names._this));
            S.nextToken();
            accept(Token.DOT);
        } else if (S.token() == Token.SUPER) {
            t = to(jmlF.at(p).Ident(names._super));
            S.nextToken();
            accept(Token.DOT);
        }
        Name n = ident();
        if (t == null) t = toP(jmlF.at(p).Ident(n));
        else t = toP(jmlF.at(p).Select(t,n));
        return toP(jmlF.at(p).JmlGroupName(t));
    }
    
    /** Overridden in order to absorb the pushBackModifiers */
    public <T extends ListBuffer<? super JCVariableDecl>> T variableDeclarators(JCModifiers mods,
            JCExpression type,
            T vdefs)
    {
        if (pushBackModifiers != null && isNone(mods)) {
            mods = pushBackModifiers;
            pushBackModifiers = null;
        }
        T t = variableDeclaratorsRest(S.pos(), mods, type, ident(), false, null, vdefs);
        return t;
    }



    protected <T extends ListBuffer<? super JCVariableDecl>> T variableDeclaratorsRest(int pos,
            JCModifiers mods,
            JCExpression type,
            Name name,
            boolean reqInit,
            String dc,
            T vdefs)
    {
        if (S.jml) reqInit = false;  // In type checking we check this more thoroughly
                // Here we just allow having no initializer
        return super.variableDeclaratorsRest(pos,mods,type,name,reqInit,dc,vdefs);
    }

    /** This is overridden to try to get <:, <# and <=# with the right precedence */
    // FIXME - not sure this is really robust
    protected int prec(Token token) {
        if (token == CUSTOM) {
            // Caution: S may not be on the same token anymore
            if (S.jmlToken() != null && S.jmlToken() != JmlToken.SUBTYPE_OF && S.jmlToken() != JmlToken.LOCK_LT && S.jmlToken() != JmlToken.LOCK_LE) return -1; // For in/equivalence and reverse/implies
            return TreeInfo.ordPrec;  // All the JML operators are comparisons
        }
        else return super.prec(token);
    }
    
    JmlToken topOpJmlToken;
    
    // MAINTENANCE ISSUE - Duplicated from Parser.java in order to track Jml tokens
    JCExpression term2Rest(JCExpression t, int minprec) {
        List<JCExpression[]> savedOd = odStackSupply.elems;
        JCExpression[] odStack = newOdStack();
        List<Token[]> savedOp = opStackSupply.elems;
        Token[] opStack = newOpStack();
        // optimization, was odStack = new Tree[...]; opStack = new Tree[...];
        int top = 0;
        odStack[0] = t;
        int startPos = S.pos();
        Token topOp = ERROR;
        while (prec(S.token()) >= minprec) {
            opStack[top] = topOp;
            top++;
            topOp = S.token();
            topOpJmlToken = S.jmlToken();
            int pos = S.pos();
            S.nextToken();  // S.jmlToken() changes
            odStack[top] = topOp == INSTANCEOF ? type() : term3();
            while (top > 0 && prec(topOp) >= prec(S.token())) {
                odStack[top-1] = makeOp(pos, topOp, odStack[top-1],
                                        odStack[top]);
                top--;
                topOp = opStack[top];
            }
        }
        assert top == 0;
        t = odStack[0];

        if (t.getTag() == JCTree.PLUS) {
            StringBuffer buf = foldStrings(t);
            if (buf != null) {
                t = toP(F.at(startPos).Literal(TypeTags.CLASS, buf.toString()));
            }
        }

        odStackSupply.elems = savedOd; // optimization
        opStackSupply.elems = savedOp; // optimization
        return t;
    }
    protected JCExpression makeOp(int pos,  // DRC - changed from private to protected
            Token topOp,
            JCExpression od1,
            JCExpression od2)
    {
        if (topOp == CUSTOM) { // <:
            JCExpression e = jmlF.at(pos).JmlBinary(topOpJmlToken, od1, od2);
            storeEnd(e,getEndPos(od2));
            return e;
        }
        return super.makeOp(pos, topOp, od1, od2);
    }

    
    /** Skips up to and including a semicolon, though not including any EOF or ENDJMLCOMMENT */
    public void skipThroughSemi() {
        while (S.token() != Token.SEMI && S.token() != Token.EOF && S.jmlToken() != JmlToken.ENDJMLCOMMENT)
            S.nextToken();
        if (S.token() == Token.SEMI) S.nextToken();
    }

    /** Skips up to but not including a semicolon or EOF or ENDJMLCOMMENT */
    public void skipToSemi() {
        while (S.token() != Token.SEMI && S.token() != Token.EOF && S.jmlToken() != JmlToken.ENDJMLCOMMENT)
            S.nextToken();
    }

    /** Skips up to but not including a semicolon or comma or EOF or ENDJMLCOMMENT */
    public void skipToCommaOrSemi() {
        while (S.token() != Token.SEMI && S.token() != Token.COMMA && S.token() != Token.EOF && S.jmlToken() != JmlToken.ENDJMLCOMMENT)
            S.nextToken();
    }

    /** Skips up to a EOF or ENDJMLCOMMENT or up to and including a right parenthesis */
    public void skipThroughRightParen() {
        while (S.token() != Token.RPAREN && S.token() != Token.EOF && S.jmlToken() != JmlToken.ENDJMLCOMMENT)
            S.nextToken();
        if (S.token() != Token.EOF) S.nextToken();
    }

}
