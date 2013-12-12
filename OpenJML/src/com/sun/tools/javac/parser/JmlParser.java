/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.parser;

import static com.sun.tools.javac.parser.Token.*;
import static com.sun.tools.javac.util.ListBuffer.lb;
import static org.jmlspecs.openjml.JmlToken.*;

import java.io.PrintStream;
import java.util.Iterator;

import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlTree.JmlChoose;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodSig;
import org.jmlspecs.openjml.JmlTree.JmlDoWhileLoop;
import org.jmlspecs.openjml.JmlTree.JmlEnhancedForLoop;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlImport;
import org.jmlspecs.openjml.JmlTree.JmlLblExpression;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseCallable;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignals;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignalsOnly;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlStatementLoop;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefArrayRange;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefKeyword;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConstraint;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseIn;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMaps;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMonitorsFor;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTree.JmlWhileLoop;
import org.jmlspecs.openjml.esc.Label;

import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.main.OptionName;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Position;

/** This class extends the javac parser to parse JML constructs as well. */
public class JmlParser extends EndPosParser {

    /** The context this parser was created for */
    // @ non_null
    public Context          context;

    /** Cached value of the utilities object */
    // @ non_null
    protected Utils         utils;

    /** The scanner associated with the parser */
    // @ non_null
    protected JmlScanner    S;

    /** The node factory to use */
    // @ non_null
    protected JmlTree.Maker jmlF;

    /** The table of identifiers */
    // @ non_null
    protected Names         names;

    /** True only when we are parsing within a model program */
    protected boolean       inModelProgram = false;

    /**
     * A constructor for a new parser, but you should get new instances of the
     * parser from the parser factory, that is, by
     * JmlParser.instance(context).newParser(...).
     * 
     * @param fac
     *            the node factory to use to create parse trees
     * @param S
     *            the scanner to produce tokens for the parser to ask for
     * @param keepDocComments
     *            whether to keep javadoc comments
     */
    protected JmlParser(ParserFactory fac, Lexer S, boolean keepDocComments) {
        super(fac, S, keepDocComments, true); // true = keepLineMap
        if (!(S instanceof JmlScanner)) {
            log.error("jml.internal",
                    "S expected to be a JmlScanner in JmlParser");
            throw new JmlInternalError("Expected a JmlScanner for a JmlParser");
        }
        if (!(F instanceof JmlTree.Maker)) {
            log.error("jml.internal",
                    "F expected to be a JmlTree.Maker in JmlParser");
            throw new JmlInternalError(
                    "Expected a JmlTree.Maker for a JmlParser");
        }
        this.S = (JmlScanner) S;
        this.jmlF = (JmlTree.Maker) F;
    }

    /** Returns the scanner being used by the parser */
    public JmlScanner getScanner() {
        return S;
    }

    /** Returns the node factory being used by the parser */
    public JmlTree.Maker maker() {
        return jmlF;
    }
    
    /** Returns true if the -deprecation option is set */
    public boolean isDeprecationSet() {
        return Options.instance(context).isSet("-Xlint:deprecation");
    }

    /**
     * Parses a compilation unit using tokens from the scanner - generally the
     * entry point used to parse a Java/JML file.
     */
    @Override
    public JCTree.JCCompilationUnit parseCompilationUnit() {
        JCTree.JCCompilationUnit u = super.parseCompilationUnit();
        if (u instanceof JmlCompilationUnit) {
            JmlCompilationUnit jmlcu = (JmlCompilationUnit) u;
            // sort the JML declarations from the Java declarations
            ListBuffer<JCTree> list = new ListBuffer<JCTree>();
            for (JCTree t : u.defs) {
                if (t instanceof JmlClassDecl) {
                    JmlClassDecl jcd = (JmlClassDecl) t;
                    jcd.toplevel = jmlcu;
                    if (utils.isJML(((JmlClassDecl) t).mods)) {
                        // These are declarations that were declared within
                        // a JML comment - they should have, but might
                        // erroneously be missing, a model modifier
                        jmlcu.parsedTopLevelModelTypes.add(jcd);
                    } else {
                        list.append(t);
                    }
                } else {
                    list.append(t);
                }
            }
            jmlcu.defs = list.toList();
        } else {
            log.error(
                    "jml.internal",
                    "JmlParser.compilationUnit expects to receive objects of type JmlCompilationUnit, but it found a "
                            + u.getClass()
                            + " instead, for source "
                            + u.getSourceFile().toUri().getPath());
        }
        return u;
    }

    /**
     * Overrides the super class importDeclaration in order to recognize model
     * import statements.
     * 
     * @return null or a JCImport node
     */
    // @ ensures \result == null || \result instanceof JCTree.JCImport;
    // @ nullable
    @Override
    protected JCTree importDeclaration() {
        int p = S.pos();
        boolean modelImport = S.jmlToken() == JmlToken.MODEL;
        if (!modelImport && S.jml) {
            jmlerror(p,S.endPos(),"jml.import.no.model");
            modelImport = true;
        }
        JCTree t = super.importDeclaration();
        ((JmlImport) t).isModel = modelImport;
        t.setPos(p);
        if (S.jmlToken() == JmlToken.ENDJMLCOMMENT) {
            S.nextToken();
        }
        return t;
    }

    /**
     * This parses a class, interface or enum declaration after the parser has
     * seen a group of modifiers and an optional javadoc comment. This can be a
     * declaration at the top-level in the compilation unit, within a class
     * body, or a local declaration in a method body.
     * 
     * @param mods
     *            the preceding modifiers and (java) annotations
     * @param dc
     *            the preceding javadoc comment
     * @return a JCStatement that is a declaration
     */
    @Override
    protected JCStatement classOrInterfaceOrEnumDeclaration(JCModifiers mods,
            String dc) {
        boolean prevInJmlDeclaration = inJmlDeclaration;
        JCStatement s;
        try {
            if (S.jml) {
                if (mods == null) {
                    mods = jmlF.at(Position.NOPOS).Modifiers(0);
                    storeEnd(mods, Position.NOPOS);
                }
                if (!inJmlDeclaration) utils.setJML(mods);
                inJmlDeclaration = true;
            }
            Token token = S.token();
            if (token == IMPORT && !isNone(mods)) {
                JCAnnotation a = utils
                        .findMod(
                                mods,
                                names.fromString(Strings.modelAnnotation));
                if (a != null) {
                    skipToSemi();
                    int p = mods.annotations.head.pos;
                    jmlerror(p, S.endPos(), "jml.illformed.model.import");
                    s = toP(F.Exec(toP(F.at(p).Erroneous(List.<JCTree> nil()))));
                    skipThroughSemi();
                } else {
                    int p = mods.annotations.head.pos;
                    s = toP(F.Exec(toP(F.at(p).Erroneous(List.<JCTree> nil()))));
                    jmlerror(mods.getStartPosition(),
                            mods.getEndPosition(endPositions),
                            "jml.no.mods.on.import");
                }
                mods.flags = 0;
                mods.annotations = List.<JCAnnotation> nil();
            } else if (!inJmlDeclaration || token == Token.CLASS || token == Token.INTERFACE || token == Token.ENUM) {
                // The guard above is used because if it is false, we want to produce
                // a better error message than we otherwise get, for misspelled
                // JML modifiers. However, the test above replicates tests in
                // the super method and may become obsolete.
                s = super.classOrInterfaceOrEnumDeclaration(mods, dc);
            } else {
                int p = S.pos();
                jmlerror(S.pos(),
                        S.endPos(),
                        "jml.unexpected.or.misspelled.jml.token",
                            token == null ? S.jmlToken().internedName() : S.stringVal() );
                
                setErrorEndPos(S.pos());
                s = toP(F.Exec(toP(F.at(p).Erroneous(List.<JCTree> nil()))));
                //S.nextToken();
            }
            if (s instanceof JCClassDecl && (((JCClassDecl)s).mods.flags & Flags.ENUM) != 0) {
                ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
                JCClassDecl cd = (JCClassDecl)s;
                Name n = jmlF.Name("_JML_enum_"); // FIXME - move to strings
                JCExpression disj = null;
                for (JCTree d: cd.defs) {
                    if (!(d instanceof JCVariableDecl)) continue;
                    JCExpression id = jmlF.at(d.pos).Ident(((JCVariableDecl)d).getName());
                    args.add(id);
                    id = jmlF.at(d.pos).Ident(((JCVariableDecl)d).getName());
                    JCExpression ide = jmlF.at(d.pos).Ident(n);
                    JCExpression ex = jmlF.at(id.pos).Binary(JCTree.EQ, ide, id);
                    disj = disj == null ? ex : jmlF.at(ex.pos).Binary(JCTree.OR,disj,ex);
                }
                args.add(F.Literal(TypeTags.BOT,null));
                JCExpression ex = jmlF.at(s.pos).JmlMethodInvocation(JmlToken.BSDISTINCT,args.toList());
                JmlTypeClauseExpr axiom = jmlF.at(s.pos).JmlTypeClauseExpr(jmlF.Modifiers(0),JmlToken.AXIOM,ex);
                cd.defs = cd.defs.append(axiom);
                JCVariableDecl decl = jmlF.at(cd.pos).VarDef(jmlF.Modifiers(0),n,jmlF.Ident(jmlF.Name("Object")),null);
                ex = jmlF.JmlQuantifiedExpr(JmlToken.BSFORALL,List.<JCVariableDecl>of(decl), null,
                        jmlF.JmlBinary(JmlToken.EQUIVALENCE, jmlF.TypeTest(jmlF.Ident(n), jmlF.Ident(cd.getSimpleName())),disj));
                axiom = jmlF.at(s.pos).JmlTypeClauseExpr(jmlF.Modifiers(0),JmlToken.AXIOM,ex);
                cd.defs = cd.defs.append(axiom);
            }
            // Can also be a JCErroneous
            if (s instanceof JmlClassDecl)
                filterTypeBodyDeclarations((JmlClassDecl) s, context, jmlF);
            if (S.jmlToken == JmlToken.ENDJMLCOMMENT) {
                S.nextToken();
            }
        } finally {
            inJmlDeclaration = prevInJmlDeclaration;
        }
        return s;
    }

    /**
     * This override is needed in order to manage the value of S.jmlKeyword. In
     * parsing a class body, the value starts out true; however, the value might
     * be false on entering this method if we are parsing the class body of an
     * anonymous class expression.
     */
    @Override
    List<JCTree> classOrInterfaceBody(Name className, boolean isInterface) {
        boolean savedJmlKeyword = S.jmlkeyword;
        S.setJmlKeyword(true);
        try {
            return super.classOrInterfaceBody(className, isInterface);
        } finally {
            S.setJmlKeyword(savedJmlKeyword);
        }

    }

    /**
     * This parses a sequence of statements that can appear in a block. JML
     * overrides it in order to include JML assert, assume, set, debug, ghost
     * declarations, unreachable, loop invariants and any other JML specs that
     * can appear in the body of a method.
     * 
     * @return a list of JmlStatement nodes (despite the required type of the
     *         method)
     */
    @Override
    public List<JCStatement> blockStatements() {
        ListBuffer<JCStatement> list = new ListBuffer<JCStatement>();
        int pos = -1;
        JCModifiers mods = null;
        while (S.token() != Token.RBRACE && S.token() != EOF) {
            // If the following equality is true, then the scanner has made no
            // progress in the previous loop iteration. Presumably some error
            // has occurred; for example no next statement is recognized.
            // So we just abort the loop. Since the next token is not a right
            // brace, an error will be issued when an attempt is made to read
            // the right brace that closes the block.
            if (S._pos == pos) break;
            pos = S._pos;
            // Only certain qualifiers can appear here - perhaps limit the 
            // parsing of modifiers to just that set. Java explicitly has
            // final abstract strictfp; also synchronized but not as a modifier.
            // FIXME - this needs more testing
            if (S.token() != Token.SYNCHRONIZED) {
                mods = modifiersOpt(); // read any additional modifiers (e.g.
                                   // JML ones)
            }
            JmlToken jt = S.jmlToken();
            if (jt != null) {

                if (isJmlTypeToken(jt)) {
                    JCExpression t = parseType();
                    ListBuffer<JCStatement> vdefs = new ListBuffer<JCStatement>();
                    variableDeclarators(mods, t, vdefs);
                    if (S.token() == Token.SEMI) {
                        accept(SEMI);
                    } else {
                        accept(SEMI); // To get the error message
                        skipThroughSemi();
                    }
                    for (JCStatement vdef : vdefs) {
                        utils.setJML(((JmlVariableDecl) vdef).mods);
                        list.append(vdef);
                    }
                } else {
                    pushBackModifiers = mods;
                    mods = null;
                    JCStatement st = parseStatement();
                    list.append(st);
                }
            } else {
                pushBackModifiers = mods;
                mods = null;
                if (S.jml) {
                    boolean prevInJmlDeclaration = inJmlDeclaration;
                    inJmlDeclaration = true;
                    List<JCTree.JCStatement> dlist = super.blockStatements();
                    inJmlDeclaration = prevInJmlDeclaration;
                    if (inJmlDeclaration || inLocalOrAnonClass) {
                        // In this case we are in the body of a model method.
                        // Within the body we don't mark any local variables
                        // or classes as ghost or model (with setJML).
                        list.appendList(dlist);
                    } else {
                        for (JCTree.JCStatement t : dlist) {
                            if (t instanceof JmlVariableDecl) {
                                JmlVariableDecl d = (JmlVariableDecl) t;
                                utils.setJML(d.mods);
                            } else if (t instanceof JmlClassDecl) {
                                JmlClassDecl d = (JmlClassDecl) t;
                                utils.setJML(d.mods);
                            } else if (t instanceof JCTree.JCSkip) {
                                // An empty statement is not really allowed
                                // within
                                // a JML annotation, but it is common to find
                                // one
                                // after a local class declaration, so we won't
                                // complain.
                            } else {
                                jmlerror(t.pos, "jml.expected.decl.or.jml");
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
        int endPos = -1;
        for (JCStatement s : list) {
            if (s instanceof JmlStatementLoop) {
                loops.append((JmlStatementLoop) s);
                endPos = getEndPos(s);
                continue;
            } else if (s instanceof JmlForLoop) {
                ((JmlForLoop) s).loopSpecs = loops.toList();
                loops = new ListBuffer<JmlStatementLoop>();
            } else if (s instanceof JmlEnhancedForLoop) {
                ((JmlEnhancedForLoop) s).loopSpecs = loops.toList();
                loops = new ListBuffer<JmlStatementLoop>();
            } else if (s instanceof JmlWhileLoop) {
                ((JmlWhileLoop) s).loopSpecs = loops.toList();
                loops = new ListBuffer<JmlStatementLoop>();
            } else if (s instanceof JmlDoWhileLoop) {
                ((JmlDoWhileLoop) s).loopSpecs = loops.toList();
                loops = new ListBuffer<JmlStatementLoop>();
            } else {
                if (loops.size() != 0) {
                    jmlerror(getStartPos(loops.first()), loops.first().pos,
                            endPos, "jml.loop.spec.misplaced");
                    loops = new ListBuffer<JmlStatementLoop>();
                }
            }
            newlist.append(s);
        }
        if (loops.size() != 0) {
            jmlerror(getStartPos(loops.first()), loops.first().pos, endPos,
                    "jml.loop.spec.misplaced");
        }
        return newlist.toList();
    }

    /** Overridden to parse JML statements */
    @Override
    public JCStatement parseStatement() {
        JCStatement st;
        String reason = null;
        if (S.token() == Token.CUSTOM) { // Note that declarations may start
            boolean needSemi = true;
            if (S.jmlToken() != JmlToken.ENDJMLCOMMENT) {
                int pos = S.pos();
                JmlToken jtoken = S.jmlToken();
                JmlSpecificationCase spc;
                if (jtoken != null)
                    reason = jtoken.internedName() + " statement";
                if (jtoken == JmlToken.ASSUME || jtoken == JmlToken.ASSERT) {
                    S.setJmlKeyword(false);
                    S.nextToken();
                    JCExpression t = null;
                    t = parseExpression();
                    JmlTree.JmlStatementExpr ste = jmlF
                            .at(pos)
                            .JmlExpressionStatement(
                                    jtoken,
                                    jtoken == JmlToken.ASSUME ? Label.EXPLICIT_ASSUME
                                            : Label.EXPLICIT_ASSERT, t);
                    if (S.token() == Token.COLON) {
                        S.nextToken();
                        ste.optionalExpression = parseExpression();
                    }
                    toP(ste);
                    ste.source = log.currentSourceFile();
                    //ste.line = log.currentSource().getLineNumber(pos);
                    st = ste;
                } else if (jtoken == HENCE_BY || jtoken == UNREACHABLE || jtoken == REACHABLE) {
                    S.setJmlKeyword(false);
                    S.nextToken();
                    JCExpression t = null;
                    if (jtoken == REACHABLE) {
                        if (S.token() != Token.SEMI) t = parseExpression();
                        else t = toP(jmlF.at(S.pos()).Literal(TypeTags.BOOLEAN, 1)); // Boolean.TRUE;
                    }
                    else if (jtoken != UNREACHABLE) t = parseExpression();
                    JmlTree.JmlStatementExpr ste = to(jmlF.at(pos)
                            .JmlExpressionStatement(jtoken, 
                                    jtoken == REACHABLE ? Label.REACHABLE : Label.UNREACHABLE,
                                    t));
                    ste.source = log.currentSourceFile();
                    //ste.line = log.currentSource().getLineNumber(pos);
                    st = ste;
                    if (jtoken == REACHABLE && JmlOption.isOption(context, JmlOption.STRICT)) {
                        log.warning(ste.pos,"jml.not.strict",jtoken.internedName());
                    }
                } else if (jtoken == DECREASES || jtoken == LOOP_INVARIANT) {
                    S.setJmlKeyword(false);
                    S.nextToken();
                    JCExpression t = parseExpression();
                    JmlStatementLoop ste = to(jmlF.at(pos).JmlStatementLoop(
                            jtoken, t));
                    // ste.source = log.currentSourceFile();
                    // ste.line = log.currentSource().getLineNumber(pos);
                    st = ste;
                } else if (jtoken == JmlToken.HAVOC ) {
                    S.setJmlKeyword(false);
                    S.nextToken();

                    ListBuffer<JCExpression> list = parseStoreRefList(false);
                    if (S.token() == SEMI) {
                        // OK, go on
                    } else if (S.jmlToken() == ENDJMLCOMMENT) {
                        syntaxError(S.pos(), null, "jml.missing.semi");
                    }
                    S.setJmlKeyword(true);
                    if (S.token() != SEMI) {
                        // error already reported
                        skipThroughSemi();
                    } else {
                        if (list.isEmpty()) {
                            syntaxError(S.pos(), null, "jml.use.nothing.assignable");
                        }
                        S.nextToken();
                    }
                    st = toP(jmlF.at(pos).JmlHavocStatement(list.toList()));
                    S.setJmlKeyword(true); // This comes a token too late.
                    needSemi = false;
                } else if (jtoken == JmlToken.SET || jtoken == JmlToken.DEBUG) {
                    S.setJmlKeyword(false);
                    S.nextToken();
                    // Only StatementExpressions are allowed - 
                    // assignment statements and stand-alone method calls -
                    // but JML constructs are allowed.
                    JCStatement t = super.parseStatement();
                    if (!(t instanceof JCExpressionStatement)) {
                        jmlerror(t.getStartPosition(),
                                t.getEndPosition(endPositions),
                                "jml.bad.statement.in.set.debug");
                        t = null;
                    }
                    st = toP(jmlF.at(pos).JmlStatement(jtoken, (JCExpressionStatement)t));
                    S.setJmlKeyword(true); // This comes a token too late.
                    needSemi = false;

                } else if (methodClauseTokens.contains(jtoken)) {
                    // TODO - if strict JML, requires a REFINING token first
                    JCModifiers mods = jmlF.Modifiers(0);
                    JmlMethodSpecs specs = parseMethodSpecs(mods);
                    for (JmlSpecificationCase c : specs.cases) {
                        if (!isNone(c.modifiers)) {
                            jmlerror(c.modifiers.getStartPosition(),
                                    c.modifiers.getEndPosition(endPositions),
                                    "jml.no.mods.in.refining");
                        }
                    }
                    st = jmlF.at(pos).JmlStatementSpec(specs);
                    storeEnd(st, specs.getEndPosition(endPositions));
                    needSemi = false;

                } else if (jtoken == JmlToken.REFINING) {
                    S.nextToken();
                    if (S.jmlToken() == JmlToken.ALSO) {
                        jmlerror(S.pos(), S.endPos(), "jml.invalid.also");
                        S.nextToken();
                    }
                    JCModifiers mods = modifiersOpt();
                    JmlMethodSpecs specs = parseMethodSpecs(mods);
                    for (JmlSpecificationCase c : specs.cases) {
                        if (!isNone(c.modifiers)) {
                            jmlerror(c.modifiers.getStartPosition(),
                                    c.modifiers.getEndPosition(endPositions),
                                    "jml.no.mods.in.refining");
                        }
                    }
                    st = jmlF.at(pos).JmlStatementSpec(specs);
                    storeEnd(st, specs.getEndPosition(endPositions));
                    needSemi = false;

                } else if (inModelProgram && jtoken == JmlToken.CHOOSE) {
                    st = parseChoose();
                    return toP(st); // FIXME - is this the correct end position?
                } else if (inModelProgram && jtoken == JmlToken.CHOOSE_IF) {
                    st = parseChooseIf();
                    return toP(st); // FIXME - is this the correct end position?
                } else if (inModelProgram && jtoken == JmlToken.INVARIANT) {
                    JCTree t = parseInvariantInitiallyAxiom(null);
                    st = jmlF.JmlModelProgramStatement(t);
                    return st;
                } else if (inModelProgram
                        && (spc = parseSpecificationCase(null, false)) != null) {
                    st = jmlF.JmlModelProgramStatement(spc);
                    return st;

                    // A JML statement can also be a ghost declaration that
                    // begins with a JML type. These are parsed in
                    // blockStatements() because they produce more than one
                    // statement at a time.
                    // This (old) implementation only allowed one variable to be
                    // declared.
                    // } else if (isJmlTypeToken(jtoken)) {
                    // JCExpression t = parseType();
                    // ListBuffer<JCStatement> vdefs = new
                    // ListBuffer<JCStatement>();
                    // variableDeclarators(null, t, vdefs);
                    // st = vdefs.first();
                    // accept(SEMI);
                    // utils.setJML(((JmlVariableDecl) st).mods);
                    // return st;
                } else {
                    jmlerror(S.pos(), S.endPos(), "jml.unknown.statement",
                            jtoken.internedName());
                    skipToSemi();
                    st = jmlF.at(S.pos()).Skip();
                }
            } else {
                S.nextToken(); // swallows the ENDJMLCOMMENT
                JCStatement stt = super.parseStatement();
                return stt;
            }
            S.setJmlKeyword(true);
            if (!needSemi) {
                // If we do not need a semicolon yet (e.g. because we already
                // parsed it or because the statement does not end with one,
                // then the scanner has already scanned the next symbol,
                // with setJmlKeyword having been (potentially) false.
                // So we need to do the following conversion.
                if (S.token() == Token.IDENTIFIER && S.jml) {
                    JmlToken tt = JmlToken.allTokens.get(S.name().toString());
                    if (tt != null) {
                        S.token(CUSTOM);
                        S.jmlToken = tt;
                    }
                }
            } else if (S.token() != Token.SEMI) {
                jmlerror(S.pos(), S.endPos(), "jml.bad.construct", reason);
                skipThroughSemi();
            } else {
                S.nextToken(); // skip the semi
            }
            if (S.jmlToken() == JmlToken.ENDJMLCOMMENT) S.nextToken();
            return st;
        }
        JCStatement stt = super.parseStatement();
        return stt;
    }

    /** Returns true if the token is a JML type token */
    public boolean isJmlTypeToken(JmlToken t) {
        return t == JmlToken.BSTYPEUC || t == JmlToken.BSBIGINT
                || t == JmlToken.BSREAL;
    }

    /** Parses a choose statement (the choose token is already read) */
    public JmlChoose parseChoose() {
        JmlToken jt = S.jmlToken();
        S.nextToken();
        ListBuffer<JCBlock> orBlocks = new ListBuffer<JCBlock>();
        orBlocks.append(block()); // FIXME - here and below - what if block()
                                  // returns null.
        while (S.jmlToken() == JmlToken.OR) {
            S.nextToken();
            orBlocks.append(block());
        }
        return jmlF.JmlChoose(jt, orBlocks.toList(), null);
    }

    /**
     * Parses a choose_if statement (the choose_if token is already read);
     * choose_if statements differ from choose statements in that the first
     * statement of a choose_if must be an assume statement. This is not checked
     * here. (FIXME - check for the assume?)
     */

    public JmlChoose parseChooseIf() {
        JmlToken jt = S.jmlToken();
        ListBuffer<JCBlock> orBlocks = new ListBuffer<JCBlock>();
        JCBlock elseBlock = null;
        S.nextToken();
        orBlocks.append(block());
        while (S.jmlToken() == JmlToken.OR) {
            S.nextToken();
            orBlocks.append(block());
        }
        if (S.token() == Token.ELSE) {
            S.nextToken();
            elseBlock = block();
        }
        return jmlF.JmlChoose(jt, orBlocks.toList(), elseBlock);
    }

    /**
     * Prints an AST using JmlDebugTreePrinter
     * 
     * @param t
     *            the tree to print
     * @param out
     *            the PrintStream on which to write the output
     */
    void printTree(JCTree t, PrintStream out) {
        new JmlDebugTreePrinter(out, endPositions).scan(t);
    }

    /**
     * when true we are parsing declarations within a model method or class, so
     * the individual declarations are not themselves considered JML
     * declarations even though they may be within a JML comment.
     */
    protected boolean inJmlDeclaration = false;

    /**
     * Overridden in order to parse JML declarations and clauses within the body
     * of a class or interface.
     */
    @Override
    protected List<JCTree> classOrInterfaceBodyDeclaration(Name className,
            boolean isInterface) {

        ListBuffer<JCTree> list = new ListBuffer<JCTree>();
        loop: while (true) {
            String dc = S.docComment();
            if (S.jmlToken() == ENDJMLCOMMENT) {
                S.nextToken(); // swallows the ENDJMLCOMMENT
                break loop;
            }
            S.docComment = dc;
            if (S.jml) S.setJmlKeyword(true);
            JCModifiers mods = modifiersOpt(); // Gets anything that is in
                                               // pushBackModifiers
            int pos = S.pos();
            JmlToken jt = S.jmlToken();
            if (jt == null || isJmlTypeToken(jt)) {
                pushBackModifiers = mods; // This is used to pass the modifiers
                // into super.classOrInterfaceBodyDeclaration
                mods = null;
                boolean startsInJml = S.jml;
                if (startsInJml && !inLocalOrAnonClass) {
                    boolean prevInJmlDeclaration = inJmlDeclaration;
                    inJmlDeclaration = true;
                    List<JCTree> t = super.classOrInterfaceBodyDeclaration(
                            className, isInterface);
                    inJmlDeclaration = prevInJmlDeclaration;
                    if (!inJmlDeclaration) {
                        for (JCTree tr : t) {
                            JCTree ttr = tr;
                            if (tr instanceof JmlClassDecl) {
                                JmlClassDecl d = (JmlClassDecl) tr;
                                utils.setJML(d.mods);
                                //d.toplevel.sourcefile = log.currentSourceFile();
                                ttr = toP(jmlF.at(pos).JmlTypeClauseDecl(d));
                                attach(d, dc);
                                d.docComment = dc;
                            } else if (tr instanceof JmlMethodDecl) {
                                JmlMethodDecl d = (JmlMethodDecl) tr;
                                utils.setJML(d.mods);
                                d.sourcefile = log.currentSourceFile();
                                ttr = toP(jmlF.at(pos).JmlTypeClauseDecl(d));
                                attach(d, dc);
                                d.docComment = dc;
                            } else if (tr instanceof JmlVariableDecl) {
                                JmlVariableDecl d = (JmlVariableDecl) tr;
                                utils.setJML(d.mods);
                                d.sourcefile = log.currentSourceFile();
                                ttr = toP(jmlF.at(pos).JmlTypeClauseDecl(d));
                                attach(d, dc);
                                d.docComment = dc;
                            }
                            dc = null;
                            list.append(ttr);
                        }
                    } else {
                        list.appendList(t);
                    }
                } else {
                    // no longer in JML
                    S.docComment = dc;
                    List<JCTree> t = super.classOrInterfaceBodyDeclaration(
                            className, isInterface);
                    list.appendList(t);
                }
                break;
            } else if (jt == INVARIANT || jt == INITIALLY || jt == AXIOM) {
                list.append(parseInvariantInitiallyAxiom(mods));
            } else if (jt == CONSTRAINT) {
                list.append(parseConstraint(mods));
            } else if (jt == REPRESENTS) {
                list.append(parseRepresents(mods));
            } else if (methodClauseTokens.contains(jt)
                    || specCaseTokens.contains(jt) 
                    || jt == SPEC_GROUP_START) {
                list.append(parseMethodSpecs(mods));
                S.docComment = dc;
                // getMethodSpecs may have already parsed some modifiers.
                // They will be in pushBackModifiers
            } else if (jt == IN) {
                list.append(parseIn(pos, mods));
            } else if (jt == MAPS) {
                JmlTypeClauseMaps st = parseMaps(pos, mods, list);
                if (st != null) list.append(st);
            } else if (jt == READABLE || jt == WRITABLE) {
                list.append(parseReadableWritable(mods, jt));
            } else if (jt == MONITORS_FOR) {
                list.append(parseMonitorsFor(mods));
            } else if (jt == INITIALIZER || jt == STATIC_INITIALIZER) {
                list.append(to(jmlF.at(S.pos()).JmlTypeClauseInitializer(jt)));
                S.nextToken();
            } else {
                jmlerror(S.pos(), S.endPos(),
                        "jml.illegal.token.for.declaration", jt.internedName());
                skipThroughSemi();
                break;
            }
        }
        return list.toList();
    }

    /**
     * This method runs through a list of declarations in a class body, finding
     * the JML declarations and associating them with the correct Java
     * declarations, issuing errors if they are in the wrong place.
     * 
     */
    // This is static because it is called outside the parser as well
    static public void filterTypeBodyDeclarations(JmlClassDecl decl,
            Context context, JmlTree.Maker jmlF) {
        Log log = Log.instance(context);
        List<JCTree> list = decl.defs;
        JmlSpecs.TypeSpecs typeSpecs = new JmlSpecs.TypeSpecs(decl);
        ListBuffer<JCTree> newlist = lb();
        Iterator<JCTree> iter = list.iterator();
        JmlVariableDecl currentVarDecl = null;
        JmlVariableDecl mostRecentVarDecl = null;

        while (iter.hasNext()) {
            JCTree tree = iter.next();
            mostRecentVarDecl = currentVarDecl;
            currentVarDecl = null;
            if (tree instanceof JmlVariableDecl) {
                newlist.append(tree);
                currentVarDecl = (JmlVariableDecl) tree;
            } else if (tree instanceof JmlTypeClauseIn
                    || tree instanceof JmlTypeClauseMaps) {
                /**
                 * in and maps clauses get attached to the just preceding
                 * variable declaration
                 */
                if (tree instanceof JmlTypeClauseIn)
                    ((JmlTypeClauseIn) tree).parentVar = mostRecentVarDecl;
                if (mostRecentVarDecl == null) {
                    log.error(tree.pos(), "jml.misplaced.var.spec",
                            ((JmlTypeClause) tree).token.internedName());
                } else {
                    if (mostRecentVarDecl.fieldSpecs == null) {
                        mostRecentVarDecl.fieldSpecs = new JmlSpecs.FieldSpecs(
                                mostRecentVarDecl.mods);
                    }
                    mostRecentVarDecl.fieldSpecs.list
                            .append((JmlTypeClause) tree);
                    currentVarDecl = mostRecentVarDecl;
                }
            } else if (tree instanceof JmlMethodSpecs) {
                // Method specifications come before the declaration they
                // specify.
                // They can apply to (a) a method declaration, (b) a ghost or
                // model declaration
                // (c) a JML initializer clause, or (d) a Java initializer
                // block.
                // All consecutive method spec clauses are grouped together into
                // one JmlMethodSpecs
                JmlMethodSpecs mspecs = (JmlMethodSpecs) tree;
                if (iter.hasNext()) {
                    tree = iter.next();
                    if (tree instanceof JmlMethodDecl) {
                        JmlMethodDecl mdecl = (JmlMethodDecl) tree;
                        mdecl.cases = mspecs;
                        mspecs.decl = mdecl;
                        newlist.append(mdecl);
                    } else if (tree instanceof JmlTypeClauseDecl
                            && ((JmlTypeClauseDecl) tree).decl instanceof JmlMethodDecl) {
                        JmlMethodDecl mdecl = (JmlMethodDecl) ((JmlTypeClauseDecl) tree).decl;
                        mdecl.cases = mspecs;
                        typeSpecs.clauses.append((JmlTypeClause) tree);
                    } else if (tree instanceof JmlTypeClauseInitializer) {
                        JmlTypeClauseInitializer tsp = (JmlTypeClauseInitializer) tree;
                        tsp.specs = mspecs;
                        checkInitializer(tsp, typeSpecs, context, jmlF);
                    } else if (tree instanceof JCTree.JCBlock) {
                        typeSpecs.blocks
                                .put((JCTree.JCBlock) tree,
                                        new JmlSpecs.MethodSpecs(
                                                JmlTree.Maker.instance(context)
                                                        .Modifiers(0), mspecs));
                        newlist.append(tree);
                    } else {
                        log.error(mspecs.pos(), "jml.misplaced.method.spec");
                    }
                } else {
                    log.error(mspecs.pos(), "jml.misplaced.method.spec");
                }
            } else if (tree instanceof JmlTypeClauseDecl) {
                // A ghost or model declaration within a class
                JmlTypeClauseDecl tcd = (JmlTypeClauseDecl) tree;
                tree = tcd.decl;
                if (tree instanceof JmlVariableDecl) {
                    currentVarDecl = (JmlVariableDecl) tcd.decl;
                } else if (tree instanceof JmlMethodDecl) {
                    // OK
                } else if (tree instanceof JmlClassDecl) {
                    JmlClassDecl jcd = (JmlClassDecl) tree;
                    typeSpecs.modelTypes.append(jcd);
                    // model types are their own specs
                    jcd.specsDecls = jcd;
                    tree = null; // model types are not in clauses
                    // OK
                } else {
                    log.error(tree.pos(), "jml.internal.notsobad",
                            "An unknown kind of JmlTypeClauseDecl was encountered and not handled: "
                                    + tree.getClass());
                    tree = null;
                }
                if (tree != null) typeSpecs.clauses.append(tcd);
            } else if (tree instanceof JmlTypeClause) {
                if (tree instanceof JmlTypeClauseInitializer)
                    checkInitializer((JmlTypeClauseInitializer) tree,
                            typeSpecs, context, jmlF);
                else
                    typeSpecs.clauses.append((JmlTypeClause) tree);
            } else {
                // presume that everything left is a valid Java declaration
                newlist.append(tree);
            }
        }
        typeSpecs.modifiers = decl.mods;
        typeSpecs.file = decl.source();
        typeSpecs.decl = decl;
        decl.defs = newlist.toList();
        decl.typeSpecs = typeSpecs; // The type specs from just this compilation
                                    // unit
    }

    /**
     * Checks for just one instance and one static initializer JML
     * specification, initializing the initializerSpec and staticInitializerSpec
     * fields of tspecs
     * 
     * @param tsp
     *            a initializer spec declaration from a class declaration
     * @param tspecs
     *            the typeSpecs structure for that class declaration
     */
    // @ modifies tspecs.initializerSpec, tspecs.staticInitializerSpec,
    // log.errorOutput;
    static public void checkInitializer(JmlTypeClauseInitializer tsp,
            JmlSpecs.TypeSpecs tspecs, Context context, JmlTree.Maker jmlF) {
        Log log = Log.instance(context);
        if (tsp.token == JmlToken.INITIALIZER) { // not static
            if (tspecs.initializerSpec != null) {
                log.error(tsp.pos(), "jml.one.initializer.spec.only");
            } else {
                tspecs.clauses.append(tsp);
                tspecs.initializerSpec = tsp;
                if (tsp.specs == null)
                    tsp.specs = jmlF.JmlMethodSpecs(List
                            .<JmlTree.JmlSpecificationCase> nil());
            }
        } else { // static initializer
            if (tspecs.staticInitializerSpec != null) {
                log.error(tsp.pos(), "jml.one.initializer.spec.only");
            } else {
                tspecs.clauses.append(tsp);
                tspecs.staticInitializerSpec = tsp;
                if (tsp.specs == null)
                    tsp.specs = jmlF.JmlMethodSpecs(List
                            .<JmlTree.JmlSpecificationCase> nil());
            }
        }

    }

    /** Parses a maps clause */
    public JmlTypeClauseMaps parseMaps(int pos, JCModifiers mods,
            ListBuffer<JCTree> list) {
        if (!isNone(mods))
            jmlerror(mods.getStartPosition(), mods.getPreferredPosition(),
                    getEndPos(mods), "jml.no.mods.allowed",
                    JmlToken.MAPS.internedName());
        S.setJmlKeyword(false);
        S.nextToken(); // skip over the maps token
        JCExpression e = parseMapsTarget();
        ListBuffer<JmlGroupName> glist;
        if (S.jmlToken() != JmlToken.BSINTO) {
            jmlerror(S.pos(), S.endPos(), "jml.expected",
                    "an \\into token here, or the maps target is ill-formed");
            glist = new ListBuffer<JmlGroupName>();
            S.setJmlKeyword(true);
            skipThroughSemi();
        } else {
            S.nextToken();
            glist = parseGroupNameList();
            S.setJmlKeyword(true);
            if (S.token() != Token.SEMI) {
                jmlerror(S.pos(), S.endPos(), "jml.bad.construct",
                        "maps clause");
                skipThroughSemi();
            } else {
                S.nextToken();
            }
        }
        return toP(jmlF.at(pos).JmlTypeClauseMaps(e, glist.toList()));
    }

    /** Parses the target portion (before the \\into) of a maps clause */
    public JCExpression parseMapsTarget() {
        int p = S.pos();
        if (S.token() != Token.IDENTIFIER) {
            jmlerror(S.pos(), S.endPos(), "jml.expected", "an identifier");
            skipThroughSemi();
            return toP(jmlF.at(p).Erroneous());
        }
        Name n = ident();
        JCExpression result = to(jmlF.at(p).Ident(n));
        if (S.token() == Token.LBRACKET) {
            result = parseArrayRangeExpr(result, false);
        }
        if (S.token() == Token.DOT) {
            S.nextToken();
            if (S.token() == Token.STAR) {
                S.nextToken();
                n = null;
            } else if (S.token() == Token.IDENTIFIER) {
                n = ident();
            } else {
                jmlerror(S.pos(), S.endPos(), "jml.ident.or.star.after.dot");
                skipThroughSemi();
                return toP(jmlF.at(p).Erroneous());
            }
            // Caution: Java will not expect n to be null
            // It is null to denote a wildcard selector
            result = to(jmlF.at(p).Select(result, n));
        } else if (!(result instanceof JmlStoreRefArrayRange)) {
            jmlerror(S.pos(), S.endPos(), "jml.expected",
                    "a . to select a field");
            skipThroughSemi();
            return to(jmlF.at(p).Erroneous());
        }
        return result;
    }

    /** Parses an in clause */
    public JmlTypeClauseIn parseIn(int pos, JCModifiers mods) {
        if (!isNone(mods))
            jmlerror(pos, "jml.no.mods.allowed", JmlToken.IN.internedName());
        S.setJmlKeyword(false);
        S.nextToken(); // skip over the in token
        ListBuffer<JmlGroupName> list = parseGroupNameList();
        S.setJmlKeyword(true);
        accept(SEMI);
        return toP(jmlF.at(pos).JmlTypeClauseIn(list.toList()));
    }

    /** Parses an invariant, initially, or axiom declaration */
    public JmlTypeClauseExpr parseInvariantInitiallyAxiom(JCModifiers mods) {
        int pos = S.pos();
        JmlToken jt = S.jmlToken();
        S.setJmlKeyword(false);
        S.nextToken();
        JCExpression e = parseExpression();
        S.setJmlKeyword(true);
        if (S.token() != SEMI) {
            jmlerror(S.pos(), S.endPos(), "jml.bad.construct",
                    jt.internedName() + " declaration");
            skipThroughSemi();
        } else {
            S.nextToken();
        }
        if (mods == null) mods = jmlF.at(pos).Modifiers(0);
        JmlTypeClauseExpr tcl = to(jmlF.at(pos).JmlTypeClauseExpr(mods, jt, e));
        tcl.source = log.currentSourceFile();
        return tcl;
    }

    /** Parses a represents clause */
    public JmlTypeClauseRepresents parseRepresents(JCModifiers mods) {
        S.setJmlKeyword(false);
        int pos = S.pos();
        S.nextToken();
        JCExpression id = parseStoreRef(true);
        boolean suchThat;
        JCExpression e;
        if (S.token() == Token.EQ) {
            suchThat = false;
            S.nextToken();
            e = parseExpression();
        } else if (S.jmlToken() == JmlToken.LEFT_ARROW) {
            if (isDeprecationSet() || JmlOption.isOption(context, JmlOption.STRICT)) {
                log.warning(S.pos(), "jml.deprecated.left.arrow.in.represents");
            }
            suchThat = false;
            S.nextToken();
            e = parseExpression();
        } else if (S.jmlToken() == JmlToken.BSSUCHTHAT) {
            suchThat = true;
            S.nextToken();
            e = parseExpression();
        } else {
            jmlerror(S.pos(), S.endPos(), "jml.bad.represents.token");
            e = null;
            skipToSemi();
            suchThat = false;
        }
        S.setJmlKeyword(true);
        if (e == null) { // skip
            e = jmlF.Erroneous();
        } else if (S.token() != Token.SEMI) {
            jmlerror(S.pos(), S.endPos(),
                    "jml.invalid.expression.or.missing.semi");
            skipThroughSemi();
        } else {
            S.nextToken();
        }
        if (mods == null) mods = jmlF.at(pos).Modifiers(0);
        JmlTypeClauseRepresents tcl = to(jmlF.at(pos).JmlTypeClauseRepresents(
                mods, id, suchThat, e));
        tcl.source = log.currentSourceFile();
        return tcl;
    }

    /** Parses a constraint clause */
    public JmlTypeClauseConstraint parseConstraint(JCModifiers mods) {
        int pos = S.pos();
        S.setJmlKeyword(false);
        S.nextToken();
        JCExpression e = parseExpression();
        S.setJmlKeyword(true);
        List<JmlMethodSig> sigs = null;
        if (S.token() == Token.FOR) {
            S.nextToken();
            if (S.jmlToken == JmlToken.BSEVERYTHING) {
                S.nextToken();
                // This is the default, so we just leave sigs null
            } else {
                sigs = parseMethodNameList();
            }
        }
        if (mods == null) mods = jmlF.at(pos).Modifiers(0);
        JmlTypeClauseConstraint tcl = to(jmlF.at(pos).JmlTypeClauseConstraint(
                mods, e, sigs));
        tcl.source = log.currentSourceFile();
        if (S.token() != SEMI) {
            jmlerror(S.pos(), S.endPos(), "jml.bad.construct",
                    "constraint declaration");
            skipThroughSemi();
        } else {
            S.nextToken();
        }
        return tcl;
    }

    /**
     * Parses a list of method-name; returns a possibly empty list; does not
     * parse the terminating semicolon
     */
    public List<JmlMethodSig> parseMethodNameList() {
        S.setJmlKeyword(false);
        ListBuffer<JmlMethodSig> sigs = new ListBuffer<JmlMethodSig>();
        while (true) {
            JmlMethodSig m = parseMethodName();
            if (m == null) {
                skipToCommaOrParenOrSemi();
            } else {
                sigs.append(m);
            }
            if (S.token() != COMMA) break;
            S.nextToken();
        }
        S.setJmlKeyword(true);
        return sigs.toList();
    }

    /** Parses a method-name */
    public JmlMethodSig parseMethodName() {
        int initpos = S.pos();
        int p = initpos;
        Name n = null;
        JCTree newType = null;
        if (S.token() == Token.NEW) {
            newType = parseType();
            // FIXME - check that it is a reference type
        } else if (S.token() == Token.IDENTIFIER) {
            n = ident();
        } else if (S.token() == Token.THIS) {
            n = names._this;
            S.nextToken();
        } else if (S.token() == Token.SUPER) {
            n = names._super;
            S.nextToken();
        } else {
            jmlerror(S.pos(), S.endPos(), "jml.bad.construct",
                    "constraint method");
            return null;
        }
        JCExpression id = null;
        if (newType == null) {
            id = jmlF.at(p).Ident(n);
            boolean first = true;
            while (S.token() == Token.DOT) {
                S.nextToken();
                p = S.pos();
                if (S.token() == Token.IDENTIFIER) {
                    n = ident();
                } else if (S.token() == Token.THIS) {
                    n = names._this;
                    S.nextToken();
                } else if (S.token() == Token.STAR) {
                    // * may only be the only thing after any dot, if it is
                    // present
                    if (!first) {
                        jmlerror(S.pos(), S.endPos(), "jml.expected",
                                "identifier or this, since a * may only be used after the first dot");
                    }
                    n = names.asterisk;
                    S.nextToken();
                    if (S.token() == Token.DOT) {
                        jmlerror(S.pos(), S.endPos(), "jml.expected",
                                "no dot, since a dot may not be used after a *");
                    }
                } else {
                    jmlerror(S.pos(), S.endPos(), "jml.expected",
                            "identifier or this");
                    break;
                }
                id = jmlF.at(p).Select(id, n);
                first = false;
                if (n == names.asterisk) {
                    return jmlF.at(initpos).JmlConstraintMethodSig(id, null);
                }
            }
        }
        ListBuffer<JCExpression> args = null;
        if (S.token() == Token.LPAREN) {
            args = new ListBuffer<JCExpression>();
            S.nextToken();
            if (S.token() != Token.RPAREN) {
                JCExpression arg = parseType();
                args.append(arg);
                while (S.token() == Token.COMMA) {
                    S.nextToken();
                    arg = parseType();
                    args.append(arg);
                }
                if (S.token() != RPAREN) {
                    jmlerror(S.pos(), S.endPos(), "jml.expected",
                            "comma or right parenthesis");
                } else {
                    S.nextToken();
                }
            } else {
                S.nextToken(); // consume the RPAREN
            }
        }
        return jmlF.at(initpos).JmlConstraintMethodSig(id,
                args == null ? null : args.toList());
    }

    /** Parse a readable or writable clause */
    public JmlTypeClauseConditional parseReadableWritable(JCModifiers mods,
            JmlToken token) {
        int p = S.pos();
        S.setJmlKeyword(false);
        S.nextToken();
        Name n;
        JCExpression e;
        int identPos = S.pos();
        if (S.token() != Token.IDENTIFIER) {
            jmlerror(S.pos(), S.endPos(), "jml.expected", "an identifier");
            n = names.asterisk; // place holder for an error situation
            e = jmlF.Erroneous();
        } else {
            n = ident();
            if (S.token() != Token.IF) {
                jmlerror(S.pos(), S.endPos(), "jml.expected", "an if token");
                e = jmlF.Erroneous();
            } else {
                accept(Token.IF);
                e = parseExpression();
            }
        }
        JCTree.JCIdent id = to(jmlF.at(identPos).Ident(n));
        S.setJmlKeyword(true);
        if (e.getTag() == JCTree.ERRONEOUS || S.token() != SEMI) {
            skipThroughSemi();
        } else {
            S.nextToken();
        }
        return toP(jmlF.at(p).JmlTypeClauseConditional(mods, token, id, e));
    }

    /** Parse a monitors_for clause */
    public JmlTypeClauseMonitorsFor parseMonitorsFor(JCModifiers mods) {
        int p = S.pos();
        S.setJmlKeyword(false);
        S.nextToken();
        ListBuffer<JCExpression> elist = new ListBuffer<JCExpression>();
        Name n;
        int identPos = S.pos();
        if (S.token() != Token.IDENTIFIER) {
            jmlerror(S.pos(), S.endPos(), "jml.expected", "an identifier");
            n = names.asterisk; // place holder for an error situation
        } else {
            n = ident();
            if (S.token() != Token.EQ && S.jmlToken() != JmlToken.LEFT_ARROW) {
                jmlerror(S.pos(), S.endPos(), "jml.expected",
                        "an = or <- token");
            } else {
                S.nextToken();
                elist = expressionList();
            }
        }
        JCTree.JCIdent id = to(jmlF.at(identPos).Ident(n));
        S.setJmlKeyword(true);
        if (S.token() != SEMI) {
            skipThroughSemi();
        } else {
            S.nextToken();
        }
        return toP(jmlF.at(p).JmlTypeClauseMonitorsFor(mods, id, elist.toList()));
    }

    /**
     * This parses a comma-separated list of expressions; the last expression in
     * the list parses until it can parse no more - the caller needs to check
     * that the next token is an expected token in the context, such as a right
     * parenthesis.
     * 
     * @return a ListBuffer of expressions, which may be empty or contain
     *         JCErroneous expressions if errors occurred
     */
    public ListBuffer<JCExpression> expressionList() {
        ListBuffer<JCExpression> args = lb();
        args.append(parseExpression());
        while (S.token() == COMMA) {
            S.nextToken();
            JCExpression e = parseExpression();
            args.append(e); // e might be a JCErroneous
        }
        return args;
    }

    public JCExpression parseStoreRefListExpr() {
        int p = S.pos();
        JmlToken jt = S.jmlToken();
        S.nextToken();
        accept(LPAREN);
        ListBuffer<JCExpression> list = parseStoreRefList(false);
        if (S.token() != RPAREN) {
            jmlerror(S.pos(), S.endPos(), "log.expected", "right parenthesis");
            skipThroughRightParen();
        } else {
            S.nextToken();
        }
        return toP(jmlF.at(p).JmlStoreRefListExpression(jt, list.toList()));
    }

    public JmlMethodSpecs parseMethodSpecs(JCModifiers mods) {
        // Method specifications are a sequence of specification cases
        ListBuffer<JmlSpecificationCase> cases = new ListBuffer<JmlSpecificationCase>();
        JmlSpecificationCase c;
        JmlToken t;
        int pos = S.pos();
        int lastPos = Position.NOPOS;
        while ((c = parseSpecificationCase(mods, false)) != null) {
            cases.append(c);
            lastPos = c.getEndPosition(endPositions);
            mods = modifiersOpt();
        }
        JmlMethodSpecs sp = jmlF.at(pos).JmlMethodSpecs(cases.toList());
        // end position set below
        if ((t = S.jmlToken()) == JmlToken.IMPLIES_THAT) {
            if (!isNone(mods))
                jmlerror(S.pos(), S.endPos(), "jml.no.mods.allowed",
                        t.internedName());
            S.nextToken();
            mods = modifiersOpt();
            cases = new ListBuffer<JmlSpecificationCase>();
            while ((c = parseSpecificationCase(mods, false)) != null) {
                cases.append(c);
                lastPos = c.getEndPosition(endPositions);
                mods = modifiersOpt();
            }
            if (cases.size() > 0) cases.first().also = t;
            sp.impliesThatCases = cases.toList();
        }
        if ((t = S.jmlToken()) == JmlToken.FOR_EXAMPLE) {
            if (!isNone(mods))
                jmlerror(mods.getStartPosition(),
                        mods.getEndPosition(endPositions),
                        "jml.no.mods.allowed", t.internedName());
            S.nextToken();
            mods = modifiersOpt();
            cases = new ListBuffer<JmlSpecificationCase>();
            while ((c = parseSpecificationCase(mods, true)) != null) {
                cases.append(c);
                lastPos = c.getEndPosition(endPositions);
                mods = modifiersOpt();
            }
            if (cases.size() > 0) cases.first().also = t;
            sp.forExampleCases = cases.toList();
        }
        storeEnd(sp, lastPos);
        // We may have parsed some modifiers and then found out that we are not
        // at the beginning of a spec case (perhaps at the beginning of a method
        // declaration for example). So we have to preserve the modifiers that
        // have already been parsed.
        pushBackModifiers = mods;
        // It is possible that a problem in parsing results in
        // an empty set of specification cases. That would not be legal
        // JML, but I expect that a message has been logged about it already.
        return sp;
    }

    /**
     * Returns true if no modifiers or annotations (of any kind) have been set
     * 
     * @param mods
     *            the modifiers structure to check
     * @return true if any flags or annotations are set
     */
    public boolean isNone(JCModifiers mods) {
        return mods == null
                || ((mods.flags & Flags.StandardFlags) == 0 && (mods.annotations == null || mods.annotations
                        .isEmpty()));
    }

    // [ also ] [ modifiers ] [ | behavior | normal_behavior |
    // exceptional_behavior ] [ clause ]*
    public JmlSpecificationCase parseSpecificationCase(JCModifiers mods,
            boolean exampleSection) {
        JmlToken also = null;
        JmlToken ijt = S.jmlToken();
        if (ijt == ALSO) {
            if (!isNone(mods)) {
                jmlerror(mods.getStartPosition(), S.endPos(),
                        "jml.no.mods.allowed", ijt.internedName());
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
        if (jt == JmlToken.BEHAVIOR || jt == JmlToken.NORMAL_BEHAVIOR
                || jt == JmlToken.EXCEPTIONAL_BEHAVIOR
                || (jt == JmlToken.ABRUPT_BEHAVIOR && inModelProgram)) {
            if (exampleSection) {
                log.warning(S.pos(), "jml.example.keyword", "must not",
                        jt.internedName());
            }
            S.nextToken();
        } else if (jt == JmlToken.EXAMPLE || jt == JmlToken.NORMAL_EXAMPLE
                || jt == JmlToken.EXCEPTIONAL_EXAMPLE) {
            if (!exampleSection) {
                log.warning(S.pos(), "jml.example.keyword", "must",
                        jt.internedName());
            }
            S.nextToken();
        } else if (jt == MODEL_PROGRAM) {
            JmlSpecificationCase j = parseModelProgram(mods, code, also);
            j.sourcefile = log.currentSourceFile();
            return j;
        } else if (jt == null && S.jml && also != null) {
            jmlerror(S.pos(), S.endPos(), "jml.invalid.keyword.in.spec",
                    S.stringVal());
            skipThroughSemi();
            // Call it lightweight
        } else {
            jt = null;
            if (code) log.warning(codePos, "jml.misplaced.code");
            // lightweight
        }
        
        ListBuffer<JmlMethodClause> clauses = new ListBuffer<JmlMethodClause>();
        JmlMethodClause e;
        while (S.token() == CUSTOM && (e = getClause()) != null) {
            clauses.append(e);
        }

        if (clauses.size() == 0) {
            if (jt != null) {
                jmlerror(pos, "jml.empty.specification.case");
            }
            if (also == null && !code) return null;
        }
        if (jt == null && code) code = false; // Already warned about this
        JmlSpecificationCase j = jmlF.at(pos).JmlSpecificationCase(mods, code,
                jt, also, clauses.toList());
        storeEnd(j, j.clauses.isEmpty() ? pos + 1 : getEndPos(j.clauses.last()));
        j.sourcefile = log.currentSourceFile();
        return j;
    }

    /** Issues a warning that the named construct is parsed and ignored */
    public void warnNotImplemented(int pos, String construct, String location) {
        if (JmlOption.isOption(context, JmlOption.SHOW_NOT_IMPLEMENTED))
            log.warning(pos, "jml.unimplemented.construct", construct, location);
    }

    /** Parses a model program; presumes the current token is model_program */
    public JmlSpecificationCase parseModelProgram(JCModifiers mods,
            boolean code, JmlToken also) {
        int pos = S.pos();
        S.nextToken(); // skip over the model_program token

        JCBlock stat;
        JmlSpecificationCase spc;
        try {
            inJmlDeclaration = true;
            inModelProgram = true;
            stat = block();
            spc = toP(jmlF.at(pos).JmlSpecificationCase(mods, code,
                    MODEL_PROGRAM, also, stat));
        } finally {
            inJmlDeclaration = false;
            inModelProgram = false;
        }
        return spc;
    }

    /**
     * Parses an entire specification group; the current token must be the
     * SPEC_GROUP_START and upon return the SPEC_GROUP_END will have been
     * consumed.
     * 
     * @return a JMLMethodClauseGroup AST node
     */
    public JmlMethodClauseGroup getSpecificationGroup() {
        int p = S.pos();
        ListBuffer<JmlSpecificationCase> list = new ListBuffer<JmlSpecificationCase>();
        S.nextToken();
        do {
            JmlSpecificationCase g = parseSpecificationCase(null, false);
            list.append(g);
            if (S.jmlToken() == ENDJMLCOMMENT) S.nextToken();
        } while (S.jmlToken == ALSO);
        if (S.jmlToken() == ENDJMLCOMMENT) S.nextToken();
        if (S.jmlToken != SPEC_GROUP_END) {
            jmlerror(S.pos(), S.endPos(), "jml.invalid.spec.group.end");
            while (S.jmlToken() != JmlToken.ENDJMLCOMMENT && S.token() != EOF)
                S.nextToken();
            if (S.token() != EOF) S.nextToken();
        } else {
            S.nextToken();
        }
        return toP(jmlF.at(p).JmlMethodClauseGroup(list.toList()));
    }

    /**
     * Parses a method specification clause; the current token must be the token
     * indication the kind of clause; upon return the terminating semicolon will
     * have been consumed. It is also legal for the current token to be
     * ENDJMLCOMMENT, in which case it is consumed. The
     * method returns null when no more clauses are recognized.
     * 
     * @return a JmlMethodClause AST node, or null if there is no clause
     *         recognized
     */
    public JmlMethodClause getClause() {
        String dc = S.docComment; // FIXME - do we need to do this?
        while (S.jmlToken() == ENDJMLCOMMENT) {
            S.nextToken();
            S.docComment = dc;
        }
        JmlToken jt = S.jmlToken();
        int pos = S.pos();
        S.setJmlKeyword(false);
        JmlMethodClause res = null;
        if (jt != null)
            switch (jt) {

                // The cases have to include all clause types.

                case REQUIRES:
                case ENSURES:
                case DIVERGES:
                case WHEN:
                    res = parseExprClause();
                    break;

                case SIGNALS: // signals (Exception e) parseExpression ;
                    res = parseSignals();
                    break;

                case SIGNALS_ONLY:
                    res = parseSignalsOnly();
                    break;

                case ASSIGNABLE:
                case ACCESSIBLE:
                case CAPTURES:
                    res = parseStoreRefClause();
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

                case CALLABLE:
                    warnNotImplemented(S.pos(), jt.internedName(),
                            "JmlParser.getClause()");
                    S.nextToken();
                    JmlStoreRefKeyword refkeyword = parseOptStoreRefKeyword();
                    List<JmlMethodSig> sigs = null;
                    if (refkeyword == null) {
                        sigs = parseMethodNameList();
                    }
                    S.setJmlKeyword(true);
                    accept(SEMI);
                    JmlMethodClauseCallable ec;
                    if (refkeyword != null) {
                        ec = toP(jmlF.at(pos).JmlMethodClauseCallable(
                                refkeyword));
                    } else {
                        ec = toP(jmlF.at(pos).JmlMethodClauseCallable(sigs));
                    }
                    res = ec;
                    break;

                case SPEC_GROUP_START:
                    S.setJmlKeyword(true);
                    res = getSpecificationGroup();
                    break;

                case CONTINUES:
                case BREAKS:
                case RETURNS:
                    if (!inModelProgram) {
                        jmlerror(S.pos(), S.endPos(),
                                "jml.misplaced.modelprogram.statement",
                                jt.toString());
                    }
                    res = parseExprClause();
                    // FIXME _ continues, breaks may have an optional label
                    break;

                default:
                    // For any other token we just exit this loop,
                    // WITHOUT HAVING CALLED nextToken()!!!!
                    break;

            }
        if (res != null) res.sourcefile = log.currentSourceFile();
        S.setJmlKeyword(true); // Just in case, but it is too late, since the
        // token after the semicolon is already read
        return res;
    }

    /** Parses either a \\not_specified token or a JML expression */
    public JCExpression parsePredicateOrNotSpecified() {
        if (S.jmlToken() == BSNOTSPECIFIED) {
            int pos = S.pos();
            S.nextToken();
            return toP(jmlF.at(pos).JmlSingleton(BSNOTSPECIFIED));
        } else {
            return parseExpression();
        }
    }

    /**
     * Parses a method specification clause that takes a
     * predicate-or-not-specified argument
     * 
     * @return the parsed JmlMethodClause
     */
    public JmlMethodClauseExpr parseExprClause() {
        JmlToken jt = S.jmlToken();
        int pos = S.pos();
        S.nextToken();
        JCExpression e = parsePredicateOrNotSpecified();
        S.setJmlKeyword(true);
        if (S.token() != Token.SEMI) {
            syntaxError(S.pos(), null, "jml.invalid.expression.or.missing.semi");
            skipThroughSemi();
        } else {
            S.nextToken(); // skip SEMI
        }
        JmlMethodClauseExpr cl = jmlF.at(pos).JmlMethodClauseExpr(jt, e);
        return toP(cl);
    }

    /**
     * Parses a signals method specification clause
     * 
     * @return the parsed JmlMethodClause
     */
    public JmlMethodClauseSignals parseSignals() {
        JmlToken jt = S.jmlToken();
        int pos = S.pos();
        JCExpression e;
        S.nextToken();
        JCExpression t = null;
        Name ident = null;
        int rpos = pos;
        if (S.token() != Token.LPAREN) {
            syntaxError(S.pos(), null, "jml.expected.lparen.signals");
            t = to(jmlF.at(S.pos()).Ident(names.fromString("java")));
            t = to(jmlF.at(S.pos()).Select(t, names.fromString("lang")));
            t = to(jmlF.at(S.pos()).Select(t, names.fromString("Exception")));
            e = parsePredicateOrNotSpecified();
        } else {
            S.nextToken();
            // Get type
            t = parseType();
            // Get identifier (optional)
            if (S.token() == IDENTIFIER) {
                ident = ident();
            }
            rpos = S.pos();
            if (S.token() != Token.RPAREN) {
                syntaxError(S.pos(), null, "jml.expected.rparen.signals");
                skipToSemi();
                e = toP(jmlF.at(S.pos()).Erroneous());
            } else {
                S.nextToken();
                if (S.token() == Token.SEMI) {
                    e = toP(jmlF.at(S.pos()).Literal(TypeTags.BOOLEAN, 1)); // Boolean.TRUE));
                } else {
                    e = parsePredicateOrNotSpecified();
                }
            }
        }
        S.setJmlKeyword(true);
        JCTree.JCVariableDecl var = jmlF.at(t.pos).VarDef(
                jmlF.at(t.pos).Modifiers(0), ident, t, null);
        storeEnd(var, rpos);
        if (S.token() != Token.SEMI) {
            if (e.getKind() != Kind.ERRONEOUS)
                syntaxError(S.pos(), null, "jml.missing.semi");
            skipThroughSemi();
        } else {
            S.nextToken();
        }
        return toP(jmlF.at(pos).JmlMethodClauseSignals(jt, var, e));
    }

    /**
     * Parses a signals_only clause. The current token must be the signals_only
     * token; upon return the terminating semicolon will have been parsed.
     * 
     * @return a JmlMethodClauseSignalsOnly AST node
     */
    public JmlMethodClauseSignalsOnly parseSignalsOnly() {
        JmlToken jt = S.jmlToken();
        int pos = S.pos();
        S.nextToken();
        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();

        if (S.jmlToken() == BSNOTHING) {
            S.setJmlKeyword(true);
            S.nextToken();
            if (S.token() != SEMI) {
                syntaxError(S.pos(), null, "jml.expected.semi.after.nothing");
                skipThroughSemi();
            } else {
                S.nextToken();
            }
        } else if (S.token() == SEMI) {
            S.setJmlKeyword(true);
            syntaxError(S.pos(), null, "jml.use.nothing", jt.internedName());
            S.nextToken();
        } else {
            while (true) {
                JCExpression typ = parseType(); // if this fails, a JCErroneous
                // is returned
                list.append(typ);
                if (S.token() == SEMI) {
                    S.setJmlKeyword(true);
                    S.nextToken();
                    break;
                } else if (S.token() == COMMA) {
                    S.nextToken();
                    continue;
                } else if (typ instanceof JCErroneous) {
                    S.setJmlKeyword(true);
                    skipThroughSemi();
                    break;
                } else if (S.jmlToken() == ENDJMLCOMMENT) {
                    syntaxError(S.pos(), null, "jml.missing.semi");
                } else {
                    syntaxError(S.pos(), null, "jml.missing.comma");
                    continue;
                }
                // error
                S.setJmlKeyword(true);
                skipThroughSemi();
                break;
            }
        }
        return toP(jmlF.at(pos).JmlMethodClauseSignalsOnly(jt, list.toList()));
    }

    public JmlMethodClauseDecl parseForallOld() {
        int pos = S.pos();
        JmlToken jt = S.jmlToken();
        S.nextToken();
        // non_null and nullable and perhaps other type modifiers in the
        // future are allowed
        JCModifiers mods = modifiersOpt();
        JCExpression t = parseType();
        boolean prev = inJmlDeclaration;
        inJmlDeclaration = true; // allows non-ghost declarations
        ListBuffer<JCTree.JCVariableDecl> decls = variableDeclarators(mods, t,
                new ListBuffer<JCVariableDecl>());
        inJmlDeclaration = prev;
        JmlMethodClauseDecl res = to(jmlF.at(pos)
                .JmlMethodClauseDecl(jt, decls.toList()));
        S.setJmlKeyword(true);
        if (S.token() == Token.SEMI) {
            S.nextToken();
        } else {
            jmlerror(S.pos(), S.endPos(), "jml.bad.construct",
                    jt.internedName() + " specification");
            skipThroughSemi();
        }
        return res;
    }

    /**
     * Parses (duration|working_space|?) (<expression>|"\\not_specified") [ "if"
     * <expression> ] ";"
     */
    public JmlMethodClauseConditional parseDurationEtc() {
        int pos = S.pos();
        JmlToken jt = S.jmlToken();
        JCExpression p = null;
        S.nextToken();
        JCExpression e = parsePredicateOrNotSpecified();
        if (S.token() == Token.IF) { // The if is not allowed if the
            // expression is not_specified, but we test that
            // during type checking
            S.nextToken();
            p = parseExpression();
        }
        JmlMethodClauseConditional res = to(jmlF.at(pos)
                .JmlMethodClauseConditional(jt, e, p));
        S.setJmlKeyword(true);
        if (S.token() == Token.SEMI) {
            S.nextToken();
        } else {
            jmlerror(S.pos(), S.endPos(), "jml.bad.construct",
                    jt.internedName() + " specification");
            skipThroughSemi();
        }
        return res;
    }

    /** Parses "assignable" <store-ref-list> ";" */
    public JmlMethodClauseStoreRef parseStoreRefClause() {
        JmlToken jt = S.jmlToken();
        int pos = S.pos();
        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
        S.nextToken(); // skip over the assignable token
        if (S.token() == SEMI) {
            syntaxError(S.pos(), null, "jml.use.nothing.assignable");
            S.setJmlKeyword(true);
            S.nextToken(); // skip over the SEMI
        } else {
            list = parseStoreRefList(false);
            if (S.token() == SEMI) {
                // OK, go on
            } else if (S.jmlToken() == ENDJMLCOMMENT) {
                syntaxError(S.pos(), null, "jml.missing.semi");
            }
            S.setJmlKeyword(true);
            if (S.token() != SEMI) {
                // error already reported
                skipThroughSemi();
            } else {
                if (list.isEmpty()) {
                    syntaxError(S.pos(), null, "jml.use.nothing.assignable");
                }
                S.nextToken();
            }
        }
        return toP(jmlF.at(pos).JmlMethodClauseStoreRef(jt, list.toList()));
    }

    /**
     * Parses ("\|nothing"|"\\everything"|"\\not_specified"| <store-ref> [ ","
     * <store-ref> ]* ) ";" <BR>
     * a store-ref is a JCIdent, a JCSelect (potentially with a null field), or
     * a JmlStoreRefArrayRange; there may be more than one use of a
     * JmlStoreRefArrayRange, e.g. a[2..3][4..5] or a.f[4..5].g[6..7]
     * 
     * @param strictId
     *            if true, keywords and wildcards are not allowed
     * @return list of zero or more store-refs or a list of one
     *         store-ref-keyword;
     */
    public ListBuffer<JCExpression> parseStoreRefList(boolean strictId) {
        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
        if (!strictId) {
            JCExpression s = parseOptStoreRefKeyword();
            if (s != null) {
                list.append(s);
                return list;
            }
        }
        while (true) {
            JCExpression r = parseStoreRef(false);
            if (r != null) list.append(r);
            if (S.token() == COMMA) {
                S.nextToken();
                continue;
            } else if (S.token() == SEMI || S.token() == RPAREN) {
                return list;
            } else if (S.jmlToken == ENDJMLCOMMENT) {
                // The missing semi-colon is reported by the caller
                return list;
            } else {
                syntaxError(S.pos(), null, "jml.missing.comma");
                if (r == null) return list;
            }
        }
    }

    /** Parses a storeRefKeyword or returns null (with no error message) */
    public JmlStoreRefKeyword parseOptStoreRefKeyword() {
        JmlToken jt = S.jmlToken();
        int p = S.pos();
        if (jt == BSNOTHING || jt == BSEVERYTHING || jt == BSNOTSPECIFIED) {
            JmlStoreRefKeyword s = to(jmlF.at(p).JmlStoreRefKeyword(jt));
            S.nextToken();
            return s;
        }
        return null;
    }

    /**
     * Parses (<informal-comment>| (<identifier>|"this"|"super") [ "." "*" | "."
     * <identifier> | <array-range-expr> ]* ) except that "this" or "super" must
     * have something following them.
     * 
     * @param strictId
     *            if true, no informal comments or wildcards are allowed
     * @return a JCExpression or JmlStoreRefKeyword
     */
    public/* @ nullable */JCExpression parseStoreRef(boolean strictId) {
        JCExpression ss = parseStoreRefInit(strictId);
        if (ss instanceof JmlStoreRefKeyword)
            return ss;
        else {
            JCExpression e = ss;
            while (true) {
                if (S.token() == Token.DOT) {
                    int dotpos = S.pos();
                    S.nextToken();
                    if (!strictId && S.token() == Token.STAR) {
                        S.nextToken();
                        // Caution: Java will not expect the field selector to
                        // be null
                        e = toP(jmlF.at(dotpos).Select(e, (Name) null));
                        if (S.token() != Token.COMMA && S.token() != Token.SEMI
                                && S.token() != Token.RPAREN) {
                            jmlerror(S.pos(), S.endPos(), "jml.not.after.star");
                            skipToCommaOrSemi();
                        }
                        break;
                    } else if (S.token() == Token.IDENTIFIER) {
                        Name n = ident();
                        e = to(jmlF.at(dotpos).Select(e, n));
                        continue;
                    } else {
                        if (strictId)
                            jmlerror(S.pos(), S.endPos(), "jml.expected.id");
                        else
                            jmlerror(S.pos(), S.endPos(),
                                    "jml.ident.or.star.after.dot");
                        skipToCommaOrSemi();
                        break;
                    }

                } else if (S.token() == Token.LBRACKET) {
                    e = parseArrayRangeExpr(e, strictId);
                } else {
                    break;
                }
            }
            if (e instanceof JCIdent) {
                if (((JCIdent) e).name == names._this
                        || ((JCIdent) e).name == names._super) {
                    log.error(e.pos(), "jml.naked.this.super");
                    // A standalone this or super is not allowed. We state the
                    // error but the parse tree is this.* or super.*
                    e = to(jmlF.at(e.pos).Select(e, (Name) null));
                }
            }
            ss = e;
        }
        return ss;
    }

    /**
     * Parses the initial part of a store-ref:
     * (<informal-comment>|<identifier>|"this"|"super")
     * 
     * @param strictId
     *            when true, only store-refs that start with identifiers, this,
     *            or super are allowed
     * @return an AST for the parsed code
     */
    // @ ensures \result == null || \result instanceof JmlStoreRefKeyword ||
    // \result instanceof JCIdent;
    protected JCExpression parseStoreRefInit(boolean strictId) {
        JmlToken jt = S.jmlToken;
        int p = S.pos();
        if (!strictId && (jt == INFORMAL_COMMENT)) {
            JCExpression s = to(jmlF.at(p).JmlStoreRefKeyword(jt));
            S.nextToken();
            return s;
        } else if (S.token() == Token.IDENTIFIER) {
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
        jmlerror(p, S.endPos(), "jml.bad.store.ref");
        skipToCommaOrSemi();
        return null;
    }

    /**
     * Parses [ "[" ( "*" | <expression> | <expression> ".." "*" | <expression>
     * ".." | <expression> ".." <expression> ) "]" ]*
     * 
     * @param t
     *            the leading expression for which the array index or range is a
     *            suffix
     * @param strictId
     *            if true, no wildcards or ranges are allowed
     * @return an AST for the parsed code
     */
    protected JCExpression parseArrayRangeExpr(JCExpression t, boolean strictId) {
        while (S.token() == Token.LBRACKET) {
            S.nextToken(); // move past the LBRACKET
            if (!strictId && S.token() == Token.STAR) {
                S.nextToken();
                if (S.token() == Token.RBRACKET) {
                    S.nextToken();
                    t = toP(jmlF.at(t.pos).JmlStoreRefArrayRange(t, null, null));
                    continue;
                } else {
                    jmlerror(S.pos(), S.endPos(), "jml.expected.rbracket.star");
                    skipToCommaOrSemi();
                    break;
                }
            } else {
                JCExpression lo = parseExpression();
                if (S.token() == Token.RBRACKET) {
                    t = to(jmlF.at(t.pos).JmlStoreRefArrayRange(t, lo, lo));
                    S.nextToken();
                    continue;
                } else if (!strictId && S.jmlToken() == DOT_DOT) {
                    S.nextToken();
                    JCExpression hi = null;
                    int rbracketPos = S.pos();
                    if (S.token() == STAR) {
                        S.nextToken();
                    } else if (S.token() == Token.RBRACKET) {
                        if (JmlOption.isOption(context, JmlOption.STRICT)) {
                            log.warning(rbracketPos,"jml.not.strict","storeref with implied end-of-range (a[i..])");
                        }
                        // OK - missing hi end implies end of array
                    } else {
                        hi = parseExpression();
                    }
                    if (S.token() == Token.RBRACKET) {
                        t = to(jmlF.at(t.pos).JmlStoreRefArrayRange(t, lo, hi));
                        S.nextToken();
                    } else {
                        jmlerror(S.pos(), S.endPos(), "jml.expected.rbracket");
                        skipToCommaOrSemi();
                        break;
                    }
                    continue;
                } else {
                    jmlerror(S.pos(), S.endPos(),
                            "jml.invalid.expression.succeeding.token");
                    skipToCommaOrSemi();
                    break;
                }
            }
        }
        return t;
    }

    protected JCModifiers pushBackModifiers = null;

    /**
     * Overridden so that anything in 'pushBackModifiers' is incorporated into
     * the result of the call
     * 
     * @return combination of 'pushBackModifiers' and any modifiers that are
     *         next in the token string
     */
    @Override
    protected JCModifiers modifiersOpt() {
        JCModifiers partial = pushBackModifiers;
        pushBackModifiers = null;
        return modifiersOpt(partial);
    }

    /**
     * Combines 'pushBackModifiers', the argument and any modifiers that are
     * next in the token string (including JML modifiers)
     * 
     * @return combination of 'pushBackModifiers' and any modifiers that are
     *         next in the token string
     */
    @Override
    protected JCModifiers modifiersOpt(JCModifiers partial) {
        if (partial == null) {
            partial = pushBackModifiers;
            pushBackModifiers = null;
        } else if (pushBackModifiers != null) {
            jmlerror(
                    S.pos(),
                    S.endPos(),
                    "jml.internal.notsobad",
                    "This code branch in modifiersOpt() is not expected to be executed and is not fully implemented - please report with code samples");
            // I don't think this is ever executed. If it is we need to check
            // that
            // there is no duplication of modifiers.
            long flags = partial.flags | pushBackModifiers.flags;
            // long same = (partial.flags & pushBackModifiers.flags);
            ListBuffer<JCAnnotation> annotations = new ListBuffer<JCAnnotation>();
            annotations.appendList(pushBackModifiers.annotations);
            annotations.appendList(partial.annotations);
            partial = jmlF.at(pushBackModifiers.pos()).Modifiers(flags,
                    annotations.toList());
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

    /**
     * Converts a token to an annotation expression, or to null if there is no
     * corresponding annotation.
     * 
     * @param jt
     *            the input token
     * @param position
     *            the character position
     * @return the annotation expression
     */
    protected/* @ nullable */JCAnnotation tokenToAnnotationAST(JmlToken jt,
            int position, int endpos) {
        Class<?> c = jt.annotationType;
        if (c == null) return null;
        JCExpression t = to(F.at(position).Ident(names.fromString("org")));
        t = to(F.at(position).Select(t, names.fromString("jmlspecs")));
        t = to(F.at(position).Select(t, names.fromString("annotation")));
        t = to(F.at(position).Select(t, names.fromString(c.getSimpleName())));
        JCAnnotation ann = to(F.at(position).Annotation(t,
                List.<JCExpression> nil()));
        storeEnd(ann, endpos);
        return ann;
    }

    /**
     * Reads any JML modifiers, combining them with the input to produce a new
     * JCModifiers object
     * 
     * @param partial
     *            input modifiers and annotations
     * @return combined modifiers and annotations
     */
    protected JCModifiers jmlModifiersOpt(JCModifiers partial) {
        ListBuffer<JCAnnotation> annotations = new ListBuffer<JCAnnotation>();
        if (partial != null) annotations.appendList(partial.annotations);
        int pos = Position.NOPOS;
        int last = Position.NOPOS;
        if (partial != null) {
            pos = partial.pos;
        }
        JmlToken j;
        while ((j = S.jmlToken()) != null) {
            if (JmlToken.modifiers.contains(j)) {
                last = S.endPos();
                JCAnnotation a = tokenToAnnotationAST(j, S._pos, last);
                if (a != null) {
                    annotations.append(a);
                    if (pos == Position.NOPOS) pos = a.getStartPosition();
                }
                // a is null if no annotation is defined for the modifier;
                // we just silently ignore that situation
                // (this is true at the moment for math annotations, but could
                // also be true for a modifier someone forgot)
                if (JmlToken.extensions.contains(j) && JmlOption.isOption(context, JmlOption.STRICT)) {
                    log.warning(S._pos,"jml.not.strict",j.internedName());
                }
            } else if (j == ENDJMLCOMMENT) {
                // skip over
            } else if (j == CONSTRUCTOR || j == FIELD || j == METHOD) {
                // FIXME - do we want to save this anywhere; check that it
                // matches the declaration; check that it is not used on
                // something other than a declaration?
                // Also setJmlKeyword back to true
                S.setJmlKeyword(false);
            } else {
                // Not a modifier
                break;
            }
            S.nextToken();
        }
        JCModifiers mods = F.at(pos).Modifiers(
                partial == null ? 0 : partial.flags, annotations.toList());
        if (last != Position.NOPOS) storeEnd(mods, last);
        return mods;
    }

    @Override
    public JCPrimitiveTypeTree basicType() {
        JmlToken jt = S.jmlToken();
        if (jt == null) {
            return super.basicType();
        } else if (jt == JmlToken.BSTYPEUC || jt == JmlToken.BSBIGINT
                || jt == JmlToken.BSREAL) {
            JCPrimitiveTypeTree t = to(jmlF.at(S.pos())
                    .JmlPrimitiveTypeTree(jt));
            S.nextToken();
            return t;
        } else {
            jmlerror(S.pos(), S.endPos(), "jml.expected", "JML type token");
            JCPrimitiveTypeTree t = to(F.at(S.pos()).TypeIdent(
                    typetag(Token.VOID)));
            S.nextToken();
            return t;
        }
    }
    
    @Override
    protected Name ident() {
        if (S.token() == Token.CUSTOM) {
            jmlerror(S.pos(),S.endPos(),"jml.keyword.instead.of.ident",S.jmlToken.internedName());
            S.nextToken();
            return names.error;
        } else {
            return super.ident();
        }
    }


    // Have to replicate this method because we cannot just add the JML
    // operators into the token set for the Java operators.
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
        if ((mode & EXPR) != 0
                && (S.jmlToken() == JmlToken.EQUIVALENCE || S.jmlToken() == JmlToken.INEQUIVALENCE)) {
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
        if ((mode & EXPR) != 0
                && (S.jmlToken() == JmlToken.IMPLIES || S.jmlToken() == JmlToken.REVERSE_IMPLIES)) {
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
                syntaxError(S.pos(), null, "jml.mixed.implies");
                skipToSemi();
            }
        } else if (jt == JmlToken.REVERSE_IMPLIES) {
            // For REVERSE_IMPLIES we do the conventional association to the
            // left
            do {
                int ppos = S.pos(); // position of the operator
                S.nextToken();
                JCExpression tt = term2();
                t = toP(jmlF.at(ppos).JmlBinary(jt, t, tt));
                jt = S.jmlToken();
            } while (jt == JmlToken.REVERSE_IMPLIES);
            if (jt == JmlToken.IMPLIES) {
                syntaxError(S.pos(), null, "jml.mixed.implies");
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
        // No JML function expects type arguments. If they did we would parse
        // them here (before seeing the JML token). But we can't do that just
        // to check, because super.term3() down below expects to parse them
        // itself. So if someone does write type arguments for a JML function
        // the code will fall into the super.term3() call and the token will not
        // be recognized - no chance for a nice error message.
        if (S.token() == Token.CUSTOM) {
            JCExpression t;
            JmlToken jt = S.jmlToken();
            int p = S.pos(); // Position of the keyword

            if (isJmlTypeToken(jt)) {
                t = to(jmlF.at(p).JmlPrimitiveTypeTree(jt));
                S.nextToken();
                t = bracketsSuffix(bracketsOpt(t));
                return t;
            }
            switch (jt) {
                case BSEXCEPTION:// FIXME - what can follow this?
                case BSINDEX:
                case BSVALUES:// FIXME - what can follow this?
                    if (JmlOption.isOption(context,JmlOption.STRICT)) {
                        log.warning(p,"jml.not.strict",jt.internedName());
                    }
                case BSRESULT:// FIXME - what can follow this?
                case BSLOCKSET: // FIXME - what can follow this?
                    t = to(jmlF.at(p).JmlSingleton(jt));
                    S.nextToken();
                    if (S.token() == Token.LPAREN) {
                        JCExpression res = syntaxError(S.pos(), null,
                                "jml.no.args.allowed", jt.internedName());
                        primarySuffix(t, typeArgs); // Parse arguments and
                        // ignore, both to do as much
                        // type checking as possible and to skip valid
                        // constructs to avoid extra errors
                        return res;
                    } else {
                        return primarySuffix(t, typeArgs);
                    }

                case BSSAME:
                    t = to(jmlF.at(p).JmlSingleton(jt));
                    S.nextToken();
                    return t;

                case INFORMAL_COMMENT:
                    t = to(jmlF.at(p).JmlSingleton(jt));
                    ((JmlSingleton) t).info = S.stringVal();
                    S.nextToken();
                    return t;

                case BSTYPELC:
                    int start = S.pos();
                    S.nextToken();
                    p = S.pos();
                    if (S.token() != Token.LPAREN) {
                        return syntaxError(p, List.<JCTree> nil(),
                                "jml.args.required", jt);
                    } else {
                        accept(Token.LPAREN);
                        JCExpression e;
                        if (S.token() == Token.VOID) {
                            e = to(F.at(S.pos()).TypeIdent(TypeTags.VOID));
                            S.nextToken();
                        } else {
                            e = parseType();
                        }
                        if (S.token() != Token.RPAREN) {
                            if (!(e instanceof JCErroneous))
                                jmlerror(S.pos(), S.endPos(),
                                        "jml.bad.bstype.expr");
                            skipThroughRightParen();
                        } else
                            S.nextToken();
                        // FIXME - this should be a type literal
                        e = toP(jmlF.at(p).JmlMethodInvocation(jt, List.of(e)));
                        ((JmlMethodInvocation)e).startpos = start;
                        return primarySuffix(e, null);
                    }

                case BSNONNULLELEMENTS:
                case BSMAX:
                case BSFRESH:
                case BSREACH:
                case BSSPACE:
                case BSWORKINGSPACE:
                case BSDISTINCT:
                case BSDURATION:
                case BSISINITIALIZED:
                case BSINVARIANTFOR:
                    int startx = S.pos();
                    S.nextToken();
                    if (S.token() != Token.LPAREN) {
                        if (jt == BSMAX) {
                            return parseQuantifiedExpr(p, jt);
                        }
                        return syntaxError(p, null, "jml.args.required",
                                jt.internedName());
                    } else {
                        int preferred = S.pos();
                        List<JCExpression> args = arguments();
                        JCExpression te = jmlF.at(preferred).JmlMethodInvocation(
                                jt, args);
                        ((JmlMethodInvocation)te).startpos = startx;
                        te = toP(te);
                        if (jt == BSREACH || jt == BSMAX) {
                            te = primaryTrailers(te, null);
                        }
                        return te;
                    }

                case BSELEMTYPE:
                case BSTYPEOF:
                case BSPAST:
                case BSOLD:
                case BSPRE:
                case BSNOWARN:
                case BSNOWARNOP:
                case BSWARN:
                case BSWARNOP:
                case BSBIGINT_MATH:
                case BSSAFEMATH:
                case BSJAVAMATH:
                    ExpressionExtension ne = Extensions.instance(context).find(S.pos(),
                            jt);
                    if (ne == null) {
                        jmlerror(S.pos(), S.endPos(), "jml.no.such.extension",
                                jt.internedName());
                        return jmlF.at(S.pos()).Erroneous();
                    } else {
                        return ne.parse(this, typeArgs);
                    }

                case BSNOTMODIFIED:
                case BSNOTASSIGNED:
                case BSONLYACCESSED:
                case BSONLYCAPTURED:
                case BSONLYASSIGNED:
                    return parseStoreRefListExpr();

                case BSFORALL:
                case BSEXISTS:
                case BSPRODUCT:
                case BSSUM:
                case BSNUMOF:
                case BSMIN:
                    S.nextToken();
                    return parseQuantifiedExpr(p, jt);

                case NONNULL:
                case NULLABLE:
                case BSPEER:
                case BSREADONLY:
                case BSREP:
                case READONLY:
                    S.nextToken();
                    warnNotImplemented(S.pos(), jt.internedName(),
                            "JmlParser.term3(), as type modifiers");

                    // FIXME - ignoring these type modifiers for now
                    return term3();

                case BSLBLANY:
                case BSLBLNEG:
                case BSLBLPOS:
                    S.nextToken();
                    return parseLblExpr(p, jt);

                case BSLET:
                    S.nextToken();
                    return parseLet(p);
                    
                case BSONLYCALLED:
                    warnNotImplemented(S.pos(), jt.internedName(),
                            "\\only_called");
                    S.nextToken();
                    if (S.token() != LPAREN) {
                        accept(LPAREN); // fails
                        skipThroughRightParen();
                    } else {
                        accept(LPAREN);
                        parseMethodNameList();
                        if (S.token() != RPAREN) {
                            accept(RPAREN); // fails
                            skipThroughRightParen();
                        } else {
                            accept(RPAREN);
                        }
                    }
                    // FIXME - needs implementation
                    return toP(jmlF.at(p).Erroneous());

                default:
                    jmlerror(p, S.endPos(), "jml.bad.type.expression",
                            "( token " + jt.internedName()
                                    + " in JmlParser.term3())");
                    return toP(jmlF.at(p).Erroneous());
            }
        }
        return toP(super.term3());
    }

    protected boolean inCreator = false;

    public JCExpression parseQuantifiedExpr(int pos, JmlToken jt) {
        JCModifiers mods = modifiersOpt();
        JCExpression t = parseType();
        if (t.getTag() == JCTree.ERRONEOUS) return t;
        if (mods.pos == -1) {
            mods.pos = t.pos; // set the beginning of the modifiers
            storeEnd(mods,t.pos);
        }
                                              // modifiers
        // to the beginning of the type, if there
        // are no modifiers
        ListBuffer<JCVariableDecl> decls = new ListBuffer<JCVariableDecl>();
        int idpos = S.pos();
        Name id = ident(); // FIXME JML allows dimensions after the ident
        decls.append(toP(jmlF.at(idpos).VarDef(mods, id, t, null)));
        while (S.token() == COMMA) {
            S.nextToken();
            idpos = S.pos();
            id = ident(); // FIXME JML allows dimensions after the ident
            decls.append(toP(jmlF.at(idpos).VarDef(mods, id, t, null)));
        }
        if (S.token() != SEMI) {
            jmlerror(S.pos(), S.endPos(), "jml.expected.semicolon.quantified");
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
            pred = parseExpression();
        } else {
            range = parseExpression();
            if (S.token() == SEMI) {
                // type id ; range ; predicate
                S.nextToken();
                pred = parseExpression();
            } else if (S.token() == RPAREN) {
                // type id ; predicate
                pred = range;
                range = null;
            } else {
                jmlerror(S.pos(), S.endPos(),
                        "jml.expected.semicolon.quantified");
                int p = S.pos();
                skipThroughRightParen();
                return toP(jmlF.at(p).Erroneous());
            }
        }
        JmlQuantifiedExpr q = toP(jmlF.at(pos).JmlQuantifiedExpr(jt, decls.toList(),
                range, pred));
        return q;
    }

    // MAINTENANCE ISSUE:
    // This is a copy from JavacParser, so we can add in parseSetComprehension
    JCExpression creator(int newpos, List<JCExpression> typeArgs) {
        switch (S.token()) {
            case BYTE:
            case SHORT:
            case CHAR:
            case INT:
            case LONG:
            case FLOAT:
            case DOUBLE:
            case BOOLEAN:
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
            t = typeArguments(t,false); // FIXME - true or false:
        }
        while (S.token() == DOT) {
            int pos = S.pos();
            S.nextToken();
            t = toP(F.at(pos).Select(t, ident()));
            if (S.token() == LT) {
                checkGenerics();
                t = typeArguments(t,false); // FIXME - true or false:
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
                syntaxError(pos, null,
                        "cannot.create.array.with.type.arguments");
                return toP(F.at(newpos).Erroneous(typeArgs.prepend(e)));
            }
            return e;
        } else if (S.token() == LPAREN) {
            boolean prev = inLocalOrAnonClass;
            try {
                inLocalOrAnonClass = true;
                JCNewClass anon = classCreatorRest(newpos, null, typeArgs, t);
                if (anon.def != null) {
                    filterTypeBodyDeclarations((JmlClassDecl) anon.def, context,
                            jmlF);
                }
                return anon;
            } finally {
                inLocalOrAnonClass = prev;
            }
        } else if (S.token() == LBRACE) {
            return parseSetComprehension(t);
        } else {
            // FIXME - what is expected3 here?
            syntaxError(S.pos(), null, "expected3", "\'(\'", "\'{\'", "\'[\'");
            t = toP(F.at(newpos).NewClass(null, typeArgs, t,
                    List.<JCExpression> nil(), null));
            return toP(F.at(newpos).Erroneous(List.<JCTree> of(t)));
        }
    }
    
    protected boolean inLocalOrAnonClass = false;

    /**
     * Parses: <identifier> <expression>
     * 
     * @param pos
     *            character position of the lbl token
     * @param jmlToken
     *            either the LBLPOS or LBLNEG token
     * @return a JmlLblExpression
     */
    protected JCExpression parseLblExpr(int pos, JmlToken jmlToken) {
        // The JML token is already scanned
        // pos is the position of the \lbl token
        int labelPos = S.pos();
        Name n = ident();
        JCExpression e = parseExpression();
        if (jmlToken == JmlToken.BSLBLANY && JmlOption.isOption(context,JmlOption.STRICT)) {
            log.warning(pos,"jml.not.strict","\\lbl");
        }
        return toP(jmlF.at(pos).JmlLblExpression(labelPos,jmlToken, n, e));
    }
    
    public JCExpression parseLet(int pos) {
        ListBuffer<JCVariableDecl> vdefs = new ListBuffer<JCVariableDecl>();
        do {
            int pm = S.pos();
            JCModifiers mods = jmlF.Modifiers(0); // FIXME - there are some modifiers allowed?
            if (mods.pos == -1) {
                mods.pos = pm;
                storeEnd(mods,pm);
            }
            JCExpression type = parseType();
            int p = S.pos();
            Name name = ident();
            JCVariableDecl decl = variableDeclaratorRest(pos,mods,type,name,true,null);
            decl.pos = p;
            if (decl.init == null) toP(decl);
            vdefs.add(decl);
            if (S.token() != COMMA) break;
            accept(COMMA);
        } while (true);
        accept(SEMI);
        JCExpression expr = parseExpression();
        return toP(jmlF.at(pos).LetExpr(vdefs.toList(),expr));
    }

    /** Parses: "{" [ <modifiers> ] <type> <identifier> "|" <expression> "}" */
    public JCExpression parseSetComprehension(JCExpression type) {
        JCExpression sc = null;
        int begin = S.pos();
        if (S.token() != LBRACE) {
            accept(LBRACE); // fails
        } else {
            accept(LBRACE);
            JCModifiers mods = modifiersOpt();
            int tpos = S.pos();
            JCTree.JCExpression t = parseType();
            if (t != null && !(t instanceof JCErroneous)) {
                Name n = ident();
                if (n != names.error) {
                    JCTree.JCVariableDecl v = toP(jmlF.at(tpos).VarDef(mods, n,
                            t, null));
                    if (S.token() != BAR) {
                        accept(BAR); // fails
                    } else {
                        accept(BAR);
                        JCExpression predicate = parseExpression();
                        if (predicate != null
                                && !(predicate instanceof JCErroneous)) {
                            if (S.token() != RBRACE) {
                                accept(RBRACE); // fails
                            } else {
                                accept(RBRACE);
                                sc = toP(jmlF.at(begin).JmlSetComprehension(
                                        type, v, predicate));
                            }
                        }
                    }
                }
            }
        }
        if (sc == null) {
            skipThroughRightBrace();
            sc = jmlF.Erroneous();
        }
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

    /** Parses: [ "this" "." | "super" "." ] <identifier> */
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
        if (t == null)
            t = toP(jmlF.at(p).Ident(n));
        else
            t = toP(jmlF.at(p).Select(t, n));
        return toP(jmlF.at(p).JmlGroupName(t));
    }

    /** Overridden in order to absorb the pushBackModifiers */
    @Override
    public <T extends ListBuffer<? super JCVariableDecl>> T variableDeclarators(
            JCModifiers mods, JCExpression type, T vdefs) {
        if (pushBackModifiers != null && isNone(mods)) {
            mods = pushBackModifiers;
            pushBackModifiers = null;
        }
        T t = variableDeclaratorsRest(S.pos(), mods, type, ident(), false,
                null, vdefs);
        return t;
    }

    @Override
    protected <T extends ListBuffer<? super JCVariableDecl>> T variableDeclaratorsRest(
            int pos, JCModifiers mods, JCExpression type, Name name,
            boolean reqInit, String dc, T vdefs) {
        if (S.jml) reqInit = false; // In type checking we check this more
                                    // thoroughly
        // Here we just allow having no initializer
        return super.variableDeclaratorsRest(pos, mods, type, name, reqInit,
                dc, vdefs);
    }

    @Override
    public JCExpression variableInitializer() {
        S.setJmlKeyword(false);
        try {
            return super.variableInitializer();
        } finally {
            // We should be looking at a comma or a semicolon or a right brace,
            // so we are not too late to set this
            S.setJmlKeyword(true);
        }
    }

    /**
     * This is overridden to try to get <:, <# and <=# with the right precedence
     */
    // FIXME - not sure this is really robust
    protected int prec(Token token) {
        if (token == CUSTOM) {
            // Caution: S may not be on the same token anymore
            if (S.jmlToken() != null && S.jmlToken() != JmlToken.SUBTYPE_OF
                    && S.jmlToken() != JmlToken.JSUBTYPE_OF
                    && S.jmlToken() != JmlToken.LOCK_LT
                    && S.jmlToken() != JmlToken.LOCK_LE) return -1; // For
                                                                    // inequivalence
                                                                    // and
                                                                    // reverse/implies
            return TreeInfo.ordPrec; // All the JML operators are comparisons
        } else
            return super.prec(token);
    }

    // MAINTENANCE ISSUE - (Almost) Duplicated from JavacParser.java in order to track
    // Jml tokens
    protected JCExpression term2Rest(JCExpression t, int minprec) {
        List<JCExpression[]> savedOd = odStackSupply.elems;
        JCExpression[] odStack = newOdStack();
        List<Token[]> savedOp = opStackSupply.elems;
        Token[] opStack = newOpStack();
        List<int[]> savedPos = posStackSupply.elems;
        int[] posStack = newPosStack();
        // optimization, was odStack = new Tree[...]; opStack = new Tree[...];
        int top = 0;
        odStack[0] = t;
        int startPos = S.pos();
        Token topOp = ERROR;
        int topOpPos = Position.NOPOS;
        while (prec(S.token()) >= minprec) {
            posStack[top] = topOpPos;
            opStack[top] = topOp;
            top++;
            topOp = S.token();
            topOpPos = S.pos();
            JmlToken topOpJmlToken = S.jmlToken();
            S.nextToken(); // S.jmlToken() changes
            odStack[top] = (topOp == INSTANCEOF) ? parseType() : term3();
            while (top > 0 && prec(topOp) >= prec(S.token())) {
                if (topOp == CUSTOM) { // <:
                    JCExpression e = jmlF.at(topOpPos).JmlBinary(topOpJmlToken, odStack[top - 1],
                            odStack[top]);
                    storeEnd(e, getEndPos(odStack[top]));
                    odStack[top - 1] = e;
                } else {
                    odStack[top - 1] = makeOp(topOpPos, topOp, odStack[top - 1],
                        odStack[top]);
                }
                top--;
                topOp = opStack[top];
                topOpPos = posStack[top];
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
        posStackSupply.elems = savedPos; // optimization
        return t;
    }

    /**
     * Skips up to and including a semicolon, though not including any EOF or
     * ENDJMLCOMMENT
     */
    protected void skipThroughSemi() {
        while (S.token() != Token.SEMI && S.token() != Token.EOF
                && S.jmlToken() != JmlToken.ENDJMLCOMMENT)
            S.nextToken();
        if (S.token() == Token.SEMI) S.nextToken();
    }

    /** Skips up to but not including a semicolon or EOF or ENDJMLCOMMENT */
    protected void skipToSemi() {
        while (S.token() != Token.SEMI && S.token() != Token.EOF
                && S.jmlToken() != JmlToken.ENDJMLCOMMENT)
            S.nextToken();
    }

    /**
     * Skips up to but not including a semicolon or comma or EOF or
     * ENDJMLCOMMENT
     */
    protected void skipToCommaOrSemi() {
        while (S.token() != Token.SEMI && S.token() != Token.COMMA
                && S.token() != Token.EOF
                && S.jmlToken() != JmlToken.ENDJMLCOMMENT)
            S.nextToken();
    }

    /**
     * Skips up to but not including a right-parenthesis or comma or EOF or
     * ENDJMLCOMMENT
     */
    protected void skipToCommaOrParenOrSemi() {
        while (S.token() != Token.RPAREN && S.token() != Token.COMMA
                && S.token() != Token.SEMI && S.token() != Token.EOF
                && S.jmlToken() != JmlToken.ENDJMLCOMMENT)
            S.nextToken();
    }

    /**
     * Skips up to a EOF or ENDJMLCOMMENT or up to and including a right brace
     */
    public void skipThroughRightBrace() {
        while (S.token() != Token.RBRACE && S.token() != Token.EOF
                && S.jmlToken() != JmlToken.ENDJMLCOMMENT)
            S.nextToken();
        if (S.token() != Token.EOF) S.nextToken();
    }

    /**
     * Skips up to a EOF or ENDJMLCOMMENT or up to and including a right
     * parenthesis
     */
    public void skipThroughRightParen() {
        while (S.token() != Token.RPAREN && S.token() != Token.EOF
                && S.jmlToken() != JmlToken.ENDJMLCOMMENT)
            S.nextToken();
        if (S.token() != Token.EOF) S.nextToken();
    }

    public JCErroneous syntaxError(int pos, List<JCTree> errs, String key,
            Object... args) {
        setErrorEndPos(pos);
        reportSyntaxError(pos, key, args);
        return toP(F.at(pos).Erroneous(errs));
    }

    // FIXME - do we need to set errorEndPos in the following?

    /** Creates an error message for which the source is a single character */
    public void jmlerror(int pos, String key, Object... args) {
        log.error(new JmlScanner.DiagnosticPositionSE(pos, pos), key, args);
    }

    /**
     * Creates an error message for which the source is a range of characters,
     * from begin up to and not including end; the identified line is that of
     * the begin position.
     */
    public void jmlerror(int begin, int end, String key, Object... args) {
        log.error(new JmlScanner.DiagnosticPositionSE(begin, end - 1), key,
                args); // TODO - not unicode friendly
    }

    /**
     * Creates an error message for which the source is a range of characters,
     * from begin up to and not including end; it also specifies a preferred
     * location to highlight if the output format can only identify a single
     * location; the preferred location is also the line that is identified.
     */
    public void jmlerror(int begin, int preferred, int end, String key,
            Object... args) {
        log.error(
                new JmlScanner.DiagnosticPositionSE(begin, preferred, end - 1),
                key, args);// TODO - not unicode friendly
    }
    
//    /** If next input token matches given token, skip it, otherwise report
//     *  an error; this method is overridden in order to give a slightly better
//     *  error message on misspelled JML tokens.
//     */
//    public void accept(Token token) {
//        if (!inJmlDeclaration) {
//            super.accept(token);
//        } else {
//            if (S.token() == token) {
//                S.nextToken();
//            } else if (S.token() == null) {
//                setErrorEndPos(S.pos());
//                reportSyntaxError(S.prevEndPos(), "expected, not a misspelled or unexpected JML token", token);
//            } else {
//                setErrorEndPos(S.pos());
//                reportSyntaxError(S.prevEndPos(), "expected", token);
//            }
//        }
//    }



    // FIXME - check the use of Token.CUSTOM vs. null
    // FIXME - review the remaining uses of log.error vs. jmlerror
    // FIXME - refactor to better match the grammar as a top-down parser
    // FIXME - refactor for extension
    // FIXME - need to sort out the various modes - isJml isJmlDeclaration isLocalOrAnonClass...
}
