/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.parser;

import static com.sun.tools.javac.parser.Tokens.TokenKind.*;
import static org.jmlspecs.openjml.JmlTokenKind.*;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.jdt.annotation.Nullable;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlTree.IJmlLoop;
import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;
import org.jmlspecs.openjml.JmlTree.JmlAnnotation;
import org.jmlspecs.openjml.JmlTree.JmlBlock;
import org.jmlspecs.openjml.JmlTree.JmlChoose;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlDoWhileLoop;
import org.jmlspecs.openjml.JmlTree.JmlEnhancedForLoop;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlImport;
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
import org.jmlspecs.openjml.JmlTree.JmlMethodSig;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlStatement;
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
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.parser.JavacParser.ParensResult;
import com.sun.tools.javac.parser.Tokens.Comment;
import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.parser.Tokens.Comment.CommentStyle;
import com.sun.tools.javac.parser.Tokens.ITokenKind;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCErroneous;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCNewClass;
import com.sun.tools.javac.tree.JCTree.JCPrimitiveTypeTree;
import com.sun.tools.javac.tree.JCTree.JCSkip;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Assert;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Position;

/** This class extends the javac parser to parse JML constructs as well. */
public class JmlParser extends JavacParser {

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
        super(fac, S, keepDocComments, true, true); // true = keepLineMap, keepEndPositions
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
    
    /** Beginning position of current token */
    public int pos() {
        return token.pos;
    }

    /** End position of current token */
    public int endPos() {
        return token.endPos;
    }
    
    public JmlTokenKind jmlTokenKind() {
        return token.ikind instanceof JmlTokenKind ? (JmlTokenKind)token.ikind : null;
    }

    /** Returns the scanner being used by the parser */
    public JmlScanner getScanner() {
        return S;
    }

    /** Returns the node factory being used by the parser */
    public JmlTree.Maker maker() {
        return jmlF;
    }
    
    public void rescan() {
        token = S.rescan();
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
        if (!(u instanceof JmlCompilationUnit)) {
            log.error(
                    "jml.internal",
                    "JmlParser.compilationUnit expects to receive objects of type JmlCompilationUnit, but it found a "
                            + u.getClass()
                            + " instead, for source "
                            + u.getSourceFile().toUri().getPath());
        } else {
            JmlCompilationUnit jmlcu = (JmlCompilationUnit) u;
            setTopLevel(jmlcu,jmlcu.defs);
        }
        return u;
    }
    
    /** Recursively sets the toplevel field of class declarations */
    private void setTopLevel(JmlCompilationUnit cu, List<JCTree> defs) {
        for (JCTree t : defs) {
            if (t instanceof JmlClassDecl) {
                JmlClassDecl jcd = (JmlClassDecl) t;
                jcd.toplevel = cu;
                setTopLevel(cu, jcd.defs);
            }
        }
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
    protected JCTree importDeclaration(JCModifiers mods) {
        int p = pos();
        boolean modelImport = false;
        for (JCAnnotation a: mods.annotations) {
            if (a.annotationType.toString().equals("org.jmlspecs.annotation.Model")) { modelImport = true; }
            else jmlerror(a.pos, "jml.no.mods.on.import");
        }
        boolean importIsInJml = S.jml();
        if (!modelImport && importIsInJml) {
            jmlerror(p, endPos(), "jml.import.no.model");
            modelImport = true;
        }
        JCTree t = super.importDeclaration(mods);
        ((JmlImport) t).isModel = modelImport;
        if (modelImport && !importIsInJml) {
            jmlerror(p, t.getEndPosition(endPosTable), "jml.illformed.model.import");
        }
        if (jmlTokenKind() == JmlTokenKind.ENDJMLCOMMENT) {
            nextToken();
        }
        return t;
    }
    
    @Override
    JCAnnotation annotation(int pos, JCTree.Tag kind) {
        JCAnnotation a = super.annotation(pos, kind);
        ((JmlTree.JmlAnnotation)a).sourcefile = log.currentSourceFile();
        return a;
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
    protected JCStatement classOrInterfaceOrEnumDeclaration(JCModifiers mods, Comment dc) {
        boolean prevInJmlDeclaration = inJmlDeclaration;
        JCStatement s;
        try {
            if (S.jml()) {
                if (mods == null) {
                    mods = jmlF.at(Position.NOPOS).Modifiers(0);
                    storeEnd(mods, Position.NOPOS);
                }
                if (!inJmlDeclaration) utils.setJML(mods);
                inJmlDeclaration = true;
            }
            if (token.kind == IMPORT) { // FIXME - I don't think this is used anymore
                JCAnnotation a = utils
                        .findMod(
                                mods,
                                names.fromString(Strings.modelAnnotation));
                if (a != null) {
                    skipToSemi();
                    int p = mods.annotations.head.pos;
                    jmlerror(p, endPos(), "jml.illformed.model.import");
                    s = toP(F.Exec(toP(F.at(p).Erroneous(List.<JCTree> nil()))));
                    skipThroughSemi();
                } else {
                    int p = mods.annotations.head.pos;
                    s = toP(F.Exec(toP(F.at(p).Erroneous(List.<JCTree> nil()))));
                    jmlerror(mods.getStartPosition(),
                            getEndPos(mods),
                            "jml.no.mods.on.import");
                }
                mods.flags = 0;
                mods.annotations = List.<JCAnnotation> nil();
            } else if (!inJmlDeclaration || token.kind == CLASS || token.kind == INTERFACE || token.kind == ENUM) {
                // The guard above is used because if it is false, we want to produce
                // a better error message than we otherwise get, for misspelled
                // JML modifiers. However, the test above replicates tests in
                // the super method and may become obsolete.
                s = super.classOrInterfaceOrEnumDeclaration(mods, dc);

            } else {
                int p = pos();
                jmlerror(pos(),
                        endPos(),
                        "jml.unexpected.or.misspelled.jml.token",
                            token == null ? jmlTokenKind().internedName() : S.chars() );
                
                setErrorEndPos(pos());
                s = toP(F.Exec(toP(F.at(p).Erroneous(List.<JCTree> nil()))));
                //nextToken();
            }
            if (s instanceof JCClassDecl && (((JCClassDecl)s).mods.flags & Flags.ENUM) != 0) {
                ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
                JCClassDecl cd = (JCClassDecl)s;
                Name n = jmlF.Name(Strings.enumVar);
                JCExpression disj = null;
                for (JCTree d: cd.defs) {
                    if (!(d instanceof JCVariableDecl)) continue;
                    JCVariableDecl decl = (JCVariableDecl)d;
                    long flags = decl.mods.flags;
                    long expected = Flags.PUBLIC | Flags.STATIC | Flags.FINAL;
                    if ((flags & expected) != expected || decl.init == null) continue;
                    if (!(decl.vartype instanceof JCIdent && ((JCIdent)decl.vartype).name.equals(cd.name))) continue;
                    JCExpression id = jmlF.at(d.pos).Ident(decl.getName());
                    args.add(id);
                    id = jmlF.at(d.pos).Ident(decl.getName());
                    JCExpression ide = jmlF.at(d.pos).Ident(n);
                    JCExpression ex = jmlF.at(id.pos).Binary(JCTree.Tag.EQ, ide, id);
                    disj = disj == null ? ex : jmlF.at(ex.pos).Binary(JCTree.Tag.OR,disj,ex);
                }
                args.add(F.Literal(TypeTag.BOT,null));
                JCExpression ex = jmlF.at(s.pos).JmlMethodInvocation(JmlTokenKind.BSDISTINCT,args.toList());
                JmlTypeClauseExpr axiom = jmlF.at(s.pos).JmlTypeClauseExpr(jmlF.Modifiers(0),JmlTokenKind.AXIOM,ex);
                cd.defs = cd.defs.append(axiom);
                JCVariableDecl decl = jmlF.at(cd.pos).VarDef(jmlF.Modifiers(0),n,jmlF.Ident(jmlF.Name("Object")),null);
                ex = jmlF.JmlQuantifiedExpr(JmlTokenKind.BSFORALL,List.<JCVariableDecl>of(decl), null,
                        jmlF.JmlBinary(JmlTokenKind.EQUIVALENCE, jmlF.TypeTest(jmlF.Ident(n), jmlF.Ident(cd.getSimpleName())),disj));
                axiom = jmlF.at(s.pos).JmlTypeClauseExpr(jmlF.Modifiers(0),JmlTokenKind.AXIOM,ex);
                cd.defs = cd.defs.append(axiom);
            }
            // Can also be a JCErroneous
//            if (s instanceof JmlClassDecl) {
//                filterTypeBodyDeclarations((JmlClassDecl) s, context, jmlF);
//            }
            if (jmlTokenKind() == JmlTokenKind.ENDJMLCOMMENT) {
                nextToken();
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
            rescan();
        }

    }

//    /**
//     * This parses a sequence of statements that can appear in a block. JML
//     * overrides it in order to include JML assert, assume, set, debug, ghost
//     * declarations, unreachable, loop invariants and any other JML specs that
//     * can appear in the body of a method.
//     * 
//     * @return a list of JmlStatement nodes (despite the required type of the
//     *         method)
//     */
//    @Override
//    public List<JCStatement> blockStatements() {
//        ListBuffer<JCStatement> list = new ListBuffer<JCStatement>();
//        int pos = -1;
//        JCModifiers mods = null;
//        while (token.kind != RBRACE && token.kind != EOF) {
//            // If the following equality is true, then the scanner has made no
//            // progress in the previous loop iteration. Presumably some error
//            // has occurred; for example no next statement is recognized.
//            // So we just abort the loop. Since the next token is not a right
//            // brace, an error will be issued when an attempt is made to read
//            // the right brace that closes the block.
//            if (S.currentPos() == pos) break;
//            pos = S.currentPos();
//            // Only certain qualifiers can appear here - perhaps limit the 
//            // parsing of modifiers to just that set. Java explicitly has
//            // final abstract strictfp; also synchronized but not as a modifier.
//            // FIXME - this needs more testing
//            if (token.kind != SYNCHRONIZED) {
//                mods = modifiersOpt(); // read any additional modifiers (e.g.
//                                   // JML ones)
//            }
//            JmlTokenKind jt = jmlTokenKind();
//            if (jt != null) {
//
//                if (isJmlTypeToken(jt)) {
//                    JCExpression t = parseType();
//                    ListBuffer<JCStatement> vdefs = new ListBuffer<JCStatement>();
//                    variableDeclarators(mods, t, vdefs);
//                    if (token.kind == SEMI) {
//                        accept(SEMI);
//                    } else {
//                        accept(SEMI); // To get the error message
//                        skipThroughSemi();
//                    }
//                    for (JCStatement vdef : vdefs) {
//                        JmlVariableDecl jmldef = (JmlVariableDecl) vdef;
//                        utils.setJML(jmldef.mods);
//                        list.append(vdef);
//                    }
//                } else {
//                    pushBackModifiers = mods;
//                    mods = null;
//                    JCStatement st = parseStatement();
//                    list.append(st);
//                }
//            } else {
//                pushBackModifiers = mods;
//                mods = null;
//                if (S.jml()) {
//                    boolean prevInJmlDeclaration = inJmlDeclaration;
//                    inJmlDeclaration = true;
//                    List<JCTree.JCStatement> dlist = super.blockStatements();
//                    inJmlDeclaration = prevInJmlDeclaration;
//                    if (inJmlDeclaration || inLocalOrAnonClass) {
//                        // In this case we are in the body of a model method.
//                        // Within the body we don't mark any local variables
//                        // or classes as ghost or model (with setJML).
//                        list.appendList(dlist);
//                    } else {
//                        for (JCTree.JCStatement t : dlist) {
//                            if (t instanceof JmlVariableDecl) {
//                                JmlVariableDecl d = (JmlVariableDecl) t;
//                                utils.setJML(d.mods);
//                            } else if (t instanceof JmlClassDecl) {
//                                JmlClassDecl d = (JmlClassDecl) t;
//                                utils.setJML(d.mods);
//                            } else if (t instanceof JCTree.JCSkip) {
//                                // An empty statement is not really allowed
//                                // within
//                                // a JML annotation, but it is common to find
//                                // one
//                                // after a local class declaration, so we won't
//                                // complain.
//                            } else {
//                                jmlerror(t.pos, "jml.expected.decl.or.jml");
//                            }
//                            list.append(t);
//                        }
//                    }
//                } else {
//                    list.appendList(super.blockStatements());
//                }
//            }
//        }

//    }
    
    @Override List<JCStatement> blockStatements() {
        List<JCStatement> stats = super.blockStatements();
        ListBuffer<JCStatement> newstats = new ListBuffer<>();
        ListBuffer<JmlStatementLoop> loopspecs = new ListBuffer<>();
        for (JCStatement s: stats) {
            if (s instanceof JmlStatementLoop) {
                loopspecs.add((JmlStatementLoop)s);
                continue;
            }
            if (!loopspecs.isEmpty()) {
                if (s instanceof IJmlLoop) {
                    ((IJmlLoop)s).setLoopSpecs(loopspecs.toList());
                } else {
                    jmlerror(loopspecs.first().pos,
                            loopspecs.last().getEndPosition(endPosTable),
                            "jml.loop.spec.misplaced");
                }
                loopspecs = new ListBuffer<>();
            }
            newstats.add(s);
        }
        if (!loopspecs.isEmpty()) {
            jmlerror(loopspecs.first().pos,
                    loopspecs.last().getEndPosition(endPosTable),
                    "jml.loop.spec.misplaced");
            loopspecs = new ListBuffer<>();
        }
        return newstats.toList();
    }

    @Override
    protected List<JCStatement> blockStatement() {
        while (true) {
            if (!(token instanceof JmlToken)) {
                boolean inJml = S.jml();
                List<JCStatement> stats = super.blockStatement();
                if (inJml) {
                    for (JCStatement s: stats) {
                        if (s instanceof JCVariableDecl) {
                            utils.setJML(((JCVariableDecl)s).mods);
                        } else if (s instanceof JCClassDecl || s instanceof JmlAbstractStatement || s instanceof JCSkip) {
                            // OK
                        } else if (!inJmlDeclaration && !inModelProgram && !inLocalOrAnonClass) { // FIXME - unsure of this test
                            jmlerror(s.pos, "jml.expected.decl.or.jml");
                        }
                    }
                }
                return stats;
            }
            JmlTokenKind jkind = ((JmlToken)token).jmlkind;
            if (modifiers.contains(jkind)) {
                // MAINTENCE: Copied from JavacParser.blockStatement, FINAL case
                Comment dc = token.comment(CommentStyle.JAVADOC);
                JCModifiers mods = modifiersOpt();
                if (S.jml()) utils.setJML(mods); // Added this to mark declarations in JML annotations
                if (token.kind == INTERFACE ||
                        token.kind == CLASS ||
                        allowEnums && token.kind == ENUM) {
                    return List.of(classOrInterfaceOrEnumDeclaration(mods, dc));
                } else {
                    JCExpression t = parseType();
                    ListBuffer<JCStatement> stats =
                            variableDeclarators(mods, t, new ListBuffer<JCStatement>());
                    // A "LocalVariableDeclarationStatement" subsumes the terminating semicolon
                    storeEnd(stats.last(), token.endPos);
                    accept(SEMI);
                    return stats.toList();
                }
            } else if (jkind == ENDJMLCOMMENT) {
                S.setJml(false);
                nextToken();
                continue;
            }
            JCStatement s = parseStatement();
            return List.<JCStatement>of(s);
        }
    }
    
    /** Overridden to parse JML statements */
    @Override
    public JCStatement parseStatement() {
        JCStatement st;
        String reason = null;
        JmlTokenKind jtoken = jmlTokenKind();
        if (token.kind == CUSTOM) {
            boolean needSemi = true;
            if (jtoken != JmlTokenKind.ENDJMLCOMMENT) {
                int pos = pos();
                JmlSpecificationCase spc;
                if (jtoken != null)
                    reason = jtoken.internedName() + " statement";
                if (jtoken == JmlTokenKind.ASSUME || jtoken == JmlTokenKind.ASSERT) {
                    S.setJmlKeyword(false);
                    nextToken();
                    JCExpression t = null;
                    t = parseExpression();
                    JmlTree.JmlStatementExpr ste = jmlF
                            .at(pos)
                            .JmlExpressionStatement(
                                    jtoken,
                                    jtoken == JmlTokenKind.ASSUME ? Label.EXPLICIT_ASSUME
                                            : Label.EXPLICIT_ASSERT, t);
                    if (token.kind == COLON) {
                        nextToken();
                        ste.optionalExpression = parseExpression();
                    }
                    toP(ste);
                    ste.source = log.currentSourceFile();
                    //ste.line = log.currentSource().getLineNumber(pos);
                    st = ste;
                } else if (jtoken == UNREACHABLE || jtoken == REACHABLE) {
                    S.setJmlKeyword(false);
                    nextToken();
                    JCExpression t = null;
                    if (token.ikind != ENDJMLCOMMENT && token.kind != SEMI) {
                        t = parseExpression();
                    }
                    JmlTree.JmlStatementExpr ste = to(jmlF.at(pos)
                            .JmlExpressionStatement(jtoken, 
                                    jtoken == REACHABLE ? Label.REACHABLE : Label.UNREACHABLE,
                                    t));
                    ste.source = log.currentSourceFile();
                    st = ste;
                    if (JmlOption.isOption(context, JmlOption.STRICT)) {
                        // FIXME - why the difference in the positions of these two warnings
                        if (jtoken == UNREACHABLE && t != null) log.warning(pos(),"jml.not.strict","unreachable statement with expression");
                        if (jtoken == REACHABLE) log.warning(ste.pos,"jml.not.strict",jtoken.internedName());
                    }
                } else if (jtoken == HENCE_BY) {
                    S.setJmlKeyword(false);
                    nextToken();
                    JCExpression t = parseExpression();
                    JmlTree.JmlStatementExpr ste = to(jmlF.at(pos)
                            .JmlExpressionStatement(jtoken, 
                                    Label.EXPLICIT_ASSUME,
                                    t));
                    ste.source = log.currentSourceFile();
                    st = ste;
                } else if (jtoken == DECREASES || jtoken == LOOP_INVARIANT) {
                    S.setJmlKeyword(false);
                    nextToken();
                    JCExpression t = parseExpression();
                    JmlStatementLoop ste = to(jmlF.at(pos).JmlStatementLoop(
                            jtoken, t));
                    // ste.source = log.currentSourceFile();
                    // ste.line = log.currentSource().getLineNumber(pos);
                    st = ste;
                } else if (jtoken == JmlTokenKind.HAVOC ) {
                    S.setJmlKeyword(false);
                    nextToken();

                    ListBuffer<JCExpression> list = parseStoreRefList(false);
                    if (token.kind == SEMI) {
                        // OK, go on
                    } else if (jmlTokenKind() == ENDJMLCOMMENT) {
                        syntaxError(pos(), null, "jml.missing.semi");
                    }
                    S.setJmlKeyword(true);
                    if (token.kind != SEMI) {
                        // error already reported
                        skipThroughSemi();
                    } else {
                        if (list.isEmpty()) {
                            syntaxError(pos(), null, "jml.use.nothing.assignable");
                        }
                        nextToken();
                    }
                    st = toP(jmlF.at(pos).JmlHavocStatement(list.toList()));
                    S.setJmlKeyword(true); // This comes a token too late.
                    rescan();
                    needSemi = false;
                } else if (jtoken == JmlTokenKind.SET || jtoken == JmlTokenKind.DEBUG) {
                    S.setJmlKeyword(false);
                    nextToken();
                    // Only StatementExpressions are allowed - 
                    // assignment statements and stand-alone method calls -
                    // but JML constructs are allowed.
                    boolean prev = inJmlDeclaration;
                    inJmlDeclaration = true;
                    JCStatement t = super.parseStatement();
                    inJmlDeclaration = prev;
                    if (!(t instanceof JCExpressionStatement)) {
                        jmlerror(t.getStartPosition(),
                                getEndPos(t),
                                "jml.bad.statement.in.set.debug");
                        t = null;
                    }
                    st = toP(jmlF.at(pos).JmlStatement(jtoken, (JCExpressionStatement)t));
                    S.setJmlKeyword(true); // This comes a token too late.
                    rescan();
                    needSemi = false;

                } else if (methodClauseTokens.contains(jtoken)) {
                    if (JmlOption.isOption(context, JmlOption.STRICT)) {
                        log.warning(pos(),"jml.refining.required");
                    }
                    JCModifiers mods = jmlF.Modifiers(0);
                    JmlMethodSpecs specs = parseMethodSpecs(mods);
                    for (JmlSpecificationCase c : specs.cases) {
                        if (!isNone(c.modifiers)) {
                            jmlerror(c.modifiers.getStartPosition(),
                                    getEndPos(c.modifiers),
                                    "jml.no.mods.in.refining");
                        }
                    }
                    st = jmlF.at(pos).JmlStatementSpec(specs);
                    storeEnd(st, getEndPos(specs));
                    needSemi = false;

                } else if (jtoken == JmlTokenKind.REFINING) {
                    nextToken();
                    if (jmlTokenKind() == JmlTokenKind.ALSO) {
                        jmlerror(pos(), endPos(), "jml.invalid.also");
                        nextToken();
                    }
                    JCModifiers mods = modifiersOpt();
                    JmlMethodSpecs specs = parseMethodSpecs(mods);
                    for (JmlSpecificationCase c : specs.cases) {
                        if (!isNone(c.modifiers)) {
                            jmlerror(c.modifiers.getStartPosition(),
                                    getEndPos(c.modifiers),
                                    "jml.no.mods.in.refining");
                        }
                    }
                    st = jmlF.at(pos).JmlStatementSpec(specs);
                    storeEnd(st, getEndPos(specs));
                    needSemi = false;

                } else if (inModelProgram && jtoken == JmlTokenKind.CHOOSE) {
                    st = parseChoose();
                    return toP(st); // FIXME - is this the correct end position?
                } else if (inModelProgram && jtoken == JmlTokenKind.CHOOSE_IF) {
                    st = parseChooseIf();
                    return toP(st); // FIXME - is this the correct end position?
                } else if (inModelProgram && jtoken == JmlTokenKind.INVARIANT) {
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
                } else if (JmlTokenKind.modifiers.contains(jtoken)) {
                    List<JCStatement> stats = super.blockStatement();
                    if (stats.size() > 1) jmlerror(stats.get(0).pos, "internal.notsobad", "Multiple statements where one expected"); // FIXME
                    st = stats.get(0);
                    needSemi = false;
                } else {
                    jmlerror(pos(), endPos(), "jml.unknown.statement",
                            jtoken.internedName());
                    skipToSemi();
                    st = jmlF.at(pos()).Skip();
                }
            } else {
                nextToken(); // swallows the ENDJMLCOMMENT
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
                if (token.kind == IDENTIFIER && S.jml()) {
                    JmlTokenKind tt = JmlTokenKind.allTokens.get(S.chars());
                    if (tt != null) {
                        S.setToken(new JmlToken(tt, null, pos(), endPos())); // FIXME - but S.token is not set
                    }
                }
            } else if (token.ikind == ENDJMLCOMMENT) {
                log.warning(pos(), "jml.missing.semi", jtoken);
            	
            } else if (token.kind != SEMI) {
                jmlerror(pos(), endPos(), "jml.bad.construct", reason);
                skipThroughSemi();
            } else {
                nextToken(); // skip the semi
            }
            if (jmlTokenKind() == JmlTokenKind.ENDJMLCOMMENT) nextToken();
            return st;
        }
//        if (S.jml() && !inModelProgram && !inJmlDeclaration && !inLocalOrAnonClass) { // FIXME - unsure of this test
//            jmlerror(pos(),"jml.expected.decl.or.jml");
//        }
        JCStatement stt = super.parseStatement();
        return stt;
    }
    
    /** Returns true if the token is a JML type token */
    public boolean isJmlTypeToken(JmlTokenKind t) {
        return t == JmlTokenKind.BSTYPEUC || t == JmlTokenKind.BSBIGINT
                || t == JmlTokenKind.BSREAL;
    }

    /** Parses a choose statement (the choose token is already read) */
    public JmlChoose parseChoose() {
        JmlTokenKind jt = jmlTokenKind();
        nextToken();
        ListBuffer<JCBlock> orBlocks = new ListBuffer<JCBlock>();
        orBlocks.append(block()); // FIXME - here and below - what if block()
                                  // returns null.
        while (jmlTokenKind() == JmlTokenKind.OR) {
            nextToken();
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
        JmlTokenKind jt = jmlTokenKind();
        ListBuffer<JCBlock> orBlocks = new ListBuffer<JCBlock>();
        JCBlock elseBlock = null;
        nextToken();
        orBlocks.append(block());
        while (jmlTokenKind() == JmlTokenKind.OR) {
            nextToken();
            orBlocks.append(block());
        }
        if (token.kind == ELSE) {
            nextToken();
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
        new JmlDebugTreePrinter(out, endPosTable).scan(t);
    }

    /**
     * when true we are parsing declarations within a model method or class, so
     * the individual declarations are not themselves considered JML
     * declarations even though they may be within a JML comment.
     */
    protected boolean inJmlDeclaration = false;
    protected @Nullable JmlMethodSpecs currentMethodSpecs = null;
    protected @Nullable JmlVariableDecl currentVariableDecl = null;
    

    /**
     * Overridden in order to parse JML declarations and clauses within the body
     * of a class or interface.
     */
    @Override
    protected List<JCTree> classOrInterfaceBodyDeclaration(Name className,
            boolean isInterface) {

        ListBuffer<JCTree> list = new ListBuffer<JCTree>();
        loop: while (true) {
            JmlVariableDecl mostRecentVarDecl = currentVariableDecl;
            currentVariableDecl = null;
            
            Comment dc = token.comment(CommentStyle.JAVADOC);
            if (jmlTokenKind() == ENDJMLCOMMENT) {
                nextToken(); // swallows the ENDJMLCOMMENT
                currentVariableDecl = mostRecentVarDecl;
                break loop;
            }
            if (S.jml()) S.setJmlKeyword(true);
            JCModifiers mods = modifiersOpt(); // Gets anything that is in
                                               // pushBackModifiers
            int pos = pos();
            JmlTokenKind jt = jmlTokenKind();
//            check: if (S.jml() && jt == null && !inJmlDeclaration && !inLocalOrAnonClass) {
//                String tokenString = S.chars();
//                if (!tokenString.isEmpty()) {
//                    if (mods.annotations != null) for (JCAnnotation a: mods.annotations) {
//                        if (a.annotationType.toString().endsWith("Model")) break check;
//                        if (a.annotationType.toString().endsWith("Ghost")) break check;
//                    }
//                    log.error(pos,  "jml.bad.keyword", tokenString);
//                    skipThroughSemi();
//                    break loop;
//                }
//            }
            if (jt == null || isJmlTypeToken(jt)) {
                pushBackModifiers = mods; // This is used to pass the modifiers
                // into super.classOrInterfaceBodyDeclaration
                mods = null;
                boolean startsInJml = S.jml();
                List<JCTree>  t;
                if (startsInJml && !inLocalOrAnonClass) {
                    boolean prevInJmlDeclaration = inJmlDeclaration;
                    inJmlDeclaration = true;
                    t = super.classOrInterfaceBodyDeclaration(
                            className, isInterface);
                    inJmlDeclaration = prevInJmlDeclaration;
                } else {

                    // no longer in JML
                    // FIXME - attach doc comment?
                    t = super.classOrInterfaceBodyDeclaration(
                            className, isInterface);
                }
                if (!inJmlDeclaration) {
                    for (JCTree tr : t) {
                        JCTree ttr = tr;
                        if (tr instanceof JmlClassDecl) {
                            JmlClassDecl d = (JmlClassDecl) tr;
                            if (startsInJml) utils.setJML(d.mods);
                            //d.toplevel.sourcefile = log.currentSourceFile();
                            ttr = tr; // toP(jmlF.at(pos).JmlTypeClauseDecl(d));
                            attach(d, dc);
                        } else if (tr instanceof JmlMethodDecl) {
                            JmlMethodDecl d = (JmlMethodDecl) tr;
                            if (startsInJml) utils.setJML(d.mods);
                            d.sourcefile = log.currentSourceFile();
                            ttr = tr; // toP(jmlF.at(pos).JmlTypeClauseDecl(d));
                            attach(d, dc);
                            d.cases = currentMethodSpecs;
                            if (currentMethodSpecs != null) {
                                currentMethodSpecs.decl = d;
                                currentMethodSpecs = null;
                            }
                            
                        } else if (tr instanceof JmlBlock) {
                            JmlBlock d = (JmlBlock) tr;
                            ttr = tr; // toP(jmlF.at(pos).JmlTypeClauseDecl(d));
                            attach(d, dc);
                            d.cases = currentMethodSpecs;
                            if (currentMethodSpecs != null) {
                                currentMethodSpecs.decl = null; // FIXME - point to the block?
                                currentMethodSpecs = null;
                            }

                        } else if (tr instanceof JmlVariableDecl) {
                            JmlVariableDecl d = (JmlVariableDecl) tr;
                            if (startsInJml) utils.setJML(d.mods);
                            d.sourcefile = log.currentSourceFile();
                            ttr = tr; // toP(jmlF.at(pos).JmlTypeClauseDecl(d));
                            attach(d, dc);
                            currentVariableDecl = d;

                        } else {
                            tr = null;
                        }
                        //                            if (tr != null && utils.findMod(tmods, JmlTokenKind.MODEL) == null && utils.findMod(tmods, JmlTokenKind.GHOST) == null) {
                        //                                jmlerror(tr.pos, "jml.missing.ghost.model");
                        //                            }
                        dc = null;
                        list.append(ttr);
                    }
                } else if (t.head instanceof JmlMethodDecl) {
                    JmlMethodDecl d = (JmlMethodDecl) t.head;
                    if (startsInJml) utils.setJML(d.mods);
                    d.sourcefile = log.currentSourceFile();
                    attach(d, dc);
                    d.cases = currentMethodSpecs;
                    if (currentMethodSpecs != null) {
                        currentMethodSpecs.decl = d;
                        currentMethodSpecs = null;
                    }
                    list.append(d);

                } else if (t.head instanceof JmlTypeClauseIn
                        || t.head instanceof JmlTypeClauseMaps) {
                    JCTree tree = t.head;
                    if (tree instanceof JmlTypeClauseIn) {
                        ((JmlTypeClauseIn) tree).parentVar = mostRecentVarDecl;
                    }
                    if (mostRecentVarDecl == null) {
                        log.error(tree.pos(), "jml.misplaced.var.spec",
                                ((JmlTypeClause) tree).token.internedName());
                    } else {
                        if (mostRecentVarDecl.fieldSpecs == null) {
                            mostRecentVarDecl.fieldSpecs = new JmlSpecs.FieldSpecs(
                                    mostRecentVarDecl);
                        }
                        mostRecentVarDecl.fieldSpecs.list
                        .append((JmlTypeClause) tree);
                        currentVariableDecl = mostRecentVarDecl;
                    }

                } else if (t.head instanceof JmlMethodSpecs) {
                    currentMethodSpecs = (JmlMethodSpecs)t.head;

                } else {
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
                currentMethodSpecs = parseMethodSpecs(mods);
                //list.append(parseMethodSpecs(mods));
                // FIXME - attach doc comment?
                // getMethodSpecs may have already parsed some modifiers.
                // They will be in pushBackModifiers
            } else if (jt == IN) {
                JmlTypeClauseIn inClause = parseIn(pos, mods);
                inClause.parentVar = mostRecentVarDecl;
                if (mostRecentVarDecl == null) {
                    log.error(inClause.pos(), "jml.misplaced.var.spec",
                            inClause.token.internedName());
                } else {
                    if (mostRecentVarDecl.fieldSpecs == null) {
                        mostRecentVarDecl.fieldSpecs = new JmlSpecs.FieldSpecs(
                                mostRecentVarDecl);
                    }
                    mostRecentVarDecl.fieldSpecs.list.append(inClause);
                    currentVariableDecl = mostRecentVarDecl;
                }
            } else if (jt == MAPS) {
                JmlTypeClauseMaps mapsClause = parseMaps(pos, mods, list);
                if (mostRecentVarDecl == null) {
                    log.error(mapsClause.pos(), "jml.misplaced.var.spec",
                            mapsClause.token.internedName());
                } else {
                    if (mostRecentVarDecl.fieldSpecs == null) {
                        mostRecentVarDecl.fieldSpecs = new JmlSpecs.FieldSpecs(
                                mostRecentVarDecl);
                    }
                    mostRecentVarDecl.fieldSpecs.list.append(mapsClause);
                    currentVariableDecl = mostRecentVarDecl;
                }
            } else if (jt == READABLE || jt == WRITABLE) {
                list.append(parseReadableWritable(mods, jt));
            } else if (jt == MONITORS_FOR) {
                list.append(parseMonitorsFor(mods));
            } else if (jt == INITIALIZER || jt == STATIC_INITIALIZER) {
                //@ FIXME - modifiers?
                JmlTypeClauseInitializer initializer = jmlF.at(pos()).JmlTypeClauseInitializer(jt,mods);
                initializer.specs = currentMethodSpecs;
                currentMethodSpecs = null;
                list.append(to(initializer));
                nextToken();
            } else {
                jmlerror(pos(), endPos(),
                        "jml.illegal.token.for.declaration", jt.internedName());
                skipThroughSemi();
                break;
            }
        }
        return list.toList();
    }

    /**
     * This method runs through a list of declarations in a class body, finding
     * the method and field annotations and associating them with the correct
     * declarations, issuing errors if they are in the wrong place. It also sorts 
     * out the Java declarations and the specifications.
     * 
     */
//    // This is static because it is called outside the parser as well
//    static public void filterTypeBodyDeclarations(JmlClassDecl decl,
//            Context context, JmlTree.Maker jmlF) {
//        Log log = Log.instance(context);
//        
//        // decl.defs contains all of the declarations in the decl class,
//        // including method and field annotations as individual declarations.
//        // In the end we want two things:
//        // a) All method and field specs associated with the appropriate method
//        // or field declaration, and not in the decl.defs list
//        // b) The decl.defs list should just have Java declarations and the
//        // decl.typespecs list should have all the class, method, field and initializer
//        // declarations that were in decl.defs, in the same order.
//        List<JCTree> list = decl.defs;
//        JmlSpecs.TypeSpecs typeSpecs = new JmlSpecs.TypeSpecs(decl);
//        ListBuffer<JCTree> javalist = new ListBuffer<>();
//        JmlVariableDecl currentVarDecl = null;
//        JmlVariableDecl mostRecentVarDecl = null;
//        JmlMethodSpecs currentMethodSpecs = null;
//        
//        Iterator<JCTree> iter = list.iterator();
//        while (iter.hasNext()) {
//            JCTree tree = iter.next();
//            mostRecentVarDecl = currentVarDecl;
//            currentVarDecl = null;
//            if (tree instanceof JmlVariableDecl) {
//                // A Java field declaration
//                currentVarDecl = (JmlVariableDecl) tree;
//                JCModifiers mods = currentVarDecl.mods;
//                if (currentVarDecl.fieldSpecs == null) {
//                    currentVarDecl.fieldSpecs = new JmlSpecs.FieldSpecs(mods);
//                } else {
//                    currentVarDecl.fieldSpecs.mods.annotations.appendList(mods.annotations);
//                }
//                javalist.append(tree);
//                
//            } else if (tree instanceof JmlTypeClauseIn
//                    || tree instanceof JmlTypeClauseMaps) {
//                /**
//                 * in and maps clauses get attached to the just preceding
//                 * variable declaration
//                 */
//                if (tree instanceof JmlTypeClauseIn) {
//                    ((JmlTypeClauseIn) tree).parentVar = mostRecentVarDecl;
//                }
//                if (mostRecentVarDecl == null) {
//                    log.error(tree.pos(), "jml.misplaced.var.spec",
//                            ((JmlTypeClause) tree).token.internedName());
//                } else {
//                    if (mostRecentVarDecl.fieldSpecs == null) {
//                        mostRecentVarDecl.fieldSpecs = new JmlSpecs.FieldSpecs(
//                                mostRecentVarDecl.mods);
//                    }
//                    mostRecentVarDecl.fieldSpecs.list
//                            .append((JmlTypeClause) tree);
//                    currentVarDecl = mostRecentVarDecl;
//                }
//            } else if (tree instanceof JmlMethodDecl) {
//                JmlMethodDecl mdecl = (JmlMethodDecl) tree;
//                mdecl.cases = currentMethodSpecs;
//                currentMethodSpecs.decl = mdecl;
//                javalist.append(mdecl);
//                currentMethodSpecs = null;
//            } else if (tree instanceof JmlMethodSpecs) {
//                // Method specifications come before the declaration they
//                // specify.
//                // They can apply to (a) a method declaration, (b) a ghost or
//                // model method declaration
//                // (c) a JML initializer clause, or (d) a Java initializer
//                // block.
//                // All consecutive method spec clauses are grouped together into
//                // one JmlMethodSpecs
//                currentMethodSpecs = (JmlMethodSpecs) tree;
//                continue;
//
//            } else if (tree instanceof JmlTypeClauseDecl) {
//                // A ghost or model declaration within a class
//                JmlTypeClauseDecl tcd = (JmlTypeClauseDecl) tree;
//                tree = tcd.decl;
//                if (tree instanceof JmlVariableDecl) {
//                    if (currentMethodSpecs != null) log.error(currentMethodSpecs.pos(), "jml.misplaced.method.spec");
//                    currentVarDecl = (JmlVariableDecl) tree;
//                } else if (tree instanceof JmlMethodDecl) {
//                    if ( ((JmlMethodDecl)tree).name.toString().equals("initialCharSequence")) Utils.stop();
//                    JmlMethodDecl mdecl = (JmlMethodDecl) ((JmlTypeClauseDecl) tree).decl;
//                    mdecl.cases = currentMethodSpecs;
//                } else if (tree instanceof JmlClassDecl) {
//                    // OK
//                    if (currentMethodSpecs != null) log.error(currentMethodSpecs.pos(), "jml.misplaced.method.spec");
//                    typeSpecs.modelTypes.add((JmlClassDecl)tree);
//                    tree = null;
//                } else {
//                    if (currentMethodSpecs != null) log.error(currentMethodSpecs.pos(), "jml.misplaced.method.spec");
//                    log.error(tree.pos(), "jml.internal.notsobad",
//                            "An unknown kind of JmlTypeClauseDecl was encountered and not handled: "
//                                    + tree.getClass());
//                    tree = null;
//                }
//                currentMethodSpecs = null;
//                if (tree != null) typeSpecs.decls.append(tcd);
//                
//                // All the declarations need to be kept in the class declaration, 
//                // in the order in which they are declared
//                if (tree != null) javalist.append(tree);
//
//            } else if (tree instanceof JmlTypeClause) {
//                if (tree instanceof JmlTypeClauseInitializer) {
//                    JmlTypeClauseInitializer tsp = (JmlTypeClauseInitializer) tree;
//                    tsp.specs = currentMethodSpecs;
//                    currentMethodSpecs = null;
//                    checkInitializer(tsp, typeSpecs, context, jmlF);
//                } else {
//                    // FIXME - what is this?
//                    typeSpecs.clauses.append((JmlTypeClause) tree);
//                }
//            } else if (tree instanceof JCTree.JCBlock) {
//                typeSpecs.blocks
//                        .put((JCTree.JCBlock) tree,
//                                new JmlSpecs.MethodSpecs(
//                                        JmlTree.Maker.instance(context)
//                                                .Modifiers(0), currentMethodSpecs));
//                currentMethodSpecs = null;
//                javalist.append(tree);
//            } else {
//                // presume that everything left is a valid Java declaration
//                javalist.append(tree);
//            }
//            if (currentMethodSpecs != null) {
//                log.error(currentMethodSpecs.pos(), "jml.misplaced.method.spec");
//                currentMethodSpecs = null;
//            }
//        }
//        typeSpecs.modifiers = decl.mods;
//        typeSpecs.file = decl.source();
//        typeSpecs.decl = decl;
//        decl.defs = javalist.toList();
//        decl.typeSpecs = typeSpecs; // The type specs from just this compilation
//                                    // unit
//    }


    /** Parses a maps clause */
    public JmlTypeClauseMaps parseMaps(int pos, JCModifiers mods,
            ListBuffer<JCTree> list) {
        if (!isNone(mods))
            jmlerror(mods.getStartPosition(), mods.getPreferredPosition(),
                    getEndPos(mods), "jml.no.mods.allowed",
                    JmlTokenKind.MAPS.internedName());
        S.setJmlKeyword(false);
        nextToken(); // skip over the maps token
        JCExpression e = parseMapsTarget();
        ListBuffer<JmlGroupName> glist;
        if (jmlTokenKind() != JmlTokenKind.BSINTO) {
            jmlerror(pos(), endPos(), "jml.expected",
                    "an \\into token here, or the maps target is ill-formed");
            glist = new ListBuffer<JmlGroupName>();
            S.setJmlKeyword(true);
            skipThroughSemi();
        } else {
            nextToken();
            glist = parseGroupNameList();
            S.setJmlKeyword(true);
            if (token.kind != TokenKind.SEMI) {
                jmlerror(pos(), endPos(), "jml.bad.construct",
                        "maps clause");
                skipThroughSemi();
            } else {
                nextToken();
            }
        }
        return toP(jmlF.at(pos).JmlTypeClauseMaps(e, glist.toList()));
    }

    /** Parses the target portion (before the \\into) of a maps clause */
    public JCExpression parseMapsTarget() {
        int p = pos();
        if (token.kind != IDENTIFIER) {
            jmlerror(pos(), endPos(), "jml.expected", "an identifier");
            skipThroughSemi();
            return toP(jmlF.at(p).Erroneous());
        }
        Name n = ident();
        JCExpression result = to(jmlF.at(p).Ident(n));
        if (token.kind == LBRACKET) {
            result = parseArrayRangeExpr(result, false);
        }
        if (token.kind == DOT) {
            nextToken();
            if (token.kind == STAR) {
                nextToken();
                n = null;
            } else if (token.kind == IDENTIFIER) {
                n = ident();
            } else {
                jmlerror(pos(), endPos(), "jml.ident.or.star.after.dot");
                skipThroughSemi();
                return toP(jmlF.at(p).Erroneous());
            }
            // Caution: Java will not expect n to be null
            // It is null to denote a wildcard selector
            result = to(jmlF.at(p).Select(result, n));
        } else if (!(result instanceof JmlStoreRefArrayRange)) {
            jmlerror(pos(), endPos(), "jml.expected",
                    "a . to select a field");
            skipThroughSemi();
            return to(jmlF.at(p).Erroneous());
        }
        return result;
    }

    /** Parses an in clause */
    public JmlTypeClauseIn parseIn(int pos, JCModifiers mods) {
        if (!isNone(mods))
            jmlerror(pos, "jml.no.mods.allowed", JmlTokenKind.IN.internedName());
        S.setJmlKeyword(false);
        nextToken(); // skip over the in token
        ListBuffer<JmlGroupName> list = parseGroupNameList();
        S.setJmlKeyword(true);
        accept(SEMI);
        return toP(jmlF.at(pos).JmlTypeClauseIn(list.toList()));
    }

    /** Parses an invariant, initially, or axiom declaration */
    public JmlTypeClauseExpr parseInvariantInitiallyAxiom(JCModifiers mods) {
        int pos = pos();
        JmlTokenKind jt = jmlTokenKind();
        S.setJmlKeyword(false);
        nextToken();
        JCExpression e = parseExpression();
        S.setJmlKeyword(true);
        if (token.kind != SEMI) {
            jmlerror(pos(), endPos(), "jml.bad.construct",
                    jt.internedName() + " declaration");
            skipThroughSemi();
        } else {
            nextToken();
        }
        if (mods == null) mods = jmlF.at(pos).Modifiers(0);
        JmlTypeClauseExpr tcl = to(jmlF.at(pos).JmlTypeClauseExpr(mods, jt, e));
        tcl.source = log.currentSourceFile();
        return tcl;
    }

    /** Parses a represents clause */
    public JmlTypeClauseRepresents parseRepresents(JCModifiers mods) {
        S.setJmlKeyword(false);
        int pos = pos();
        nextToken();
        JCExpression id = parseStoreRef(true);
        boolean suchThat;
        JCExpression e;
        if (token.kind == EQ) {
            suchThat = false;
            nextToken();
            e = parseExpression();
        } else if (jmlTokenKind() == JmlTokenKind.LEFT_ARROW) {
            if (isDeprecationSet() || JmlOption.isOption(context, JmlOption.STRICT)) {
                log.warning(pos(), "jml.deprecated.left.arrow.in.represents");
            }
            suchThat = false;
            nextToken();
            e = parseExpression();
        } else if (jmlTokenKind() == JmlTokenKind.BSSUCHTHAT) {
            suchThat = true;
            nextToken();
            e = parseExpression();
        } else {
            jmlerror(pos(), endPos(), "jml.bad.represents.token");
            e = null;
            skipToSemi();
            suchThat = false;
        }
        S.setJmlKeyword(true);
        if (e == null) { // skip
            e = jmlF.Erroneous();
        } else if (token.kind != SEMI) {
            jmlerror(pos(), endPos(),
                    "jml.invalid.expression.or.missing.semi");
            skipThroughSemi();
        } else {
            nextToken();
        }
        if (mods == null) mods = jmlF.at(pos).Modifiers(0);
        JmlTypeClauseRepresents tcl = to(jmlF.at(pos).JmlTypeClauseRepresents(
                mods, id, suchThat, e));
        tcl.source = log.currentSourceFile();
        return tcl;
    }

    /** Parses a constraint clause */
    public JmlTypeClauseConstraint parseConstraint(JCModifiers mods) {
        int pos = pos();
        S.setJmlKeyword(false);
        nextToken();
        JCExpression e = parseExpression();
        S.setJmlKeyword(true);
        List<JmlMethodSig> sigs = null;
        boolean notlist = false;
        if (token.kind == FOR) {
            nextToken();
            if (token.kind == BANG) {
                notlist = true;
                nextToken();
            }
            if (jmlTokenKind() == JmlTokenKind.BSEVERYTHING || jmlTokenKind() == JmlTokenKind.BSNOTSPECIFIED) {
                nextToken();
                // This is the default, so we just leave sigs null
                if (notlist) sigs = new ListBuffer<JmlMethodSig>().toList();
                notlist = false;
            } else if (jmlTokenKind() == JmlTokenKind.BSNOTHING) {
                nextToken();
                if (!notlist) sigs = new ListBuffer<JmlMethodSig>().toList();
                notlist = false;
                // Here we just have an empty list
            } else {
                sigs = parseMethodNameList();
            }
        }
        if (mods == null) mods = jmlF.at(pos).Modifiers(0);
        JmlTypeClauseConstraint tcl = to(jmlF.at(pos).JmlTypeClauseConstraint(
                mods, e, sigs));
        tcl.notlist = notlist;
        tcl.source = log.currentSourceFile();
        if (token.kind != SEMI) {
            jmlerror(pos(), endPos(), "jml.bad.construct",
                    "constraint declaration");
            skipThroughSemi();
        } else {
            nextToken();
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
            toP(m);
            if (token.kind != COMMA) break;
            nextToken();
        }
        S.setJmlKeyword(true);
        return sigs.toList();
    }

    /** Parses a method-name */
    public JmlMethodSig parseMethodName() {
        int initpos = pos();
        int p = initpos;
        Name n = null;
        JCTree newType = null;
        if (token.kind == NEW) {
            newType = parseType();
            // FIXME - check that it is a reference type
        } else if (token.kind == IDENTIFIER) {
            n = ident();
        } else if (token.kind == THIS) {
            n = names._this;
            nextToken();
        } else if (token.kind == SUPER) {
            n = names._super;
            nextToken();
        } else {
            jmlerror(pos(), endPos(), "jml.bad.construct",
                    "constraint method");
            return null;
        }
        JCExpression id = null;
        if (newType == null) {
            id = jmlF.at(p).Ident(n);
            boolean first = true;
            while (token.kind == DOT) {
                nextToken();
                p = pos();
                if (token.kind == IDENTIFIER) {
                    n = ident();
                } else if (token.kind == THIS) {
                    n = names._this;
                    nextToken();
                } else if (token.kind == STAR) {
                    // * may only be the only thing after any dot, if it is
                    // present
                    if (!first) {
                        jmlerror(pos(), endPos(), "jml.expected",
                                "identifier or this, since a * may only be used after the first dot");
                    }
                    n = names.asterisk;
                    nextToken();
                    if (token.kind == DOT) {
                        jmlerror(pos(), endPos(), "jml.expected",
                                "no dot, since a dot may not be used after a *");
                    }
                } else {
                    jmlerror(pos(), endPos(), "jml.expected",
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
        if (token.kind == LPAREN) {
            args = new ListBuffer<JCExpression>();
            nextToken();
            if (token.kind != RPAREN) {
                JCExpression arg = parseType();
                args.append(arg);
                while (token.kind == COMMA) {
                    nextToken();
                    arg = parseType();
                    args.append(arg);
                }
                if (token.kind != RPAREN) {
                    jmlerror(pos(), endPos(), "jml.expected",
                            "comma or right parenthesis");
                } else {
                    nextToken();
                }
            } else {
                nextToken(); // consume the RPAREN
            }
        }
        return jmlF.at(initpos).JmlConstraintMethodSig(id,
                args == null ? null : args.toList());
    }

    /** Parse a readable or writable clause */
    public JmlTypeClauseConditional parseReadableWritable(JCModifiers mods,
            JmlTokenKind jmlTokenKind) {
        int p = pos();
        S.setJmlKeyword(false);
        nextToken();
        Name n;
        JCExpression e;
        int identPos = pos();
        if (token.kind != TokenKind.IDENTIFIER) {
            jmlerror(pos(), endPos(), "jml.expected", "an identifier");
            n = names.asterisk; // place holder for an error situation
            e = jmlF.Erroneous();
        } else {
            n = ident();
            if (token.kind != IF) {
                jmlerror(pos(), endPos(), "jml.expected", "an if token");
                e = jmlF.Erroneous();
            } else {
                accept(TokenKind.IF);
                e = parseExpression();
            }
        }
        JCTree.JCIdent id = to(jmlF.at(identPos).Ident(n));
        S.setJmlKeyword(true);
        if (e.getTag() == JCTree.Tag.ERRONEOUS || token.kind != SEMI) {
            skipThroughSemi();
        } else {
            nextToken();
        }
        return toP(jmlF.at(p).JmlTypeClauseConditional(mods, jmlTokenKind, id, e));
    }

    /** Parse a monitors_for clause */
    public JmlTypeClauseMonitorsFor parseMonitorsFor(JCModifiers mods) {
        int p = pos();
        S.setJmlKeyword(false);
        nextToken();
        ListBuffer<JCExpression> elist = new ListBuffer<JCExpression>();
        Name n;
        int identPos = pos();
        ITokenKind tk = token.kind;
        if (tk != IDENTIFIER) {
            jmlerror(pos(), endPos(), "jml.expected", "an identifier");
            n = names.asterisk; // place holder for an error situation
        } else {
            n = ident(); // Advances to next token
            if (token.kind != TokenKind.EQ && jmlTokenKind() != JmlTokenKind.LEFT_ARROW) {
                jmlerror(pos(), endPos(), "jml.expected",
                        "an = or <- token");
            } else {
                nextToken();
                elist = expressionList();
            }
        }
        JCTree.JCIdent id = to(jmlF.at(identPos).Ident(n));
        S.setJmlKeyword(true);
        if (token.kind != SEMI) {
            skipThroughSemi();
        } else {
            nextToken();
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
        ListBuffer<JCExpression> args = new ListBuffer<>();
        args.append(parseExpression());
        while (token.kind == COMMA) {
            nextToken();
            JCExpression e = parseExpression();
            args.append(e); // e might be a JCErroneous
        }
        return args;
    }

    public JCExpression parseStoreRefListExpr() {
        int p = pos();
        JmlTokenKind jt = jmlTokenKind();
        nextToken();
        accept(LPAREN);
        ListBuffer<JCExpression> list = parseStoreRefList(false);
        if (token.kind != RPAREN) {
            jmlerror(pos(), endPos(), "log.expected", "right parenthesis");
            skipThroughRightParen();
        } else {
            nextToken();
        }
        return toP(jmlF.at(p).JmlStoreRefListExpression(jt, list.toList()));
    }

    public JmlMethodSpecs parseMethodSpecs(JCModifiers mods) {
        // Method specifications are a sequence of specification cases
        ListBuffer<JmlSpecificationCase> cases = new ListBuffer<JmlSpecificationCase>();
        JmlSpecificationCase c;
        JmlTokenKind t;
        int pos = pos();
        int lastPos = Position.NOPOS;
        while ((c = parseSpecificationCase(mods, false)) != null) {
            cases.append(c);
            lastPos = getEndPos(c);
            mods = modifiersOpt();
        }
        JmlMethodSpecs sp = jmlF.at(pos).JmlMethodSpecs(cases.toList());
        // end position set below
        if ((t = jmlTokenKind()) == JmlTokenKind.IMPLIES_THAT) {
            if (!isNone(mods))
                jmlerror(pos(), endPos(), "jml.no.mods.allowed",
                        t.internedName());
            nextToken();
            mods = modifiersOpt();
            cases = new ListBuffer<JmlSpecificationCase>();
            while ((c = parseSpecificationCase(mods, false)) != null) {
                cases.append(c);
                lastPos = getEndPos(c);
                mods = modifiersOpt();
            }
            if (cases.size() > 0) cases.first().also = t;
            sp.impliesThatCases = cases.toList();
        }
        if ((t = jmlTokenKind()) == JmlTokenKind.FOR_EXAMPLE) {
            if (!isNone(mods))
                jmlerror(mods.getStartPosition(),
                        getEndPos(mods),
                        "jml.no.mods.allowed", t.internedName());
            nextToken();
            mods = modifiersOpt();
            cases = new ListBuffer<JmlSpecificationCase>();
            while ((c = parseSpecificationCase(mods, true)) != null) {
                cases.append(c);
                lastPos = getEndPos(c);
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
        JmlTokenKind also = null;
        JmlTokenKind ijt = jmlTokenKind();
        if (ijt == ALSO) {
            if (!isNone(mods)) {
                jmlerror(mods.getStartPosition(), endPos(),
                        "jml.no.mods.allowed", ijt.internedName());
                mods = null;
            }
            nextToken();
            also = ijt;
            // get any modifiers
            mods = modifiersOpt();
        }
        boolean code = false;
        int codePos = 0;
        if (jmlTokenKind() == JmlTokenKind.CODE) {
            codePos = pos();
            code = true;
            nextToken();
        }

        JmlTokenKind jt = jmlTokenKind();
        int pos = pos();
        if (jt == JmlTokenKind.BEHAVIOR || jt == JmlTokenKind.NORMAL_BEHAVIOR
                || jt == JmlTokenKind.EXCEPTIONAL_BEHAVIOR
                || (jt == JmlTokenKind.ABRUPT_BEHAVIOR && inModelProgram)) {
            if (exampleSection) {
                log.warning(pos(), "jml.example.keyword", "must not",
                        jt.internedName());
            }
            nextToken();
        } else if (jt == JmlTokenKind.EXAMPLE || jt == JmlTokenKind.NORMAL_EXAMPLE
                || jt == JmlTokenKind.EXCEPTIONAL_EXAMPLE) {
            if (!exampleSection) {
                log.warning(pos(), "jml.example.keyword", "must",
                        jt.internedName());
            }
            nextToken();
        } else if (jt == MODEL_PROGRAM) {
            JmlSpecificationCase j = parseModelProgram(mods, code, also);
            j.sourcefile = log.currentSourceFile();
            return j;
        } else if (jt == null && S.jml() && also != null) {
            jmlerror(pos(), endPos(), "jml.invalid.keyword.in.spec",
                    S.chars());
            skipThroughSemi();
            // Call it lightweight
        } else {
            jt = null;
            if (code) log.warning(codePos, "jml.misplaced.code");
            // lightweight
        }
        
        ListBuffer<JmlMethodClause> clauses = new ListBuffer<JmlMethodClause>();
        JmlMethodClause e;
        while (token.kind == CUSTOM && (e = getClause()) != null) {
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
            boolean code, JmlTokenKind also) {
        int pos = pos();
        nextToken(); // skip over the model_program token

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
        int p = pos();
        ListBuffer<JmlSpecificationCase> list = new ListBuffer<JmlSpecificationCase>();
        nextToken();
        do {
            JmlSpecificationCase g = parseSpecificationCase(null, false);
            if (g == null) {
                // Empty specification group
                // Warning happens below as an invalid specification group end
            } else {
                list.append(g);
            }
            if (jmlTokenKind() == ENDJMLCOMMENT) nextToken();
        } while (jmlTokenKind() == ALSO);
        if (jmlTokenKind() == ENDJMLCOMMENT) nextToken();
        if (jmlTokenKind() != SPEC_GROUP_END) {
            jmlerror(pos(), endPos(), "jml.invalid.spec.group.end");
            while (jmlTokenKind() != JmlTokenKind.ENDJMLCOMMENT && token.kind != EOF)
                nextToken();
            if (token.kind != EOF) nextToken();
        } else {
            nextToken();
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
        //String dc = S.docComment; // FIXME - do we need to do this?
        while (jmlTokenKind() == ENDJMLCOMMENT) {
            nextToken();
            //S.docComment = dc;
        }
        JmlTokenKind jt = jmlTokenKind();
        int pos = pos();
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
                    warnNotImplemented(pos(), jt.internedName(),
                            "JmlParser.getClause()");
                    nextToken();
                    JmlStoreRefKeyword refkeyword = parseOptStoreRefKeyword();
                    List<JmlMethodSig> sigs = null;
                    if (refkeyword == null) {
                        sigs = parseMethodNameList();
                    }
                    S.setJmlKeyword(true);
                    int endpos = pos();
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
                        jmlerror(pos(), endPos(),
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
        rescan();
        return res;
    }

    /** Parses either a \\not_specified token or a JML expression */
    public JCExpression parsePredicateOrNotSpecified() {
        if (jmlTokenKind() == BSNOTSPECIFIED) {
            int pos = pos();
            nextToken();
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
        JmlTokenKind jt = jmlTokenKind();
        int pos = pos();
        nextToken();
        JCExpression e = parsePredicateOrNotSpecified();
        S.setJmlKeyword(true);
        if (token.kind != SEMI) {
            syntaxError(pos(), null, "jml.invalid.expression.or.missing.semi");
            skipThroughSemi();
        } else {
            nextToken(); // skip SEMI
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
        JmlTokenKind jt = jmlTokenKind();
        int pos = pos();
        JCExpression e;
        nextToken();
        JCExpression t = null;
        Name ident = null;
        int rpos = pos;
        if (token.kind != LPAREN) {
            syntaxError(pos(), null, "jml.expected.lparen.signals");
            t = to(jmlF.at(pos()).Ident(names.fromString("java")));
            t = to(jmlF.at(pos()).Select(t, names.fromString("lang")));
            t = to(jmlF.at(pos()).Select(t, names.fromString("Exception")));
            e = parsePredicateOrNotSpecified();
        } else {
            nextToken();
            // Get type
            t = parseType();
            // Get identifier (optional)
            if (token.kind == IDENTIFIER) {
                ident = ident();
            }
            rpos = pos();
            if (token.kind != RPAREN) {
                syntaxError(pos(), null, "jml.expected.rparen.signals");
                skipToSemi();
                e = toP(jmlF.at(pos()).Erroneous());
            } else {
                nextToken();
                if (token.kind == SEMI) {
                    e = toP(jmlF.at(pos()).Literal(TypeTag.BOOLEAN, 1)); // Boolean.TRUE));
                } else {
                    e = parsePredicateOrNotSpecified();
                }
            }
        }
        S.setJmlKeyword(true);
        JCTree.JCVariableDecl var = jmlF.at(t.pos).VarDef(
                jmlF.at(t.pos).Modifiers(0), ident, t, null);
        storeEnd(var, rpos);
        if (token.kind != SEMI) {
            if (e.getKind() != Kind.ERRONEOUS)
                syntaxError(pos(), null, "jml.missing.semi");
            skipThroughSemi();
        } else {
            nextToken();
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
        JmlTokenKind clauseType = jmlTokenKind();
        int pos = pos();
        nextToken();
        JmlTokenKind jt = jmlTokenKind();
        ITokenKind tk = token.kind;
        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();

        if (jt == BSNOTHING) {
            S.setJmlKeyword(true);
            nextToken();
            if (token.kind != SEMI) {
                syntaxError(pos(), null, "jml.expected.semi.after.nothing");
                skipThroughSemi();
            } else {
                nextToken();
            }
        } else if (tk == SEMI) {
            S.setJmlKeyword(true);
            syntaxError(pos(), null, "jml.use.nothing", clauseType.internedName());
            nextToken();
        } else {
            while (true) {
                JCExpression typ = parseType(); // if this fails, a JCErroneous
                // is returned
                list.append(typ);
                tk = token.kind;
                if (tk == SEMI) {
                    S.setJmlKeyword(true);
                    nextToken();
                    break;
                } else if (tk == COMMA) {
                    nextToken();
                    continue;
                } else if (typ instanceof JCErroneous) {
                    S.setJmlKeyword(true);
                    skipThroughSemi();
                    break;
                } else if (jmlTokenKind() == ENDJMLCOMMENT) {
                    syntaxError(pos(), null, "jml.missing.semi");
                } else {
                    syntaxError(pos(), null, "jml.missing.comma");
                    continue;
                }
                // error
                S.setJmlKeyword(true);
                skipThroughSemi();
                break;
            }
        }
        return toP(jmlF.at(pos).JmlMethodClauseSignalsOnly(clauseType, list.toList()));
    }

    public JmlMethodClauseDecl parseForallOld() {
        int pos = pos();
        JmlTokenKind jt = jmlTokenKind();
        nextToken();
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
        if (token.kind == SEMI) {
            nextToken();
        } else {
            jmlerror(pos(), endPos(), "jml.bad.construct",
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
        int pos = pos();
        JmlTokenKind jt = jmlTokenKind();
        JCExpression p = null;
        nextToken();
        JCExpression e = parsePredicateOrNotSpecified();
        if (token.kind == IF) { // The if is not allowed if the
            // expression is not_specified, but we test that
            // during type checking
            nextToken();
            p = parseExpression();
        }
        JmlMethodClauseConditional res = to(jmlF.at(pos)
                .JmlMethodClauseConditional(jt, e, p));
        S.setJmlKeyword(true);
        if (token.kind == SEMI) {
            nextToken();
        } else {
            jmlerror(pos(), endPos(), "jml.bad.construct",
                    jt.internedName() + " specification");
            skipThroughSemi();
        }
        return res;
    }

    /** Parses "assignable" <store-ref-list> ";" */
    public JmlMethodClauseStoreRef parseStoreRefClause() {
        JmlTokenKind jt = jmlTokenKind();
        int pos = pos();
        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
        nextToken(); // skip over the assignable token
        if (token.kind == SEMI) {
            syntaxError(pos(), null, "jml.use.nothing.assignable");
            S.setJmlKeyword(true);
            nextToken(); // skip over the SEMI
        } else {
            list = parseStoreRefList(false);
            if (token.kind == SEMI) {
                // OK, go on
            } else if (jmlTokenKind() == ENDJMLCOMMENT) {
                syntaxError(pos(), null, "jml.missing.semi");
            }
            S.setJmlKeyword(true);
            if (token.kind != SEMI) {
                // error already reported
                skipThroughSemi();
            } else {
                if (list.isEmpty()) {
                    syntaxError(pos(), null, "jml.use.nothing.assignable");
                }
                nextToken();
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
            ITokenKind tk = token.kind;
            if (tk == COMMA) {
                nextToken();
                continue;
            } else if (tk == SEMI || tk == RPAREN) {
                return list;
            } else if (jmlTokenKind() == ENDJMLCOMMENT) {
                // The missing semi-colon is reported by the caller
                return list;
            } else {
                syntaxError(pos(), null, "jml.missing.comma");
                if (r == null) return list;
            }
        }
    }

    /** Parses a storeRefKeyword or returns null (with no error message) */
    public JmlStoreRefKeyword parseOptStoreRefKeyword() {
        JmlTokenKind jt = jmlTokenKind();
        int p = pos();
        if (jt == BSNOTHING || jt == BSEVERYTHING || jt == BSNOTSPECIFIED) {
            JmlStoreRefKeyword s = to(jmlF.at(p).JmlStoreRefKeyword(jt));
            nextToken();
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
                if (token.kind == DOT) {
                    int dotpos = pos();
                    nextToken();
                    if (!strictId && token.kind == STAR) {
                        nextToken();
                        // Caution: Java will not expect the field selector to
                        // be null
                        e = toP(jmlF.at(dotpos).Select(e, (Name) null));
                        if (token.kind != COMMA && token.kind != SEMI
                                && token.kind != RPAREN) {
                            jmlerror(pos(), endPos(), "jml.not.after.star");
                            skipToCommaOrSemi();
                        }
                        break;
                    } else if (token.kind == IDENTIFIER) {
                        Name n = ident();
                        e = to(jmlF.at(dotpos).Select(e, n));
                        continue;
                    } else {
                        if (strictId)
                            jmlerror(pos(), endPos(), "jml.expected.id");
                        else
                            jmlerror(pos(), endPos(),
                                    "jml.ident.or.star.after.dot");
                        skipToCommaOrSemi();
                        break;
                    }

                } else if (token.kind == LBRACKET) {
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
        JmlTokenKind jt = jmlTokenKind();
        int p = pos();
        if (!strictId && (jt == INFORMAL_COMMENT)) {
            JCExpression s = to(jmlF.at(p).JmlStoreRefKeyword(jt));
            nextToken();
            return s;
        } else if (token.kind == IDENTIFIER) {
            Name n = ident();
            JCTree.JCIdent id = to(jmlF.at(p).Ident(n));
            return id;
        } else if (token.kind == SUPER) {
            nextToken(); // skip over the this or super
            JCTree.JCIdent id = toP(jmlF.at(p).Ident(names._super));
            return id;
        } else if (token.kind == THIS) {
            nextToken(); // skip over the this or super
            JCTree.JCIdent id = toP(jmlF.at(p).Ident(names._this));
            return id;
        }
        jmlerror(p, endPos(), "jml.bad.store.ref");
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
        while (token.kind == LBRACKET) {
            nextToken(); // move past the LBRACKET
            if (token.kind == STAR) {
                if (strictId) {
                    jmlerror(pos(), endPos(), "jml.no.star.in.strict.mode");
                }
                nextToken();
                if (token.kind == RBRACKET) {
                    nextToken();
                    t = toP(jmlF.at(t.pos).JmlStoreRefArrayRange(t, null, null));
                    continue;
                } else {
                    jmlerror(pos(), endPos(), "jml.expected.rbracket.star");
                    skipToCommaOrSemi();
                    break;
                }
            } else {
                JCExpression lo = parseExpression();
                if (token.kind == RBRACKET) {
                    t = to(jmlF.at(t.pos).JmlStoreRefArrayRange(t, lo, lo));
                    nextToken();
                    continue;
                } else if (!strictId && jmlTokenKind() == DOT_DOT) {
                    nextToken();
                    JCExpression hi = null;
                    int rbracketPos = pos();
                    if (token.kind == STAR) {
                        nextToken();
                    } else if (token.kind == RBRACKET) {
                        if (JmlOption.isOption(context, JmlOption.STRICT)) {
                            log.warning(rbracketPos,"jml.not.strict","storeref with implied end-of-range (a[i..])");
                        }
                        // OK - missing hi end implies end of array
                    } else {
                        hi = parseExpression();
                    }
                    if (token.kind == RBRACKET) {
                        t = to(jmlF.at(t.pos).JmlStoreRefArrayRange(t, lo, hi));
                        nextToken();
                    } else {
                        jmlerror(pos(), endPos(), "jml.expected.rbracket");
                        skipToCommaOrSemi();
                        break;
                    }
                    continue;
                } else {
                    jmlerror(pos(), endPos(),
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
                    pos(),
                    endPos(),
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
        while (token.kind == CUSTOM) {
            partial = jmlModifiersOpt(partial);
            if (token.kind == CUSTOM) break;
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
    protected/* @ nullable */JCAnnotation tokenToAnnotationAST(JmlTokenKind jt,
            int position, int endpos) {
        Class<?> c = jt.annotationType;
        if (c == null) return null;
        JCExpression t = to(F.at(position).Ident(names.fromString("org")));
        t = to(F.at(position).Select(t, names.fromString("jmlspecs")));
        t = to(F.at(position).Select(t, names.fromString("annotation")));
        t = to(F.at(position).Select(t, names.fromString(c.getSimpleName())));
        JCAnnotation ann = to(F.at(position).Annotation(t,
                List.<JCExpression> nil()));
        ((JmlTree.JmlAnnotation)ann).sourcefile = log.currentSourceFile();
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
        JmlTokenKind j;
        while ((j = jmlTokenKind()) != null) {
            if (JmlTokenKind.modifiers.contains(j)) {
                last = endPos();
                JCAnnotation a = tokenToAnnotationAST(j, pos(), last);  // FIXME -is position correct?
                if (a != null) {
                    annotations.append(a);
                    if (pos == Position.NOPOS) pos = a.getStartPosition();
                }
                // a is null if no annotation is defined for the modifier;
                // we just silently ignore that situation
                // (this is true at the moment for math annotations, but could
                // also be true for a modifier someone forgot)
                if (JmlTokenKind.extensions.contains(j) && JmlOption.isOption(context, JmlOption.STRICT)) {
                    log.warning(pos(),"jml.not.strict",j.internedName());  // FIXME - probably wrong position
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
            nextToken();
        }
        JCModifiers mods = F.at(pos).Modifiers(
                partial == null ? 0 : partial.flags, annotations.toList());
        if (last != Position.NOPOS) storeEnd(mods, last);
        return mods;
    }

    @Override
    public JCPrimitiveTypeTree basicType() {
        JmlTokenKind jt = jmlTokenKind();
        if (jt == null) {
            return super.basicType();
        } else if (jt == JmlTokenKind.BSTYPEUC || jt == JmlTokenKind.BSBIGINT
                || jt == JmlTokenKind.BSREAL) {
            JCPrimitiveTypeTree t = to(jmlF.at(pos())
                    .JmlPrimitiveTypeTree(jt));
            nextToken();
            return t;
        } else {
            jmlerror(pos(), endPos(), "jml.expected", "JML type token");
            JCPrimitiveTypeTree t = to(F.at(pos()).TypeIdent(
                    typetag(TokenKind.VOID)));
            nextToken();
            return t;
        }
    }
    
    @Override
    protected Name ident() {
        if (token.kind == CUSTOM) {
            jmlerror(pos(),endPos(),"jml.keyword.instead.of.ident",jmlTokenKind().internedName());
            nextToken();
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
        if ((mode & EXPR) != 0 && token.kind == QUES) {
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
                && (jmlTokenKind() == JmlTokenKind.EQUIVALENCE || jmlTokenKind() == JmlTokenKind.INEQUIVALENCE)) {
            mode = EXPR;
            return term2EquivRest(t);
        } else {
            return t;
        }
    }

    protected JCExpression term2EquivRest(JCExpression t) {
        JmlTokenKind jt = jmlTokenKind();
        while (jt == JmlTokenKind.EQUIVALENCE || jt == JmlTokenKind.INEQUIVALENCE) {
            int ppos = pos(); // position of the operator
            nextToken();
            JCExpression tt = term2Imp();
            t = toP(jmlF.at(ppos).JmlBinary(jt, t, tt));
            jt = jmlTokenKind();
        }
        return t;
    }

    protected JCExpression term2Imp() {
        JCExpression t = term2();
        if ((mode & EXPR) != 0 
                && (jmlTokenKind() == JmlTokenKind.IMPLIES || jmlTokenKind() == JmlTokenKind.REVERSE_IMPLIES)) {
            mode = EXPR;
            return term2ImpRest(t);
        } else {
            return t;
        }
    }

    protected JCExpression term2ImpRest(JCExpression t) {
        JmlTokenKind jt = jmlTokenKind();
        if (jt == JmlTokenKind.IMPLIES) {
            // For IMPLIES we need to associate to the right
            int ppos = pos(); // position of the operator
            nextToken();
            JCExpression tt = term2ImpRestX();
            t = toP(jmlF.at(ppos).JmlBinary(jt, t, tt));
            if (jmlTokenKind() == JmlTokenKind.REVERSE_IMPLIES) {
                syntaxError(pos(), null, "jml.mixed.implies");
                skipToSemi();
            }
        } else if (jt == JmlTokenKind.REVERSE_IMPLIES) {
            // For REVERSE_IMPLIES we do the conventional association to the
            // left
            do {
                int ppos = pos(); // position of the operator
                nextToken();
                JCExpression tt = term2();
                t = toP(jmlF.at(ppos).JmlBinary(jt, t, tt));
                jt = jmlTokenKind();
            } while (jt == JmlTokenKind.REVERSE_IMPLIES);
            if (jt == JmlTokenKind.IMPLIES) {
                syntaxError(pos(), null, "jml.mixed.implies");
                skipToSemi();
            }
        }
        return t;
    }

    /** A local call so we can use recursion to do the association to the right */
    protected JCExpression term2ImpRestX() {
        JCExpression t = term2();
        JmlTokenKind jt = jmlTokenKind();
        if (jt != JmlTokenKind.IMPLIES) return t;
        int ppos = pos();
        nextToken();
        JCExpression tt = term2ImpRestX();
        return toP(jmlF.at(ppos).JmlBinary(jt, t, tt));
    }
    
    protected ParensResult analyzeParensHelper(Token t) {
        if (!(t instanceof JmlToken)) return ParensResult.PARENS;
        JmlTokenKind jtk = ((JmlToken)t).jmlkind;
        switch (jtk) {
            case IMPLIES: case REVERSE_IMPLIES: case EQUIVALENCE: case INEQUIVALENCE: case SUBTYPE_OF:
            case JSUBTYPE_OF: case DOT_DOT: case LEFT_ARROW: case LOCK_LE: case LOCK_LT: case RIGHT_ARROW:
                return ParensResult.PARENS;
            default:
                return ParensResult.CAST;
        }
    }

    protected ParensResult analyzeParensHelper2(int lookahead, Token t) {
        if (!(t instanceof JmlToken)) return ParensResult.PARENS;
        JmlTokenKind jtk = ((JmlToken)t).jmlkind;
        switch (jtk) {
            case BSTYPEUC: case BSREAL: case BSBIGINT:
                if (peekToken(lookahead, RPAREN)) {
                    //Type, ')' -> cast
                    return ParensResult.CAST;
                } else if (peekToken(lookahead, LAX_IDENTIFIER)) {
                    //Type, Identifier/'_'/'assert'/'enum' -> explicit lambda
                    return ParensResult.EXPLICIT_LAMBDA;
                }
                return ParensResult.PARENS;
            default:
                return ParensResult.PARENS;
        }
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
        if (token.kind == CUSTOM) {
            JCExpression t;
            JmlTokenKind jt = jmlTokenKind();
            int p = pos(); // Position of the keyword

            if (isJmlTypeToken(jt)) {
                t = to(jmlF.at(p).JmlPrimitiveTypeTree(jt));
                nextToken();
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
                    nextToken();
                    if (token.kind == LPAREN) {
                        JCExpression res = syntaxError(pos(), null,
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
                    nextToken();
                    return t;

                case INFORMAL_COMMENT:
                    t = to(jmlF.at(p).JmlSingleton(jt));
                    ((JmlSingleton) t).info = S.chars();
                    nextToken();
                    return t;

                case BSTYPELC:
                    int start = pos();
                    nextToken();
                    p = pos();
                    if (token.kind != LPAREN) {
                        return syntaxError(p, List.<JCTree> nil(),
                                "jml.args.required", jt);
                    } else {
                        accept(TokenKind.LPAREN);
                        JCExpression e;
                        if (token.kind == VOID) {
                            e = to(F.at(pos()).TypeIdent(TypeTag.VOID));
                            nextToken();
                        } else {
                            e = parseType();
                        }
                        if (token.kind != RPAREN) {
                            if (!(e instanceof JCErroneous))
                                jmlerror(pos(), endPos(),
                                        "jml.bad.bstype.expr");
                            skipThroughRightParen();
                        } else
                            nextToken();
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
                    int startx = pos();
                    nextToken();
                    if (token.kind != LPAREN) {
                        if (jt == BSMAX) {
                            return parseQuantifiedExpr(p, jt);
                        }
                        return syntaxError(p, null, "jml.args.required",
                                jt.internedName());
                    } else {
                        int preferred = pos();
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
                case BSERASURE:
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
                    ExpressionExtension ne = Extensions.instance(context).find(pos(),
                            jt);
                    if (ne == null) {
                        jmlerror(p, endPos(), "jml.no.such.extension",
                                jt.internedName());
                        return jmlF.at(p).Erroneous();
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
                    nextToken();
                    return parseQuantifiedExpr(p, jt);

                case NONNULL:
                case NULLABLE:
                case BSPEER:
                case BSREADONLY:
                case BSREP:
                case READONLY:
                    nextToken();
                    warnNotImplemented(pos(), jt.internedName(),
                            "JmlParser.term3(), as type modifiers");

                    // FIXME - ignoring these type modifiers for now
                    return term3();

                case BSLBLANY:
                case BSLBLNEG:
                case BSLBLPOS:
                    nextToken();
                    return parseLblExpr(p, jt);

                case BSLET:
                    nextToken();
                    return parseLet(p);
                    
                case BSONLYCALLED:
                    warnNotImplemented(pos(), jt.internedName(),
                            "\\only_called");
                    nextToken();
                    if (token.kind != LPAREN) {
                        accept(LPAREN); // fails
                        skipThroughRightParen();
                    } else {
                        accept(LPAREN);
                        parseMethodNameList();
                        if (token.kind != RPAREN) {
                            accept(RPAREN); // fails
                            skipThroughRightParen();
                        } else {
                            accept(RPAREN);
                        }
                    }
                    // FIXME - needs implementation
                    return toP(jmlF.at(p).Erroneous());

                default:
                    jmlerror(p, endPos(), "jml.bad.type.expression",
                            "( token " + jt.internedName()
                                    + " in JmlParser.term3())");
                    return toP(jmlF.at(p).Erroneous());
            }
        }
        return toP(super.term3());
    }
    
    @Override
    protected JCExpression potentialCast() {
        JmlTokenKind t = jmlTokenKind();
        if (JmlTokenKind.jmloperators.contains(t)) return null;
        return term3();
    }


    protected boolean inCreator = false;

    public JCExpression parseQuantifiedExpr(int pos, JmlTokenKind jt) {
        JCModifiers mods = modifiersOpt();
        JCExpression t = parseType();
        if (t.getTag() == JCTree.Tag.ERRONEOUS) return t;
        if (mods.pos == -1) {
            mods.pos = t.pos; // set the beginning of the modifiers
            storeEnd(mods,t.pos);
        }
                                              // modifiers
        // to the beginning of the type, if there
        // are no modifiers
        ListBuffer<JCVariableDecl> decls = new ListBuffer<JCVariableDecl>();
        int idpos = pos();
        Name id = ident(); // FIXME JML allows dimensions after the ident
        decls.append(toP(jmlF.at(idpos).VarDef(mods, id, t, null)));
        while (token.kind == COMMA) {
            nextToken();
            idpos = pos();
            id = ident(); // FIXME JML allows dimensions after the ident
            decls.append(toP(jmlF.at(idpos).VarDef(mods, id, t, null)));
        }
        if (token.kind != SEMI) {
            jmlerror(pos(), endPos(), "jml.expected.semicolon.quantified");
            int p = pos();
            skipThroughRightParen();
            return toP(jmlF.at(p).Erroneous());
        }
        nextToken();
        JCExpression range = null;
        JCExpression pred = null;
        if (token.kind == SEMI) {
            // type id ; ; predicate
            // two consecutive semicolons is allowed, and means the
            // range is null - continue
            nextToken();
            pred = parseExpression();
        } else {
            range = parseExpression();
            if (token.kind == SEMI) {
                // type id ; range ; predicate
                nextToken();
                pred = parseExpression();
            } else if (token.kind == RPAREN) {
                // type id ; predicate
                pred = range;
                range = null;
            } else {
                jmlerror(pos(), endPos(),
                        "jml.expected.semicolon.quantified");
                int p = pos();
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
        switch ((TokenKind)token.kind) {
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
        JCExpression t = qualident(true);
        int oldmode = mode;
        mode = TYPE;
        if (token.kind == LT) {
            checkGenerics();
            t = typeArguments(t,false); // FIXME - true or false:
        }
        while (token.kind == DOT) {
            int pos = pos();
            nextToken();
            t = toP(F.at(pos).Select(t, ident()));
            if (token.kind == LT) {
                checkGenerics();
                t = typeArguments(t,false); // FIXME - true or false:
            }
        }
        mode = oldmode;
        if (token.kind == LBRACKET) {
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
        } else if (token.kind == LPAREN) {
            boolean prev = inLocalOrAnonClass;
            try {
                inLocalOrAnonClass = true;
                JCNewClass anon = classCreatorRest(newpos, null, typeArgs, t);
//                if (anon.def != null) {
//                    filterTypeBodyDeclarations((JmlClassDecl) anon.def, context,
//                            jmlF);
//                }
                return anon;
            } finally {
                inLocalOrAnonClass = prev;
            }
        } else if (token.kind == LBRACE) {
            return parseSetComprehension(t);
        } else {
            syntaxError(pos(), null, "expected3", "\'(\'", "\'{\'", "\'[\'");
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
    protected JCExpression parseLblExpr(int pos, JmlTokenKind jmlToken) {
        // The JML token is already scanned
        // pos is the position of the \lbl token
        int labelPos = pos();
        Name n = ident();
        JCExpression e = parseExpression();
        if (jmlToken == JmlTokenKind.BSLBLANY && JmlOption.isOption(context,JmlOption.STRICT)) {
            log.warning(pos,"jml.not.strict","\\lbl");
        }
        return toP(jmlF.at(pos).JmlLblExpression(labelPos,jmlToken, n, e));
    }
    
    public JCExpression parseLet(int pos) {
        ListBuffer<JCVariableDecl> vdefs = new ListBuffer<JCVariableDecl>();
        do {
            int pm = pos();
            JCModifiers mods = jmlF.Modifiers(0); // FIXME - there are some modifiers allowed?
            if (mods.pos == -1) {
                mods.pos = pm;
                storeEnd(mods,pm);
            }
            JCExpression type = parseType();
            int p = pos();
            Name name = ident();
            JCVariableDecl decl = variableDeclaratorRest(pos,mods,type,name,true,null);
            decl.pos = p;
            if (decl.init == null) toP(decl);
            vdefs.add(decl);
            if (token.kind != COMMA) break;
            accept(COMMA);
        } while (true);
        accept(SEMI);
        JCExpression expr = parseExpression();
        return toP(jmlF.at(pos).LetExpr(vdefs.toList(),expr));
    }

    /** Parses: "{" [ <modifiers> ] <type> <identifier> "|" <expression> "}" */
    public JCExpression parseSetComprehension(JCExpression type) {
        JCExpression sc = null;
        int begin = pos();
        if (token.kind != LBRACE) {
            accept(LBRACE); // fails
        } else {
            accept(LBRACE);
            JCModifiers mods = modifiersOpt();
            int tpos = pos();
            JCTree.JCExpression t = parseType();
            if (t != null && !(t instanceof JCErroneous)) {
                Name n = ident();
                if (n != names.error) {
                    JCTree.JCVariableDecl v = toP(jmlF.at(tpos).VarDef(mods, n,
                            t, null));
                    if (token.kind != BAR) {
                        accept(BAR); // fails
                    } else {
                        accept(BAR);
                        JCExpression predicate = parseExpression();
                        if (predicate != null
                                && !(predicate instanceof JCErroneous)) {
                            if (token.kind != RBRACE) {
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
        while (token.kind == COMMA) {
            nextToken();
            g = parseGroupName();
            list.append(g);
        }
        return list;
    }

    /** Parses: [ "this" "." | "super" "." ] <identifier> */
    protected JmlGroupName parseGroupName() {
        JCExpression t = null;
        int p = pos();
        if (token.kind == THIS) {
            t = to(jmlF.at(p).Ident(names._this));
            nextToken();
            accept(TokenKind.DOT);
        } else if (token.kind == SUPER) {
            t = to(jmlF.at(p).Ident(names._super));
            nextToken();
            accept(TokenKind.DOT);
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
        T t = variableDeclaratorsRest(pos(), mods, type, ident(), false,
                null, vdefs);
        return t;
    }

    @Override
    protected <T extends ListBuffer<? super JCVariableDecl>> T variableDeclaratorsRest(
            int pos, JCModifiers mods, JCExpression type, Name name,
            boolean reqInit, Comment dc, T vdefs) {
        if (S.jml()) reqInit = false; // In type checking we check this more
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
    protected int prec(ITokenKind token) {
        if (token instanceof JmlTokenKind) {
            switch ((JmlTokenKind)token) {
                // FIXME - check all these precedences
                case EQUIVALENCE: case INEQUIVALENCE: case IMPLIES: case REVERSE_IMPLIES:
                    return -1;
                case SUBTYPE_OF: case JSUBTYPE_OF: case LOCK_LT: case LOCK_LE:
                    return TreeInfo.ordPrec;
                case DOT_DOT: case ENDJMLCOMMENT:
                    return -1000;
                default:
                    return 1000;
            }
//            if (token != JmlTokenKind.SUBTYPE_OF
//                    && token != JmlTokenKind.JSUBTYPE_OF
//                    && token != JmlTokenKind.LOCK_LT
//                    && token != JmlTokenKind.LOCK_LE) return -1; // For
//                                                                    // inequivalence
//                                                                    // and
//                                                                    // reverse/implies
//            return TreeInfo.ordPrec; // All the JML operators are comparisons
        }
        return super.prec(token);
    }
    
    // MAINTENANCE ISSUE - (Almost) Duplicated from JavacParser.java in order to track
    // Jml tokens
    protected JCExpression term2Rest(JCExpression tt, int minprec) {
        boolean bad = tt instanceof JCErroneous;
        JCExpression t = tt;
        JCExpression[] odStack = newOdStack();
        Token[] opStack = newOpStack();

        // optimization, was odStack = new Tree[...]; opStack = new Tree[...];
        int top = 0;
        odStack[0] = t;
        int startPos = token.pos;
        Token topOp = Tokens.DUMMY;
        while (prec(S.token().ikind) >= minprec) { // FIXME - lookahead token - presumes scanner is just one token ahead
            opStack[top] = topOp;
            top++;
            topOp = S.token();
            JmlTokenKind topOpJmlToken = jmlTokenKind();
            nextToken(); // S.jmlToken() changes
            odStack[top] = (topOp.kind == INSTANCEOF) ? parseType() : term3();
            while (top > 0 && prec(topOp.ikind) >= prec(token.ikind)) {
                if (topOp.kind == CUSTOM) { // <:
                    JCExpression e = jmlF.at(topOp.pos).JmlBinary(topOpJmlToken, odStack[top - 1],
                            odStack[top]);
                    storeEnd(e, getEndPos(odStack[top]));
                    odStack[top - 1] = e;
                } else {
                    odStack[top - 1] = makeOp(topOp.pos, topOp.kind, odStack[top - 1],
                        odStack[top]);
                }
                top--;
                topOp = opStack[top];
            }
        }
        Assert.check(top == 0);
        t = odStack[0];

        if (t.hasTag(JCTree.Tag.PLUS)) {
            StringBuilder buf = foldStrings(t);
            if (buf != null) {
                t = toP(F.at(startPos).Literal(TypeTag.CLASS, buf.toString()));
            }
        }

        odStackSupply.add(odStack);
        opStackSupply.add(opStack);
        if (bad) return tt;
        return t;
    }

    /**
     * Skips up to and including a semicolon, though not including any EOF or
     * ENDJMLCOMMENT
     */
    protected void skipThroughSemi() {
        while (token.kind != TokenKind.SEMI && token.kind != TokenKind.EOF
                && jmlTokenKind() != JmlTokenKind.ENDJMLCOMMENT)
            nextToken();
        if (token.kind == TokenKind.SEMI) nextToken();
    }

    /** Skips up to but not including a semicolon or EOF or ENDJMLCOMMENT */
    protected void skipToSemi() {
        while (token.kind != SEMI && token.kind != EOF
                && jmlTokenKind() != JmlTokenKind.ENDJMLCOMMENT)
            nextToken();
    }

    /**
     * Skips up to but not including a semicolon or comma or EOF or
     * ENDJMLCOMMENT
     */
    protected void skipToCommaOrSemi() {
        while (token.kind != SEMI && token.kind != COMMA
                && token.kind != EOF
                && jmlTokenKind() != JmlTokenKind.ENDJMLCOMMENT)
            nextToken();
    }

    /**
     * Skips up to but not including a right-parenthesis or comma or EOF or
     * ENDJMLCOMMENT
     */
    protected void skipToCommaOrParenOrSemi() {
        while (token.kind != RPAREN && token.kind != COMMA
                && token.kind != SEMI && token.kind != EOF
                && jmlTokenKind() != JmlTokenKind.ENDJMLCOMMENT)
            nextToken();
    }

    /**
     * Skips up to a EOF or ENDJMLCOMMENT or up to and including a right brace
     */
    public void skipThroughRightBrace() {
        while (token.kind != RBRACE && token.kind != EOF
                && jmlTokenKind() != JmlTokenKind.ENDJMLCOMMENT)
            nextToken();
        if (token.kind != EOF) nextToken();
    }

    /**
     * Skips up to a EOF or ENDJMLCOMMENT or up to and including a right
     * parenthesis
     */
    public void skipThroughRightParen() {
        while (token.kind != RPAREN && token.kind != EOF
                && jmlTokenKind() != JmlTokenKind.ENDJMLCOMMENT)
            nextToken();
        if (token.kind != EOF) nextToken();
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
        log.error(new JmlTokenizer.DiagnosticPositionSE(pos, pos), key, args);
    }

    /**
     * Creates an error message for which the source is a range of characters,
     * from begin up to and not including end; the identified line is that of
     * the begin position.
     */
    public void jmlerror(int begin, int end, String key, Object... args) {
        log.error(new JmlTokenizer.DiagnosticPositionSE(begin, end - 1), key,
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
                new JmlTokenizer.DiagnosticPositionSE(begin, preferred, end - 1),
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
//                nextToken();
//            } else if (S.token() == null) {
//                setErrorEndPos(pos());
//                reportSyntaxError(S.prevEndPos(), "expected, not a misspelled or unexpected JML token", token);
//            } else {
//                setErrorEndPos(pos());
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
