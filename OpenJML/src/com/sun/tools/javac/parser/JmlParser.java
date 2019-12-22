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
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.ext.AssignableClauseExtension;
import org.jmlspecs.openjml.ext.EndStatement;
import org.jmlspecs.openjml.ext.ExpressionExtension;
import org.jmlspecs.openjml.ext.MethodSimpleClauseExtensions.MethodClauseType;
import org.jmlspecs.openjml.ext.Operators;
import org.jmlspecs.openjml.ext.QuantifiedExpressions;
import static org.jmlspecs.openjml.ext.ReachableStatement.*;
import org.jmlspecs.openjml.ext.FunctionLikeExpressions;
import static org.jmlspecs.openjml.ext.FunctionLikeExpressions.*;
import static org.jmlspecs.openjml.ext.MiscExtensions.*;
import static org.jmlspecs.openjml.ext.StateExpressions.*;
import static org.jmlspecs.openjml.ext.Operators.*;
import org.jmlspecs.openjml.ext.StatementLocationsExtension;

import static org.jmlspecs.openjml.ext.TypeExprClauseExtension.*;
import static org.jmlspecs.openjml.ext.StatementExprExtensions.*;
import static org.jmlspecs.openjml.ext.TypeInClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeMapsClauseExtension.*;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.parser.Tokens.Comment;
import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.parser.Tokens.Comment.CommentStyle;
import com.sun.tools.javac.parser.Tokens.ITokenKind;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Assert;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Position;

/** This class extends the javac parser to parse JML constructs as well. */
public class JmlParser extends JavacParser {

    /** The context this parser was created for */
    // @ non_null
    public Context          context;

    /** Cached value of the utilities object */
    // @ non_null
    public Utils            utils;

    /** The scanner associated with the parser */
    // @ non_null
    protected JmlScanner    S;

    /** The node factory to use */
    // @ non_null
    public JmlTree.Maker    jmlF;

    /** True only when we are parsing within a model program */
    public boolean       inModelProgram = false;
    
    public java.util.List<IJmlLineAnnotation> lineAnnotations = new java.util.LinkedList<>();

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
    
    
    public IJmlClauseKind jmlTokenClauseKind() {
        return jmlTokenClauseKind(token);
    }
    
    public IJmlClauseKind jmlTokenClauseKind(Token token) {
        if (token instanceof JmlToken && ((JmlToken)token).jmlclausekind != null) return ((JmlToken)token).jmlclausekind;
        if (token.kind != TokenKind.IDENTIFIER) return null;
        IJmlClauseKind t = Extensions.allKinds.get(token.name().toString());
        if (token instanceof JmlToken) ((JmlToken)token).jmlclausekind = t;
        return t;
    }
    
    public boolean tokenIsId(String ... ids) {
        if (token.kind != TokenKind.IDENTIFIER) return false;
        Name n = token.name();
        for (String id: ids) {
            if (n.toString().equals(id)) return true;
        }
        return false;
    }

    /** Returns the scanner being used by the parser */
    public JmlScanner getScanner() {
        return S;
    }

    /** Returns the node factory being used by the parser */
    public JmlTree.Maker maker() {
        return jmlF;
    }
    
    /** Backup to the beginning of the current token and rescan */
    public void rescan() {
        token = S.rescan();
    }
    
    /** Returns true if the JDK -deprecation option is set */
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
            // JML declarations at all levels of nesting
            // include a field that holds the top-level
            // compilation unit in which the declaration sits.
            // This code sets that field in after the whole tree is parsed.
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
    //@ ensures \result == null || \result instanceof JCTree.JCImport;
    //@ nullable
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
        while (jmlTokenKind() == JmlTokenKind.ENDJMLCOMMENT) {
            nextToken();
        }
        return t;
    }
    
    /** Annotation              = "@" Qualident [ "(" AnnotationFieldValues ")" ]
    * Overridden to include the source object containing the annotation
    * @param pos position of "@" token
    * @param kind Whether to parse an ANNOTATION or TYPE_ANNOTATION
    */
    @Override
    JCAnnotation annotation(int pos, JCTree.Tag kind) {
        JCAnnotation a = super.annotation(pos, kind);
        ((JmlTree.JmlAnnotation)a).sourcefile = log.currentSourceFile();
        return a;
    }
    
    /** OpenJML overrides in order to parse and insert replacement types for formal parameters */
    @Override
    protected JCVariableDecl formalParameter(boolean lambdaParameter) {
        replacementType = null;
        JmlVariableDecl param = (JmlVariableDecl)super.formalParameter(lambdaParameter);
        insertReplacementType(param,replacementType);
        replacementType = null;
        return param;
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
            if (!inJmlDeclaration || token.kind == CLASS || token.kind == INTERFACE || token.kind == ENUM) {
                // The guard above is used because if it is false, we want to produce
                // a better error message than we otherwise get, for misspelled
                // JML modifiers. However, the test above replicates tests in
                // the super method and may become obsolete.
                s = super.classOrInterfaceOrEnumDeclaration(mods, dc);

            } else {
                if (inJmlDeclaration && token.kind == IDENTIFIER) {
                    ClassLike cl = Extensions.classLike.get(token.name().toString());
                    if (cl != null) {
                        JCStatement stat = cl.parse(this,mods);
                        return stat;
                    }
                }
                int p = pos();
                int ep = endPos();
                jmlerror(p, ep,
                        "jml.unexpected.or.misspelled.jml.token",
                            token == null ? jmlTokenKind().internedName() : S.chars() );
                
                setErrorEndPos(ep);
                s = to(F.Exec(toP(F.at(p).Erroneous(List.<JCTree> nil()))));
                // TODO: Does this recover well enough?
            }
            if (s instanceof JCClassDecl && (((JCClassDecl)s).mods.flags & Flags.ENUM) != 0) {
                addImplicitEnumAxioms((JCClassDecl)s);
            }
            while (jmlTokenKind() == JmlTokenKind.ENDJMLCOMMENT) {
                nextToken();
            }
        } finally {
            inJmlDeclaration = prevInJmlDeclaration;
        }
        return s;
    }
    
    void addImplicitEnumAxioms(JCClassDecl cd) {
        if (utils.rac) return;
        ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
        ListBuffer<JCExpression> argsn = new ListBuffer<JCExpression>();
        Name n = jmlF.Name(Strings.enumVar);
        JCExpression disj = null;
        int num = 0;
        java.util.List<JCExpression> axiomExpressions = new java.util.LinkedList<>();
        long expected = Flags.PUBLIC | Flags.STATIC | Flags.FINAL;
        for (JCTree d: cd.defs) {
            if (!(d instanceof JCVariableDecl)) continue;
            JCVariableDecl decl = (JCVariableDecl)d;
            long flags = decl.mods.flags;
            if ((flags & expected) != expected || decl.init == null) continue;
            if (!(decl.vartype instanceof JCIdent && ((JCIdent)decl.vartype).name.equals(cd.name))) continue;
            JCExpression id = jmlF.at(d.pos).Ident(decl.getName());
            args.add(id);
            id = jmlF.at(d.pos).Ident(decl.getName());
            JCExpression ide = jmlF.at(d.pos).Ident(n);
            jmlF.at(id);
            JCExpression ex = jmlF.Binary(JCTree.Tag.EQ, ide, id);
            disj = disj == null ? ex : jmlF.Binary(JCTree.Tag.OR,disj,ex);
            ex = jmlF.Select(id, names.ordinal);
            ex = jmlF.Binary(JCTree.Tag.EQ,ex,jmlF.Literal(num));
            axiomExpressions.add(ex); // <e>.ordinal == [[num]]
            ex = jmlF.Indexed(jmlF.Ident("_JMLvalues"), jmlF.Literal(num));
            ex = jmlF.Binary(JCTree.Tag.EQ,ex,id);
            axiomExpressions.add(ex); // _JMLvalues[ [[num]] ] = <e>
            ex = jmlF.Select(id, names._name);
            ex = jmlF.Binary(JCTree.Tag.EQ,ex,jmlF.Literal(decl.getName().toString())); 
            axiomExpressions.add(ex); // <e>.names == <name>
            argsn.add(jmlF.Select(jmlF.Ident(decl.getName()), names._name));
            num++;
        }
        if (disj != null) { // Must be at least one value
            args.add(F.Literal(TypeTag.BOT,null));
            argsn.add(F.Literal(TypeTag.BOT,null));
            jmlF.at(cd.pos);
            ListBuffer<JCTree> newdefs = new ListBuffer<>();
            JCVariableDecl vd = jmlF.VarDef(jmlF.Modifiers(Flags.PUBLIC|Flags.STATIC),names.fromString("_JMLvalues"),jmlF.TypeArray(jmlF.Ident(cd.name)),null);
            utils.setJML(vd.mods);
            JCAnnotation a = tokenToAnnotationAST(JmlTokenKind.MODEL, cd.pos, cd.pos);  // FIXME -is position correct?
            vd.mods.annotations =  vd.mods.annotations.append(a);
            // declare _JMLvalues as model field
            newdefs.add(vd);
            JCExpression ex = jmlF.Binary(Tag.NE, jmlF.Ident(vd.name), F.Literal(TypeTag.BOT,null));
            // _JMLvalues is not null
            JmlTypeClauseExpr axiom = jmlF.JmlTypeClauseExpr(jmlF.Modifiers(0), axiomID,axiomClause,ex);
            newdefs.add(axiom); 
            ex = jmlF.JmlMethodInvocation(distinctKind,args.toList());
            ((JmlMethodInvocation)ex).kind = FunctionLikeExpressions.distinctKind;
            // The enum constants are all distinct and distinct from NULL.
            axiom = jmlF.JmlTypeClauseExpr(jmlF.Modifiers(0),axiomID,axiomClause,ex);
            newdefs.add(axiom);
            ex = jmlF.JmlMethodInvocation(distinctKind,argsn.toList());
            ((JmlMethodInvocation)ex).kind = FunctionLikeExpressions.distinctKind;
            // The enum names are all distinct and distinct from NULL.
            axiom = jmlF.JmlTypeClauseExpr(jmlF.Modifiers(0),axiomID,axiomClause,ex);
            newdefs.add(axiom);
            // Any non-null enum is one of the declared values
            JCVariableDecl decl = jmlF.VarDef(jmlF.Modifiers(0),n,jmlF.Ident(jmlF.Name("Object")),null);
            ex = jmlF.JmlQuantifiedExpr(QuantifiedExpressions.qforallKind,List.<JCVariableDecl>of(decl), null,
                    jmlF.JmlBinary(Operators.equivalenceKind, jmlF.TypeTest(jmlF.Ident(n), jmlF.Ident(cd.getSimpleName())),disj));
            axiom = jmlF.JmlTypeClauseExpr(jmlF.Modifiers(Flags.ENUM),axiomID,axiomClause,ex);
            newdefs.add(axiom);
            decl = jmlF.VarDef(jmlF.Modifiers(0),n,jmlF.Ident(cd.name),null);
            JCVariableDecl decl2 = jmlF.VarDef(jmlF.Modifiers(0),jmlF.Name("i"),jmlF.TypeIdent(TypeTag.INT),null);
            JCExpression le = jmlF.Binary(JCTree.Tag.LE, jmlF.Literal(0), jmlF.Ident("i"));
            JCExpression lt = jmlF.Binary(JCTree.Tag.LT, jmlF.Ident("i"), jmlF.Select(jmlF.Ident("_JMLvalues"),names.length));
            ex = jmlF.Binary(JCTree.Tag.AND, le, lt);
            JCExpression exists = jmlF.JmlQuantifiedExpr(QuantifiedExpressions.qexistsKind, List.<JCVariableDecl>of(decl2), ex,
                    jmlF.Binary(JCTree.Tag.EQ, jmlF.Indexed(jmlF.Ident("_JMLvalues"), jmlF.Ident("i")), jmlF.Ident(n))  );
            ex = jmlF.JmlQuantifiedExpr(QuantifiedExpressions.qforallKind,List.<JCVariableDecl>of(decl), null,
                    jmlF.JmlBinary(Operators.impliesKind, jmlF.Binary(JCTree.Tag.NE, jmlF.Ident(n), jmlF.Literal(TypeTag.BOT,null)),exists));
            axiom = jmlF.JmlTypeClauseExpr(jmlF.Modifiers(Flags.ENUM),axiomID,axiomClause,ex);
            newdefs.add(axiom);
            ex = jmlF.Select(jmlF.Ident("_JMLvalues"), names.length);
            ex = jmlF.Binary(JCTree.Tag.EQ, ex, jmlF.Literal(num));
            axiom = jmlF.JmlTypeClauseExpr(jmlF.Modifiers(Flags.ENUM),axiomID,axiomClause,ex);
            newdefs.add(axiom);
            for (JCExpression expr: axiomExpressions) {
                axiom = jmlF.JmlTypeClauseExpr(jmlF.Modifiers(Flags.ENUM),axiomID,axiomClause,expr);
                newdefs.add(axiom);
            }
            cd.defs = cd.defs.appendList(newdefs);
        }
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
        JmlMethodSpecs savedMethodSpecs = currentMethodSpecs;
        currentMethodSpecs = null;
        S.setJmlKeyword(true);
        try {
            return super.classOrInterfaceBody(className, isInterface);
        } finally {
            currentMethodSpecs = savedMethodSpecs;
            S.setJmlKeyword(savedJmlKeyword);
            rescan();
        }

    }
    
    @Override
    public JCClassDecl classDeclaration(JCModifiers mods, Comment dc) {
        JCClassDecl cd = super.classDeclaration(mods, dc);
        ((JmlClassDecl)cd).lineAnnotations = ((JmlTokenizer)S.tokenizer).lineAnnotations;
        ((JmlTokenizer)S.tokenizer).lineAnnotations = new java.util.LinkedList<>();
        return cd;
    }
    
    /** Overridden to do any post-processing of a list of block statements that JML needs,
     * possibly rewriting the list of statements;
     * at present that is to collect loop specifications and attach them to the loop statement
     * that follows them.
     */
    @Override List<JCStatement> blockStatements() {
        List<JCStatement> stats = super.blockStatements();
        return collectLoopSpecs(stats);
    }
    
    /** Attach loop specifications to their parent loop statement */
    protected List<JCStatement> collectLoopSpecs(List<JCStatement> stats) {
        ListBuffer<JCStatement> newstats = new ListBuffer<>();
        ListBuffer<JmlStatementLoop> loopspecs = new ListBuffer<>();
        JmlStatementExpr split = null;
        for (JCStatement s: stats) {
            String sss = s.toString();
            if (s instanceof JmlStatementLoop) {
                loopspecs.add((JmlStatementLoop)s);
                continue;
            }
            boolean isSplit = split != null;
            if (s instanceof JmlIfStatement) {
                ((JmlIfStatement)s).split = isSplit;
            } else if (s instanceof JmlSwitchStatement) {
                ((JmlSwitchStatement)s).split = isSplit;
            } else if (s instanceof IJmlLoop) {
                ((IJmlLoop)s).setSplit(isSplit);
            } else if (isSplit) {
                log.warning(split, "jml.message", "Ignoring out of place split statement");
            }
            split = s instanceof JmlStatementExpr && ((JmlStatementExpr)s).clauseType == splitClause && ((JmlStatementExpr)s).expression == null
                    ? (JmlStatementExpr)s : null;
            if (split != null) continue;

            if (s instanceof JmlStatement && ((JmlStatement)s).clauseType == EndStatement.endClause) {
                log.error(s, "jml.message", "Improperly nested spec-end pair");
                continue;
            }
            if (s instanceof JmlStatement && ((JmlStatement)s).clauseType == EndStatement.beginClause) {
                log.error(s, "jml.message", "Improperly nested spec-end pair");
                continue;
            }
            // This case allows grandfathering an assignable statement as a loop_modifies statement
            // if it is not the first loop specification statement
            if (s instanceof JmlMethodClauseStoreRef && ((JmlMethodClauseStoreRef)s).clauseKind == AssignableClauseExtension.assignableClauseKind) {
                JmlMethodClauseStoreRef sa = (JmlMethodClauseStoreRef)s;
                JmlStatementLoop sloop = jmlF.at(sa.pos).JmlStatementLoopModifies(StatementLocationsExtension.loopmodifiesStatement, sa.list);
                if (!loopspecs.isEmpty()) {
                    log.warning(s.pos, "jml.message", "Use 'loop_writes' keyword instead of '" + sa.keyword + "' in loop specifications");
                    loopspecs.add(sloop);
                    continue;
                }
                
            }
            if (!loopspecs.isEmpty()) {
                if (s instanceof IJmlLoop) {
                    ((IJmlLoop)s).setLoopSpecs(loopspecs.toList());
                    loopspecs = new ListBuffer<>();
                } else {
                    jmlerror(loopspecs.first().pos,
                            loopspecs.last().getEndPosition(endPosTable),
                            "jml.loop.spec.misplaced");
                    loopspecs.clear();
                }
            }
            newstats.add(s);
        }
        if (!loopspecs.isEmpty()) {
            jmlerror(loopspecs.first().pos,
                    loopspecs.last().getEndPosition(endPosTable),
                    "jml.loop.spec.misplaced");
            loopspecs.clear();
        }
        if (split != null) {
            log.warning(split, "jml.message", "Ignoring out of place split statement");
        }
        return newstats.toList();
    }
    
    protected void insertReplacementType(Object tree, JCExpression replacementType) {
        if (replacementType != null && tree instanceof JmlVariableDecl) {
            JmlVariableDecl d = (JmlVariableDecl) tree;
            d.originalVartype = d.vartype;
            d.vartype = replacementType;
            d.jmltype = true;
        }
    }
    

    /** Overridden to parse JML statements as statements in a block. 
        The parent method returns a list rather than a statement:
        Usually the list contains just one statement.
        If there is an ending construct detected (like a right brace) or an error, the list might be empty.
        In the case of a local declaration, there is a declaration statement for
        each variable declared.
        */
    @Override  // TODO - needs review
    protected List<JCStatement> blockStatement() {
        while (true) {
            // If we are in a JML comment and this first token is an identifier
            // registered as marking a JML statement or statement annotation,
            // then we proceed to parse it as a (JML) statement
            if (S.jml() && token.kind == TokenKind.IDENTIFIER) {
                String id = token.name().toString();
                IJmlClauseKind ext = Extensions.instance(context).findSM(0,id,false);
                if (ext != null) {
                    if (ext instanceof IJmlClauseKind.MethodClause) {
                        JCStatement s = parseRefining(pos(), null);
                        return List.<JCStatement>of(s);
                    } else {
                        JCStatement s = (JCStatement)ext.parse(null, id, ext, this);
                        //                    JCStatement s = parseStatement();
                        return List.<JCStatement>of(s);
                    }
                }
                ClassLike cl = Extensions.classLike.get(id);
                if (cl != null) {
                    return List.<JCStatement>of(cl.parse(this, null));
                }
                // If the identifier is not the beginning of a JML statement, then
                // it might be the type that begins a declaration (or it could be a
                // misspelled JML key word)
            }
            if (!(token instanceof JmlToken)) {
                JCExpression replacementType = null;
                if (token.kind == TokenKind.BANG) {  // TODO - is this still part of extended JML?
                    replacementType = unannotatedType();
                }
                boolean inJml = S.jml();
                List<JCStatement> stats = super.blockStatement();
                if (replacementType != null) {
                    for (JCStatement s: stats)  insertReplacementType(s,replacementType);
                    replacementType = null;
                }
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
                if (S.jml()) throw new AssertionError("Thought jml was always false at this point");
                S.setJml(false); // TOOD _ already false?
                nextToken();
                continue;
            }
            JCStatement s = parseStatement();
            return s == null ? List.<JCStatement>nil() : List.<JCStatement>of(s);
        }
    }
    
    public JCStatement parseJavaStatement() {
        return super.parseStatement();
    }
    
    /** Overridden to parse JML statements */
    @Override  // TODO - needs REVIEW
    public JCStatement parseStatement() {
        int pos = pos();
        JCStatement st;
        String reason = null;
        JmlTokenKind jtoken = jmlTokenKind();
        String id = null;
        if (S.jml()) {
            if (token.kind == TokenKind.IDENTIFIER) {
                boolean needSemi = true;
                id = token.name().toString();
                IJmlClauseKind clauseType = Extensions.instance(context).findSM(pos(),id,false);
                if (clauseType instanceof IJmlClauseKind.Statement) {
                    st = (JmlAbstractStatement)clauseType.parse(null,id,clauseType,this);
                    needSemi = false; // OK for set // FIXME - not sure this is needed
                    S.setJmlKeyword(true);
                    if (!needSemi) { // TODO - when nwe get rid of all keywords, this block can be deleted
                        // If we do not need a semicolon yet (e.g. because we already
                        // parsed it or because the statement does not end with one,
                        // then the scanner has already scanned the next symbol,
                        // with setJmlKeyword having been (potentially) false.
                        // So we need to do the following conversion.
                        if (token.kind == IDENTIFIER && S.jml()) {
                            JmlTokenKind tt = JmlTokenKind.allTokens.get(S.chars());
                            IJmlClauseKind tk = Extensions.allKinds.get(S.chars());
                            if (tt != null) {
                                S.setToken(new JmlToken(tt, tk, null, pos(), endPos()));
                            }
                        }
                    } else if (token.ikind == ENDJMLCOMMENT) {
                        log.warning(pos()-2, "jml.missing.semi", jtoken);
                    } else if (token.kind != SEMI) {
                        jmlerror(pos(), endPos(), "jml.bad.construct", reason);
                        skipThroughSemi();
                    } else {
                        nextToken(); // skip the semicolon
                    }
                    while (jmlTokenClauseKind() == Operators.endjmlcommentKind) nextToken();
                    return st;
                } else if (clauseType instanceof IJmlClauseKind.MethodClause) {
                    st = parseRefining(pos(),null);
                    return st;
                } else if (token.kind == TokenKind.ASSERT) {
                    clauseType = assertClause;
                    st = (JCStatement)clauseType.parse(null,id,clauseType,this);
                } else {
                    log.error(pos, "jml.message", "Unexpected statement type: " + id);
                }
            }
        }
        if (token.kind == CUSTOM) {
            boolean needSemi = true;
            if (jtoken != JmlTokenKind.ENDJMLCOMMENT) {
                pos = pos();
                JmlSpecificationCase spc;
                if (jtoken != null)
                    reason = jtoken.internedName() + " statement";
//                if (jtoken == JmlTokenKind.ASSUME || jtoken == JmlTokenKind.ASSERT || jtoken == JmlTokenKind.USE) {
//                    S.setJmlKeyword(false);
//                    nextToken();
//                    JCExpression t = null;
//                    t = parseExpression();
//                    JmlTree.JmlStatementExpr ste = jmlF
//                            .at(pos)
//                            .JmlExpressionStatement(
//                                    jtoken,
//                                    jtoken == JmlTokenKind.ASSUME ? Label.EXPLICIT_ASSUME
//                                            : Label.EXPLICIT_ASSERT, t);
//                    if (token.kind == COLON) {
//                        nextToken();
//                        ste.optionalExpression = parseExpression();
//                    }
//                    toP(ste);
//                    ste.source = log.currentSourceFile();
//                    //ste.line = log.currentSource().getLineNumber(pos);
//                    st = ste;
//                } else if (jtoken == INLINED_LOOP) {  // FIXME - use extensions
//                    S.setJmlKeyword(false);
//                    nextToken();
//                    JmlTree.JmlInlinedLoop ste = to(jmlF.at(pos).JmlInlinedLoop(null));
////                    ste.source = log.currentSourceFile();
//                    st = ste;
//                    if (JmlOption.isOption(context, JmlOption.STRICT)) {
//                        log.warning(ste.pos,"jml.not.strict",jtoken.internedName());
//                    }
//                } else if (jtoken == UNREACHABLE || jtoken == REACHABLE) {
//                    S.setJmlKeyword(false);
//                    nextToken();
//                    JCExpression t = null;
//                    if (token.ikind != ENDJMLCOMMENT && token.kind != SEMI) {
//                        t = parseExpression();
//                    }
//                    JmlTree.JmlStatementExpr ste = to(jmlF.at(pos)
//                            .JmlExpressionStatement(jtoken, 
//                                    jtoken == REACHABLE ? Label.REACHABLE : Label.UNREACHABLE,
//                                    t));
//                    ste.source = log.currentSourceFile();
//                    st = ste;
//                    if (JmlOption.isOption(context, JmlOption.STRICT)) {
//                        // FIXME - why the difference in the positions of these two warnings
//                        if (jtoken == UNREACHABLE && t != null) log.warning(pos(),"jml.not.strict","unreachable statement with expression");
//                        if (jtoken == REACHABLE) log.warning(ste.pos,"jml.not.strict",jtoken.internedName());
//                    }
//                } else if (jtoken == HENCE_BY) {
//                    S.setJmlKeyword(false);
//                    nextToken();
//                    JCExpression t = parseExpression();
//                    JmlTree.JmlStatementExpr ste = to(jmlF.at(pos)
//                            .JmlExpressionStatement(jtoken, 
//                                    Label.EXPLICIT_ASSUME,
//                                    t));
//                    ste.source = log.currentSourceFile();
//                    st = ste;
//                } else 
//                if (jtoken == loopdecreasesClause || jtoken == loopinvariantClause) {
//                    S.setJmlKeyword(false);
//                    nextToken();
//                    JCExpression t = parseExpression();
//                    JmlStatementLoopExpr ste = to(jmlF.at(pos).JmlStatementLoopExpr(
//                            jtoken, t));
//                    ste.source = log.currentSourceFile();
//                    // ste.line = log.currentSource().getLineNumber(pos);
//                    st = ste;
//                } else if (jtoken == loopmodifiesClause || jtoken == havocClause ) {
//                    S.setJmlKeyword(false);
//                    nextToken();
//
//                    ListBuffer<JCExpression> list = parseStoreRefList(false);
//                    if (token.kind == SEMI) {
//                        // OK, go on
//                    } else if (jmlTokenKind() == ENDJMLCOMMENT) {
//                        syntaxError(pos(), null, "jml.missing.semi");
//                    }
//                    S.setJmlKeyword(true);
//                    if (token.kind != SEMI) {
//                        // error already reported
//                        skipThroughSemi();
//                    } else {
//                        if (list.isEmpty()) {
//                            syntaxError(pos(), null, "jml.use.nothing.assignable");
//                        }
//                        nextToken();
//                    }
//                    if (jtoken == JmlTokenKind.HAVOC) {
//                        st = toP(jmlF.at(pos).JmlHavocStatement(list.toList()));
//                    } else {
//                        JmlStatementLoop ste = toP(jmlF.at(pos).JmlStatementLoopModifies(jtoken,list.toList()));
//                        ste.source = log.currentSourceFile();
//                        st = ste;
//                    }
//
//                    S.setJmlKeyword(true); // This comes a token too late.
//                    rescan();
//                    needSemi = false;
//                } else if (id == "set".intern() || id == "debug".intern()) {
//                //} else if (jtoken == JmlTokenKind.SET || jtoken == JmlTokenKind.DEBUG) {
//                    S.setJmlKeyword(false);
//                    nextToken();
//                    // Only StatementExpressions are allowed - 
//                    // assignment statements and stand-alone method calls -
//                    // but JML constructs are allowed.
//                    boolean prev = inJmlDeclaration;
//                    inJmlDeclaration = true;
//                    JCStatement t = super.parseStatement();
//                    inJmlDeclaration = prev;
//                    if (!(t instanceof JCExpressionStatement)) {
//                        jmlerror(t.getStartPosition(),
//                                getEndPos(t),
//                                "jml.bad.statement.in.set.debug");
//                        t = null;
//                    }
//                    st = toP(jmlF.at(pos).JmlStatement(jtoken, (JCExpressionStatement)t));
//                    S.setJmlKeyword(true); // This comes a token too late.
//                    rescan();
//                    needSemi = false;

//                } else if (jtoken == JmlTokenKind.END) {
//                    S.setJmlKeyword(true);
//                    nextToken();
//                    boolean prev = inJmlDeclaration;
//                    if (token.kind == TokenKind.SEMI) {
//                        // this is what we expect
//                        accept(TokenKind.SEMI);
//                    } else if (token.ikind == JmlTokenKind.ENDJMLCOMMENT) {
//                        // show with no list and no semicolon
//                        jmlerror(pos()-1, pos(), "jml.missing.semicolon.in.show");  // FIXME - fix error message
//                    } else {
//                        jmlerror(pos(), pos()+1, "jml.bad.expression.list.in.show"); // FIXME 
//                        skipThroughSemi();
//                    }
//                    st = toP(jmlF.at(pos).JmlStatement(jtoken, null));
//                    needSemi = false;

//                } else if (jtoken == JmlTokenKind.SHOW) {
//                    if (JmlOption.isOption(context, JmlOption.STRICT)) {
//                        log.warning(pos(),"jml.not.strict","show statement");
//                    }
//                    S.setJmlKeyword(false);
//                    ListBuffer<JCExpression> expressions = new ListBuffer<>();
//                    boolean prev = inJmlDeclaration;
//                    nextToken();
//                    if (token.kind == TokenKind.SEMI) {
//                        // empty expression list - OK
//                        // list is empty
//                        accept(TokenKind.SEMI);
//                    } else if (token.ikind == JmlTokenKind.ENDJMLCOMMENT) {
//                        // show with no list and no semicolon
//                        jmlerror(pos()-1, pos(), "jml.missing.semicolon.in.show");
//                    } else {
//                        // Only expressions are allowed -
//                        // but JML constructs are allowed.
//                        inJmlDeclaration = true;
//                        JCExpression t = super.parseExpression();
//                        expressions.add(t);
//                        while (token.kind == TokenKind.COMMA) {
//                            accept(TokenKind.COMMA);
//                            t = super.parseExpression();
//                            expressions.add(t);
//                        }
//                        S.setJmlKeyword(true);
//                        if (token.kind == TokenKind.SEMI) {
//                            accept(TokenKind.SEMI);
//                        } else if (token.ikind == JmlTokenKind.ENDJMLCOMMENT) {
//                            jmlerror(pos()-1, pos(), "jml.missing.semicolon.in.show");
//                        } else {
//                            jmlerror(pos(), pos()+1, "jml.bad.expression.list.in.show");
//                            skipThroughSemi();
//                        }
//                    }
//                    st = toP(jmlF.at(pos).JmlStatementShow(jtoken,expressions.toList()));
//                    inJmlDeclaration = prev;
//                    needSemi = false;

                if (methodClauseTokens.contains(jtoken)) {
                    st = parseRefining(pos,jtoken);
                    needSemi = false;

                } else if (jtoken == JmlTokenKind.REFINING) {
                    S.setJmlKeyword(true);
                    st = parseRefining(pos,jtoken);
                    needSemi = false;

//                } else if (inModelProgram && jtoken == JmlTokenKind.CHOOSE) {
//                    st = parseChoose();
//                    return toP(st); // FIXME - is this the correct end position?
//                } else if (inModelProgram && jtoken == JmlTokenKind.CHOOSE_IF) {
//                    st = parseChooseIf();
//                    return toP(st); // FIXME - is this the correct end position?
//                } else if (inModelProgram && jtoken == JmlTokenKind.INVARIANT) {
//                    JCTree t = parseInvariantInitiallyAxiom(null);
//                    st = jmlF.JmlModelProgramStatement(t);
//                    return st;
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
                    IJmlClauseKind tk = Extensions.allKinds.get(S.chars());
                    if (tt != null) {
                        S.setToken(new JmlToken(tt, tk, null, pos(), endPos()));
                    }
                }
            } else if (token.ikind == ENDJMLCOMMENT) {
                log.warning(pos()-2, "jml.missing.semi", jtoken);
            	
            } else if (token.kind != SEMI) {
                jmlerror(pos(), endPos(), "jml.bad.construct", reason);
                skipThroughSemi();
                st = null;
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
    
    JCStatement parseRefining(int pos, JmlTokenKind jt) {
        JmlStatementSpec ste;
        ListBuffer<JCIdent> exports = new ListBuffer<>();
        if (jt == JmlTokenKind.REFINING) {
            nextToken();
            if (jmlTokenKind() == JmlTokenKind.ALSO) {
                jmlerror(pos(), endPos(), "jml.invalid.also");
                nextToken();
            }
            if (token.ikind == TokenKind.ELSE) {
                jmlerror(pos(), endPos(), "jml.invalid.also"); // FIXME - should warn about else
                nextToken();
            }
            if (token.kind == TokenKind.COLON) { 
                nextToken();
                exports.add(jmlF.at(pos()).Ident(ident()));
                while (token.kind == TokenKind.COMMA) {
                    nextToken();
                    exports.add(jmlF.at(pos()).Ident(ident()));
                }
                if (token.kind != TokenKind.SEMI) {
                    jmlerror(pos(),endPos(), "jml.message", "Expected a comma or semicolon here");
                }
                nextToken();
            }
        } else {
            //if (JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
                log.warning(pos(),"jml.refining.required");
            //}
        }
        JCModifiers mods = modifiersOpt();
        JmlMethodSpecs specs = parseMethodSpecs(mods);
        for (JmlSpecificationCase c : specs.cases) {
            if (!isNone(c.modifiers)) {
                jmlerror(c.modifiers.getStartPosition(),
                        getEndPos(c.modifiers),
                        "jml.no.mods.in.refining");
                c.modifiers = jmlF.Modifiers(0);
            }
        }
        ste = jmlF.at(pos).JmlStatementSpec(specs);
        ste.exports = exports.toList();
        storeEnd(ste, getEndPos(specs));

        List<JCStatement> stat = blockStatement();
        if (stat == null || stat.isEmpty()) {
            log.error(ste, "jml.message", "Statement specs found at the end of a block (or before an erroneous statement)");
            return null;
        }
        ListBuffer<JCStatement> stats = new ListBuffer<>();
        if (stat.head instanceof JmlStatement && ((JmlStatement)stat.head).clauseType == EndStatement.beginClause) {
            JCStatement begin = stat.head;
            // Has a begin statement, so we read statement until an end
            while (true) {
                stat = blockStatement();
                if (stat.isEmpty()) {
                    log.error(begin, "jml.message", "Expected an 'end' statement to match the begin statement before the end of block");
                    break;
                } else if (stat.get(0) instanceof JmlStatement && ((JmlStatement)stat.get(0)).clauseType == EndStatement.endClause) {
                    break;
                } else {
                    stats.addAll(stat);
                }
            }
        } else if (stat.isEmpty()) {
            log.error(ste, "jml.message", "Statement specs found at the end of a block (or before an erroneous statement)");
        } else {
            stats.addAll(stat);
        }
        ste.statements = collectLoopSpecs(stats.toList());
        return ste;
    }
    
    /* Replicated and slightly altered from JavacParser in order to handle the case where a JML statement
     * precedes a single Java statement that should be a block (e.g. one statement in a if statement or loop)
     */
    JCStatement parseStatementAsBlock() {
        ListBuffer<JCStatement> stats = new ListBuffer<>();
        JCStatement stat = super.parseStatementAsBlock();
        while (stat instanceof JmlAbstractStatement) {
            stats.add(stat);
            stat = super.parseStatementAsBlock();
        }
        if (stat != null) stats.add(stat);
        if (stats.size() > 1) return F.at(stats.first().pos).Block(0, stats.toList());
        return stats.first();
    }

    // TODO - generalize this and move it out of JmlParser
    /** Returns true if the token is a JML type token */
    public boolean isJmlTypeToken(JmlTokenKind t) {
        return t == JmlTokenKind.BSTYPEUC || t == JmlTokenKind.BSBIGINT
                || t == JmlTokenKind.BSREAL || t == JmlTokenKind.PRIMITIVE_TYPE;
    }

    /** Parses a choose statement (the choose token is already read) */
//    public JmlChoose parseChoose() {
//        int pp = pos();
//        nextToken();
//        ListBuffer<JCBlock> orBlocks = new ListBuffer<JCBlock>();
//        orBlocks.append(block()); // FIXME - here and below - what if block()
//                                  // returns null.
//        while (jmlTokenKind() == JmlTokenKind.OR) {
//            nextToken();
//            orBlocks.append(block());
//        }
//        JCBlock elseBlock = null;
//        if (token.kind == ELSE) {
//            nextToken();
//            elseBlock = block();
//        }
//        return toP(jmlF.at(pp).JmlChoose("choose", ChooseClause.chooseClause, orBlocks.toList(), elseBlock));
//    }


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
    
    public boolean setInJmlDeclaration(boolean newValue) {
        boolean b = inJmlDeclaration;
        inJmlDeclaration = newValue;
        return b;
    }
    
    /** Accumulates method specs from multiple consecutive JML
     * declarations. The field is reset to null when a method
     * declaration incorporates the specs.
     */
    public @Nullable JmlMethodSpecs currentMethodSpecs = null;
    /** The most recent field declaration within a class body. */
    public @Nullable JmlVariableDecl currentVariableDecl = null;
    
    /** Returns true if the argument is a possible beginning of a 
     * method specs, after any modifiers */
    protected boolean startOfMethodSpecs(Token possibleKeyword) {
        if (!(S.jml())) return false;
        if (possibleKeyword.kind == TokenKind.IDENTIFIER) {
            return Extensions.instance(context).findTM(0,possibleKeyword.name().toString(),false) instanceof IJmlClauseKind.MethodClause;
        } else {
            ITokenKind jt = possibleKeyword.ikind;
            return (jt == JmlTokenKind.ALSO 
                    || jt == JmlTokenKind.BEHAVIOR 
                    || jt == JmlTokenKind.NORMAL_BEHAVIOR
                    || jt == JmlTokenKind.EXCEPTIONAL_BEHAVIOR
                    || jt == JmlTokenKind.FEASIBLE_BEHAVIOR
                    || jt == JmlTokenKind.IMPLIES_THAT
                    || jt == JmlTokenKind.CODE
                    || jt == JmlTokenKind.MODEL_PROGRAM
                    || jt == JmlTokenKind.FOR_EXAMPLE
                    || jt == JmlTokenKind.EXAMPLE
                    || jt == JmlTokenKind.NORMAL_EXAMPLE
                    || jt == JmlTokenKind.EXCEPTIONAL_EXAMPLE
                    || jt == JmlTokenKind.ABRUPT_BEHAVIOR
                    || jt == TokenKind.ELSE
                    );
        }
    }

    /** Returns true if the argument is a possible initial token
     * of a type specification, after any modifiers.
     */
    protected boolean startOfTypeSpec(Token possibleKeyword) {
        if (!(S.jml())) return false;
        if (possibleKeyword.kind == TokenKind.IDENTIFIER) {
            return Extensions.instance(context).findTM(0,possibleKeyword.name().toString(),false) instanceof IJmlClauseKind.TypeClause;
        } else {
            ITokenKind jt = possibleKeyword.ikind;
            return (jt == JmlTokenKind.INITIALIZER || jt == JmlTokenKind.STATIC_INITIALIZER);
        }
    }
    
    /** Returns non-null if the token introduces a new JML kind of class
     * (e.g. inductive datatype).
     */
    public JmlExtension.ClassLike isJmlClassLike(Token token) {
        if (token.kind != TokenKind.IDENTIFIER) return null;
        String n = ((Tokens.NamedToken)token).name.toString();
        return Extensions.classLike.get(n);
    }

    /**
     * Overridden in order to parse JML declarations and clauses within the body
     * of a class or interface.
     */
    @Override
    public List<JCTree> classOrInterfaceBodyDeclaration(Name className,
            boolean isInterface) {

        ListBuffer<JCTree> list = new ListBuffer<JCTree>();
        loop: while (token.ikind != TokenKind.RBRACE) {
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
            if (jt != null && !isJmlTypeToken(jt) && currentMethodSpecs != null && !startOfMethodSpecs(token) && jt != INITIALIZER && jt != STATIC_INITIALIZER) {
                log.error(currentMethodSpecs.pos, "jml.message", "Misplaced method specifications preceding a " + jt.internedName() + " clause (ignored)");
                currentMethodSpecs = null;
            }
            IJmlClauseKind ct = null;
            String id = null;
            if (S.jml() && token.kind == TokenKind.IDENTIFIER) {
                id = token.name().toString();
                ct = Extensions.instance(context).findTM(0,id,false);
            }
            if (ct != null) {
                if (startOfMethodSpecs(token)) {
                    currentMethodSpecs = parseMethodSpecs(mods);
                    continue;
                } else if (startOfTypeSpec(token)) {
                    JCTree tc = parseTypeSpecs(mods);
                    if (tc instanceof JmlTypeClause && currentMethodSpecs != null && jt != INITIALIZER && jt != STATIC_INITIALIZER) {
                        log.error(currentMethodSpecs.pos, "jml.message", "Misplaced method specifications preceding a " + ((JmlTypeClause)tc).clauseType.name() + " clause (ignored)");
                        currentMethodSpecs = null;
                    }
                    if (tc instanceof JmlTypeClauseIn
                            || tc instanceof JmlTypeClauseMaps) {
                        JCTree tree = tc;
                        if (tree instanceof JmlTypeClauseIn) {
                            ((JmlTypeClauseIn) tree).parentVar = mostRecentVarDecl;
                        }
                        if (mostRecentVarDecl == null) {
                            log.error(tree.pos(), "jml.misplaced.var.spec",
                                    ((JmlTypeClause) tree).keyword);
                        } else {
                            if (mostRecentVarDecl.fieldSpecs == null) {
                                mostRecentVarDecl.fieldSpecs = new JmlSpecs.FieldSpecs(
                                        mostRecentVarDecl);
                            }
                            mostRecentVarDecl.fieldSpecs.list.append((JmlTypeClause) tree);
                            currentVariableDecl = mostRecentVarDecl;
                        }
                    } else {
                        list.append(tc);
                    }
                    continue;
                } else if (utils.findMod(mods,JmlTokenKind.MODEL) == null && utils.findMod(mods,JmlTokenKind.GHOST) == null) {
                    log.error(token.pos, "jml.illegal.token.for.declaration", id);
                    skipThroughSemi();
                    continue;
                }
            } else if (startOfMethodSpecs(token)) {
                currentMethodSpecs = parseMethodSpecs(mods);
                continue;
            } else if (startOfTypeSpec(token)) {
                JCTree tc = parseTypeSpecs(mods);
                list.append(tc);
                continue;
            }
            if (jt == null || isJmlTypeToken(jt)) {
                pushBackModifiers = mods; // This is used to pass the modifiers
                // into super.classOrInterfaceBodyDeclaration
                mods = null;
                boolean startsInJml = S.jml();
                List<JCTree>  t;
                if (startsInJml && !inLocalOrAnonClass) {
                    boolean prevInJmlDeclaration = inJmlDeclaration;
                    inJmlDeclaration = true;
                    if (token.kind == TokenKind.BANG) {
                        replacementType = unannotatedType();
                        inJmlDeclaration = false;
                        startsInJml = false;
                    }
                    if (token.kind == TokenKind.SEMI && currentMethodSpecs != null) {
                        log.error(token.pos, "jml.message", "Method specs preceding an empty declaration are ignored");
                        currentMethodSpecs = null;
                    }
                    ClassLike cl =  null;
                    if ((cl = isJmlClassLike(token)) != null) {
                        t = List.<JCTree>of(cl.parse(this, mods));
                    } else {
                        t = super.classOrInterfaceBodyDeclaration(
                                className, isInterface);
                        if (isInterface && t.head instanceof JmlMethodDecl) {
                            JmlMethodDecl md = (JmlMethodDecl)t.head;
                            if (utils.findMod(md.mods,JmlTokenKind.MODEL)!= null
                                    && (md.mods.flags & Flags.STATIC) == 0) {
                                md.mods.flags |= Flags.DEFAULT;
                            }
                        }
                    }
                    inJmlDeclaration = prevInJmlDeclaration;
                } else {

                    if (token.kind == TokenKind.SEMI && currentMethodSpecs != null) {
                        log.error(token.pos, "jml.message", "Method specs preceding an empty declaration are ignored");
                        currentMethodSpecs = null;
                    }
                    // no longer in JML
                    // FIXME - attach doc comment?
                    t = super.classOrInterfaceBodyDeclaration(
                            className, isInterface);
                }
                if (!inJmlDeclaration) {
                    for (JCTree tr : t) {
                        JCTree ttr = tr;
                        if (tr instanceof JmlClassDecl) {
                            if (currentMethodSpecs != null) {
                                log.error(tr.pos, "jml.message", "Method specs may not precede a class declaration");
                                currentMethodSpecs = null;
                            }
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
                            if (currentMethodSpecs != null) {
                                log.error(tr.pos, "jml.message", "Method specs may not precede a variable declaration");
                                currentMethodSpecs = null;
                            }
                            JmlVariableDecl d = (JmlVariableDecl) tr;
                            if (replacementType != null) {
                                insertReplacementType(d,replacementType);
                                replacementType = null;
                            } else {
                                if (startsInJml) utils.setJML(d.mods);  // FIXME - should this be executed even when there is a replacement type?
                            }
                            d.sourcefile = log.currentSourceFile();
                            ttr = tr; // toP(jmlF.at(pos).JmlTypeClauseDecl(d));
                            attach(d, dc);
                            currentVariableDecl = d;
                        } else {
                            if (currentMethodSpecs != null) {
                                log.error(tr.pos, "jml.message", "Method specs that do not precede a method declaration are ignored");
                                currentMethodSpecs = null;
                            }
                            ttr = null;
                        }
                        //                            if (tr != null && utils.findMod(tmods, JmlTokenKind.MODEL) == null && utils.findMod(tmods, JmlTokenKind.GHOST) == null) {
                        //                                jmlerror(tr.pos, "jml.missing.ghost.model");
                        //                            }
                        dc = null;
                        if (ttr != null) list.append(ttr);
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
                                ((JmlTypeClause) tree).keyword);
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
//            } else if (jt == INVARIANT || jt == INITIALLY || jt == AXIOM) {
//                appendIfNotNull(list,parseInvariantInitiallyAxiom(mods));
//            } else if (jt == CONSTRAINT) {
//                appendIfNotNull(list,parseConstraint(mods));
//            } else if (jt == REPRESENTS) {
//                appendIfNotNull(list,parseRepresents(mods));
            } else if (startOfMethodSpecs(token)) {
                currentMethodSpecs = parseMethodSpecs(mods);
                //list.append(parseMethodSpecs(mods));
                // FIXME - attach doc comment?
                // getMethodSpecs may have already parsed some modifiers.
                // They will be in pushBackModifiers
//            } else if (jt == IN) {
//                JmlTypeClauseIn inClause = parseIn(pos, mods);
//                inClause.parentVar = mostRecentVarDecl;
//                if (mostRecentVarDecl == null) {
//                    log.error(inClause.pos(), "jml.misplaced.var.spec",
//                            inClause.keyword);
//                } else {
//                    if (mostRecentVarDecl.fieldSpecs == null) {
//                        mostRecentVarDecl.fieldSpecs = new JmlSpecs.FieldSpecs(
//                                mostRecentVarDecl);
//                    }
//                    mostRecentVarDecl.fieldSpecs.list.append(inClause);
//                    currentVariableDecl = mostRecentVarDecl;
//                }
//            } else if (jt == MAPS) {
//                JmlTypeClauseMaps mapsClause = parseMaps(pos, mods, list);
//                if (mostRecentVarDecl == null) {
//                    log.error(mapsClause.pos(), "jml.misplaced.var.spec",
//                            mapsClause.keyword);
//                } else {
//                    if (mostRecentVarDecl.fieldSpecs == null) {
//                        mostRecentVarDecl.fieldSpecs = new JmlSpecs.FieldSpecs(
//                                mostRecentVarDecl);
//                    }
//                    mostRecentVarDecl.fieldSpecs.list.append(mapsClause);
//                    currentVariableDecl = mostRecentVarDecl;
//                }
//            } else if (jt == readasbleClause || jt == writableClause) {
//                appendIfNotNull(list,parseReadableWritable(mods, jt));
//            } else if (jt == monnitorsforClause) {
//                appendIfNotNull(list,parseMonitorsFor(mods));
            } else if (jt == INITIALIZER || jt == STATIC_INITIALIZER) {
                //@ FIXME - modifiers?
//                JmlTypeClauseInitializer initializer = jmlF.at(pos()).JmlTypeClauseInitializer(jt,mods);
//                //@ FIXME - parse failure?
//                initializer.specs = currentMethodSpecs;
                currentMethodSpecs = null;
//                list.append(to(initializer));
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
    
    public void appendIfNotNull(ListBuffer<JCTree> list, JmlTypeClause clause) {
        if (clause != null) list.append(clause);
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
                    mapsClause.name());
        S.setJmlKeyword(false);
        nextToken(); // skip over the maps token
        JCExpression e = parseMapsTarget();
        ListBuffer<JmlGroupName> glist;
        if (jmlTokenClauseKind() != intoKind) {
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
            jmlerror(pos, "jml.no.mods.allowed", inClause.name());
        S.setJmlKeyword(false);
        nextToken(); // skip over the in token
        ListBuffer<JmlGroupName> list = parseGroupNameList();
        S.setJmlKeyword(true);
        accept(SEMI);
        return toP(jmlF.at(pos).JmlTypeClauseIn(list.toList()));
    }

    /** Parses an invariant, initially, or axiom declaration */
//    public JmlTypeClauseExpr parseInvariantInitiallyAxiom(JCModifiers mods) {
//        int pos = pos();
//        JmlTokenKind jt = jmlTokenKind();
//        S.setJmlKeyword(false);
//        nextToken();
//        JCExpression e = parseExpression();
//        S.setJmlKeyword(true);
//        if (token.kind != SEMI) {
//            jmlerror(pos(), endPos(), "jml.bad.construct",
//                    jt.internedName() + " declaration");
//            skipThroughSemi();
//        } else {
//            nextToken();
//        }
//        if (mods == null) mods = jmlF.at(pos).Modifiers(0);
//        JmlTypeClauseExpr tcl = to(jmlF.at(pos).JmlTypeClauseExpr(mods, jt, e));
//        tcl.source = log.currentSourceFile();
//        return tcl;
//    }

//    /** Parses a represents clause */
//    public JmlTypeClauseRepresents parseRepresents(JCModifiers mods) {
//        S.setJmlKeyword(false);
//        int pos = pos();
//        nextToken();
//        JCExpression id = parseStoreRef(true);
//        boolean suchThat;
//        JCExpression e;
//        if (token.kind == EQ) {
//            suchThat = false;
//            nextToken();
//            e = parseExpression();
//        } else if (jmlTokenKind() == JmlTokenKind.LEFT_ARROW) {
//            if (isDeprecationSet() || JmlOption.isOption(context, JmlOption.STRICT)) {
//                log.warning(pos(), "jml.deprecated.left.arrow.in.represents");
//            }
//            suchThat = false;
//            nextToken();
//            e = parseExpression();
//        } else if (jmlTokenKind() == JmlTokenKind.BSSUCHTHAT) {
//            suchThat = true;
//            nextToken();
//            e = parseExpression();
//        } else {
//            if (id != null) jmlerror(pos(), endPos(), "jml.bad.represents.token");
//            e = null;
//            skipToSemi();
//            suchThat = false;
//        }
//        S.setJmlKeyword(true);
//        if (e == null) { // skip
//            e = jmlF.Erroneous();
//        } else if (token.kind != SEMI) {
//            jmlerror(pos(), endPos(),
//                    "jml.invalid.expression.or.missing.semi");
//            skipThroughSemi();
//        } else {
//            nextToken();
//        }
//        if (id == null) return null;
//        if (mods == null) mods = jmlF.at(pos).Modifiers(0);
//        JmlTypeClauseRepresents tcl = to(jmlF.at(pos).JmlTypeClauseRepresents(
//                mods, id, suchThat, e));
//        tcl.source = log.currentSourceFile();
//        return tcl;
//    }

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
            if (tokenIsId(everythingID,notspecifiedID)) {
                nextToken();
                // This is the default, so we just leave sigs null
                if (notlist) sigs = new ListBuffer<JmlMethodSig>().toList();
                notlist = false;
            } else if (tokenIsId(nothingID)) {
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

//    /** Parse a readable or writable clause */
//    public JmlTypeClauseConditional parseReadableWritable(JCModifiers mods,
//            JmlTokenKind jmlTokenKind) {
//        int p = pos();
//        S.setJmlKeyword(false);
//        nextToken();
//        Name n;
//        JCExpression e;
//        int identPos = pos();
//        if (token.kind != TokenKind.IDENTIFIER) {
//            jmlerror(pos(), endPos(), "jml.expected", "an identifier");
//            n = names.asterisk; // place holder for an error situation
//            e = jmlF.Erroneous();
//        } else {
//            n = ident();
//            if (token.kind != IF) {
//                jmlerror(pos(), endPos(), "jml.expected", "an if token");
//                e = jmlF.Erroneous();
//            } else {
//                accept(TokenKind.IF);
//                e = parseExpression();
//            }
//        }
//        JCTree.JCIdent id = to(jmlF.at(identPos).Ident(n));
//        S.setJmlKeyword(true);
//        if (e.getTag() == JCTree.Tag.ERRONEOUS || token.kind != SEMI) {
//            skipThroughSemi();
//        } else {
//            nextToken();
//        }
//        return toP(jmlF.at(p).JmlTypeClauseConditional(mods, jmlTokenKind, id, e));
//    }

//<<<<<<< HEAD
//    /** Parse a monitors_for clause */
//    public JmlTypeClauseMonitorsFor parseMonitorsFor(JCModifiers mods) {
//        int p = pos();
//        S.setJmlKeyword(false);
//        nextToken();
//        ListBuffer<JCExpression> elist = new ListBuffer<JCExpression>();
//        Name n;
//        int identPos = pos();
//        ITokenKind tk = token.kind;
//        if (tk != IDENTIFIER) {
//            jmlerror(pos(), endPos(), "jml.expected", "an identifier");
//            n = names.asterisk; // place holder for an error situation
//        } else {
//            n = ident(); // Advances to next token
//            if (token.kind != TokenKind.EQ && jmlTokenKind() != JmlTokenKind.LEFT_ARROW) {
//                jmlerror(pos(), endPos(), "jml.expected",
//                        "an = or <- token");
//            } else {
//                nextToken();
//                elist = expressionList();
//            }
//        }
//        JCTree.JCIdent id = to(jmlF.at(identPos).Ident(n));
//        S.setJmlKeyword(true);
//        if (token.kind != SEMI) {
//            skipThroughSemi();
//        } else {
//            nextToken();
//        }
//        return toP(jmlF.at(p).JmlTypeClauseMonitorsFor(mods, id, elist.toList()));
//    }
    /** Parse a monitors_for clause */
    public JmlTypeClauseMonitorsFor parseMonitorsFor(JCModifiers mods) {
        int p = pos();
        S.setJmlKeyword(false);
        nextToken();
        List<JCExpression> elist = List.<JCExpression>nil();
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
                elist = parseExpressionList();
            }
        }
        JCTree.JCIdent id = to(jmlF.at(identPos).Ident(n));
        S.setJmlKeyword(true);
        if (token.kind != SEMI) {
            skipThroughSemi();
        } else {
            nextToken();
        }
        return toP(jmlF.at(p).JmlTypeClauseMonitorsFor(mods, id, elist));
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
    public List<JCExpression> parseExpressionList() {
        ListBuffer<JCExpression> args = new ListBuffer<>();
        args.append(parseExpression());
        while (token.kind == COMMA) {
            nextToken();
            JCExpression e = parseExpression();
            args.append(e); // e might be a JCErroneous
        }
        return args.toList();
    }
    
    protected JCExpression term3Rest(JCExpression t,
            List<JCExpression> typeArgs) {
        int p = S.token().pos;
        while (S.jml() && ((token.kind == DOT && S.token(1).kind == INTLITERAL) || 
                (token.kind == TokenKind.DOUBLELITERAL && token.stringVal().charAt(0) == '.'))) {
            //System.out.println("PB " + t.getStartPosition() + " " + t.getPreferredPosition() + " " + t.pos + " " + t);
            if (token.kind == DOUBLELITERAL) {
                t = jmlF.at(p).Select(t, names.fromString("_$T" + token.stringVal().substring(1)));
                accept(DOUBLELITERAL);
                toP(t);
            } else {
                accept(DOT);
                String d = token.stringVal();
                t = jmlF.at(p).Select(t, names.fromString("_$T" + d));
                accept(INTLITERAL);
                toP(t);
                //System.out.println("P " + t.getStartPosition() + " " + t.getPreferredPosition() + " " + t.pos + " " + t);
            }
            p = S.token().pos;
        }
        t = super.term3Rest(t, typeArgs);
        if (S.jml() && token.kind == MONKEYS_AT) {
            accept(MONKEYS_AT);
            int pp = pos();
            Name label = ident();
            JCIdent id = this.maker().at(pp).Ident(label);
            JmlMethodInvocation tt = toP(this.maker().at(t).JmlMethodInvocation(oldKind, List.<JCExpression>of(t,id)));
            return tt;
        }
        return t;    
    }
    
    public JCExpression parseQualifiedIdent(boolean allowAnnos) {
        return qualident(allowAnnos);
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
    
    public JCExpression replacementType;
    
    @Override
    public JCExpression unannotatedType() {
        JCExpression replacementType = null;
        {
            boolean isBrace = token.kind == TokenKind.LBRACE;
            if (isBrace || token.kind==TokenKind.BANG) {
                boolean b = S.jmlkeyword;
                try {
                    // We need to be in non-JML mode so that we don't interpret 
                    S.setJmlKeyword(false);
                    nextToken();
                    replacementType = super.unannotatedType();
                } finally {
                    S.setJmlKeyword(b);
                    if (isBrace) accept(TokenKind.RBRACE);
                    if (token.ikind != JmlTokenKind.ENDJMLCOMMENT) {
                        log.error(token.pos,"jml.bad.construct","JML construct");
                    }
                    skipThroughEndOfJML();
                }
                if (!isBrace) {
                    return replacementType;
                }
            }
        }
        JCExpression type = super.unannotatedType();
        this.replacementType = replacementType;
        return type;
    }
    
    public JCTree parseTypeSpecs(JCModifiers mods) {
        String id = token.kind == TokenKind.IDENTIFIER ?  token.name().toString() : jmlTokenKind().internedName();
        IJmlClauseKind ct = Extensions.instance(context).findTM(0,id,false);
        JCTree t = ct.parse(mods, id, ct, this);
        return t;
    }

    // Parses a sequence of specification cases, having already
    // parsed a sequence of modifiers
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
        if ((t = jmlTokenKind()) == JmlTokenKind.FEASIBLE_BEHAVIOR) {
            if (!isNone(mods))
                jmlerror(pos(), endPos(), "jml.no.mods.allowed",
                        t.internedName());
            nextToken();
            mods = modifiersOpt();
            ListBuffer<JmlMethodClause> clauses = new ListBuffer<JmlMethodClause>();
            JmlMethodClause cl;
            while ((cl = getClause()) != null) {
                clauses.append(cl);
                lastPos = getEndPos(cl);
                mods = modifiersOpt();
            }
            sp.feasible = clauses.toList();
        }
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
    
    public int casenum = 0;

    // [ also ] [ modifiers ] [ | behavior | normal_behavior |
    // exceptional_behavior ] [ clause ]*
    public JmlSpecificationCase parseSpecificationCase(JCModifiers mods,
            boolean exampleSection) {
        JmlTokenKind also = null;
        JmlTokenKind ijt = jmlTokenKind();
        if (ijt == ALSO || token.ikind == TokenKind.ELSE) {
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
        if (jmlTokenKind() == JmlTokenKind.FEASIBLE_BEHAVIOR) return null;
        if (jmlTokenKind() == JmlTokenKind.CODE) {
            codePos = pos();
            code = true;
            nextToken();
        }

        boolean bb = log.currentSourceFile().toString().contains("Stream.jml");
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
            nextToken(); // skip over the model_program token

//            JCBlock stat = parseModelProgramBlock();
//            JmlSpecificationCase spc = toP(jmlF.at(pos).JmlSpecificationCase(mods, code,
//                        MODEL_PROGRAM, also, List.<JmlMethodClause>nil(), stat));
//            spc.sourcefile = log.currentSourceFile();
//            return spc;
//        } else if (jt == null && S.jml() && also != null) {
//            jmlerror(pos(), endPos(), "jml.invalid.keyword.in.spec",
//                    S.chars());
//            skipThroughSemi();
//            // Call it lightweight
        } else {
            jt = null;
            if (code) log.warning(codePos, "jml.misplaced.code");
            // lightweight
        }
        
        ListBuffer<JmlMethodClause> clauses = new ListBuffer<JmlMethodClause>();
        JmlMethodClause e;
        JCBlock stat = null;
        while (true) {
//            if (token.kind == TokenKind.IDENTIFIER) {
//                String id = ident().toString();
//                extensions.find
//            } else 
            if ((e = getClause()) != null) {
                clauses.append(e);
            } else if (S.jml() && token.kind == TokenKind.LBRACE) {
                if (stat != null) {
                    // FIXME - error
                }
                stat = parseModelProgramBlock();
            } else {
                break;
            }
        }

        if (clauses.size() == 0 && stat == null) {
            if (jt != null && JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
                jmlerror(pos, "jml.empty.specification.case");
            }
            if (jt == null && also == null && !code) return null;
        }
        if (jt == null && code) code = false; // Already warned about this
        JmlSpecificationCase j = jmlF.at(pos).JmlSpecificationCase(mods, code,
                jt, also, clauses.toList(), stat);
        j.name = "_case_" + (++casenum);
        storeEnd(j, j.clauses.isEmpty() ? pos + 1 : getEndPos(j.clauses.last()));
        j.sourcefile = log.currentSourceFile();
        return j;
    }

    /** Issues a warning that the named construct is parsed and ignored */
    public void warnNotImplemented(int pos, String construct, String location) {
        if (JmlOption.isOption(context, JmlOption.SHOW_NOT_IMPLEMENTED))
            log.warning(pos, "jml.unimplemented.construct", construct, location);
    }

    public JCBlock parseModelProgramBlock() {
        try {
            inJmlDeclaration = true;
            inModelProgram = true;
            return block();
        } finally {
            inJmlDeclaration = false;
            inModelProgram = false;
        }
    }
    
//    /** Parses a model program; presumes the current token is model_program */
//    public JmlSpecificationCase parseModelProgram(JCModifiers mods,
//            boolean code, JmlTokenKind also) {
//        int pos = pos();
//        nextToken(); // skip over the model_program token
//
//        JCBlock stat;
//        JmlSpecificationCase spc;
//            stat = parseModelProgramBlock();
//            spc = toP(jmlF.at(pos).JmlSpecificationCase(mods, code,
//                    MODEL_PROGRAM, also, stat));
//            spc.clauses = List.<JmlMethodClause>nil();
//        return spc;
//    }

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
        } while (jmlTokenKind() == ALSO || token.ikind == TokenKind.ELSE);
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
        
        String keyword = null;
        if (token().kind == IDENTIFIER && S.jml() && S.jmlKeywordMode()) keyword = token().name().toString();
        if (keyword != null) {
            IJmlClauseKind clauseType = Extensions.instance(context).findTM(pos(), keyword, true);
            if (clauseType instanceof MethodClauseType) {
                if (clauseType != null) {
                    return ((MethodClauseType)clauseType).parse(null, keyword, clauseType, this);
                }
            } else {
                // INTENRAL ERROR
            }
        }
        JmlTokenKind jt = jmlTokenKind();
        int pos = pos();
        S.setJmlKeyword(false);
        JmlMethodClause res = null;
        if (jt == null && keyword != null) {
            IJmlClauseKind ct = Extensions.instance(context).findTM(token().pos, keyword, true);
            if (ct instanceof IJmlClauseKind.MethodClause) {
                res = (JmlMethodClause)ct.parse(null,keyword,ct,this);
            }
        }
        else if (jt != null)
            switch (jt) {

//                // The cases have to include all clause types.
//
//                case REQUIRES:
//                case ENSURES:
//                case DIVERGES:
//                case WHEN:
//                    res = parseExprClause();
//                    break;
//
//                case SIGNALS: // signals (Exception e) parseExpression ;
//                    res = parseSignals();
//                    break;
//
//                case SIGNALS_ONLY:
//                    res = parseSignalsOnly();
//                    break;
//
//                case ASSIGNABLE:
//                case ACCESSIBLE:
//                case CAPTURES:
//                    res = parseStoreRefClause();
//                    break;

//                case FORALL:
//                case OLD:
//                    res = parseForallOld();
//                    break;

//                case WORKING_SPACE:
//                case MEASURED_BY:
//                case DURATION:
//                    res = parseDurationEtc();
//                    break;

//                case CALLABLE:
//                    warnNotImplemented(pos(), jt.internedName(),
//                            "JmlParser.getClause()");
//                    nextToken();
//                    JmlStoreRefKeyword refkeyword = parseOptStoreRefKeyword();
//                    List<JmlMethodSig> sigs = null;
//                    if (refkeyword == null) {
//                        sigs = parseMethodNameList();
//                    }
//                    S.setJmlKeyword(true);
//                    int endpos = pos();
//                    accept(SEMI);
//                    JmlMethodClauseCallable ec;
//                    if (refkeyword != null) {
//                        ec = toP(jmlF.at(pos).JmlMethodClauseCallable(
//                                refkeyword));
//                    } else {
//                        ec = toP(jmlF.at(pos).JmlMethodClauseCallable(sigs));
//                    }
//                    res = ec;
//                    break;

                case SPEC_GROUP_START:
                    S.setJmlKeyword(true);
                    res = getSpecificationGroup();
                    break;

//                case CONTINUES:
//                case BREAKS:
//                case RETURNS:
//                    if (!inModelProgram) {
//                        jmlerror(pos(), endPos(),
//                                "jml.misplaced.modelprogram.statement",
//                                jt.toString());
//                    }
//                    res = parseExprClause();
//                    // FIXME _ continues, breaks may have an optional label
//                    break;

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
        if ( jmlTokenClauseKind() == notspecifiedKind) {
            int pos = pos();
            nextToken();
            JmlSingleton e = jmlF.at(pos).JmlSingleton(notspecifiedKind);
            return toP(e);
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
//    public JmlMethodClauseExpr parseExprClause() {
//        JmlTokenKind jt = jmlTokenKind();
//        int pos = pos();
//        nextToken();
//        JCExpression e = parsePredicateOrNotSpecified();
//        S.setJmlKeyword(true);
//        if (token.kind != SEMI) {
//            syntaxError(pos(), null, "jml.invalid.expression.or.missing.semi");
//            skipThroughSemi();
//        } else {
//            nextToken(); // skip SEMI
//        }
//        JmlMethodClauseExpr cl = jmlF.at(pos).JmlMethodClauseExpr(jt, e);
//        return toP(cl);
//    }

//    /**
//     * Parses a signals method specification clause
//     * 
//     * @return the parsed JmlMethodClause
//     */
//    public JmlMethodClauseSignals parseSignals() {
//        JmlTokenKind jt = jmlTokenKind();
//        int pos = pos();
//        JCExpression e;
//        nextToken();
//        JCExpression t = null;
//        Name ident = null;
//        int rpos = pos;
//        if (token.kind != LPAREN) {
//            syntaxError(pos(), null, "jml.expected.lparen.signals");
//            t = to(jmlF.at(pos()).Ident(names.fromString("java")));
//            t = to(jmlF.at(pos()).Select(t, names.fromString("lang")));
//            t = to(jmlF.at(pos()).Select(t, names.fromString("Exception")));
//            e = parsePredicateOrNotSpecified();
//        } else {
//            nextToken();
//            // Get type
//            t = parseType();
//            // Get identifier (optional)
//            if (token.kind == IDENTIFIER) {
//                ident = ident();
//            }
//            rpos = pos();
//            if (token.kind != RPAREN) {
//                syntaxError(pos(), null, "jml.expected.rparen.signals");
//                skipToSemi();
//                e = toP(jmlF.at(pos()).Erroneous());
//            } else {
//                nextToken();
//                if (token.kind == SEMI) {
//                    e = toP(jmlF.at(pos()).Literal(TypeTag.BOOLEAN, 1)); // Boolean.TRUE));
//                } else {
//                    e = parsePredicateOrNotSpecified();
//                }
//            }
//        }
//        S.setJmlKeyword(true);
//        JCTree.JCVariableDecl var = jmlF.at(t.pos).VarDef(
//                jmlF.at(t.pos).Modifiers(0), ident, t, null);
//        storeEnd(var, rpos);
//        if (token.kind != SEMI) {
//            if (e.getKind() != Kind.ERRONEOUS)
//                syntaxError(pos(), null, "jml.missing.semi");
//            skipThroughSemi();
//        } else {
//            nextToken();
//        }
//        return toP(jmlF.at(pos).JmlMethodClauseSignals(jt, var, e));
//    }
//
//    /**
//     * Parses a signals_only clause. The current token must be the signals_only
//     * token; upon return the terminating semicolon will have been parsed.
//     * 
//     * @return a JmlMethodClauseSignalsOnly AST node
//     */
//    public JmlMethodClauseSignalsOnly parseSignalsOnly() {
//        JmlTokenKind clauseType = jmlTokenKind();
//        int pos = pos();
//        nextToken();
//        JmlTokenKind jt = jmlTokenKind();
//        ITokenKind tk = token.kind;
//        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
//
//        if (jt == BSNOTHING) {
//            S.setJmlKeyword(true);
//            nextToken();
//            if (token.kind != SEMI) {
//                syntaxError(pos(), null, "jml.expected.semi.after.nothing");
//                skipThroughSemi();
//            } else {
//                nextToken();
//            }
//        } else if (tk == SEMI) {
//            S.setJmlKeyword(true);
//            syntaxError(pos(), null, "jml.use.nothing", clauseType.internedName());
//            nextToken();
//        } else {
//            while (true) {
//                JCExpression typ = parseType(); // if this fails, a JCErroneous
//                // is returned
//                list.append(typ);
//                tk = token.kind;
//                if (tk == SEMI) {
//                    S.setJmlKeyword(true);
//                    nextToken();
//                    break;
//                } else if (tk == COMMA) {
//                    nextToken();
//                    continue;
//                } else if (typ instanceof JCErroneous) {
//                    S.setJmlKeyword(true);
//                    skipThroughSemi();
//                    break;
//                } else if (jmlTokenKind() == ENDJMLCOMMENT) {
//                    syntaxError(pos(), null, "jml.missing.semi");
//                } else {
//                    syntaxError(pos(), null, "jml.missing.comma");
//                    continue;
//                }
//                // error
//                S.setJmlKeyword(true);
//                skipThroughSemi();
//                break;
//            }
//        }
//        return toP(jmlF.at(pos).JmlMethodClauseSignalsOnly(clauseType, list.toList()));
//    }

//    public JmlMethodClauseDecl parseForallOld() {
//        int pos = pos();
//        JmlTokenKind jt = jmlTokenKind();
//        nextToken();
//        // non_null and nullable and perhaps other type modifiers in the
//        // future are allowed
//        JCModifiers mods = modifiersOpt();
//        JCExpression t = parseType();
//        boolean prev = inJmlDeclaration;
//        inJmlDeclaration = true; // allows non-ghost declarations
//        ListBuffer<JCTree.JCVariableDecl> decls = variableDeclarators(mods, t,
//                new ListBuffer<JCVariableDecl>());
//        inJmlDeclaration = prev;
//        JmlMethodClauseDecl res = to(jmlF.at(pos)
//                .JmlMethodClauseDecl(jt, decls.toList()));
//        S.setJmlKeyword(true);
//        if (token.kind == SEMI) {
//            nextToken();
//        } else {
//            jmlerror(pos(), endPos(), "jml.bad.construct",
//                    jt.internedName() + " specification");
//            skipThroughSemi();
//        }
//        return res;
//    }

//    /**
//     * Parses (duration|working_space|?) (<expression>|"\\not_specified") [ "if"
//     * <expression> ] ";"
//     */
//    public JmlMethodClauseConditional parseDurationEtc() {
//        int pos = pos();
//        JmlTokenKind jt = jmlTokenKind();
//        JCExpression p = null;
//        nextToken();
//        JCExpression e = parsePredicateOrNotSpecified();
//        if (token.kind == IF) { // The if is not allowed if the
//            // expression is not_specified, but we test that
//            // during type checking
//            nextToken();
//            p = parseExpression();
//        }
//        JmlMethodClauseConditional res = to(jmlF.at(pos)
//                .JmlMethodClauseConditional(jt, e, p));
//        S.setJmlKeyword(true);
//        if (token.kind == SEMI) {
//            nextToken();
//        } else {
//            jmlerror(pos(), endPos(), "jml.bad.construct",
//                    jt.internedName() + " specification");
//            skipThroughSemi();
//        }
//        return res;
//    }

//    /** Parses "assignable" <store-ref-list> ";" */
//    public JmlMethodClauseStoreRef parseStoreRefClause() {
//        JmlTokenKind jt = jmlTokenKind();
//        int pos = pos();
//        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
//        nextToken(); // skip over the assignable token
//        if (token.kind == SEMI) {
//            syntaxError(pos(), null, "jml.use.nothing.assignable");
//            S.setJmlKeyword(true);
//            nextToken(); // skip over the SEMI
//        } else {
//            list = parseStoreRefList(false);
//            if (token.kind == SEMI) {
//                // OK, go on
//            } else if (jmlTokenKind() == ENDJMLCOMMENT) {
//                syntaxError(pos(), null, "jml.missing.semi");
//            }
//            S.setJmlKeyword(true);
//            if (token.kind != SEMI) {
//                // error already reported
//                skipThroughSemi();
//            } else {
//                if (list.isEmpty()) {
//                    syntaxError(pos(), null, "jml.use.nothing.assignable");
//                }
//                nextToken();
//            }
//        }
//        return toP(jmlF.at(pos).JmlMethodClauseStoreRef(jt, list.toList()));
//    }

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
        int p = pos();
        if (tokenIsId(nothingID)) {
            JmlStoreRefKeyword s = to(jmlF.at(p).JmlStoreRefKeyword(nothingKind));
            nextToken();
            return s;
        }
        if (tokenIsId(everythingID)) {
            JmlStoreRefKeyword s = to(jmlF.at(p).JmlStoreRefKeyword(everythingKind));
            nextToken();
            return s;
        }
        if (tokenIsId(notspecifiedID)) {
            JmlStoreRefKeyword s = to(jmlF.at(p).JmlStoreRefKeyword(notspecifiedKind));
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
        else if (ss == null) {
            // Error happened and was reported
            return null;
        } else {
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
        int p = pos();
        if (token.kind == IDENTIFIER) {
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
//        } else if (!strictId && (jt == INFORMAL_COMMENT)) {
//            JCExpression s = to(jmlF.at(p).JmlStoreRefKeyword(everythingKind));
//            nextToken();
//            return s;  // FIXME
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
                        if (JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
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
    public JCModifiers modifiersOpt() {
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

    public/* @ nullable */JCAnnotation tokenToAnnotationAST(String annName,
            int position, int endpos) {
        JCExpression t = to(F.at(position).Ident(names.fromString("org")));
        t = to(F.at(position).Select(t, names.fromString("jmlspecs")));
        t = to(F.at(position).Select(t, names.fromString("annotation")));
        t = to(F.at(position).Select(t, names.fromString(annName)));
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
                if (JmlTokenKind.extensions.contains(j) && JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
                    log.warning(pos(),"jml.not.strict",j.internedName());  // FIXME - probably wrong position
                }
            } else if (j == ENDJMLCOMMENT) {
                // skip over
            } else if (tokenIsId(constructorID,fieldID,methodID)) {
                // FIXME - do we want to save this anywhere; check that it
                // matches the declaration; check that it is not used on
                // something other than a declaration?
                // Also setJmlKeyword back to true
                S.setJmlKeyword(false);
            } else if (j == CONSTRUCTOR | j == METHOD | j == FIELD) {
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
                    .JmlPrimitiveTypeTree(jt,null));
            nextToken();
            return t;
        } else if (jt == JmlTokenKind.PRIMITIVE_TYPE) {
            JCPrimitiveTypeTree t = to(jmlF.at(pos())
                    .JmlPrimitiveTypeTree(jt,ident()));
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
    
    public boolean underscoreOK = false;
    
    @Override
    public Name ident() {
        if (token.kind == CUSTOM) {
            if (((JmlToken)token).jmlkind == JmlTokenKind.ENDJMLCOMMENT) {
                jmlerror(pos(),endPos(),"jml.end.instead.of.ident");
                nextToken();
                return names.error;
// We used to give an error if a JML reserved word was used as an identifier. But this should
// be allowed in Java code. We relax it everywhere though this may have some unintended consequences.
//              jmlerror(pos(),endPos(),"jml.keyword.instead.of.ident",jmlTokenKind().internedName());
//              nextToken();
//              return names.error;
            } else {
                Name name = names.fromString(((JmlToken)token).jmlkind.internedName());
                token = new Tokens.NamedToken(IDENTIFIER, token.pos, token.endPos, name, token.comments);
                return super.ident();
            }
        } else if (underscoreOK && token.kind == UNDERSCORE) {
            Name name = token.name();
            nextToken();
            return name;
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
        IJmlClauseKind jt = jmlTokenClauseKind();
        while (jt == equivalenceKind || jt == inequivalenceKind) {
            int ppos = pos(); // position of the operator
            nextToken();
            JCExpression tt = term2Imp();
            t = toP(jmlF.at(ppos).JmlBinary(jt, t, tt));
            jt = jmlTokenClauseKind();
        }
        return t;
    }

    protected JCExpression term2Imp() {
        JCExpression t = term2();
        if ((mode & EXPR) != 0 
                && (jmlTokenClauseKind() == impliesKind || jmlTokenClauseKind() == reverseimpliesKind)) {
            mode = EXPR;
            return term2ImpRest(t);
        } else {
            return t;
        }
    }

    protected JCExpression term2ImpRest(JCExpression t) {
        IJmlClauseKind jt = jmlTokenClauseKind();
        if (jt == impliesKind) {
            // For IMPLIES we need to associate to the right
            int ppos = pos(); // position of the operator
            nextToken();
            JCExpression tt = term2ImpRestX();
            t = toP(jmlF.at(ppos).JmlBinary(jt, t, tt));
            if (jmlTokenClauseKind() == reverseimpliesKind) {
                syntaxError(pos(), null, "jml.mixed.implies");
                skipToSemi();
            }
        } else if (jt == reverseimpliesKind) {
            // For REVERSE_IMPLIES we do the conventional association to the
            // left
            do {
                int ppos = pos(); // position of the operator
                nextToken();
                JCExpression tt = term2();
                t = toP(jmlF.at(ppos).JmlBinary(jt, t, tt));
                jt = jmlTokenClauseKind();
            } while (jt == reverseimpliesKind);
            if (jt == impliesKind) {
                syntaxError(pos(), null, "jml.mixed.implies");
                skipToSemi();
            }
        }
        return t;
    }

    /** A local call so we can use recursion to do the association to the right */
    protected JCExpression term2ImpRestX() {
        JCExpression t = term2();
        IJmlClauseKind jt = jmlTokenClauseKind();
        if (jt != impliesKind) return t;
        int ppos = pos();
        nextToken();
        JCExpression tt = term2ImpRestX();
        return toP(jmlF.at(ppos).JmlBinary(jt, t, tt));
    }
    
    protected ParensResult analyzeParens() {
        if (S.token(0).kind == TokenKind.LPAREN) {
            Token t = S.token(1);
            if (t.kind == TokenKind.IDENTIFIER) {
                if (t.name().charAt(0) == '\\') return ParensResult.PARENS;
            }
        }
        return super.analyzeParens();
    }
    
    protected ParensResult analyzeParensHelper(Token t) {
        if (!(t instanceof JmlToken)) return ParensResult.PARENS;
        IJmlClauseKind jtk = ((JmlToken)t).jmlclausekind;
        switch (jtk.name()) {
            case impliesID: case reverseimpliesID: case equivalenceID: case inequivalenceID: case subtypeofID: case subtypeofeqID:
            case jsubtypeofID: case jsubtypeofeqID: case dotdotID: case leftarrowID: case lockleID: case lockltID:
                return ParensResult.PARENS;
            default:
                return ParensResult.CAST;
        }
    }

    protected ParensResult analyzeParensHelper2(int lookahead, Token t) {
        if (!(t instanceof JmlToken)) return ParensResult.PARENS;
        JmlTokenKind jtk = ((JmlToken)t).jmlkind;
        switch (jtk) {
            case BSTYPEUC: case BSREAL: case BSBIGINT: case ENDJMLCOMMENT:
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
    public JCExpression term3() {
        List<JCExpression> typeArgs = null;
        int p = pos(); // Position of the keyword
        if (token.kind == IDENTIFIER) {
            String id = token.name().toString();
            if (id.charAt(0) == '\\') {
                IJmlClauseKind kind = Extensions.instance(context).findK(pos(),id,false);
                if (kind == null && !id.equals("\\locset")) { // and we have a leading \
                    jmlerror(p, endPos(), "jml.message", "Unknown backslash identifier: " + id);
                    return jmlF.at(p).Erroneous();
                } else if (kind instanceof IJmlClauseKind.Expression) {
                    if (kind instanceof IJmlClauseKind.Expression) {
                        JCExpression tt = ((IJmlClauseKind.Expression)kind).parse(null, id, kind, this);
                        return primaryTrailers(tt, typeArgs);
                    } else {
                        jmlerror(p, endPos(), "jml.message",
                                "Token " + id + " does not introduce an expression");
                        return jmlF.at(p).Erroneous();
                    }
                }
            }
        }
        // No JML function expects type arguments. If they did we would parse
        // them here (before seeing the JML token). But we can't do that just
        // to check, because super.term3() down below expects to parse them
        // itself. So if someone does write type arguments for a JML function
        // the code will fall into the super.term3() call and the token will not
        // be recognized - no chance for a nice error message.
        if (token.kind == CUSTOM || jmlTokenKind() == JmlTokenKind.PRIMITIVE_TYPE) {
            JCExpression t;
            JmlTokenKind jt = jmlTokenKind();

            if (isJmlTypeToken(jt)) {
                String n = jt.internedName();
                t = to(jmlF.at(p).JmlPrimitiveTypeTree(jt,names.fromString(n)));
                nextToken();
                // Could be just a type value
                if (token.kind == TokenKind.DOT || token.kind == TokenKind.LBRACKET) {
                    t = bracketsSuffix(bracketsOpt(t));
                }
                return t;
            }
            switch (jt) {
                case NONNULL:
                case NULLABLE:
                case READONLY:
                    nextToken();
                    warnNotImplemented(pos(), jt.internedName(),
                            "JmlParser.term3(), as type modifiers");

                    // FIXME - ignoring these type modifiers for now
                    return term3();

                case BSLET:
                    nextToken();
                    return parseLet(p);
                    

                default:
                {
                    String id = jt.internedName();
                    IJmlClauseKind kind = Extensions.instance(context).findK(pos(),id,false);
                    if (kind != null) {
                        if (kind instanceof IJmlClauseKind.Expression) {
                            JCExpression tt = ((IJmlClauseKind.Expression)kind).parse(null, id, kind, this);
                            return primaryTrailers(tt, typeArgs);
                        } else {
                            jmlerror(p, endPos(), "jml.message",
                                    "Token " + id + " does not introduce an expression");
                            return jmlF.at(p).Erroneous();
                        }
                    } else {
                        ExpressionExtension ne = (ExpressionExtension)Extensions.instance(context).findE(pos(),id,false);
                        if (ne == null) {
                            jmlerror(p, endPos(), "jml.bad.type.expression",
                                    "( token " + jt.internedName()
                                    + " in JmlParser.term3())");
                            //                        jmlerror(p, endPos(), "jml.no.such.extension",
                            //                                jt.internedName());
                            return jmlF.at(p).Erroneous();
                        } else {
                            return ne.parse(this, typeArgs);
                        }
                    }
                }
            }
        }
        if (S.jml() && token.kind == TokenKind.LBRACE) {
            accept(LBRACE);
            JCExpression jmltype = parseType();
            accept(RBRACE);
            skipThroughEndOfJML();
            JCExpression e = toP(super.term3());
            JCExpression ee = e;
            while (ee instanceof JCParens) ee = ((JCParens)ee).expr;
            if (ee instanceof JmlLambda) {
                ((JmlLambda)ee).jmlType = jmltype;
            } else {
                e = jmlF.TypeCast(jmltype, e);
                //log.warning(jmltype,"jml.message", "Ignoring JML type cast before a non-lambda expression (" + ee.getClass().toString() + ")");
            }
            return e;
        }
        if (S.jml() && token.kind == LPAREN) {
            // This code is copied from super.term3 in order to 
            // parse tuples
            int pos = token.pos;
            if ((mode & EXPR) != 0) {
                ParensResult pres = analyzeParens();
                if (pres == ParensResult.PARENS) {
                    accept(LPAREN);
                    mode = EXPR;
                    java.util.List<JCExpression> tuple = new java.util.LinkedList<>();
                    JCExpression t = termRest(term1Rest(term2Rest(term3(), TreeInfo.orPrec)));
                    tuple.add(t);
                    while (token.kind == COMMA) {
                        accept(COMMA);
                        t = termRest(term1Rest(term2Rest(term3(), TreeInfo.orPrec)));
                        tuple.add(t);
                    }
                    accept(RPAREN);
                    if (tuple.size() == 1) {
                        t = toP(F.at(pos).Parens(t));
                    } else {
                        t = toP(jmlF.at(pos).JmlTuple(tuple));
                    }
                    return primaryTrailers(t, null);
                }
            }
        }
        JCExpression eee = toP(super.term3());
        return eee;
    }

    public JCExpression primarySuffix(JCExpression t, List<JCExpression> typeArgs) {
        if (S.jml() && token.kind == MONKEYS_AT) {
            accept(MONKEYS_AT);
            int pp = pos();
            Name label = ident();
            JCIdent id = this.maker().at(pp).Ident(label);
            JmlMethodInvocation tt = toP(this.maker().at(t).JmlMethodInvocation(oldKind, List.<JCExpression>of(t,id)));
            return tt;
        }
        JCExpression e = super.primarySuffix(t,typeArgs);
        return e;
    }

    public JCExpression trailingAt(JCExpression t, int p) {
        if (S.jml() && token.kind == MONKEYS_AT) {
            accept(MONKEYS_AT);
            int pp = pos();
            Name label = ident();
            JCIdent id = this.maker().at(pp).Ident(label);
            JmlMethodInvocation tt = toP(this.maker().at(t).JmlMethodInvocation(oldKind, List.<JCExpression>of(t,id)));
            return tt;
        }
        return t;
    }


    
    protected boolean inCreator = false;

//    public JCExpression parseQuantifiedExpr(int pos, JmlTokenKind jt) {
//        JCModifiers mods = modifiersOpt();
//        JCExpression t = parseType();
//        if (t.getTag() == JCTree.Tag.ERRONEOUS) return t;
//        if (mods.pos == -1) {
//            mods.pos = t.pos; // set the beginning of the modifiers
//            storeEnd(mods,t.pos);
//        }
//                                              // modifiers
//        // to the beginning of the type, if there
//        // are no modifiers
//        ListBuffer<JCVariableDecl> decls = new ListBuffer<JCVariableDecl>();
//        int idpos = pos();
//        Name id = ident(); // FIXME JML allows dimensions after the ident
//        decls.append(toP(jmlF.at(idpos).VarDef(mods, id, t, null)));
//        while (token.kind == COMMA) {
//            nextToken();
//            idpos = pos();
//            id = ident(); // FIXME JML allows dimensions after the ident
//            decls.append(toP(jmlF.at(idpos).VarDef(mods, id, t, null)));
//        }
//        if (token.kind != SEMI) {
//            jmlerror(pos(), endPos(), "jml.expected.semicolon.quantified");
//            int p = pos();
//            skipThroughRightParen();
//            return toP(jmlF.at(p).Erroneous());
//        }
//        nextToken();
//        JCExpression range = null;
//        JCExpression pred = null;
//        if (token.kind == SEMI) {
//            // type id ; ; predicate
//            // two consecutive semicolons is allowed, and means the
//            // range is null - continue
//            nextToken();
//            pred = parseExpression();
//        } else {
//            range = parseExpression();
//            if (token.kind == SEMI) {
//                // type id ; range ; predicate
//                nextToken();
//                pred = parseExpression();
//            } else if (token.kind == RPAREN || token.kind == COLON) {
//                // type id ; predicate
//                pred = range;
//                range = null;
//            } else {
//                jmlerror(pos(), endPos(),
//                        "jml.expected.semicolon.quantified");
//                int p = pos();
//                skipThroughRightParen();
//                return toP(jmlF.at(p).Erroneous());
//            }
//        }
//        List<JCExpression> triggers = null;
//        if (token.kind == COLON) {
//            accept(COLON);
//            // triggers
//            if (token.kind != RPAREN) {
//                triggers = parseExpressionList();
//            }
//        }
//        JmlQuantifiedExpr q = toP(jmlF.at(pos).JmlQuantifiedExpr(jt, decls.toList(),
//                range, pred));
//        q.triggers = triggers;
//        return q;
//    }

    // MAINTENANCE ISSUE:
    // This is a copy from JavacParser, so we can add in parseSetComprehension
    JCExpression creator(int newpos, List<JCExpression> typeArgs) {
    	List<JCAnnotation> newAnnotations = typeAnnotationsOpt();
    	
        switch ((TokenKind)token.kind) {
            case BYTE:
            case SHORT:
            case CHAR:
            case INT:
            case LONG:
            case FLOAT:
            case DOUBLE:
            case BOOLEAN:
                if (typeArgs == null) {
                	if (newAnnotations.isEmpty()) {
                		return arrayCreatorRest(newpos, basicType());
                	} else {
                		return arrayCreatorRest(newpos, toP(F.at(newAnnotations.head.pos).AnnotatedType(newAnnotations, basicType())));
                	}
                }
                break;
            default:
        }
        JCExpression t = qualident(true);
        int oldmode = mode;
        mode = TYPE;
        boolean diamondFound = false;
        int lastTypeargsPos = -1;
        if (token.kind == LT) {
            checkGenerics();
            lastTypeargsPos = token.pos;
            t = typeArguments(t,true);
            diamondFound = (mode & DIAMOND) != 0;
        }
        while (token.kind == DOT) {
        	if (diamondFound) {
        		// cannot select after diamond
        		illegal();
        	}
            int pos = token.pos;
            nextToken();
            List<JCAnnotation> tyannos = typeAnnotationsOpt();
            t = toP(F.at(pos).Select(t, ident()));
            
            if (tyannos != null && tyannos.nonEmpty()) {
            	t = toP(F.at(tyannos.head.pos).AnnotatedType(tyannos, t));
            }
            
            if (token.kind == LT) {
                checkGenerics();
                lastTypeargsPos = token.pos;
                t = typeArguments(t,true);
                diamondFound = (mode & DIAMOND) != 0;
            }
        }
        mode = oldmode;
        if (token.kind == LBRACKET || token.kind == MONKEYS_AT) {
            // handle type annotations for non primitive arrays
            if (newAnnotations.nonEmpty()) {
            	t = insertAnnotationsToMostInner(t, newAnnotations, false);
            }
            
            JCExpression e = arrayCreatorRest(newpos, t);
            if (diamondFound) {
            	reportSyntaxError(lastTypeargsPos, "cannot.create.array.with.diamond");
            	return toP(F.at(newpos).Erroneous(List.of(e)));
            }
            if (typeArgs != null) {
                int pos = newpos;
                if (!typeArgs.isEmpty() && typeArgs.head.pos != Position.NOPOS) {
                    // note: this should always happen but we should
                    // not rely on this as the parser is continuously
                    // modified to improve error recovery.
                    pos = typeArgs.head.pos;
                }
                setErrorEndPos(S.prevToken().endPos);
                JCErroneous err = F.at(newpos).Erroneous(typeArgs.prepend(e));
                reportSyntaxError(err, "cannot.create.array.with.type.arguments");
                return toP(err);
            }
            return e;
        } else if (token.kind == LPAREN) {
          boolean prev = inLocalOrAnonClass;
          inLocalOrAnonClass = true;
          try {
            JCNewClass newClass = classCreatorRest(newpos, null, typeArgs, t);
            if (newClass.def != null) {
            	assert newClass.def.mods.annotations.isEmpty();
            	if (newAnnotations.nonEmpty()) {
            		newClass.def.mods.pos = earlier(newClass.def.mods.pos, newAnnotations.head.pos);
            		newClass.def.mods.annotations = newAnnotations;
            	}
            } else {
            	// handle type annotations for instantiations
            	if (newAnnotations.nonEmpty()) {
            		t = insertAnnotationsToMostInner(t, newAnnotations, false);
            		newClass.clazz = t;
            	}
            }
            return newClass;
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
    
//    protected JCExpression moreCreator(TokenKind token, int newpos, JCExpression t, List<JCExpression> typeArgs) {
//    	if (token.kind == LBRACE) {
//    		return parseSetComprehension(t);
//    	}
//    }
    
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
//    protected JCExpression parseLblExpr(int pos, JmlTokenKind jmlToken) {
//        // The JML token is already scanned
//        // pos is the position of the \lbl token
//        int labelPos = pos();
//        if (token.kind == TokenKind.LPAREN) {
//            if (JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
//                log.warning(pos,"jml.not.strict","functional form of lbl expression");
//            }
//            nextToken();
//            List<JCExpression> args = parseExpressionList();
//            if (token.kind != TokenKind.RPAREN) {
//                log.error(pos(),"jml.message", "Expected a comma or right parenthesis here");
//            } else if (args.length() != 2) {
//                log.error(labelPos, "jml.message", "Expected two arguments to a lbl experession");
//            } else if (!(args.get(0) instanceof JCIdent)) {
//                log.error(args.get(0).pos, "jml.message", "The first argument of a lbl expression must be an identifier");
//            } else {
//                nextToken(); // skip the RPAREN
//                Name id = ((JCIdent)args.get(0)).name;
//                return toP(jmlF.at(pos).JmlLblExpression(args.get(0).pos,jmlToken, id, args.get(1)));
//            }
//            return toP(jmlF.at(labelPos).Erroneous());
//        } else {
//            Name n = ident();
//            JCExpression e = parseExpression();
//            if (jmlToken == JmlTokenKind.BSLBLANY && JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
//                log.warning(pos,"jml.not.strict","\\lbl");
//            }
//            return toP(jmlF.at(pos).JmlLblExpression(labelPos,jmlToken, n, e));
//        }
//        }
    
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
    public ListBuffer<JmlGroupName> parseGroupNameList() {
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
        T list = super.variableDeclarators(mods,type,vdefs);
        if (replacementType != null) {
            for (Object decl: list) insertReplacementType(decl,replacementType);
            replacementType = null;
        }
        return list;
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
            return jmlPrecedence((JmlTokenKind)token);
        }
        return precFactor*super.prec(token);
    }
    
    public static final int precFactor = 100;
    
    public static int jmlPrecedence(JmlTokenKind tkind) {
        switch (tkind) {
            // FIXME - check all these precedences
            case EQUIVALENCE: case INEQUIVALENCE:
                return -2; // TreeInfo.orPrec;  // Between conditional and or
            case IMPLIES: case REVERSE_IMPLIES:
                return -2; // TreeInfo.orPrec;  // FBetween conditional and or
            case SUBTYPE_OF: case JSUBTYPE_OF: case SUBTYPE_OF_EQ: case JSUBTYPE_OF_EQ: case LOCK_LT: case LOCK_LE:
                return precFactor*TreeInfo.ordPrec;
            case WF_LT: case WF_LE:
                return precFactor*TreeInfo.ordPrec;
            case DOT_DOT: case ENDJMLCOMMENT:
                return -1000;
            default:
                return 1000;
        }
    }
    
    public static int jmlPrecedence(IJmlClauseKind tkind) {
        switch (tkind.name()) {
            // FIXME - check all these precedences
            case equivalenceID: case inequivalenceID:
                return -2; // TreeInfo.orPrec;  // Between conditional and or
            case impliesID: case reverseimpliesID:
                return -2; // TreeInfo.orPrec;  // FBetween conditional and or
            case subtypeofID: case jsubtypeofID: case subtypeofeqID: case jsubtypeofeqID: case lockltID: case lockleID:
                return precFactor*TreeInfo.ordPrec;
            case wfltID: case wfleID:
                return precFactor*TreeInfo.ordPrec;
            case dotdotID: case endjmlcommentID:
                return -1000;
            default:
                return 1000;
        }
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
        while (prec(S.token().ikind) >= precFactor*minprec) { // FIXME - lookahead token - presumes scanner is just one token ahead
            opStack[top] = topOp;
            top++;
            topOp = S.token();
            JmlTokenKind topOpJmlToken = jmlTokenKind();
            IJmlClauseKind topOpKind = jmlTokenClauseKind();
            nextToken(); // S.jmlToken() changes
            odStack[top] = (topOp.kind == INSTANCEOF) ? parseType() : term3();
            // odStack[top] is the next argument; token is the operator after that, as in [topOp] arg [token]
            // if the precedence of [topOp] is lower than the precedence of [token] we have to read more before constructing expressions
            int p;
            while (top > 0 && (p=prec(topOp.ikind)) >= prec(token.ikind)) {
                if (topOp.kind == CUSTOM) { // <:
                    JCExpression e = jmlF.at(topOp.pos).JmlBinary(topOpKind, odStack[top - 1],
                            odStack[top]);
                    storeEnd(e, getEndPos(odStack[top]));
                    odStack[top - 1] = e;
                } else {
                    odStack[top - 1] = makeOp(topOp.pos, topOp.kind, odStack[top - 1],
                        odStack[top]);
                }
                top--;
                topOp = opStack[top];
                if (p == precFactor*TreeInfo.ordPrec && prec(token.ikind) < precFactor*TreeInfo.ordPrec) {
                    odStack[top] = chain(odStack[top]);
                }
            }
        }
        odStack[top] = chain(odStack[top]);
        
        Assert.check(top == 0);
        t = odStack[0];

        if (t.hasTag(JCTree.Tag.PLUS)) {
            t = foldStrings(t);
// FIXME: The following code is present in JavacParser.term2Rest. However, it turns noinn-string
// string expressions into string expressions. Can't be correct.
//            if (t != null) {
//                t = toP(F.at(startPos).Literal(TypeTag.CLASS, t.toString()));
//            }
        }

        odStackSupply.add(odStack);
        opStackSupply.add(opStack);
        if (bad) return tt;
        return t;
    }
    
    public JCExpression chain(JCExpression e) {
        JCExpression fe = e;
        if (!(fe instanceof JCBinary)) return fe;
        JCBinary be = (JCBinary)e;
        if (be.opcode == JCTree.Tag.LT || be.opcode == JCTree.Tag.LE) {
            ListBuffer<JCBinary> args = new ListBuffer<JCBinary>();
            while (true) {
                args.prepend(be);
                fe = be.lhs;
                if (!(fe instanceof JCBinary)) break;
                be = (JCBinary)fe;
                if (!(be.opcode == JCTree.Tag.LT || be.opcode == JCTree.Tag.LE)) {
                    if (be.opcode == JCTree.Tag.GT || be.opcode == JCTree.Tag.GE) {
                        jmlwarning(be.pos,"jml.message","Cannot chain comparisons that are in different directions");
                    } else {
                        break;
                    }
                }
                args.first().lhs = be.rhs;
            }
            if (args.size() == 1) return e;
            e = jmlF.at(e.pos).JmlChained(args.toList());
            return e;
        } else if (be.opcode == JCTree.Tag.GT || be.opcode == JCTree.Tag.GE) {
            ListBuffer<JCBinary> args = new ListBuffer<JCBinary>();
            while (true) {
                args.prepend(be);
                fe = be.lhs;
                if (!(fe instanceof JCBinary)) break;
                be = (JCBinary)fe;
                if (!(be.opcode == JCTree.Tag.GT || be.opcode == JCTree.Tag.GE)) {
                    if (be.opcode == JCTree.Tag.LT || be.opcode == JCTree.Tag.LE) {
                        jmlwarning(be.pos,"jml.message","Cannot chain comparisons that are in different directions");
                    } else {
                        break;
                    }
                }
                args.first().lhs = be.rhs;
            }
            if (args.size() == 1) return e;
            e = jmlF.at(e.pos).JmlChained(args.toList());
            return e;
        } else {
            return e;
        }
    }

    /**
     * Skips up to and including a semicolon, though not including any EOF or
     * ENDJMLCOMMENT
     */
    public void skipThroughSemi() {
        while (token.kind != TokenKind.SEMI && token.kind != TokenKind.EOF
                && jmlTokenKind() != JmlTokenKind.ENDJMLCOMMENT)
            nextToken();
        if (token.kind == TokenKind.SEMI) nextToken();
    }

    /** Skips up to but not including a semicolon or EOF or ENDJMLCOMMENT */
    public void skipToSemi() {
        while (token.kind != SEMI && token.kind != EOF
                && jmlTokenKind() != JmlTokenKind.ENDJMLCOMMENT)
            nextToken();
    }

    /**
     * Skips up to but not including a semicolon or comma or EOF or
     * ENDJMLCOMMENT
     */
    public void skipToCommaOrSemi() {
        while (token.kind != SEMI && token.kind != COMMA
                && token.kind != EOF
                && jmlTokenKind() != JmlTokenKind.ENDJMLCOMMENT)
            nextToken();
    }

    /**
     * Skips up to but not including a right-parenthesis or comma or EOF or
     * ENDJMLCOMMENT
     */
    public void skipToCommaOrParenOrSemi() {
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

    public void skipThroughEndOfJML() {
        while (token.ikind != ENDJMLCOMMENT && token.kind != EOF)
            nextToken();
        S.setJmlKeyword(false);
        S.setJml(false);
        inJmlDeclaration = false;
        if (token.kind != EOF) nextToken();
    }

    public void acceptEndOfJMLOptional() {
        if (token.ikind == ENDJMLCOMMENT) {
            S.setJml(false);
            inJmlDeclaration = false;
            nextToken();
        }
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

    /** Creates a warning message for which the source is a single character */
    public void jmlwarning(int pos, String key, Object... args) {
        log.warning(new JmlTokenizer.DiagnosticPositionSE(pos, pos), key, args);
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
     * Creates a warning message for which the source is a range of characters,
     * from begin up to and not including end; the identified line is that of
     * the begin position.
     */
    public void jmlwarning(int begin, int end, String key, Object... args) {
        log.warning(new JmlTokenizer.DiagnosticPositionSE(begin, end - 1), key,
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
    
    /**
     * Creates a warning message for which the source is a range of characters,
     * from begin up to and not including end; it also specifies a preferred
     * location to highlight if the output format can only identify a single
     * location; the preferred location is also the line that is identified.
     */
    public void jmlwarning(int begin, int preferred, int end, String key,
            Object... args) {
        log.warning(
                new JmlTokenizer.DiagnosticPositionSE(begin, preferred, end - 1),
                key, args);// TODO - not unicode friendly
    }
    
    // Just to make the visibility public
    public List<JCTypeParameter> typeParametersOpt() {
        return super.typeParametersOpt();
    }
    


    // FIXME - check the use of Token.CUSTOM vs. null
    // FIXME - review the remaining uses of log.error vs. jmlerror
    // FIXME - refactor to better match the grammar as a top-down parser
    // FIXME - refactor for extension
    // FIXME - need to sort out the various modes - isJml isJmlDeclaration isLocalOrAnonClass...
}
