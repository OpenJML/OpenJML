/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.parser;

import static com.sun.tools.javac.parser.Tokens.TokenKind.*;
import static org.jmlspecs.openjml.ext.MethodSimpleClauseExtensions.*;
import static org.jmlspecs.openjml.JmlTokenKind.*;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.jdt.annotation.Nullable;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.IJmlClauseKind.MethodSpecClauseKind;
import org.jmlspecs.openjml.IJmlClauseKind.ModifierKind;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.ext.AssignableClauseExtension;
import org.jmlspecs.openjml.ext.DatatypeExt.JmlDatatypeDecl;
import org.jmlspecs.openjml.ext.EndStatement;
import org.jmlspecs.openjml.ext.ExpressionExtension;
import org.jmlspecs.openjml.ext.Operators;
import org.jmlspecs.openjml.ext.QuantifiedExpressions;
import org.jmlspecs.openjml.ext.SingletonExpressions;

import static org.jmlspecs.openjml.ext.ReachableStatement.*;
import org.jmlspecs.openjml.ext.FunctionLikeExpressions;
import org.jmlspecs.openjml.ext.MatchExt;
import org.jmlspecs.openjml.ext.Modifiers;

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
    
    public boolean isJmlModifier() {
        return token.kind == IDENTIFIER && Extensions.findKeyword(token.name()) instanceof ModifierKind;
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
                    IJmlClauseKind cl = Extensions.findKeyword(token);
                    if (cl instanceof IJmlClauseKind.ClassLikeKind) {
                        JmlDatatypeDecl stat = (JmlDatatypeDecl)cl.parse(mods,token.name().toString(),cl,this);
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
    
    // TODO: THese should be moved to JmlAssertionAdder, so that
    // they work for binary Enums aas well.
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
            JCAnnotation a = utils.modToAnnotationAST(Modifiers.MODEL, cd.pos, cd.pos);  // FIXME -is position correct?
            vd.mods.annotations =  vd.mods.annotations.append(a);
            // declare _JMLvalues as model field
            newdefs.add(vd);
            JCExpression ex = jmlF.Binary(Tag.NE, jmlF.Ident(vd.name), F.Literal(TypeTag.BOT,null));
            // _JMLvalues is not null
            JmlTypeClauseExpr axiom = jmlF.JmlTypeClauseExpr(jmlF.Modifiers(0), axiomID,axiomClause,ex);
            newdefs.add(axiom); 
            ex = jmlF.JmlMethodInvocation(distinctKind,args.toList());
            //((JmlMethodInvocation)ex).kind = FunctionLikeExpressions.distinctKind;
            // The enum constants are all distinct and distinct from NULL.
            //axiom = jmlF.JmlTypeClauseExpr(jmlF.Modifiers(0),axiomID,axiomClause,ex);
            //newdefs.add(axiom);
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
    
    @Override
    List<JCTree> classOrInterfaceBody(Name className, boolean isInterface) {
        JmlMethodSpecs savedMethodSpecs = currentMethodSpecs;
        currentMethodSpecs = null;
        try {
            return super.classOrInterfaceBody(className, isInterface);
        } finally {
            currentMethodSpecs = savedMethodSpecs;
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
        //return collectLoopSpecs(stats);
        return stats;
    }
    
    /** Attach loop specifications to their parent loop statement */
    public List<JCStatement> collectLoopSpecs(List<JCStatement> stats) {
        ListBuffer<JCStatement> newstats = new ListBuffer<>();
        ListBuffer<JmlStatementLoop> loopspecs = new ListBuffer<>();
        JmlStatementExpr split = null;
        JCLabeledStatement labeled = null;
        for (JCStatement s: stats) {
            String sss = s.toString();
            if (s instanceof JmlStatementLoop) {
                loopspecs.add((JmlStatementLoop)s);
                continue;
            } else if (s instanceof JCLabeledStatement && ((JCLabeledStatement)s).body instanceof JmlStatementLoop) {
                labeled = (JCLabeledStatement)s;
                loopspecs.add((JmlStatementLoop)((JCLabeledStatement)s).body);
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
                JmlStatementLoop sloop = jmlF.at(sa.pos).JmlStatementLoopModifies(StatementLocationsExtension.loopwritesStatement, sa.list);
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
                    if (labeled != null) {
                        labeled.body = s;
                        s = labeled;
                    }
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
    public List<JCStatement> blockStatement() {
        while (true) {
            // If we are in a JML comment and this first token is an identifier
            // registered as marking a JML statement or statement annotation,
            // then we proceed to parse it as a (JML) statement
            String id = null;
            IJmlClauseKind anyext = null;
            if (S.jml() && token.kind == TokenKind.IDENTIFIER) {
                id = token.name().toString();
                anyext = Extensions.allKinds.get(id);
            }
            if (anyext != null) {
                IJmlClauseKind ext = Extensions.findSM(id);
                if (ext != null) {
                    JCStatement s;
                    if (ext instanceof IJmlClauseKind.MethodClauseKind
                            || ext == EndStatement.refiningClause) {
                        s = (JCStatement)EndStatement.refiningClause.parse(null, id, ext, this);
                        //s = parseRefining(pos(), ext);
                    } else {
                        s = (JCStatement)ext.parse(null, id, ext, this);
                        while (jmlTokenClauseKind() == Operators.endjmlcommentKind) nextToken();
                        if (s instanceof JmlStatementLoop) {
                            s = parseLoopWithSpecs((JmlStatementLoop)s, true);
                        } else if (id.equals(EndStatement.beginID)) {
                            log.error(s, "jml.message", "Improperly nested spec-end pair");
                        } else if (id.equals(EndStatement.endID)) {
                          log.error(s, "jml.message", "Improperly nested spec-end pair");
                        }
                    }
                    if (s == null) return List.<JCStatement>nil();
                    return List.<JCStatement>of(s);
                }
                IJmlClauseKind cl = Extensions.findKeyword(token);
                if (cl instanceof IJmlClauseKind.ClassLikeKind) {
                    return List.<JCStatement>of((JmlDatatypeDecl)cl.parse(null, cl.keyword, cl, this));
                }
                // If the identifier is not the beginning of a JML statement, then
                // it might be the type that begins a declaration (or it could be a
                // misspelled JML key word)
            }
            if (!(token instanceof JmlToken) && anyext == null) {
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
            if (anyext instanceof ModifierKind) {
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
            } else if (((JmlToken)token).jmlkind == ENDJMLCOMMENT) {
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

    public JCStatement parseLoopWithSpecs(JmlStatementLoop firstSpec) {
        return parseLoopWithSpecs(firstSpec, false);
    }
    public JCStatement parseLoopWithSpecs(JmlStatementLoop firstSpec, boolean block) {
        JCStatement stt = block ? blockStatement().head : parseStatement();
        if (stt instanceof IJmlLoop) {
            IJmlLoop loop = (IJmlLoop)stt;
            List<JmlStatementLoop> specs = loop.loopSpecs();
            if (specs == null) {
                specs = List.<JmlStatementLoop>of(firstSpec);
            } else {
                specs = specs.prepend(firstSpec);
            }
            loop.setLoopSpecs(specs);
        } else {
            log.error(firstSpec, "jml.message", "Loop specifications must immediately precede a loop statement");
        }
        return stt;
    }
    
    /** Overridden to parse JML statements */
    @Override  // TODO - needs REVIEW
    public JCStatement parseStatement() {
        int pos = pos();
        JCStatement st;
        String id = null;
        if (S.jml()) {
            if (token.kind == TokenKind.IDENTIFIER) {
                id = token.name().toString();
                IJmlClauseKind clauseType = Extensions.findSM(id);
                if (clauseType instanceof IJmlClauseKind.Statement) {
                    st = (JmlAbstractStatement)clauseType.parse(null,id,clauseType,this);
                    while (jmlTokenClauseKind() == Operators.endjmlcommentKind) nextToken();
                    if (st instanceof JmlStatementLoop) {
                        st = parseLoopWithSpecs((JmlStatementLoop)st);
                    }
                    return st;
                } else if (clauseType instanceof IJmlClauseKind.MethodClauseKind) {
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
        JCStatement stt = super.parseStatement();
        return stt;
    }
    
    JCStatement parseRefining(int pos, IJmlClauseKind jt) {
        JmlStatementSpec ste;
        ListBuffer<JCIdent> exports = new ListBuffer<>();
        if (jt == EndStatement.refiningClause) {
            nextToken();
            IJmlClauseKind ext = methodSpecKeywordS(0);
            if (ext == alsoClause) { // jmlTokenKind() == JmlTokenKind.ALSO) {
                jmlerror(pos(), endPos(), "jml.invalid.also");
                nextToken();
            }
            if (ext == elseClause) {
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
        } else if (jt == EndStatement.beginClause) {
            log.error(pos, "jml.message", "Improperly nested spec-end pair");
        } else if (jt == EndStatement.endClause) {
            log.error(pos, "jml.message", "Improperly nested spec-end pair");
        } else {
            log.warning(pos(),"jml.refining.required");
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
        } else if (stat.head instanceof JmlAbstractStatement && stat.head.toString() == EndStatement.beginID) {
            log.error(stat.head, "jml.message", "Statement specs may not precede a JML statement clause");
            return stat.head;
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
        } else if (stat.head instanceof JmlStatement && ((JmlStatement)stat.head).clauseType == EndStatement.beginClause) {
            log.error(ste, "jml.message", "Improperly nested spec-end pair");
        } else if (stat.isEmpty()) {
            log.error(ste, "jml.message", "Statement specs found at the end of a block (or before an erroneous statement)");
        } else {
            stats.addAll(stat);
        }
        //ste.statements = collectLoopSpecs(stats.toList());
        ste.statements = (stats.toList());
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
        //List<JCStatement> statslist = collectLoopSpecs(stats.toList());
        List<JCStatement> statslist = stats.toList();
        if (statslist.size() > 1) return F.at(statslist.head.pos).Block(0, statslist);
        return statslist.head;
    }

    // TODO - generalize this and move it out of JmlParser
    /** Returns true if the token is a JML type token */
    public boolean isJmlTypeToken(JmlTokenKind t) {
        return t == JmlTokenKind.BSTYPEUC || t == JmlTokenKind.BSBIGINT
                || t == JmlTokenKind.BSREAL || t == JmlTokenKind.PRIMITIVE_TYPE;
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
            if (possibleKeyword.name().toString().equals("code")) return true;
            IJmlClauseKind ext = Extensions.findSM(possibleKeyword.name().toString());
            return ext instanceof IJmlClauseKind.MethodClauseKind;
        }
        return false;
    }

    /** Returns true if the argument is a possible initial token
     * of a type specification, after any modifiers.
     */
    protected boolean startOfTypeSpec(Token possibleKeyword) {
        if (!(S.jml())) return false;
        if (possibleKeyword.kind == TokenKind.IDENTIFIER) {
            return Extensions.findTM(possibleKeyword.name().toString()) instanceof IJmlClauseKind.TypeClause;
        }
        return false;
    }
    
    /** Returns non-null if the token introduces a new JML kind of class
     * (e.g. inductive datatype).
     */
    public IJmlClauseKind.ClassLikeKind isJmlClassLike(Token token) {
        IJmlClauseKind k = Extensions.findKeyword(token);
        if (k instanceof IJmlClauseKind.ClassLikeKind) return (IJmlClauseKind.ClassLikeKind)k;
        return null;
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
            JCModifiers mods = modifiersOpt(); // Gets anything that is in
                                               // pushBackModifiers
            int pos = pos();
            JmlTokenKind jt = jmlTokenKind();
            if (jt != null && !isJmlTypeToken(jt) && currentMethodSpecs != null && !startOfMethodSpecs(token)) {
                log.error(currentMethodSpecs.pos, "jml.message", "Misplaced method specifications preceding a " + jt.internedName() + " clause (ignored)");
                currentMethodSpecs = null;
            }
            IJmlClauseKind ct = null;
            String id = null;
            if (S.jml() && token.kind == TokenKind.IDENTIFIER) {
                id = token.name().toString();
                ct = Extensions.findTM(id);
            }
            if (ct != null) {
                if (startOfMethodSpecs(token)) {
                    currentMethodSpecs = parseMethodSpecs(mods);
                    continue;
                } else if (startOfTypeSpec(token)) {
                    JCTree tc = parseTypeSpecs(mods);
                    if (tc instanceof JmlTypeClause && currentMethodSpecs != null) {
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
                } else if (utils.findMod(mods,Modifiers.MODEL) == null && utils.findMod(mods,Modifiers.GHOST) == null) {
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
            } else if (S.jml() && id != null && Extensions.findSM(id) != null && !"set".equals(id)) {
                jmlerror(pos(), endPos(),
                        "jml.illegal.token.for.declaration", id);
                skipThroughSemi();
                break;
                
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
                    IJmlClauseKind.ClassLikeKind cl =  null;
                    if ((cl = isJmlClassLike(token)) != null) {
                        t = List.<JCTree>of(cl.parse(mods, cl.keyword, cl, this));
                    } else {
                        t = super.classOrInterfaceBodyDeclaration(
                                className, isInterface);
                        if (isInterface && t.head instanceof JmlMethodDecl) {
                            JmlMethodDecl md = (JmlMethodDecl)t.head;
                            if (utils.findMod(md.mods,Modifiers.MODEL)!= null
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
            } else if (startOfMethodSpecs(token)) {
                currentMethodSpecs = parseMethodSpecs(mods);
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


//    /** Parses an in clause */
//    public JmlTypeClauseIn parseIn(int pos, JCModifiers mods) {
//        if (!isNone(mods))
//            jmlerror(pos, "jml.no.mods.allowed", inClause.name());
//        nextToken(); // skip over the in token
//        ListBuffer<JmlGroupName> list = parseGroupNameList();
//        accept(SEMI);
//        return toP(jmlF.at(pos).JmlTypeClauseIn(list.toList()));
//    }



//    /** Parse a monitors_for clause */
//    public JmlTypeClauseMonitorsFor parseMonitorsFor(JCModifiers mods) {
//        int p = pos();
//        nextToken();
//        List<JCExpression> elist = List.<JCExpression>nil();
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
//                elist = parseExpressionList();
//            }
//        }
//        JCTree.JCIdent id = to(jmlF.at(identPos).Ident(n));
//        if (token.kind != SEMI) {
//            skipThroughSemi();
//        } else {
//            nextToken();
//        }
//        return toP(jmlF.at(p).JmlTypeClauseMonitorsFor(mods, id, elist));
//    }

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
                try {
                    // We need to be in non-JML mode so that we don't interpret 
                    nextToken();
                    replacementType = super.unannotatedType();
                } finally {
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
    
    public IJmlClauseKind methodSpecKeyword(int lastPos) {
        IJmlClauseKind ext = null;
        if (token.kind == TokenKind.IDENTIFIER) ext = Extensions.findTM(token.name().toString());
        return ext;
    }
    
    public IJmlClauseKind methodSpecKeywordS(int lastPos) {
        IJmlClauseKind ext = null;
        if (token.kind == TokenKind.IDENTIFIER) ext = Extensions.findSM(token.name().toString());
        return ext;
    }
    
    public JCTree parseTypeSpecs(JCModifiers mods) {
        String id = token.kind == TokenKind.IDENTIFIER ?  token.name().toString() : jmlTokenKind().internedName();
        IJmlClauseKind ct = Extensions.findTM(id);
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
        IJmlClauseKind ext = methodSpecKeyword(0);
        if (ext == feasibleBehaviorClause) {
            if (!isNone(mods))
                jmlerror(pos(), endPos(), "jml.no.mods.allowed",
                        ext.keyword);
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
            ext = methodSpecKeyword(0);
        }
        if (ext == impliesThatClause) {
            if (!isNone(mods))
                jmlerror(pos(), endPos(), "jml.no.mods.allowed",
                        ext.keyword);
            nextToken();
            mods = modifiersOpt();
            cases = new ListBuffer<JmlSpecificationCase>();
            while ((c = parseSpecificationCase(mods, false)) != null) {
                cases.append(c);
                lastPos = getEndPos(c);
                mods = modifiersOpt();
            }
            if (cases.size() > 0) cases.first().also = ext;
            sp.impliesThatCases = cases.toList();
            ext = methodSpecKeyword(0);
        }
        if (ext == forExampleClause) {
            if (!isNone(mods))
                jmlerror(mods.getStartPosition(),
                        getEndPos(mods),
                        "jml.no.mods.allowed", ext.keyword);
            nextToken();
            mods = modifiersOpt();
            cases = new ListBuffer<JmlSpecificationCase>();
            while ((c = parseSpecificationCase(mods, true)) != null) {
                cases.append(c);
                lastPos = getEndPos(c);
                mods = modifiersOpt();
            }
            if (cases.size() > 0) cases.first().also = ext;
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
        IJmlClauseKind also = null;
        JmlTokenKind ijt = jmlTokenKind();
        IJmlClauseKind ext = methodSpecKeyword(0);
        if (ext == alsoClause || ext == elseClause) { //  || ijt == ALSO || token.ikind == TokenKind.ELSE) {
            if (!isNone(mods)) {
                jmlerror(mods.getStartPosition(), endPos(),
                        "jml.no.mods.allowed", ext.keyword);
                mods = null;
            }
            also = ext;
            nextToken();
            // get any modifiers
            mods = modifiersOpt();
            ext = methodSpecKeyword(0);
        }
        boolean code = false;
        int codePos = 0;
        if (ext == feasibleBehaviorClause) return null; //  || jmlTokenKind() == JmlTokenKind.FEASIBLE_BEHAVIOR) return null;
        if (ext == codeClause) {
            codePos = pos();
            code = true;
            nextToken();
            ext = methodSpecKeywordS(0);
        }

        int pos = pos();
        if (ext == behaviorClause || ext == normalBehaviorClause || ext == exceptionalBehaviorClause
                || (ext == abruptBehaviorClause || inModelProgram))
            //                || jt == JmlTokenKind.BEHAVIOR || jt == JmlTokenKind.NORMAL_BEHAVIOR
            //                || jt == JmlTokenKind.EXCEPTIONAL_BEHAVIOR
            //                || (jt == JmlTokenKind.ABRUPT_BEHAVIOR && inModelProgram)) 
        {
            if (exampleSection) {
                log.warning(pos(), "jml.example.keyword", "must not",
                        ext.keyword);
            }
            nextToken();
        } else if (ext == exampleClause || ext == normalExampleClause || ext == exceptionalExampleClause) {
            //                || jt == JmlTokenKind.EXAMPLE || jt == JmlTokenKind.NORMAL_EXAMPLE
            //                || jt == JmlTokenKind.EXCEPTIONAL_EXAMPLE) {
            if (!exampleSection) {
                log.warning(pos(), "jml.example.keyword", "must",
                        ext.keyword);
            }
            nextToken();
        } else if (ext == modelprogramClause) {
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
            ext = null;
            if (code) log.warning(codePos, "jml.misplaced.code");
            // lightweight
        }

        Name specCaseName = null;
        if (ext != null && token.kind == TokenKind.IDENTIFIER && S.token(1).kind == TokenKind.COLON) {
            // Label for the specification case
            specCaseName = ident(); // Advances token
            nextToken(); // skips over colon
        }

        ListBuffer<JmlMethodClause> clauses = new ListBuffer<JmlMethodClause>();
        JmlMethodClause e;
        JCBlock stat = null;
        while (true) {
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
            if (ext != null && JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
                jmlerror(pos, "jml.empty.specification.case");
            }
            if (ext == null && also == null && !code) return null;
        }
        if (ext == null && code) code = false; // Already warned about this
        JmlSpecificationCase j = jmlF.at(pos).JmlSpecificationCase(mods, code,
                ext, also, clauses.toList(), stat);
        j.name = specCaseName;
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
        } while (token.kind == TokenKind.IDENTIFIER && (token.name().toString().equals(alsoID) || token.name().toString().equals(elseID)));
        //} while (jmlTokenKind() == ALSO || token.ikind == TokenKind.ELSE);
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
        
        JmlMethodClause res = null;
        String keyword = null;
        if (token().kind == IDENTIFIER) keyword = token().name().toString();
        if (keyword != null) {
            IJmlClauseKind clauseType = Extensions.findTM(keyword);
            if (clauseType instanceof MethodSpecClauseKind) {
                res = (JmlMethodClause)clauseType.parse(null, keyword, clauseType, this);
            } else if (clauseType instanceof IJmlClauseKind.MethodClauseKind) {
                return null;
            }
        }
        JmlTokenKind jt = jmlTokenKind();
        if (jt != null && res == null)
            switch (jt) {
                case SPEC_GROUP_START:
                    res = getSpecificationGroup();
                    break;

                default:
                    // For any other token we just exit this loop,
                    // WITHOUT HAVING CALLED nextToken()!!!!
                    break;

            }
        if (res != null) res.sourcefile = log.currentSourceFile();
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
    public JCExpression parseArrayRangeExpr(JCExpression t, boolean strictId) {
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
    public JCModifiers modifiersOpt(JCModifiers partial) {
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
        while (token.kind == CUSTOM || isJmlModifier()) {
            int lastPos = token.endPos;
            partial = jmlModifiersOpt(partial);
            storeEnd(partial, lastPos);
            if (token.kind == CUSTOM) break;
            partial = super.modifiersOpt(partial);
        }
        return partial;
    }


    public/* @ nullable */JCAnnotation tokenToAnnotationAST(String annName,
            int position, int endpos) {
        JCExpression t = utils.nametree(position,endpos,annName,this);
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
    public JCModifiers jmlModifiersOpt(JCModifiers partial) {
        ListBuffer<JCAnnotation> annotations = new ListBuffer<JCAnnotation>();
        if (partial != null) annotations.appendList(partial.annotations);
        int pos = Position.NOPOS;
        int last = Position.NOPOS;
        if (partial != null) {
            pos = partial.pos;
        }
        JmlTokenKind j = null;
        while (isJmlModifier() || (j = jmlTokenKind()) != null) {
            if (isJmlModifier()) {
                last = endPos();
                ModifierKind mk = (ModifierKind)Extensions.findKeyword(token.name());
                JCAnnotation a = tokenToAnnotationAST(mk.fullAnnotation, pos(), last);
                if (a != null) {
                    annotations.append(a);
                    if (pos == Position.NOPOS) pos = a.getStartPosition();
                }
                // a is null if no annotation is defined for the modifier;
                // we just silently ignore that situation
                // (this is true at the moment for math annotations, but could
                // also be true for a modifier someone forgot)
                if (!mk.strict && JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
                    log.warning(pos(),"jml.not.strict",mk.keyword);  // FIXME - probably wrong position
                }
            } else if (j == ENDJMLCOMMENT) {
                // skip over
            } else if (tokenIsId(constructorID,fieldID,methodID)) {
                // FIXME - do we want to save this anywhere; check that it
                // matches the declaration; check that it is not used on
                // something other than a declaration?
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
                IJmlClauseKind kind = Extensions.findKeyword(token);
                if (kind == null && !id.equals("\\locset")) { // and we have a leading \
                    jmlerror(p, endPos(), "jml.message", "Unknown backslash identifier: " + id);
                    return jmlF.at(p).Erroneous();
                } else if (kind instanceof IJmlClauseKind.ExpressionKind) {
                    if (kind instanceof IJmlClauseKind.ExpressionKind) {
                        JCExpression tt = ((IJmlClauseKind.ExpressionKind)kind).parse(null, id, kind, this);
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
//                case NON_NULL:
//                case NULLABLE:
//                case READONLY:
//                    nextToken();
//                    warnNotImplemented(pos(), jt.internedName(),
//                            "JmlParser.term3(), as type modifiers");
//
//                    // FIXME - ignoring these type modifiers for now
//                    return term3();

//                case BSLET:
//                    nextToken();
//                    return parseLet(p);
//                    
                case INFORMAL_COMMENT: {
                    // TODO - move to a parser
                    String content = S.chars();
                    nextToken();
                    JmlSingleton tt = toP(jmlF.at(p).JmlSingleton(SingletonExpressions.informalCommentKind));
                    tt.info = content;
                    return tt;
                }
                
                default:
                {
                    IJmlClauseKind kind = Extensions.findKeyword(token);
                    if (kind != null) {
                        if (kind instanceof IJmlClauseKind.ExpressionKind) {
                            JCExpression tt = ((IJmlClauseKind.ExpressionKind)kind).parse(null, token.toString(), kind, this);
                            return primaryTrailers(tt, typeArgs);
                        } else {
                            jmlerror(p, endPos(), "jml.message",
                                    "Token " + token + " does not introduce an expression");
                            return jmlF.at(p).Erroneous();
                        }
                    } else {
                        String id = token instanceof JmlToken ? ((JmlToken)token).jmlkind.internedName() : token.toString();
                        if (id.equals("match")) {
                            return new MatchExt(context).parse(this, typeArgs);
                        } else {
//                        ExpressionExtension ne = (ExpressionExtension)Extensions.instance(context).findE(pos(),id,false);
//                        if (true || ne == null) {
                            jmlerror(p, endPos(), "jml.bad.type.expression",
                                    "( token " + token
                                    + " in JmlParser.term3())");
                            //                        jmlerror(p, endPos(), "jml.no.such.extension",
                            //                                jt.internedName());
                            return jmlF.at(p).Erroneous();
//                        } else {
//                            return ne.parse(this, typeArgs);
//                        }
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


    // MAINTENANCE ISSUE:
    // This is a copy from JavacParser, so we can add in parseSetComprehension
    JCExpression creator(int newpos, List<JCExpression> typeArgs) {
    	List<JCAnnotation> newAnnotations = typeAnnotationsOpt();
    	
        switch (token.kind) {
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
    
    protected boolean inLocalOrAnonClass = false;


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
        return super.variableInitializer();
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
        S.setJml(false); // Shouldn't the scanner set this appropriately?
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
