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
import java.util.function.Function;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.IJmlClauseKind.MethodSpecClauseKind;
import org.jmlspecs.openjml.IJmlClauseKind.ModifierKind;
import org.jmlspecs.openjml.IJmlClauseKind.TypeAnnotationKind;

import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.ext.AssignableClauseExtension;
import org.jmlspecs.openjml.ext.DatatypeExt.JmlDatatypeDecl;
import org.jmlspecs.openjml.ext.Refining;
import org.jmlspecs.openjml.ext.JmlOperatorKind;
import org.jmlspecs.openjml.ext.QuantifiedExpressions;
import org.jmlspecs.openjml.ext.SingletonExpressions;
import static org.jmlspecs.openjml.ext.JmlPrimitiveTypes.*;

import static org.jmlspecs.openjml.ext.ReachableStatement.*;
import org.jmlspecs.openjml.ext.FunctionLikeExpressions;
import org.jmlspecs.openjml.ext.InlinedLoopStatement;
import org.jmlspecs.openjml.ext.JmlPrimitiveTypes;
import org.jmlspecs.openjml.ext.MatchExt;
import org.jmlspecs.openjml.ext.MiscExpressions;
import org.jmlspecs.openjml.ext.Modifiers;

import static org.jmlspecs.openjml.ext.FunctionLikeExpressions.*;
import static org.jmlspecs.openjml.ext.MiscExtensions.*;
import static org.jmlspecs.openjml.ext.StateExpressions.*;
import static org.jmlspecs.openjml.ext.JmlOperatorKind.*;
import org.jmlspecs.openjml.ext.StatementLocationsExtension;

import static org.jmlspecs.openjml.ext.TypeExprClauseExtension.*;
import static org.jmlspecs.openjml.ext.StatementExprExtensions.*;
import static org.jmlspecs.openjml.ext.TypeInClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeMapsClauseExtension.*;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.*;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Source.Feature;
import com.sun.tools.javac.parser.Scanner;
import com.sun.tools.javac.parser.JavacParser.ParensResult;
import com.sun.tools.javac.parser.Tokens.Comment;
import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.parser.Tokens.Comment.CommentStyle;
import com.sun.tools.javac.parser.Tokens.ITokenKind;
import com.sun.tools.javac.resources.CompilerProperties.Errors;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Assert;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Position;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticFlag;
import com.sun.tools.javac.util.JCDiagnostic.Error;

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
    
    public boolean       addOrgJmlspecsLang = true;

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
    protected JmlParser(ParserFactory fac, JmlScanner S, boolean keepDocComments) {
        super(fac, S, keepDocComments, true, true); // true = keepLineMap, keepEndPositions
        if (!(F instanceof JmlTree.Maker)) {
            utils.error("jml.internal",
                    "F expected to be a JmlTree.Maker in JmlParser");
            throw new JmlInternalError(
                    "Expected a JmlTree.Maker for a JmlParser");
        }
        this.S = S;
        this.jmlF = (JmlTree.Maker) F;
    }
    
    public int getStartPos(JCTree tree) {
    	if (tree instanceof IJmlTree) return ((IJmlTree)tree).getStartPosition();
        return TreeInfo.getStartPos(tree);
    }


    /** Beginning position of current token */
    public int pos() {
        return token.pos;
    }

    /** End position of current token */
    public int endPos() {
        return token.endPos;
    }
    
    /** Just to make the value public */
    public AbstractEndPosTable endPosTable() {
    	return endPosTable; 
    }
    
    public boolean isJavaModifier(Token token) {
        switch (token.kind) {
        case PRIVATE     : 
        case PROTECTED   :
        case PUBLIC      :
        case STATIC      : 
        case TRANSIENT   :
        case FINAL       :
        case ABSTRACT    :
        case NATIVE      :
        case VOLATILE    :
        case SYNCHRONIZED:
        case STRICTFP    :
        case DEFAULT:
        	return true;
        case MONKEYS_AT  : 
        	return true; // FIXME - need to skip over a qualident
//        case IDENTIFIER  : {  // FIXME - what to do about this case
//            if (isNonSealedClassStart(false)) {
//                flag = Flags.NON_SEALED;
//                nextToken();
//                nextToken();
//                break;
//            }
//            if (isSealedClassStart(false)) {
//                checkSourceLevel(Feature.SEALED_CLASSES);
//                flag = Flags.SEALED;
//                break;
//            }
//            break loop;
//        }
        default: return false;
        }

    }

    /** Returns true if the current token is a JML modifier, but not a type annotation */
    public boolean isJmlModifier(Token token) {
    	if (token.kind != IDENTIFIER) return false;
    	var m = Extensions.findKeyword(token);
    	//if (m instanceof TypeAnnotationKind) return false;
    	return m instanceof ModifierKind;
    }

    public JmlTokenKind jmlTokenKind() {
        return token.ikind instanceof JmlTokenKind ? (JmlTokenKind)token.ikind : null;
    }


    /** Returns the IJmlClauseKind for the current token, or null if none */
    public IJmlClauseKind jmlTokenClauseKind() {
        return jmlTokenClauseKind(token);
    }

    /** Returns the IJmlClauseKind for the given token, or null if none */
    public IJmlClauseKind jmlTokenClauseKind(Token token) {
        if (token instanceof JmlToken && ((JmlToken)token).jmlclausekind != null) return ((JmlToken)token).jmlclausekind;
        if (token.kind != TokenKind.IDENTIFIER) return null;
        IJmlClauseKind t = Extensions.allKinds.get(token.name().toString());
        if (token instanceof JmlToken) ((JmlToken)token).jmlclausekind = t;
        return t;
    }

    /** Returns true if the token matches any one of the ids */
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
    
    public Token afterMods() {
    	int n = 0;
    	while (true) {
    		var t = S.token(n);
 			// FIXME - it is a problem that for a EOF (a Java token), the 'kind' is not set, and might be a modifier, which leads to an endless loop here
    		if (t.ikind == JmlTokenKind.STARTJMLCOMMENT || t.ikind == JmlTokenKind.ENDJMLCOMMENT || (t.ikind != TokenKind.EOF && isJavaModifier(token)) || isJmlModifier(t)) {
    			n++;
    			continue;
    		}
    		return t;
    	}
    }
    
    protected JCTree checkForJmlDeclaration(boolean checkForImports) {
    	if (S.jml() && checkForImports) {
    		if (afterMods().kind == TokenKind.IMPORT) {
    			var mods = modifiersOpt(null);
    			var t =  importDeclaration(mods);
    			return t;
    		}
    	}
    	return null;
    }


    /**
     * Parses a compilation unit using tokens from the scanner - generally the
     * entry point used to parse a Java/JML file.
     */
    @Override
    public JCTree.JCCompilationUnit parseCompilationUnit() {
    	JCTree.JCCompilationUnit u = null;
    	try {
    		u = super.parseCompilationUnit();
    		storeEnd(u, pos());
    		if (!(u instanceof JmlCompilationUnit)) {
    			utils.error(
    					"jml.internal",
    					"JmlParser.compilationUnit expects to receive objects of type JmlCompilationUnit, but it found a "
    							+ u.getClass()
    							+ " instead, for source "
    							+ u.getSourceFile().toUri().getPath());
    		} else {
    			// JML class-like declarations at all levels of nesting
    			// include a field that holds the top-level
    			// compilation unit in which the declaration sits.
    			// This code sets that field in after the whole tree is parsed.
    			JmlCompilationUnit jmlcu = (JmlCompilationUnit) u;
    			if (addOrgJmlspecsLang) {
    				var p = (JCFieldAccess)utils.nametree(0, 0, "org.jmlspecs.lang.*", this);
        			JmlImport m = jmlF.at(0).Import(p,  false);
        			storeEnd(m, 0);
        			m.isModel = true;
        			if (jmlcu.defs.head instanceof JCPackageDecl) {
        				JCTree t = jmlcu.defs.head;
        				jmlcu.defs = jmlcu.defs.tail.prepend(m).prepend(t);
        			} else {
        				jmlcu.defs = jmlcu.defs.prepend(m);
        			}
    			}
    			setTopLevel(jmlcu,jmlcu.defs);
    		}
    	} catch (Exception e) {
           	var S = getScanner();
           	utils.unexpectedException(e, "Exception during parsing near " + ((JmlTokenizer)S.tokenizer).getCharacters(S.tokenizer.position()-10, S.tokenizer.position()+50));
        }
        return u; // Might be null if an error happens, though prefer a partial tree
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
    public JCTree importDeclaration(JmlModifiers mods) {
        int p = pos();
        int pp = Position.NOPOS;
        boolean modelImport = false;
        for (var t: mods.jmlmods) {
            if (t.jmlclausekind == Modifiers.MODEL) { modelImport = true; break; }
            else utils.error(t.pos, t.endPos, "jml.no.mods.on.import");
        }
        if (!modelImport) for (var t: mods.annotations) {
        	if (t instanceof JmlAnnotation ta) {
                if (ta.kind == Modifiers.MODEL) { modelImport = true; pp = ta.pos; break; }
                else utils.error(ta.pos, endPos(), "jml.no.mods.on.import"); // FIXME endpos
            }
        }
        boolean importIsInJml = S.jml();
        if (!modelImport && importIsInJml) {
            utils.error(p, endPos(), "jml.import.no.model");
            modelImport = true;
        }
        JCTree t = super.importDeclaration();
        if (t != null) {
        	((JmlImport) t).isModel = modelImport;
        	if (modelImport && !importIsInJml) {
        		utils.error(p, t.getEndPosition(endPosTable), "jml.illformed.model.import");
        	}
        }
        acceptEndJML();
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
        ((JmlTree.JmlAnnotation)a).sourcefile = currentSourceFile();
        String s = a.getAnnotationType().toString();
        // FIXME - problem here - if the annotation is not fully qualified, it is possible that
        // the annotation will resolve to a type in a different package than org.jmlspecs.annotation
        // which will mean it erroneously is marked as a JML modifier. But we need to know at least
        // whether it is a MODEL, and maybe a type annotation, in JmlEnter, before attribution
        ((JmlAnnotation)a).kind = Extensions.findModifier(s);
        return a;
    }
    
    public List<JCAnnotation> extractTypeAnnotations(JCModifiers mods) {
        ListBuffer<JCAnnotation> typeAnnotations = new ListBuffer<>();
        ListBuffer<JCAnnotation> otherAnnotations = new ListBuffer<>();
        for (JCAnnotation a: mods.annotations) {
            // FIXME - an true Java annotation (not a synthetic one generated from a modifier) will not have ja.kind set
            // and consequently will not be pushed into the type properly
            if (a instanceof JmlAnnotation ja && ja.kind != null && ja.kind.isTypeAnnotation()) {
                typeAnnotations.add(a);
            } else {
                otherAnnotations.add(a);
            }
        }
        mods.annotations = otherAnnotations.toList();
        return typeAnnotations.toList();
    }

    /** OpenJML overrides in order to parse and insert replacement types for formal parameters */
    @Override
    protected JCVariableDecl formalParameter(boolean lambdaParameter, boolean recordComponent) {
        replacementType = null;
        int n = Log.instance(context).nerrors;
        JmlVariableDecl param = (JmlVariableDecl)super.formalParameter(lambdaParameter, recordComponent);
        boolean print = param.name.toString().equals("stackTrace");
        insertReplacementType(param,replacementType);
        param.vartype = normalizeAnnotations((JmlModifiers)param.mods, param.vartype);
        var typeAnnotations = extractTypeAnnotations(param.mods);
        param.vartype = insertAnnotationsToMostInner(param.vartype, typeAnnotations, false);
        if (n != Log.instance(context).nerrors) {
        	skipToCommaOrParenOrSemi();
        	return param;
        }
        replacementType = null;
        return param;
    }
    
    @Override
    protected JCTree methodDeclaratorRest(int pos,
            JCModifiers mods,
            JCExpression type,
            Name name,
            List<JCTypeParameter> typarams,
            boolean isInterface, boolean isVoid,
            boolean isRecord,
            Comment dc) {
        type = normalizeAnnotations(((JmlModifiers)mods), type);
        return super.methodDeclaratorRest(pos,  mods,  type,  name, typarams, isInterface, isVoid, isRecord, dc);
    }

    // FIXME - needs to be called in casts, generic type arguments, 
    // new object, new array, nested types?
    
    protected JCExpression normalizeAnnotations(JCModifiers modifiers, JCExpression vartype) {
        if (!(modifiers instanceof JmlModifiers mods)) return vartype;
        for (JmlToken mod: mods.jmlmods) {
            vartype = normalizeAnnotation(mod, vartype, mods);
        }
        return vartype;
    }
    
    protected JCExpression normalizeAnnotation(JmlToken mod, JCExpression vartype, JmlModifiers mods) {
        var ck = (ModifierKind)mod.jmlclausekind;
        x: if (ck.isTypeAnnotation()) {
            JmlAnnotation a = JmlTreeUtils.instance(context).makeAnnotation(mod, this);

            if (a == null) break x;

            // FIXME: methodDeclarationRest and variableDeclaratorRest can be called more than once with the same modifiers
            // resulting in duplicate annotations from the same modifier
            if (mods != null) for (var aa: mods.annotations) {
                if (aa instanceof JmlAnnotation jaa && jaa.kind == ck && jaa.pos == mod.pos) {
                    //utils.warning(mod.pos, mod.endPos, "jml.message", "duplicating a modifier as an annotation: " + ck); Utils.dumpStack();
                    break x;
                }
            }
            {
                if (vartype == null) {
                    mods.annotations = mods.annotations.append(a);
                } else if (vartype instanceof JCAnnotatedType anntype) {
                    vartype = normalizeAnnotation(mod, anntype.underlyingType, null);
                    if (vartype instanceof JCAnnotatedType avt) {
                        avt.annotations = anntype.annotations.appendList(avt.annotations);
                    }
                } else if (vartype instanceof JCIdent) {
                    vartype = jmlF.at(vartype.pos).AnnotatedType(List.<JCAnnotation>of(a), vartype);
                } else if (vartype instanceof JCFieldAccess fa) {
                    vartype = jmlF.at(vartype.pos).AnnotatedType(List.<JCAnnotation>of(a), vartype);
                } else if (vartype instanceof JCArrayTypeTree fa) {
                    fa.elemtype = normalizeAnnotation(mod, fa.elemtype, mods);
                } else if (vartype instanceof JCTypeApply fa) {
                    fa.clazz = normalizeAnnotation(mod, fa.clazz, null);
                } else if (vartype instanceof JCPrimitiveTypeTree fa) {
                    utils.warning(mod.pos, "jml.message", "the type modifier/annotation (" + mod + ") is not permitted on a primitive type: " + fa);
                    // Do not add the annotation -  not permitted on a primitive type
                    // FIXME - error?
                } else {
                    System.out.println("UNKNOWN KIND OF TYPE " + vartype.getClass() + " " + vartype);
                }
//            } else {
//                //utils.warning(mod.pos, mod.endPos, "jml.message", "inserting a modifier as an annotation: " + ck); Utils.dumpStack();
//                mods.annotations = mods.annotations.append(a);
            }
        }
        return vartype;
    }

    /** Overridden to increase visibility */
    @Override
    public List<JCVariableDecl> formalParameters() {
        return super.formalParameters();
    }
    
    protected List<JCStatement> localVariableDeclarations(JCModifiers mods, JCExpression type)  {
        if (type instanceof JCTree.JCArrayTypeTree) {
            mods.annotations = List.<JCAnnotation>nil(); // FIXME - should just remove JML type annotations
        }
        return super.localVariableDeclarations(mods, type);
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
    protected JCStatement classOrRecordOrInterfaceOrEnumDeclaration(JCModifiers mods, Comment dc) {
        boolean prevInJmlDeclaration = inJmlDeclaration;
        JCStatement s = null;
        while (true) try {
            int p = pos();
            if (S.jml()) {
                if (mods == null) {
                    mods = jmlF.at(Position.NOPOS).Modifiers(0);
                    storeEnd(mods, Position.NOPOS);
                }
                inJmlDeclaration = true;
                mods = modifiersOpt(mods);
            }
            if (!inJmlDeclaration || token.kind == CLASS || token.kind == INTERFACE || token.kind == ENUM || (token.kind == IDENTIFIER && token.name() == names.record)) {
                // The guard above is used because if it is false, we want to produce
                // a better error message than we otherwise get, for misspelled
                // JML modifiers. However, the test above replicates tests in
                // the super method and may become obsolete.
                normalizeAnnotations(mods, null);
                s = super.classOrRecordOrInterfaceOrEnumDeclaration(mods, dc);
                if (s instanceof JCExpressionStatement && ((JCExpressionStatement)s).expr instanceof JCErroneous) {
                	var errs = ((JCErroneous)((JCExpressionStatement)s).expr).errs;
                	if (errs != null && !errs.isEmpty() && errs.head.pos == Position.NOPOS) {
                		errs.head.pos = s.pos;
                	}
                }
            } else {
                if (inJmlDeclaration && token.kind == IDENTIFIER) {
                    IJmlClauseKind cl = Extensions.findKeyword(token);
                    if (cl instanceof IJmlClauseKind.ClassLikeKind) {
                        s = (JmlDatatypeDecl)cl.parse(mods,token.name().toString(),cl,this);
                    } else {
                    	// FIXME - the identifier might be an annotation
                        int ep = endPos();
                        utils.error(p, ep,
                                "jml.unexpected.or.misspelled.jml.token", token.name());
                        setErrorEndPos(endPos());
                        //s = jmlF.at(p).Exec(jmlF.at(p).Erroneous());
                    	nextToken();
                        while (jmlTokenClauseKind() == JmlOperatorKind.endjmlcommentKind) nextToken();
                        mods = modifiersOpt(mods);
                    	continue; // ignore token and try again
                    }
                } else if (inJmlDeclaration && token.kind == IMPORT) {
//                	pushBackModifiers = mods;
                	importDeclaration((JmlModifiers)mods);
                	mods = null;
                	utils.warning(p, pos(), "jml.message", "misplaced model import");
                    setErrorEndPos(endPos());
                    //s = jmlF.at(p).Exec(jmlF.at(p).Erroneous());
                    continue;
                } else {
                    int ep = endPos();
                    utils.error(p, ep,
                            "jml.unexpected.or.misspelled.jml.token",
                            token == null ? jmlTokenKind().internedName() : S.chars() );

                    setErrorEndPos(ep);
                	nextToken();
                    while (jmlTokenClauseKind() == JmlOperatorKind.endjmlcommentKind) nextToken();
                    //s = to(F.Exec(toP(F.at(p).Erroneous(List.<JCTree> nil()))));
                    mods = modifiersOpt(mods);
                    continue; // ignore token and try again
                }
            }
            if (s instanceof JCClassDecl && (((JCClassDecl)s).mods.flags & Flags.ENUM) != 0) {
                addImplicitEnumAxioms((JCClassDecl)s); // FIXME - causes compile errors in module system
            }
            while (jmlTokenKind() == JmlTokenKind.ENDJMLCOMMENT) {
                nextToken();
            }
            break;
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
//        {
//        	var pos = cd;
//        	JCExpression restype = jmlF.at(pos).Ident(cd.name);
//        	JCVariableDecl param = jmlF.at(pos).VarDef(jmlF.Modifiers(0L), names.fromString("x"), jmlF.at(pos).Ident(names.fromString("String")), null);
//        	param.mods.annotations = param.mods.annotations.append(utils.modToAnnotationAST(Modifiers.NULLABLE, pos.pos, pos.pos));
//        	JCExpression thrown = jmlF.at(pos).Ident("NullPointerException");
//            var mdef = (JmlMethodDecl)jmlF.at(pos).MethodDef(jmlF.at(pos).Modifiers(Flags.PUBLIC|Flags.STATIC), names.valueOf, restype,
//            		List.<JCTypeParameter>nil(), List.<JCVariableDecl>of(param), List.<JCExpression>of(thrown), null,null);
//            mdef.mods.annotations = mdef.mods.annotations.append(utils.modToAnnotationAST(Modifiers.PURE, pos.pos, pos.pos));
//            mdef.mods.annotations = mdef.mods.annotations.append(utils.modToAnnotationAST(Modifiers.HELPER, pos.pos, pos.pos));
//            mdef.mods.annotations = mdef.mods.annotations.append(utils.modToAnnotationAST(Modifiers.NON_NULL, pos.pos, pos.pos));
//            cd.defs = cd.defs.append(mdef);
//        }
        if (disj != null) { // Must be at least one value
            args.add(F.Literal(TypeTag.BOT,null));
            argsn.add(F.Literal(TypeTag.BOT,null));
            jmlF.at(cd.pos);
            ListBuffer<JCTree> newdefs = new ListBuffer<>();
            JCVariableDecl vd = jmlF.VarDef(jmlF.Modifiers(Flags.PUBLIC|Flags.STATIC),names.fromString("_JMLvalues"),jmlF.TypeArray(jmlF.Ident(cd.name)),null);
            utils.setJML(vd.mods);
//            JCAnnotation a = utils.modToAnnotationAST(Modifiers.MODEL, cd.pos, cd.pos);  // FIXME -is position correct?
//            vd.mods.annotations =  vd.mods.annotations.append(a);
            ((JmlModifiers)vd.mods).jmlmods.add(new JmlToken(Modifiers.MODEL, log.currentSourceFile(), cd.pos, cd.pos));
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
                    jmlF.JmlBinary(JmlOperatorKind.equivalenceKind, jmlF.TypeTest(jmlF.Ident(n), jmlF.Ident(cd.getSimpleName())),disj));
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
                    jmlF.JmlBinary(JmlOperatorKind.impliesKind, jmlF.Binary(JCTree.Tag.NE, jmlF.Ident(n), jmlF.Literal(TypeTag.BOT,null)),exists));
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
//        if (org.jmlspecs.openjml.Main.useJML) {
//        	System.out.println("ENUM " + cd.name);
//        	for (var t: cd.defs) {
//            	System.out.println("ENUMDEF " + JmlPretty.write(t));
//        	}
//        }
    }

    @Override
    List<JCTree> classInterfaceOrRecordBody(Name className, boolean isInterface, boolean isRecord) {
        JmlMethodSpecs savedMethodSpecs = currentMethodSpecs; // TODO - why do we need to save and restore the method specs
        currentMethodSpecs = null;
        try {
            return super.classInterfaceOrRecordBody(className, isInterface, isRecord);
        } finally {
            currentMethodSpecs = savedMethodSpecs;
        }

    }

    /** Overrides in order to collect and reset line annotations for this declaration */
    @Override
    public JCClassDecl classDeclaration(JCModifiers mods, Comment dc) {
    	boolean injml = inJmlDeclaration;
        JCClassDecl cd = super.classDeclaration(mods, dc);
        ((JmlClassDecl)cd).lineAnnotations = S.lineAnnotations;
        if (injml) utils.setJML(cd.mods);
        S.lineAnnotations = new java.util.LinkedList<>();
        ListBuffer<JCTree> newdefs = new ListBuffer<>();
        for (var d: cd.defs) {
            if (d instanceof JmlTypeClauseConditional ct) {
                x: { 
                    JCIdent id = ct.identifier;
                    for (var dd: cd.defs) {
                        if (dd instanceof JmlVariableDecl vd && vd.name == id.name) {
                            vd.fieldSpecs.list.add(ct);
                            break x;
                        }
                    }
                    utils.error(id, "jml.message", "The identifier must be a member of the enclosing class: " + id);
                }
            } else {
                newdefs.add(d);
            }
        }
        cd.defs = newdefs.toList();
        return cd;
    }

 
    protected void insertReplacementType(Object tree, JCExpression replacementType) {
        if (replacementType != null && tree instanceof JmlVariableDecl) {
            JmlVariableDecl d = (JmlVariableDecl) tree;
            d.originalVartype = d.vartype;
            d.jmltype = true;
            if (d.vartype instanceof JCAnnotatedType at) {
                d.vartype = jmlF.at(at.pos).AnnotatedType(at.annotations, replacementType);
            } else {
                d.vartype = replacementType;
            }
        }
    }
    
    boolean isLoopSpec(IJmlClauseKind kind) {
    	return kind == loopinvariantClause || kind == StatementLocationsExtension.loopwritesStatement
    			|| kind == loopdecreasesClause;
    }

    public JCBlock block(int pos, long flags) {
    	var saved = S.jmltokenizer.noJML;
    	S.jmltokenizer.noJML = false;
    	
    	// The body of super.block(pos,flags) is replicated here (potential maintenance problem) because we need to reset noJML
    	// before we accept RBRACE, in case there is a JML annotation immediately following the RBRACE.
    	// Even so, there could be a problem if any lookahead tokens are already scanned.
//    		return super.block(pos,flags);
        accept(LBRACE);
        List<JCStatement> stats = blockStatements();
        JCBlock t = F.at(pos).Block(flags, stats);
        while (token.kind == CASE || token.kind == DEFAULT) {
            syntaxError(token.pos, Errors.Orphaned(token.kind));
            switchBlockStatementGroups();
        }
        // the Block node has a field "endpos" for first char of last token, which is
        // usually but not necessarily the last char of the last token.
        t.endpos = token.pos;
    	if (saved && !S.savedTokens.isEmpty()) utils.warning(token.pos, "jml.message", "Lookahead present when noJML is reset");
    	S.jmltokenizer.noJML = saved;
        accept(RBRACE);
        return toP(t);
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
    	// The while is just to be able to retry if we skip past something
    	// Actual statements issue return statements
        while (true) {
            // If we are in a JML comment and this first token is an identifier
            // registered as marking a JML statement or statement annotation,
            // then we proceed to parse it as a (JML) statement
            String id = null;
            IJmlClauseKind anyext = null;
            jml: if (S.jml()) {
            	while (isStartJml(token)) nextToken();
            	if (!S.jml()) break jml; // Empty JML comment
            	if (token.kind == TokenKind.IDENTIFIER) {
            		id = token.name().toString();
            		anyext = Extensions.allKinds.get(id);
            	}
            	try {
            	if (anyext != null) {
            		IJmlClauseKind ext = Extensions.findSM(id);
            		if (ext != null) {
            			JCStatement s;
            			if (ext instanceof IJmlClauseKind.MethodClauseKind
            					|| ext == Refining.refiningClause) {
            				s = (JCStatement)Refining.refiningClause.parse(null, id, ext, this);
            			} else if (isLoopSpec(ext)) {
            				s = parseLoopWithSpecs();
            			} else {
            				// FIXME - change this to not have to parse one loop spec first -- move to extensions
            				s = (JCStatement)ext.parse(null, id, ext, this);
            				while (jmlTokenClauseKind() == JmlOperatorKind.endjmlcommentKind) nextToken();
            				//                        if (s instanceof JmlStatementLoop) {
            				//                            s = parseLoopWithSpecs((JmlStatementLoop)s, true);
            				//                        } else 
            				if (id.equals(Refining.beginID)) {
            					utils.error(s, "jml.message", "Improperly nested spec-end pair");
            				} else if (id.equals(Refining.endID)) {
            					utils.error(s, "jml.message", "Improperly nested spec-end pair");
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
            	// FIXME - I would expect token to always be a JmlToken, even if it just wraps a Java token
            	if (!(token instanceof JmlToken) && anyext == null) {
            		JCExpression replacementType = parseOptionalReplacementType(); // Needed for local variable declarations -- removes leading jml comment or left bracket
            		boolean inJml = S.jml();
            		List<JCStatement> stats = super.blockStatement();
            		if (replacementType != null) {
            			for (JCStatement s: stats)  insertReplacementType(s,replacementType);
            			replacementType = null;
            		}
            		if (inJml) {
            			for (JCStatement s: stats) {
            				if (s instanceof JCVariableDecl) {
            					// OK
            				} else if (s instanceof JCClassDecl || s instanceof JmlAbstractStatement || s instanceof JCSkip) {
            					// OK
            				} else if (!inJmlDeclaration && !inModelProgram && !inLocalOrAnonClass) { // FIXME - unsure of this test
            					utils.error(s.pos, "jml.expected.decl.or.jml");
            				}
            			}
            		}
            		return stats;
            	}
            	if (anyext instanceof ModifierKind) {
            		// MAINTENCE: Copied from JavacParser.blockStatement, FINAL case
            		Comment dc = token.comment(CommentStyle.JAVADOC);
            		JCModifiers mods = modifiersOpt();
            		if (token.kind == INTERFACE ||
            				token.kind == CLASS ||
            				token.kind == ENUM) {
            			if (S.jml()) utils.setJML(mods); // Added this to mark declarations in JML annotations
            			normalizeAnnotations(mods,null);
            			return List.of(super.classOrRecordOrInterfaceOrEnumDeclaration(mods, dc));
            		} else {
            			JCExpression t = parseType(true);
            			startOfDeclaration(mods);
            			ListBuffer<JCStatement> stats =
            					variableDeclarators(mods, t, new ListBuffer<JCStatement>(), false); // FIXME - is false correcct?
            			// A "LocalVariableDeclarationStatement" subsumes the terminating semicolon
            			storeEnd(stats.last(), token.endPos);
            			accept(SEMI);
            			return stats.toList();
            		}
            	} else if (isEndJml(token)) {
            		if (S.jml()) throw new AssertionError("Thought jml was always false at this point");
            		S.setJml(false); // TOOD _ already false?
            		nextToken();
            		continue;
            	}
            	} finally {
            		while (isEndJml(token)) nextToken();
            	}
            }
            // Nothing JML -- parse a Java statement
            return super.blockStatement();
        }
    }

    public JCStatement parseJavaStatement() {
        var stats = super.blockStatement();
        if (stats.isEmpty()) return maker().at(pos()).Exec(maker().at(pos()).Erroneous());
        if (stats.size() > 1) utils.error(stats.get(1), "jml.message", "Expected just one statement here");
        return stats.head;
    }
    
    @Override
    List<JCStatement> forInit() {
        ListBuffer<JCStatement> stats = new ListBuffer<>();
        int pos = token.pos;
        if (token.kind == FINAL || token.kind == MONKEYS_AT || S.jml()) {
            var mods = optFinal(0);
            var type = parseType(true);
            if (type != null) {
                var typeannotations = extractTypeAnnotations(mods);
                type = insertAnnotationsToMostInner(type, typeannotations, false);
            }
            var lst = variableDeclarators(mods, type, stats, true).toList();
            return lst;
        } else {
            return super.forInit();
        }
    }

    
    public JCStatement parseLoopWithSpecs() {
    	ListBuffer<JmlStatementLoop> loopSpecs = new ListBuffer<>();
    	while (true) {
    		if (!(S.jml() && token.kind == TokenKind.IDENTIFIER)) break;
    		String id = token.name().toString();
    		IJmlClauseKind anyext = Extensions.allKinds.get(id);
    		if (anyext == InlinedLoopStatement.inlinedLoopStatement || anyext == splitClause) {
    			break;
    		} else if (!isLoopSpec(anyext)) {
                utils.error(token.pos, "jml.message", "Expected loop specifications while in JML: " + id + " is not a loop specification keyword");
    			skipThroughSemi();
    		} else {
    			JmlStatementLoop t = (JmlStatementLoop)anyext.parse(null, id, anyext, this);
    			if (t != null) loopSpecs.add(t);
    		}
    		while (jmlTokenClauseKind() == JmlOperatorKind.endjmlcommentKind) nextToken();
    	}
    	JCStatement stat = parseStatement();
    	if (stat instanceof IJmlLoop) {
    		((IJmlLoop)stat).setLoopSpecs(loopSpecs.toList());
        } else {
            utils.error(loopSpecs.isEmpty() ? stat : loopSpecs.first(), "jml.message", "Loop specifications must immediately precede a loop statement");
        }
        return stat;
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
            utils.error(firstSpec, "jml.message", "Loop specifications must immediately precede a loop statement");
        }
        return stt;
    }

    /** Overridden to parse JML statements */
    @Override  // TODO - needs REVIEW - shouldn't this be in blockStatement()
    public JCStatement parseStatement() {
        int pos = pos();
        JCStatement st;
        String id = null;
        if (S.jml() && token.kind == TokenKind.IDENTIFIER) {
        	List<JCStatement> sts = blockStatement();
        	return sts == null ? null : sts.head;
        }
        JCStatement stt = super.parseStatement();
        return stt;
    }

    // FIXME - should this still be here?
    JCStatement parseRefining(int pos, IJmlClauseKind jt) {
        JmlStatementSpec ste;
        ListBuffer<JCIdent> exports = new ListBuffer<>();
        if (jt == Refining.refiningClause) {
            nextToken();
            IJmlClauseKind ext = methodSpecKeywordS();
            if (ext == alsoClause) { // jmlTokenKind() == JmlTokenKind.ALSO) {
                utils.error(pos(), endPos(), "jml.invalid.also");
                nextToken();
            }
            if (ext == elseClause) {
                utils.error(pos(), endPos(), "jml.invalid.also"); // FIXME - should warn about else
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
                    utils.error(pos(),endPos(), "jml.message", "Expected a comma or semicolon here");
                }
                nextToken();
            }
        } else if (jt == Refining.beginClause) {
            utils.error(pos, "jml.message", "Improperly nested spec-end pair");
        } else if (jt == Refining.endClause) {
            utils.error(pos, "jml.message", "Improperly nested spec-end pair");
        } else {
            utils.warning(pos(),"jml.refining.required");
        }
        JCModifiers mods = modifiersOpt();
        JmlMethodSpecs specs = parseMethodSpecs(mods);
        mods = pushBackModifiers;
        for (JmlSpecificationCase c : specs.cases) {
            if (!isNone(c.modifiers)) {
                utils.error(c.modifiers.getStartPosition(),
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
            utils.error(ste, "jml.message", "Statement specs found at the end of a block (or before an erroneous statement)");
            return null;
        } else if (stat.head instanceof JmlAbstractStatement && stat.head.toString() == Refining.beginID) {
            utils.error(stat.head, "jml.message", "Statement specs may not precede a JML statement clause");
            return stat.head;
        }
        ListBuffer<JCStatement> stats = new ListBuffer<>();
        if (stat.head instanceof JmlStatement && ((JmlStatement)stat.head).clauseType == Refining.beginClause) {
            JCStatement begin = stat.head;
            // Has a begin statement, so we read statement until an end
            while (true) {
                stat = blockStatement();
                if (stat.isEmpty()) {
                    utils.error(begin, "jml.message", "Expected an 'end' statement to match the begin statement before the end of block");
                    break;
                } else if (stat.get(0) instanceof JmlStatement && ((JmlStatement)stat.get(0)).clauseType == Refining.endClause) {
                    break;
                } else {
                    stats.addAll(stat);
                }
            }
        } else if (stat.head instanceof JmlStatement && ((JmlStatement)stat.head).clauseType == Refining.beginClause) {
            utils.error(ste, "jml.message", "Improperly nested spec-end pair");
        } else if (stat.isEmpty()) {
            utils.error(ste, "jml.message", "Statement specs found at the end of a block (or before an erroneous statement)");
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
        List<JCStatement> statslist = stats.toList();
        if (statslist.size() > 1) return F.at(statslist.head.pos).Block(0, statslist);
        return statslist.head;
    }

    // TODO - generalize this and move it out of JmlParser
    /** Returns true if the token is a JML type token */
    public boolean isJmlTypeToken(JmlTokenKind t) {
        return t == JmlTokenKind.BSBIGINT
                || t == JmlTokenKind.PRIMITIVE_TYPE;
    }
    
    public boolean isJmlType(Token token) {
        var jtk = jmlTokenClauseKind();
        var jt = jmlTokenKind();
        return jtk instanceof JmlTypeKind || isJmlTypeToken(jt);
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
    public /*@nullable*/ JmlMethodSpecs currentMethodSpecs = null;
    /** The most recent field declaration within a class body. */
    public /*@nullable*/ JmlVariableDecl currentVariableDecl = null;

    /** Returns true if the argument is a possible beginning of a
     * method specs, after any modifiers */
    protected boolean startOfMethodSpecs(Token possibleKeyword) {
        if (!(S.jml())) return false;
        if (possibleKeyword.kind == TokenKind.IDENTIFIER) {
            if (possibleKeyword.name().toString().equals("code")) return true;
            IJmlClauseKind ext = Extensions.findKeyword(possibleKeyword);
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
            return Extensions.findKeyword(possibleKeyword) instanceof IJmlClauseKind.TypeClause;
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
     * of a class or interface or record.
     */
    @Override
    public List<JCTree> classOrInterfaceOrRecordBodyDeclaration(JCModifiers mods, Name className, boolean isInterface, boolean isRecord) {

        ListBuffer<JCTree> list = new ListBuffer<JCTree>();
        loop: while (token.ikind != TokenKind.RBRACE && token.ikind != TokenKind.EOF) {
        	// Skip over any JML start tokens
            if (isStartJml(token)) {
            	nextToken();
            	continue;
            }
            JmlVariableDecl mostRecentVarDecl = currentVariableDecl; // Just saves the current value so it can be set to null in most cases
            currentVariableDecl = null;

            Comment dc = token.comment(CommentStyle.JAVADOC);

            // Get any modifiers (legal or not)
            mods = modifiersOpt(mods);
            
            // Get type annotations?
            List<JCAnnotation> typeAnns = null; // typeAnnotationsOpt();
            
            // Get the keyword for the JML clause, if any
            int pos = pos();
            JmlTokenKind jt = jmlTokenKind();
            if (jt != null && !isJmlType(token) && currentMethodSpecs != null && !startOfMethodSpecs(token)) {
                utils.error(currentMethodSpecs.pos, "jml.message", "Misplaced method specifications preceding a " + jt.internedName() + " clause (ignored)");
                currentMethodSpecs = null;
            }
            IJmlClauseKind ct = null;
            String id = null;
            if (token.kind == TokenKind.SEMI && !isNone(mods)) {
            	utils.error(token.pos, "jml.message", "Orphaned modifiers found before an empty declaration");
            }
            
            // Look up the keyword
            if (S.jml() && token.kind == TokenKind.IDENTIFIER) {
                id = token.name().toString();
                ct = Extensions.findTM(id);
            }
            if (ct != null) {
            	// It is something JML - but only type or method specification clauses
                if (startOfMethodSpecs(token)) {
                	// Method specs
                    currentMethodSpecs = parseMethodSpecs(mods);
                    if (((JmlModifiers)mods).anyModsInJava) {
                    	utils.error(currentMethodSpecs.pos,  "jml.message", "A method specification incorrectly follows non-JML modifiers");
                    }
                    mods = pushBackModifiers;
                } else if (startOfTypeSpec(token)) {
                	// Type specs
                    normalizeAnnotations(mods, null);
                    JCTree tc = parseTypeSpecs(mods);
                    if (((JmlModifiers)mods).anyModsInJava) {
                    	utils.error(tc.pos,  "jml.message", "A JML clause incorrectly follows non-JML modifiers");
                    }
                    mods = null;
                    if (tc instanceof JmlTypeClause && currentMethodSpecs != null) {
                        utils.error(currentMethodSpecs.pos, "jml.message", "Misplaced method specifications preceding a " + ((JmlTypeClause)tc).clauseType.keyword() + " clause (ignored)");
                        currentMethodSpecs = null;
                    }
                    if (tc instanceof JmlTypeClauseIn
                            || tc instanceof JmlTypeClauseMaps) {
                        JCTree tree = tc;
                        if (tree instanceof JmlTypeClauseIn inclause) {
                            inclause.parentVar = mostRecentVarDecl;
                        }
                        if (mostRecentVarDecl == null) {
                            utils.error(tree.pos(), "jml.misplaced.var.spec",
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
                } else if (utils.findMod(mods,Modifiers.MODEL) == null && utils.findMod(mods,Modifiers.GHOST) == null) {
                	// FIXME _ what could this be
                    utils.error(token.pos, "jml.illegal.token.for.declaration", id);
                    skipThroughSemi();
                    mods = null;
                } else {
                	// internal error -- token recognized by findTM but starts neither a method or type spec
                }
                continue;
            } else if (isStartJml(token)) { // FIXME - is this needed - modifiersOpt reads any start or end JML tokens
            	nextToken();
            	continue;
            } else if (S.jml() && id != null && Extensions.findSM(id) != null && !"set".equals(id)) {
                utils.error(pos(), endPos(), "jml.illegal.token.for.declaration", id);
                skipThroughSemi(); // FIXME - or right brace?
                mods = null;
                break;

            }
            // Possibly Java, possibly JML but then is a ghost or model declaration
            if (jt == null || isJmlType(token)) {
                // Either a Java declaration or a JML declaration that starts with a JML type
                boolean startsInJml = S.jml();
                List<JCTree>  t;
                if (startsInJml && !inLocalOrAnonClass) {
                    boolean prevInJmlDeclaration = inJmlDeclaration;
                    // Parse any replacement type early because otherwise it appears we are in JML
                    replacementType = parseOptionalReplacementType();
                    inJmlDeclaration = S.jml();
                    startsInJml = S.jml();
                    if (token.kind == TokenKind.SEMI && currentMethodSpecs != null) {
                        utils.error(token.pos, "jml.message", "Method specs preceding an empty declaration are ignored");
                        currentMethodSpecs = null;
                    }
                    IJmlClauseKind.ClassLikeKind cl =  null;
                    if ((cl = isJmlClassLike(token)) != null) {
                        t = List.<JCTree>of(cl.parse(mods, cl.keyword, cl, this));
                        // FIXME - attach the doc comment
                    } else {
                        boolean inJml = S.jml();
                        t = super.classOrInterfaceOrRecordBodyDeclaration(mods, className, isInterface, isRecord);
                        if (inJml) acceptEndJML();
                        if (inJml && ((JmlModifiers)mods).anyModsInJava) {
                        	utils.error(t.head.pos,  "jml.message", "A JML declaration incorrectly follows non-JML modifiers");
                        }
                        if (isInterface && t.head instanceof JmlMethodDecl) {
                            JmlMethodDecl md = (JmlMethodDecl)t.head;
                            if (utils.hasMod(md.mods,Modifiers.MODEL)
                                    && (md.mods.flags & Flags.STATIC) == 0) {
                               md.mods.flags |= Flags.DEFAULT; // Mark a model method as DEFAULT, so subclasses are not required to have an implementation
                            }
                        }
                    }
                    inJmlDeclaration = prevInJmlDeclaration;
                } else {

                    if (token.kind == TokenKind.SEMI && currentMethodSpecs != null) {
                        utils.error(token.pos, "jml.message", "Method specs preceding an empty declaration are ignored");
                        currentMethodSpecs = null;
                    }
                    boolean inJml = S.jml();
                    t = super.classOrInterfaceOrRecordBodyDeclaration(mods, className, isInterface, isRecord);
                    if (inJml) acceptEndJML();
                }
                mods = null;
                if (!inJmlDeclaration) {
                    for (JCTree tr : t) {
                        JCTree ttr = tr;
                        if (tr instanceof JmlClassDecl d) {
                            if (currentMethodSpecs != null) {
                                utils.error(tr.pos, "jml.message", "Method specs may not precede a class declaration");
                                currentMethodSpecs = null;
                            }
                            if (startsInJml) utils.setJML(d.mods);
                            //d.toplevel.sourcefile = log.currentSourceFile();
                            ttr = tr; // toP(jmlF.at(pos).JmlTypeClauseDecl(d));
                            attach(d, dc); // FIXME - already attached I think; here and below
                        } else if (tr instanceof JmlMethodDecl d) {
                            d.sourcefile = currentSourceFile();
                            ttr = tr; // toP(jmlF.at(pos).JmlTypeClauseDecl(d));
                            attach(d, dc);
                            d.cases = currentMethodSpecs;
                            if (currentMethodSpecs != null) {
                                currentMethodSpecs.decl = d;
                                currentMethodSpecs = null;
                            }

                        } else if (tr instanceof JmlBlock d) {
                            ttr = tr; // toP(jmlF.at(pos).JmlTypeClauseDecl(d));
                            attach(d, dc);
                            d.specificationCases = currentMethodSpecs;
                            d.isInitializerBlock = true;
                            d.sourcefile = currentSourceFile();
                            if (currentMethodSpecs != null) {
                                currentMethodSpecs.decl = null; // null means the JmlMethodSpecs belons to a block, not a method
                                currentMethodSpecs = null;
                            }

                        } else if (tr instanceof JmlVariableDecl vd) {
                            if (currentMethodSpecs != null) {
                                utils.error(tr.pos, "jml.message", "Method specs may not precede a variable declaration");
                                currentMethodSpecs = null;
                            }
                            if (replacementType != null) {
                                insertReplacementType(vd,replacementType);
                                replacementType = null;
                            }
                            vd.sourcefile = currentSourceFile();
                            ttr = tr; // toP(jmlF.at(pos).JmlTypeClauseDecl(d));
                            attach(vd, dc);
                            if (startsInJml) utils.setJML(vd.mods);
                            currentVariableDecl = vd;
                            currentVariableDecl.fieldSpecs = new JmlSpecs.FieldSpecs(currentVariableDecl);
                        } else {
                            if (currentMethodSpecs != null) {
                                utils.error(tr.pos, "jml.message", "Method specs that do not precede a method declaration are ignored");
                                currentMethodSpecs = null;
                            }
                            ttr = null;
                        }
                        dc = null;
                        if (ttr != null) list.append(ttr);
                    }
                } else if (t.head instanceof JmlMethodDecl md) {
                    md.sourcefile = currentSourceFile();
                    attach(md, dc);
                    md.cases = currentMethodSpecs;
                    if (currentMethodSpecs != null) {
                        currentMethodSpecs.decl = md;
                        currentMethodSpecs = null;
                    }
                    list.append(md);

                } else if (t.head instanceof JmlVariableDecl vd) {
                    if (vd.fieldSpecs == null) vd.fieldSpecs = new JmlSpecs.FieldSpecs(vd);
                    vd.sourcefile = currentSourceFile();
                    if (startsInJml) utils.setJML(vd.mods);
                    attach(vd, dc);
                    list.append(vd);
                    currentVariableDecl = vd;
                   
                } else if (t.head instanceof JmlTypeClauseIn
                        || t.head instanceof JmlTypeClauseMaps) {
                    JCTree tree = t.head;
                    if (tree instanceof JmlTypeClauseIn) {
                        ((JmlTypeClauseIn) tree).parentVar = mostRecentVarDecl;
                    }
                    if (mostRecentVarDecl == null) {
                        utils.error(tree.pos(), "jml.misplaced.var.spec",
                                ((JmlTypeClause) tree).keyword);
                    } else {
//                        if (mostRecentVarDecl.fieldSpecs == null) {
//                            mostRecentVarDecl.fieldSpecs = new JmlSpecs.FieldSpecs(
//                                    mostRecentVarDecl);
//                        }
                        mostRecentVarDecl.fieldSpecs.list.append((JmlTypeClause) tree);
                        currentVariableDecl = mostRecentVarDecl;
                    }

                } else if (t.head instanceof JmlMethodSpecs) {
                    currentMethodSpecs = (JmlMethodSpecs)t.head;

                } else {
                    list.appendList(t);
                }
            } else if (startOfMethodSpecs(token)) {
            	utils.error(pos(), "jml.message", "DO NOT EXPECT TO EVER BE HERE");
                currentMethodSpecs = parseMethodSpecs(mods);
                mods = pushBackModifiers;
            } else {
                utils.error(pos(), endPos(),
                        "jml.illegal.token.for.declaration", jt.internedName());
                skipThroughSemi();
                break;
            }
        }
        acceptEndJML();
        if (currentMethodSpecs != null) {
        	utils.error(currentMethodSpecs, "jml.message", "Method specifications without a following method declaration");
        }
        return list.toList();
    }
    
    protected void startOfDeclaration(JCModifiers mods) {
    	if (savedTypeAnnotations != null) {
    		mods.annotations = mods.annotations.appendList(savedTypeAnnotations);
    		savedTypeAnnotations = null;
    	}
    	if (S.jml()) utils.setJML(mods); // TODO - is this actually useful?
    }
    
    List<JCAnnotation> savedTypeAnnotations = null;

//    public JCExpression parseType(boolean allowVar, List<JCAnnotation> annotations) {
//        replacementType = parseOptionalReplacementType();
//        return super.parseType(allowVar, annotations);
//    }

    public JCExpression parseOptionalReplacementType() {
        JCExpression r = null;
        while (isStartJml(token)) nextToken();
        if (token.kind == TokenKind.LBRACKET) {
        	nextToken();
            r = unannotatedType(false);
            accept(TokenKind.RBRACKET);
            acceptEndJML();
        }
        return r;
    }
    
    /**
     * This parses a comma-separated list of expressions; the last expression in
     * the list parses until it can parse no more - the caller needs to check
     * that the next token is an expected token in the context, such as a right
     * parenthesis.
     *
     * @return a List of expressions, which may be empty or contain
     *         JCErroneous expressions if errors occurred
     */
    public List<JCExpression> parseExpressionList() {
        ListBuffer<JCExpression> args = new ListBuffer<>();
        while (true) {
        	var e = parseExpression();
        	if (e != null) {
        		if (e instanceof JCErroneous) {
            		if (!(token.kind == COMMA || token.kind == SEMI || token.kind == RPAREN)) nextToken();
        		} else {
            		args.append(e);
        		}
        	}
        	if (token.kind == COMMA) {
        		nextToken();
        		continue;
        	} else if (token.kind == SEMI || token.kind == RPAREN) {
        		break;
        	} else if (jmlTokenKind() == ENDJMLCOMMENT) {
        		// The missing semi-colon is reported by the caller
        		break;
        	} else {
        		syntaxError(pos(), null, "jml.missing.comma.rp");
        		if (e == null) break;
        	}
        }
        return args.toList();
    }
    
    public List<JCExpression> parseTypeList() {
        ListBuffer<JCExpression> args = new ListBuffer<>();
        while (true) {
        	var e = parseType();
        	if (e != null) {
        		if (e instanceof JCErroneous) {
            		if (!(token.kind == COMMA || token.kind == SEMI || token.kind == RPAREN)) nextToken();
        		} else {
            		args.append(e);
        		}
        	}
        	if (token.kind == COMMA) {
        		nextToken();
        		continue;
        	} else if (token.kind == SEMI || token.kind == RPAREN) {
        		break;
        	} else if (jmlTokenKind() == ENDJMLCOMMENT) {
        		syntaxError(pos(), null, "jml.missing.comma.rp");
        		break;
        	} else {
        		syntaxError(pos(), null, "jml.missing.comma.rp");
        		if (e == null) break;
        	}
        }
        return args.toList();
    }
    
    private boolean parsingLocationList = false;
    
    public List<JCExpression> parseLocationList() {
    	boolean saved = parsingLocationList;
    	parsingLocationList = true;
    	try {
    		return parseExpressionList();
    	} finally {
    		parsingLocationList = saved;
    	}
    }
    
    JCExpression lambdaStatement(List<JCVariableDecl> args, int pos, int pos2) {
        var e = super.lambdaStatement(args,  pos,  pos2);
        if (e instanceof JmlLambda) ((JmlLambda)e).sourceLocation = log.currentSourceFile();
        else System.out.println("EXPECTED JMLLAMBDA"); // FIXME
        return e;
    }

    JCExpression lambdaExpression(List<JCVariableDecl> args, int pos) {
        var e = super.lambdaExpression(args,  pos);
        if (e instanceof JmlLambda) ((JmlLambda)e).sourceLocation = log.currentSourceFile();
        else System.out.println("EXPECTED JMLLAMBDA");  // FIXME
        return e;
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
        if (S.jml() && token.kind == DOT && S.token(1).kind == STAR) {
        	nextToken();
        	nextToken();
        	return jmlF.at(p).Select(t, (Name)null);
        }
        t = super.term3Rest(t, typeArgs);
        // TODO - @ for \old can be confused with @ for type annotation -- needs careful work
//        if (S.jml() && token.kind == MONKEYS_AT) {
//            accept(MONKEYS_AT);
//            int pp = pos();
//            Name label = ident();
//            JCIdent id = this.maker().at(pp).Ident(label);
//            JmlMethodInvocation tt = toP(this.maker().at(t).JmlMethodInvocation(oldKind, List.<JCExpression>of(t,id)));
//            return tt;
//        }
        return t;
    }

    public JCExpression parseQualifiedIdent(boolean allowAnnos) {
        return qualident(allowAnnos);
    }
    
    /** Parses a name and colon, if looking at a Java identifier with a colon as lookahead,
     * otherwise does nothgin and returns null
     * @return
     */
    public Name parseOptionalName() {
    	if (token.kind == TokenKind.IDENTIFIER && S.token(1).kind==TokenKind.COLON) {
    		Name id = ident(); // advances to next token
    		accept(TokenKind.COLON);
    		return id;
    	} else {
    		return null;
    	}	
    }

//    public JCExpression parseStoreRefListExpr() {
//        int p = pos();
//        JmlTokenKind jt = jmlTokenKind();
//        nextToken();
//        accept(LPAREN);
//        ListBuffer<JCExpression> list = parseStoreRefList(false);
//        if (token.kind != RPAREN) {
//            utils.error(pos(), endPos(), "log.expected", "right parenthesis");
//            skipThroughRightParen();
//        } else {
//            nextToken();
//        }
//        return toP(jmlF.at(p).JmlStoreRefListExpression(jt, list.toList()));
//    }

    public JCExpression replacementType;
    
    @Override
    public JCExpression unannotatedType(boolean allowVar) {
        while (isStartJml(token)) nextToken();
        boolean isBrace = S.jml() && token.kind == TokenKind.LBRACKET;
        if (isBrace) {
        	this.replacementType = null;
        	try {
        		// We need to be in non-JML mode so that we don't interpret
        		nextToken();
        		this.replacementType = super.unannotatedType(allowVar);
        	} finally {
        		if (isBrace) accept(TokenKind.RBRACKET);
        		if (token.ikind != JmlTokenKind.ENDJMLCOMMENT) {
        			utils.error(token.pos,"jml.bad.construct","JML construct");
        		}
        		skipThroughEndOfJML();
        	}
        }
        while (isEndJml(token)) nextToken();
        var clausekind = Extensions.findKeyword(token);
        if (clausekind instanceof JmlTypeKind kind) {

            int prevmode = mode;
            setMode(TYPE);
            JCExpression type = kind.parse(null, token.name().toString(), clausekind, this);
            setLastMode(mode);
            setMode(prevmode);
            return type;
        }
        JCExpression type = super.unannotatedType(allowVar);
        return type;
    }

    public IJmlClauseKind methodSpecKeyword() {
        IJmlClauseKind ext = null;
        if (token.kind == TokenKind.IDENTIFIER) ext = Extensions.findTM(token.name().toString());
        return ext;
    }

    public IJmlClauseKind methodSpecKeywordS() {
        IJmlClauseKind ext = null;
        if (token.kind == TokenKind.IDENTIFIER) ext = Extensions.findSM(token.name().toString());
        return ext;
    }

    public JCTree parseTypeSpecs(JCModifiers mods) {
        String id = token.kind == TokenKind.IDENTIFIER ?  token.name().toString() : "";
        IJmlClauseKind ct = Extensions.findKeyword(token);
        JCTree t = ct.parse(mods, id, ct, this);
        return t;
    }

    // Parses a sequence of specification cases, having already
    // parsed a sequence of modifiers
    public JmlMethodSpecs parseMethodSpecs(JCModifiers mods) {
        // Method specifications are a sequence of specification cases
        ListBuffer<JmlSpecificationCase> cases = new ListBuffer<JmlSpecificationCase>();
        JmlSpecificationCase c;
        int pos = pos();
        int lastPos = Position.NOPOS;
        while ((c = parseSpecificationCase(mods, false)) != null) {
            cases.append(c);
            lastPos = getEndPos(c);
            mods = modifiersOpt();
        }
        JmlMethodSpecs sp = jmlF.at(pos).JmlMethodSpecs(cases.toList());
        // end position set below
        IJmlClauseKind ext = methodSpecKeyword();
        if (ext == feasibleBehaviorClause) {
            if (!isNone(mods))
                utils.warning(pos(), endPos(), "jml.no.mods.allowed",
                        ext.keyword);
            nextToken();
            mods = modifiersOpt();
            ListBuffer<JmlMethodClause> clauses = new ListBuffer<JmlMethodClause>();
            JmlMethodClause cl;
            while ((cl = parseClause()) != null) {
                clauses.append(cl);
                lastPos = getEndPos(cl);
                mods = modifiersOpt();
            }
            sp.feasible = clauses.toList();
            ext = methodSpecKeyword();
        }
        if (ext == impliesThatClause) {
            if (!isNone(mods))
                utils.warning(pos(), endPos(), "jml.no.mods.allowed",
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
            ext = methodSpecKeyword();
        }
        if (ext == forExampleClause) {
            if (!isNone(mods))
                utils.warning(mods.getStartPosition(),
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
        if (ext == behaviorsClauseKind) {
            var blist = new ListBuffer<JmlMethodClauseBehaviors>();
            JmlMethodClauseBehaviors b;
            while (ext == behaviorsClauseKind && (b = (JmlMethodClauseBehaviors)behaviorsClauseKind.parse(mods, behaviorsID, behaviorsClauseKind, this)) != null) {
                blist.append(b);
                lastPos = getEndPos(b);
                ext = methodSpecKeyword();
            }
            sp.behaviors = blist.toList();
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
     * Returns true if no standard modifiers or annotations (of any kind) have been set
     *
     * @param mods
     *            the modifiers structure to check
     * @return true if any flags or annotations are set
     */
    public boolean isNone(JCModifiers mods) {
        return mods == null
                || ((mods.flags & Flags.StandardFlags) == 0 && (mods instanceof JmlModifiers jm && jm.jmlmods.isEmpty()) && (mods.annotations == null || mods.annotations
                        .isEmpty()));
    }

    public int casenum = 0;

    // [ also ] [ modifiers ] [ | behavior | normal_behavior |
    // exceptional_behavior ] [ clause ]*
    public JmlSpecificationCase parseSpecificationCase(JCModifiers mods, boolean exampleSection) {
        IJmlClauseKind also = null;
        int alsoPos = Position.NOPOS;
        IJmlClauseKind ext = methodSpecKeyword();
        if (ext == alsoClause || ext == elseClause) {
            if (!isNone(mods)) {
                utils.warning(mods.getStartPosition(), endPos(), "jml.no.mods.allowed", ext.keyword);
                mods = null;
            }
            also = ext;
            alsoPos = pos();
            nextToken();
            acceptEndJML();
            // get any modifiers
            mods = modifiersOpt();
            ext = methodSpecKeyword();
        }
        normalizeAnnotations(mods, null);
        boolean code = false;
        int codePos = 0;
        if (ext == feasibleBehaviorClause) return null; // FIXME - do something here?
        if (ext == codeClause) {
            codePos = pos();
            code = true;
            nextToken();
            acceptEndJML();
            ext = methodSpecKeywordS();
        }

        int pos = pos();
        if (ext == behaviorClause || ext == normalBehaviorClause || ext == exceptionalBehaviorClause
                || (ext == abruptBehaviorClause || inModelProgram))
        {
            if (exampleSection) {
                utils.warning(pos(), "jml.example.keyword", "must not",
                        ext.keyword);
            }
            nextToken();
        } else if (ext == exampleClause || ext == normalExampleClause || ext == exceptionalExampleClause) {
            if (!exampleSection) {
                utils.warning(pos(), "jml.example.keyword", "must",
                        ext.keyword);
            }
            nextToken();
        } else if (ext == modelprogramClause) {
            nextToken(); // skip over the model_program token

            // FIXME - do we want to keep this?
            //            JCBlock stat = parseModelProgramBlock();
            //            JmlSpecificationCase spc = toP(jmlF.at(pos).JmlSpecificationCase(mods, code,
            //                        MODEL_PROGRAM, also, List.<JmlMethodClause>nil(), stat));
            //            spc.sourcefile = log.currentSourceFile();
            //            return spc;
            //        } else if (jt == null && S.jml() && also != null) {
            //            utils.error(pos(), endPos(), "jml.invalid.keyword.in.spec",
            //                    S.chars());
            //            skipThroughSemi();
            //            // Call it lightweight
        } else {
            if (ext != null && !isNone(mods) && !((JmlModifiers)mods).anyModsInJava) {
                utils.error(mods,"jml.no.mods.lightweight");
                mods = null;
            }
            ext = null;
            if (code) utils.warning(codePos, "jml.misplaced.code");
            // lightweight
        }
        acceptEndJML();

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
            if ((e = parseClause()) != null) {
                clauses.append(e);
                acceptEndJML(); // FIXME - part of parseClause?
            } else if (S.jml() && token.kind == TokenKind.LBRACE) {
                if (stat != null) {
                    // FIXME - error
                }
                stat = parseModelProgramBlock();
                acceptEndJML(); // FIXME - part of parseModelProgramBlock?
           } else {
                break;
            }
        }

        if (clauses.size() == 0 && stat == null) {
            if (ext != null && JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
                utils.error(pos, "jml.empty.specification.case");
            }
            if (ext == null && also == null && !code) return null;
        }
        if (ext == null && code) code = false; // Already warned about this
        JmlSpecificationCase j = jmlF.at(pos).JmlSpecificationCase(mods, code,
                ext, also, clauses.toList(), stat);
        j.alsoPos = alsoPos;
        j.name = specCaseName;
        storeEnd(j, j.clauses.isEmpty() ? pos + 1 : getEndPos(j.clauses.last()));
        j.sourcefile = currentSourceFile();
        return j;
    }

    /** Issues a warning that the named construct is parsed and ignored */
    public void warnNotImplemented(int pos, String construct, String location) {
        if (JmlOption.isOption(context, JmlOption.SHOW_NOT_IMPLEMENTED))
            utils.warning(pos, "jml.unimplemented.construct", construct, location);
    }

    public boolean acceptIf(TokenKind tk) {
        if (token.kind == tk) {
            nextToken();
            return true;
        } else {
        	return false;
        }
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
    public JmlMethodClauseGroup parseSpecificationGroup() {
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
            utils.error(pos(), endPos(), "jml.invalid.spec.group.end");
            while (jmlTokenKind() != JmlTokenKind.ENDJMLCOMMENT && token.kind != EOF)
                nextToken();
            if (token.kind != EOF) nextToken();
        } else {
            nextToken();
        }
//        System.out.println("TOKEN " + token);
//        while (token.kind == TokenKind.IDENTIFIER && token.name().toString().equals(behaviorsID)) { // FIXME - alternate spelling? Use clause kind?
//            nextToken();
//            var id = ident();            
//            if (java.util.Arrays.binarySearch(behaviorsCommands,id) < 0) { 
//                utils.error(token.pos, "jml.message", "Unexpected keyword in a 'behaviors' clause: ", id);        
//            }
//            accept(SEMI);
//            System.out.println("TOKEN " + token);
//        }
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
    // FIXME - move this to an extension file?
    public JmlMethodClause parseClause() {
         // FIXME - what do we do with doc comments
        while (jmlTokenKind() == ENDJMLCOMMENT) {
            nextToken();
        }

        JmlMethodClause res = null;
        String keyword = null;
        if (token().kind == IDENTIFIER) keyword = token().name().toString();
        if (keyword != null) {
            IJmlClauseKind clauseType = Extensions.findTM(keyword);
            if (clauseType == org.jmlspecs.openjml.ext.MethodExprClauseExtensions.behaviorsClauseKind) return null; // 'behaviors' clauses not allowed in specification cases
            if (clauseType instanceof MethodSpecClauseKind) {
                res = (JmlMethodClause)clauseType.parse(null, keyword, clauseType, this);
            } else if (clauseType instanceof IJmlClauseKind.MethodClauseKind) {
                return null;
            }
        }
        JmlTokenKind jt = jmlTokenKind();
        if (jt != null && res == null)
            switch (jt) {
            // FIXME - change this to work in the above loop
                case SPEC_GROUP_START:
                    res = parseSpecificationGroup();
                    break;

                default:
                    // For any other token we just exit this loop,
                    // WITHOUT HAVING CALLED nextToken()!!!!
                    break;

            }
        if (res != null) res.sourcefile = currentSourceFile();
        return res;
    }

    JavaFileObject currentSourceFile() {
        return Log.instance(context).currentSourceFile();
    }


    /**
     * Parses ("\\nothing"|"\\everything"| <store-ref> [ ","
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
    public ListBuffer<JCExpression> parseStoreRefListOrKeyword(boolean strictId) {
        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
        if (!strictId) {
            JCExpression s = parseOptStoreRefKeyword();
            if (s != null) {
                list.append(s);
                return list;
            }
        }
        return parseStoreRefList();
    }
        
    public ListBuffer<JCExpression> parseStoreRefList() {
        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
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

    // FIXME - move to extensions?
    /** Parses a storeRefKeyword or returns null (with no error message) */
    public JmlSingleton parseOptStoreRefKeyword() {
        int p = pos();
        if (tokenIsId(nothingID)) {
        	return (JmlSingleton)nothingKind.parse(null, nothingID, nothingKind, this);
//            var s = to(jmlF.at(p).JmlSingleton(nothingKind));
//            nextToken();
//            return s;
        }
        if (tokenIsId(everythingID)) {
        	return (JmlSingleton)everythingKind.parse(null, everythingID, everythingKind, this);
//            var s = to(jmlF.at(p).JmlSingleton(everythingKind));
//            nextToken();
//            return s;
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
                        if (token.kind == DOT || token.kind == LBRACKET) { // expected token: ; ) = ,
                            utils.error(pos(), endPos(), "jml.not.after.star");
                            skipToCommaOrSemi();
                        }
                        break;
                    } else if (token.kind == IDENTIFIER) {
                        Name n = ident();
                        e = to(jmlF.at(dotpos).Select(e, n));
                        continue;
                    } else {
                        if (strictId)
                            utils.error(pos(), endPos(), "jml.expected.id");
                        else
                            utils.error(pos(), endPos(),
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
                    utils.error(e.pos(), "jml.naked.this.super");
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
        utils.error(p, endPos(), "jml.bad.store.ref");
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
                    utils.warning(pos(), endPos(), "jml.no.star.in.strict.mode");
                }
                nextToken();
                if (token.kind == RBRACKET) {
                    nextToken();
                    t = toP(jmlF.at(t.pos).Indexed(t, jmlF.at(t.pos).JmlRange(null,null)));
                    continue;
                } else {
                    utils.error(pos(), endPos(), "jml.expected.rbracket.star");
                    skipToCommaOrSemi();
                    break;
                }
            } else {
                JCExpression index = parseExpression(); // parses an index or a range
                if (token.kind == RBRACKET) {
                    if (JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
                    	if (index instanceof JmlRange r && r.lo != null && r.hi == null) {
                    		utils.warning(token.pos,"jml.not.strict","storeref with implied end-of-range: " + index);
                    	}
                      } 
                    t = to(jmlF.at(t.pos).Indexed(t, index));
                    nextToken();
                    continue;
//                } else if (!strictId && jmlTokenKind() == DOT_DOT) {
//                    nextToken();
//                    JCExpression hi = null;
//                    int rbracketPos = pos();
//                    if (token.kind == STAR) {
//                        nextToken();
//                    } else if (token.kind == RBRACKET) {
//                        if (JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
//                            utils.warning(rbracketPos,"jml.not.strict","storeref with implied end-of-range (a[i..])");
//                        }
//                        // OK - missing hi end implies end of array
//                    } else {
//                        hi = parseExpression();
//                    }
//                    if (token.kind == RBRACKET) {
//                        t = to(jmlF.at(t.pos).Indexed(t, jmlF.at(t.pos).JmlRange(lo, hi)));
//                        nextToken();
//                    } else {
//                        utils.error(pos(), endPos(), "jml.expected.rbracket");
//                        skipToCommaOrSemi();
//                        break;
//                    }
//                    continue;
                } else {
                    utils.error(pos(), endPos(),
                            "jml.invalid.expression.succeeding.token");
                    skipToCommaOrSemi();
                    break;
                }
            }
        }
        return t;
    }
    
    protected List<JCAnnotation> annotationsOpt(Tag kind) {
    	ListBuffer<JCAnnotation> annos = new ListBuffer<>();
    	//if (kind == Tag.TYPE_ANNOTATION)System.out.println("JML-ANNOTOPT-TOKEN " + token);
    	while (true) {
    		while (S.jml()) {
    			if (isStartJml(token)) { nextToken(); continue; }
    			var mm = Extensions.findKeyword(token);
    			if (!(mm instanceof ModifierKind m)) break;
    			//System.out.println("JML-ANNOTOPT " + m);
    			
    			JmlAnnotation t;
    			if (kind != Tag.TYPE_ANNOTATION) {
                    t = utils.modToAnnotationAST(m, token.pos, token.endPos);
    			} else {
    		        if (m.isTypeAnnotation()) {
                        JCExpression p = utils.nametree(token.pos, token.endPos, m.fullAnnotation, null);
    		            t = (JmlAnnotation)F.at(token.pos).TypeAnnotation(p,
    		                com.sun.tools.javac.util.List.<JCExpression> nil());
    		            t.kind = m;
    		        } else {
    		            utils.error(token.pos, "jml.message", "A " + m + " modifier is not allowed where type annotations are expected");
    		            t = null;
    		        }
    			}
    			if (t != null) annos.append(t);
    			nextToken();
    			acceptEndJML();
                //System.out.println("READ ANNOT " + token + " " + annos);
    		}
    		var lst = super.annotationsOpt(kind);
    		if (lst.isEmpty()) return annos.toList();
    		annos.appendList(lst);
            //System.out.println("JAVA ANNOT " + token + " " + annos); Utils.dumpStack();
    	}
    }
    
    public boolean isStartJml(Token token) {
        return token.ikind == JmlTokenKind.STARTJMLCOMMENT;
    }

    public boolean isEndJml(Token token) {
        return token.ikind == JmlTokenKind.ENDJMLCOMMENT;
        // jmlTokenClauseKind(token) == JmlOperatorKind.endjmlcommentKind
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
    public JCModifiers modifiersOpt() { // Overridden to make public
        return super.modifiersOpt();
    }

    @Override
    public JmlModifiers modifiersOpt(JCModifiers partial) {
        JmlModifiers mods = (JmlModifiers)(partial == null ? jmlF.at(Position.NOPOS).Modifiers(0L) : partial);
        while (true) {
            if (acceptStartJML()) {
                continue;
            } else if (acceptEndJML()) {
                continue;
            } else if (token.kind == TokenKind.CLASS) { // FIXME - record?
                break;
            } else if (token.kind == TokenKind.ENUM) {
                // Really the beginning of a declaration, but do need to set the flag
                mods.flags |= Flags.ENUM;
                break;
            } else if (token.kind == TokenKind.INTERFACE) {
                // Really the beginning of a declaration, but do need to set the flag
                mods.flags |= Flags.INTERFACE;
                break;
            } else if (S.jml() && isJmlModifier(token)) {
                ModifierKind mk = (ModifierKind)Extensions.findKeyword(token);
                JmlToken jt = new JmlToken(mk, token);
                jt.source = Log.instance(context).currentSourceFile();
                mods.jmlmods.add(jt);
                if (mods.pos == Position.NOPOS) {
                    mods.pos = token.pos;
                }
                if (!mk.strict && JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
                    utils.warning(jt.pos,"jml.not.strict",mk.keyword);
                }
//    	    } else if (token.kind == TokenKind.RPAREN || token.kind == TokenKind.RPAREN) {
//                // Unexpected -- and other closing punctuation
//                break;
//            } else if (token.kind == TokenKind.SEMI) {
//                // Empty statement -- should be no modifiers
//                break;
//            } else if (token.kind == TokenKind.EOF) {
//                // Unexpected end of file
            } else {
                var p = token.pos;
                boolean inJML = S.jml();
                var saved = mods.anyModsInJava;
                var jmods = mods.jmlmods;
                int q = mods.pos;
                mods = (JmlModifiers)super.modifiersOpt(mods);
                if (mods.pos == Position.NOPOS) mods.pos = q; // If the line above read nothing, it sets the position to NOPOS
                mods.jmlmods.addAll(0,jmods);
                if (p != token.pos) {
                    // read something
                    mods.anyModsInJava = saved || !inJML;
                    if (mods.pos == Position.NOPOS) mods.pos = p;
                    // already advanced
                    continue;
                } else {
                    mods.anyModsInJava = saved;
                    // nothing read -- so no more modifiers of any kind
                    while (acceptEndJML()) {}
                    break;
                }
            }
            nextToken();
        }
        int endp = mods.pos != Position.NOPOS ? S.prevToken().endPos: partial != null ? endPosTable.getEndPos(partial) : Position.NOPOS;
        storeEnd(mods, endp);
        return mods;
    }

//    public/* @ nullable */JCAnnotation tokenToAnnotationAST(String annName,
//            int position, int endpos) {
//    	return utils.tokenToAnnotationAST()
//        JCExpression t = utils.nametree(position,endpos,annName,this);
//        JCAnnotation ann = to(F.at(position).Annotation(t,
//                List.<JCExpression> nil()));
//        ((JmlTree.JmlAnnotation)ann).sourcefile = currentSourceFile();
//        storeEnd(ann, endpos);
//        return ann;
//    }
//
//    /**
//     * Reads any JML modifiers, combining them with the input to produce a new
//     * JCModifiers object
//     *
//     * @param partial
//     *            input modifiers and annotations
//     * @return combined modifiers and annotations
//     */
//    public JCModifiers jmlModifiersOpt(JCModifiers partial) {
//        ListBuffer<JCAnnotation> annotations = new ListBuffer<JCAnnotation>();
//        java.util.List<JmlToken> jmlmods = new java.util.LinkedList<JmlToken>();
//        if (partial != null) annotations.appendList(partial.annotations);
//        if (partial != null) jmlmods.addAll(((JmlModifiers)partial).jmlmods);
//        int pos = Position.NOPOS;
//        int last = Position.NOPOS;
//        if (partial != null) {
//            pos = partial.pos;
//        }
//        JCModifiers mods = jmlF.at(pos).Modifiers(
//                partial == null ? 0 : partial.flags, annotations.toList(), jmlmods);
//        while (isJmlModifier(token)) {
//        	last = endPos();
//        	ModifierKind mk = (ModifierKind)Extensions.findKeyword(token);
//        	JmlToken jt = new JmlToken(mk, token);
//        	jmlmods.add(jt);
//        	jt.source = Log.instance(context).currentSourceFile();
//        	JmlAnnotation a = JmlTreeUtils.instance(context).addAnnotation(mods, jt, this);
//        	if (a != null) {
//        		if (pos == Position.NOPOS) {
//        			pos = a.getStartPosition();
//        			mods.pos = pos;
//        		}
//        	}
//        	// a is null if no annotation is defined for the modifier;
//        	// we just silently ignore that situation
//        	// (this is true at the moment for math annotations, but could
//        	// also be true for a modifier someone forgot)
//        	if (!mk.strict && JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
//        		utils.warning(pos(),"jml.not.strict",mk.keyword);  // FIXME - probably wrong position
//        	}
//            nextToken();
//            //System.out.println("READ JML MOD " + a + " " + token);
//            acceptEndJML();
//            //System.out.println("READ JML MODIFIERS " + mods + " " + mods.annotations);
//        }
//        if (last != Position.NOPOS) storeEnd(mods, last);
//        return mods;
//    }

    @Override
    public JCPrimitiveTypeTree basicType() {
        JmlTokenKind jt = jmlTokenKind();
        if (jt == null) {
            return super.basicType();
        } else if (jt == JmlTokenKind.BSBIGINT
                ) {
            JCPrimitiveTypeTree t = to(jmlF.at(pos())
                    .JmlPrimitiveTypeTree(jt,null,null));
            nextToken();
            return t;
        } else if (jt == JmlTokenKind.PRIMITIVE_TYPE) {
            JCPrimitiveTypeTree t = to(jmlF.at(pos())
                    .JmlPrimitiveTypeTree(jt,null,ident()));
            nextToken();
            return t;
        } else {
            utils.error(pos(), endPos(), "jml.expected", "JML type token");
            JCPrimitiveTypeTree t = to(F.at(pos()).TypeIdent(
                    typetag(TokenKind.VOID)));
            nextToken();
            return t;
        }
    }

    public boolean underscoreOK = false;

    @Override
    public Name ident() {
    	if (possibleDotStar && token.kind == TokenKind.STAR) {
    		nextToken();
    		return null;
    	}
        if (token.kind == CUSTOM) {
            if (((JmlToken)token).jmlkind == JmlTokenKind.ENDJMLCOMMENT) {
                utils.error(pos(),endPos(),"jml.end.instead.of.ident");
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
    	JCExpression t;
    	if (inExprMode() && jmlTokenKind() == JmlTokenKind.DOT_DOT) {
        	t = null;
        	nextToken();
    	} else if (inExprMode() && token.kind == TokenKind.STAR) {
    		t = null;
        	int dotpos = pos();
        	nextToken();
        	if (jmlTokenKind() != JmlTokenKind.DOT_DOT) {
        		JmlPrimitiveTypes.rangeTypeKind.parse(null, null,JmlPrimitiveTypes.rangeTypeKind, this);
        		return jmlF.at(dotpos).JmlRange(null,null);
        	}
        } else {
            t = term1Cond();
        }
        if (inExprMode() && jmlTokenKind() == JmlTokenKind.DOT_DOT) {
        	int dotpos = pos();
        	nextToken();
        	JCExpression tt;
        	if (token.kind == TokenKind.STAR) {
        		tt = null;
        		nextToken();
        	} else if (token.kind == TokenKind.RBRACKET || token.kind == TokenKind.RPAREN) {
                if (JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
                	utils.warning(token.pos,"jml.not.strict","storeref with implied end-of-range");
                }
        		tt = null;
        	} else {
        	    tt = term1Cond();
        	}
        	JmlPrimitiveTypes.rangeTypeKind.parse(null, null, JmlPrimitiveTypes.rangeTypeKind, this);
        	return jmlF.at(dotpos).JmlRange(t,tt);
        } else {
            return t;
        }
    }

    protected JCExpression term1Cond() {
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
            if (t.ikind == JmlTokenKind.STARTJMLCOMMENT) {
                t = S.token(2);
            }
            if (t.ikind == BSBIGINT) return ParensResult.CAST;
            if (t.kind == TokenKind.IDENTIFIER) {
                IJmlClauseKind ck = Extensions.findKeyword(t);
                if (ck instanceof JmlTypeKind) return ParensResult.CAST;
                if (ck instanceof IJmlClauseKind.TypeAnnotationKind) return ParensResult.CAST;
                if (t.name().charAt(0) == '\\') return ParensResult.PARENS;
            }
        }
        return super.analyzeParens();
    }

    protected ParensResult analyzeParensHelper(Token t, ParensResult defaultResult) {
    	if (t.kind == TokenKind.EQ) return ParensResult.PARENS;
    	if (t.kind == TokenKind.SEMI) return ParensResult.PARENS;
    	if (t.kind == TokenKind.COMMA) return ParensResult.PARENS;
    	if (t.kind == TokenKind.RPAREN) return ParensResult.PARENS;
        if (!(t instanceof JmlToken)) return defaultResult;
        IJmlClauseKind jtk = ((JmlToken)t).jmlclausekind;
        switch (jtk.keyword()) {
            case impliesID: case reverseimpliesID: case equivalenceID: case inequivalenceID: case subtypeofID: case subtypeofeqID:
            case jsubtypeofID: case jsubtypeofeqID: case dotdotID: case leftarrowID: case lockleID: case lockltID:
                return ParensResult.PARENS;
            default:
                return ParensResult.CAST;
        }
    }

//    protected ParensResult analyzeParensHelper2(int lookahead, Token t, ParensResult defaultResult) {
//        if (!(t instanceof JmlToken)) return defaultResult;
//        JmlTokenKind jtk = ((JmlToken)t).jmlkind;
//        switch (jtk) {
//            case BSTYPEUC: case BSREAL: case BSBIGINT: case ENDJMLCOMMENT:
//                if (peekToken(lookahead, RPAREN)) {
//                    //Type, ')' -> cast
//                    return ParensResult.CAST;
//                } else if (peekToken(lookahead, LAX_IDENTIFIER)) {
//                    //Type, Identifier/'_'/'assert'/'enum' -> explicit lambda
//                    return ParensResult.EXPLICIT_LAMBDA;
//                }
//                return ParensResult.PARENS;
//            default:
//                return defaultResult;
//        }
//    }
    
    public boolean inTypeMode() {
    	return (mode & TYPE) != 0;
    }


    public boolean inExprMode() {
    	return (mode & EXPR) != 0;
    }


    @Override
    public JCExpression term3() {
        List<JCExpression> typeArgs = null;
        int p = pos(); // Position of the keyword
        while (isStartJml(token)) nextToken();
        if (token.kind == IDENTIFIER) {
        	// FIXME - generally handle backslash type identifiers; verify type or expression
            String id = token.name().toString();
            if (id.charAt(0) == '\\') {
                IJmlClauseKind kind = Extensions.findKeyword(token);
                if (kind == null) { // and we have a leading \
                	// This branch should not happen as an error should have been reported in JmlTokenizer
                    utils.error(p, endPos(), "jml.message", "Unknown backslash identifier: " + id + ". Known tokens: " + Extensions.allKinds.keySet());
                    return jmlF.at(p).Erroneous();
                } else if (kind instanceof IJmlClauseKind.SingletonKind) {
                	return (JCExpression)kind.parse(null, id, kind, this);
                } else if (kind instanceof org.jmlspecs.openjml.ext.JmlPrimitiveTypes.JmlTypeKind tk) {
                    if (peekToken(t -> t == TokenKind.DOT)) {
                        JCExpression eee = toP(super.term3());
                        return eee;
                    }
                    if (!inTypeMode() && inExprMode()) {
                        utils.error(token.pos, "jml.message", "Expected an expression here, not a type");
                        nextToken();
                        return jmlF.at(p).Erroneous();
                    }
                    var typeexpr = tk.parse(null, id, kind, this);
                    typeexpr = bracketsSuffix(bracketsOpt(typeexpr));
                    return typeexpr;
                } else if (inExprMode() && kind instanceof IJmlClauseKind.ExpressionKind ek) {
                	JCExpression tt = ek.parse(null, id, kind, this);
                	return term3Rest(tt, typeArgs);
                } else if (inTypeMode() && kind == MiscExpressions.typelcKind && kind instanceof IJmlClauseKind.ExpressionKind ek) {
                	JCExpression tt = ek.parse(null, id, kind, this);
                	return term3Rest(tt, typeArgs);
                } else if (inTypeMode()) {
                	utils.error(p, endPos(), "jml.message",
                			"Token " + id + " is not a type");
                	return jmlF.at(p).Erroneous();
                } else {
                	utils.error(p, endPos(), "jml.message",
                			"Token " + id + " does not introduce an expression");
                	return jmlF.at(p).Erroneous();
                }
            }
        }
        // No JML function expects type arguments. If they did we would parse
        // them here (before seeing the JML token). But we can't do that just
        // to check, because super.term3() down below expects to parse them
        // itself. So if someone does write type arguments for a JML function
        // the code will fall into the super.term3() call and the token will not
        // be recognized - no chance for a nice error message.
        if (token.toString().contains("real")) {
            System.out.println("REAL? " + token + " " + jmlTokenKind() + " " + jmlTokenClauseKind());
        }
        if (token.kind == CUSTOM || jmlTokenKind() == JmlTokenKind.PRIMITIVE_TYPE) {
            JCExpression t;
            JmlTokenKind jt = jmlTokenKind();
            if (isJmlType(token)) {
                String n = jt.internedName();
                t = to(jmlF.at(p).JmlPrimitiveTypeTree(jt, null, names.fromString(n)));
                nextToken();
                // Could be just a type value
                if (token.kind == TokenKind.DOT || token.kind == TokenKind.LBRACKET) {
                    t = bracketsSuffix(bracketsOpt(t));
                }
                return t;
            }
            switch (jt) {
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
                            return term3Rest(tt, typeArgs);
                        } else {
                            utils.error(p, endPos(), "jml.message",
                                    "Token " + token + " does not introduce an expression");
                            return jmlF.at(p).Erroneous();
                        }
                    } else {
                        String id = token instanceof JmlToken ? ((JmlToken)token).jmlkind.internedName() : token.toString();
                        if (id.equals("match")) {
                            return null; // FIXME new MatchExt(context).parse(this, typeArgs);
                        } else {
                            utils.error(p, endPos(), "jml.bad.type.expression",
                                    "( token " + token
                                    + " in JmlParser.term3())");
                            return jmlF.at(p).Erroneous();
                        }
                    }
                }
            }
        }
        if (S.jml() && token.kind == TokenKind.LBRACE) {
            accept(LBRACE);
            JCExpression jmltype = parseType();
            accept(RBRACE);
            skipThroughEndOfJML(); // FIXME - should just be the end of JML
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
            // This code is modified from super.term3 in order to
            // parse tuples
            JCExpression t = null;
        	java.util.List<JCExpression> tuple;
            int pos = token.pos;
            if (inExprMode()) {
                ParensResult pres = analyzeParens();
                switch (pres) {
                case CAST:
                	
                	// FIXME - fit in casting to intersection type  
                    int pos0 = pos;
                    accept(LPAREN);
                    selectTypeMode();
                    tuple = new java.util.LinkedList<>();
                    int pos1 = pos;
                    List<JCExpression> targets = List.of(t = parseType());
                    while (token.kind == AMP) {
                        accept(AMP);
                        targets = targets.prepend(parseType());
                    }
                    if (targets.length() > 1) {
                        t = toP(F.at(pos1).TypeIntersection(targets.reverse()));
                    }
                    accept(RPAREN);
                    selectExprMode();
                    JCExpression t1 = term3();
                    return toP(F.at(pos0).TypeCast(t, t1));
                case IMPLICIT_LAMBDA:
                case EXPLICIT_LAMBDA:
                    t = lambdaExpressionOrStatement(true, pres == ParensResult.EXPLICIT_LAMBDA, pos);
                    break;
                case PARENS:
//                    accept(LPAREN);
//                    selectExprMode();
//                    t = termRest(term1Rest(term2Rest(term3(), TreeInfo.orPrec)));
//                    accept(RPAREN);
//                    t = toP(F.at(pos).Parens(t));
                    accept(LPAREN);
                    selectExprMode();
                    tuple = new java.util.LinkedList<>();
                    t = termRest(term1Rest(term2Rest(term3(), TreeInfo.orPrec)));
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
                    t = term3Rest(t, null);
                    break;
                default:
                	// FIXME - unexpected character
                    break;
                }
                return term3Rest(t, typeArgs);
            }
        }
        if (S.jml() && token.kind == THIS && parsingLocationList) {
            if ((mode & EXPR) != 0) {
                selectExprMode();
                JCExpression t = to(F.at(token.pos).Ident(names._this));
                nextToken();
                if (typeArgs == null)
                    t = argumentsOpt(null, t);
                else
                    t = arguments(typeArgs, t);
                typeArgs = null;
                if (token.kind != DOT) {
                    utils.error(p, "jml.naked.this.super");
                    return t;
                } else if (S.token(1).kind == STAR) {
                	t = F.at(token.pos).Select(t, (Name)null);
                    accept(DOT);
                    accept(STAR);
                    if (token.kind == DOT || token.kind == LBRACKET) { // expected token: ; ) = ,
                        utils.error(pos(), endPos(), "jml.not.after.star");
                        skipToCommaOrSemi();
                    }
                	return t;
                } else if (S.token(1).kind != IDENTIFIER) {
                    utils.error(pos(), endPos(),
                            "jml.ident.or.star.after.dot");
                	accept(DOT);
                	return t;
                }
                return term3Rest(t, typeArgs);
            }
        }
        if (S.jml() && token.kind == SUPER && parsingLocationList) {
            if ((mode & EXPR) != 0) {
                selectExprMode();
                JCExpression t = to(F.at(token.pos).Ident(names._super));
                if (S.token(1).kind != DOT) {
                    utils.error(token.pos, "jml.naked.this.super");
                	nextToken();
                    return t;
                } else if (S.token(2).kind == STAR) {
                	nextToken();
                	t = F.at(token.pos).Select(t, (Name)null);
                    accept(DOT);
                    accept(STAR);
                    if (token.kind == DOT || token.kind == LBRACKET) { // expected token: ; ) = ,
                        utils.error(pos(), endPos(), "jml.not.after.star");
                        skipToCommaOrSemi();
                    }
                    // FIXME - does not allow the typeargs as in superSuffix()
                	return t;
                } else if (S.token(2).kind != IDENTIFIER) {
                	nextToken(); // accept super
                    utils.error(pos(), endPos(),
                            "jml.ident.or.star.after.dot");
                	accept(DOT);
                	return t;
                }
                t = superSuffix(typeArgs, t); // accepts the 'super' token
                typeArgs = null;
                return term3Rest(t, typeArgs);
            }
        }
        var saved = possibleDotStar;
        possibleDotStar = true;
        try {
            int sp = pos();
        	JCExpression eee = toP(super.term3());
        	if (eee instanceof JCErroneous && sp == pos()) {
        	    // Bad expression. Advance to avoid repeating errors at the same point
        	    nextToken();
        	}
        	return eee;
        } finally {
        	possibleDotStar = saved;
        }
    }
    
    public boolean possibleDotStar = false;

    /** Public wrapper for the benefit of extension clients */
    public JCExpression primaryTrailers(JCExpression t, List<JCExpression> typeArgs) {
        return term3Rest(t, typeArgs);
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



//    protected boolean inCreator = false;


//    // MAINTENANCE ISSUE:
//    // This is a copy from JavacParser, so we can add in parseSetComprehension
//    JCExpression creator(int newpos, List<JCExpression> typeArgs) {
//        List<JCAnnotation> newAnnotations = typeAnnotationsOpt();
//
//        switch (token.kind) {
//            case BYTE:
//            case SHORT:
//            case CHAR:
//            case INT:
//            case LONG:
//            case FLOAT:
//            case DOUBLE:
//            case BOOLEAN:
//                if (typeArgs == null) {
//                    if (newAnnotations.isEmpty()) {
//                        return arrayCreatorRest(newpos, basicType());
//                    } else {
//                        return arrayCreatorRest(newpos, toP(F.at(newAnnotations.head.pos).AnnotatedType(newAnnotations, basicType())));
//                    }
//                }
//                break;
//            default:
//        }
//        JCExpression t = qualident(true);
//        int oldmode = mode;
//        mode = TYPE;
//        boolean diamondFound = false;
//        int lastTypeargsPos = -1;
//        if (token.kind == LT) {
//            checkGenerics();
//            lastTypeargsPos = token.pos;
//            t = typeArguments(t,true);
//            diamondFound = (mode & DIAMOND) != 0;
//        }
//        while (token.kind == DOT) {
//            if (diamondFound) {
//                // cannot select after diamond
//                illegal();
//            }
//            int pos = token.pos;
//            nextToken();
//            List<JCAnnotation> tyannos = typeAnnotationsOpt();
//            t = toP(F.at(pos).Select(t, ident()));
//
//            if (tyannos != null && tyannos.nonEmpty()) {
//                t = toP(F.at(tyannos.head.pos).AnnotatedType(tyannos, t));
//            }
//
//            if (token.kind == LT) {
//                checkGenerics();
//                lastTypeargsPos = token.pos;
//                t = typeArguments(t,true);
//                diamondFound = (mode & DIAMOND) != 0;
//            }
//        }
//        mode = oldmode;
//        if (token.kind == LBRACKET || token.kind == MONKEYS_AT) {
//            // handle type annotations for non primitive arrays
//            if (newAnnotations.nonEmpty()) {
//                t = insertAnnotationsToMostInner(t, newAnnotations, false);
//            }
//
//            JCExpression e = arrayCreatorRest(newpos, t);
//            if (diamondFound) {
//                reportSyntaxError(lastTypeargsPos, "cannot.create.array.with.diamond");
//                return toP(F.at(newpos).Erroneous(List.of(e)));
//            }
//            if (typeArgs != null) {
//                int pos = newpos;
//                if (!typeArgs.isEmpty() && typeArgs.head.pos != Position.NOPOS) {
//                    // note: this should always happen but we should
//                    // not rely on this as the parser is continuously
//                    // modified to improve error recovery.
//                    pos = typeArgs.head.pos;
//                }
//                setErrorEndPos(S.prevToken().endPos);
//                JCErroneous err = F.at(newpos).Erroneous(typeArgs.prepend(e));
//                reportSyntaxError(err, "cannot.create.array.with.type.arguments");
//                return toP(err);
//            }
//            return e;
//        } else if (token.kind == LPAREN) {
//          boolean prev = inLocalOrAnonClass;
//          inLocalOrAnonClass = true;
//          try {
//            JCNewClass newClass = classCreatorRest(newpos, null, typeArgs, t);
//            if (newClass.def != null) {
//                assert newClass.def.mods.annotations.isEmpty();
//                if (newAnnotations.nonEmpty()) {
//                    newClass.def.mods.pos = earlier(newClass.def.mods.pos, newAnnotations.head.pos);
//                    newClass.def.mods.annotations = newAnnotations;
//                }
//            } else {
//                // handle type annotations for instantiations
//                if (newAnnotations.nonEmpty()) {
//                    t = insertAnnotationsToMostInner(t, newAnnotations, false);
//                    newClass.clazz = t;
//                }
//            }
//            return newClass;
//          } finally {
//                inLocalOrAnonClass = prev;
//          }
//        } else if (token.kind == LBRACE) {
//            return parseSetComprehension(t);
//        } else {
//            syntaxError(pos(), null, "expected3", "\'(\'", "\'{\'", "\'[\'");
//            t = toP(F.at(newpos).NewClass(null, typeArgs, t,
//                    List.<JCExpression> nil(), null));
//            return toP(F.at(newpos).Erroneous(List.<JCTree> of(t)));
//        }
//    }

    @Override
    protected JCExpression moreCreator(Token token, JCExpression type) {
        if (token.kind == LBRACE) return parseSetComprehension(type);
        else return null;
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

    // FIXME - move this to extensions?
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

    // FIXME - move this to extensions?
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

    /** Overridden in order to absorb the pushBackModifiers and to insert any replacement types */
    @Override
    public <T extends ListBuffer<? super JCVariableDecl>> T variableDeclarators(
            JCModifiers mods, JCExpression type, T vdefs, boolean localDecl) {
//    	// FIXME - in what circumstances are the pushback modifiers needed?
//        if (pushBackModifiers != null && isNone(mods)) {
//            mods = pushBackModifiers;
//            pushBackModifiers = null;
//        }
        T list = super.variableDeclarators(mods,type,vdefs,localDecl);
        if (replacementType != null) {
            for (Object decl: list) insertReplacementType(decl,replacementType);
            replacementType = null;
        }
        return list;
    }

    @Override
    public <T extends ListBuffer<? super JCVariableDecl>> T variableDeclaratorsRest( // FIXME - does this need to be public
            int pos, JCModifiers mods, JCExpression type, Name name,
            boolean reqInit, Comment dc, T vdefs, boolean localDecl) {
        // Fields in interfaces are required to be explicitly initialized
        // But not ghost fields in JML -- this is checked in more detail in type
        // checking, but here we just allow no initializer
        if (S.jml()) reqInit = false;
        type = normalizeAnnotations(mods, type);
        var r = super.variableDeclaratorsRest(pos, mods, type, name, reqInit,
                dc, vdefs, localDecl);
        return r;
    }

    @Override
    public JCExpression variableInitializer() {
        return super.variableInitializer();
    }

    /**
     * This is overridden to assign JML operators the right precedence
     */
    protected int prec(ITokenKind token) {
        if (token instanceof JmlTokenKind) {
            return jmlPrecedence((JmlTokenKind)token);
        }
        return precFactor*super.prec(token);
    }

    public static final int precFactor = 1;

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
                return -1000; // Forces an end to all expressions
            default:
                return -10000; // Lower than all other precedences - Forces an end to all expressions
        }
    }

    public static int jmlPrecedence(IJmlClauseKind tkind) {
        switch (tkind.keyword()) {
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
    
    // MAINTENANCE ISSUE - (Almost) Duplicated from JavacParser.java in order to accommodate precedence of JML tokens
    JCExpression term2() {
        JCExpression t = term3();
        if ((mode & EXPR) != 0 && prec(token.ikind) >= precFactor*TreeInfo.orPrec) {
            selectExprMode();
            return term2Rest(t, TreeInfo.orPrec);
        } else {
            return t;
        }
    }


    // MAINTENANCE ISSUE - (Almost) Duplicated from JavacParser.java in order to accommodate precedence of JML tokens
    JCExpression term2Rest(JCExpression t, int minprec) {
        JCExpression[] odStack = newOdStack();
        Token[] opStack = newOpStack();

        // optimization, was odStack = new Tree[...]; opStack = new Tree[...];
        int top = 0;
        odStack[0] = t;
        int startPos = token.pos;
        Token topOp = Tokens.DUMMY;
        while (prec(token.ikind) >= minprec) { // OPENJML
            opStack[top] = topOp;

            if (token.kind == INSTANCEOF) {
                int pos = token.pos;
                nextToken();
                JCTree pattern;
                if (token.kind == LPAREN) { 
                    checkSourceLevel(token.pos, Feature.PATTERN_SWITCH);
                    pattern = parsePattern(token.pos, null, null, false, false);
                } else {
                    int patternPos = token.pos;
                    JCModifiers mods = optFinal(0);
                    int typePos = token.pos;
                    JCExpression type = unannotatedType(false);
                    if (token.kind == IDENTIFIER) {
                        checkSourceLevel(token.pos, Feature.PATTERN_MATCHING_IN_INSTANCEOF);
                        pattern = parsePattern(patternPos, mods, type, false, false);
                    } else if (token.kind == LPAREN) {
                        pattern = parsePattern(patternPos, mods, type, false, false);
                    } else if (token.kind == UNDERSCORE) {
                        checkSourceLevel(token.pos, Feature.UNNAMED_VARIABLES);
                        pattern = parsePattern(patternPos, mods, type, false, false); 
                    } else {
                        checkNoMods(typePos, mods.flags & ~Flags.DEPRECATED);
                        if (mods.annotations.nonEmpty()) {
                            List<JCAnnotation> typeAnnos =
                                    mods.annotations
                                        .map(decl -> {
                                            JCAnnotation typeAnno = F.at(decl.pos)
                                                                     .TypeAnnotation(decl.annotationType,
                                                                                      decl.args);
                                            endPosTable.replaceTree(decl, typeAnno);
                                            return typeAnno;
                                        });
                            type = insertAnnotationsToMostInner(type, typeAnnos, false);
                        }
                        pattern = type;
                    }
                }
                odStack[top] = F.at(pos).TypeTest(odStack[top], pattern);
            } else {
                topOp = token;
                nextToken();
                top++;
                odStack[top] = term3();
            }
            int p;
            while (top > 0 && (p=prec(topOp.ikind)) >= prec(token.ikind)) {  // OPENJML
                odStack[top - 1] = makeOp(topOp.pos, topOp, odStack[top - 1], odStack[top]); // OPENJML
                top--;
                topOp = opStack[top];
                if (p == precFactor*TreeInfo.ordPrec && prec(token.ikind) < precFactor*TreeInfo.ordPrec) {
                	odStack[top] = chain(odStack[top]);
                }
            }
        }
        Assert.check(top == 0);
        t = odStack[0];

        if (t.hasTag(JCTree.Tag.PLUS)) {
            t = foldStrings(t);
        }

        odStackSupply.add(odStack);
        opStackSupply.add(opStack);
        return t;
    }
    
//    protected JCExpression term2Rest(JCExpression tt, int minprec) {
//        boolean bad = tt instanceof JCErroneous;
//        JCExpression t = tt;
//        JCExpression[] odStack = newOdStack();
//        Token[] opStack = newOpStack();
//
//        // optimization, was odStack = new Tree[...]; opStack = new Tree[...];
//        int top = 0;
//        odStack[0] = t;
//        Token topOp = Tokens.DUMMY;
//        while (prec(S.token().ikind) >= precFactor*minprec) { // FIXME - lookahead token - presumes scanner is just one token ahead
//            opStack[top] = topOp;
//            top++;
//            topOp = S.token();
//            nextToken(); // S.jmlToken() changes
//            odStack[top] = (topOp.kind == INSTANCEOF) ? parseType() : term3();
//            // odStack[top] is the next argument; token is the operator after that, as in [topOp] arg [token]
//            // if the precedence of [topOp] is lower than the precedence of [token] we have to read more before constructing expressions
//            int p;
//            while (top > 0 && (p=prec(topOp.ikind)) >= prec(token.ikind)) {
//            	var e = makeOp(topOp.pos, topOp, odStack[top - 1], odStack[top]);
//            	storeEnd(e, getEndPos(odStack[top]));
//            	odStack[top - 1] = e;
//                top--;
//                topOp = opStack[top];
//                if (p == precFactor*TreeInfo.ordPrec && prec(token.ikind) < precFactor*TreeInfo.ordPrec) {
//                    odStack[top] = chain(odStack[top]);
//                }
//            }
//        }
//        odStack[top] = chain(odStack[top]);
//
//        Assert.check(top == 0);
//        t = odStack[0];
//
//        if (t.hasTag(JCTree.Tag.PLUS)) {
//            t = foldStrings(t);
//// FIXME: The following code is present in JavacParser.term2Rest. However, it turns noinn-string
//// string expressions into string expressions. Can't be correct.
////            if (t != null) {
////                t = toP(F.at(startPos).Literal(TypeTag.CLASS, t.toString()));
////            }
//        }
//
//        odStackSupply.add(odStack);
//        opStackSupply.add(opStack);
//        if (bad) return tt;
//        return t;
//    }

    /** Creates a Java or JML binary operation, without type information */
    protected JCExpression makeOp(int pos,
            Token opToken,
            JCExpression od1,
            JCExpression od2)
    {
        if (opToken.kind == CUSTOM) { // <:
            IJmlClauseKind ck = jmlTokenClauseKind(opToken);
            JCExpression e = jmlF.at(pos).JmlBinary(ck, od1, od2);
            storeEnd(e, getEndPos(od2));
            return e;
        } else {
            return super.makeOp(pos, opToken, od1, od2);
        }
    }

    /** Convert an expression to a JmlChained expression, if it is one */
    public JCExpression chain(JCExpression e) {
        JCExpression fe = e;
        if (!(fe instanceof JCBinary)) return fe;
        JCBinary be = (JCBinary)e;
        JCTree.Tag tag = be.getTag();
        if (tag == JCTree.Tag.LT || tag == JCTree.Tag.LE) {
            ListBuffer<JCBinary> args = new ListBuffer<JCBinary>();
            while (true) {
                args.prepend(be);
                fe = be.lhs;
                if (!(fe instanceof JCBinary)) break;
                be = (JCBinary)fe;
                tag = be.getTag();
                if (!(tag == JCTree.Tag.LT || tag == JCTree.Tag.LE)) {
                    if (tag == JCTree.Tag.GT || tag == JCTree.Tag.GE) {
                        utils.error(be.pos,"jml.message","Cannot chain comparisons that are in different directions");
                    } else {
                        break;
                    }
                }
                args.first().lhs = be.rhs;
            }
            if (args.size() == 1) return e;
            e = jmlF.at(e.pos).JmlChained(args.toList());
            return e;
        } else if (tag == JCTree.Tag.GT || tag == JCTree.Tag.GE) {
            ListBuffer<JCBinary> args = new ListBuffer<JCBinary>();
            while (true) {
                args.prepend(be);
                fe = be.lhs;
                if (!(fe instanceof JCBinary)) break;
                be = (JCBinary)fe;
                tag = be.getTag();
                if (!(tag == JCTree.Tag.GT || tag== JCTree.Tag.GE)) {
                    if (tag == JCTree.Tag.LT || tag == JCTree.Tag.LE) {
                        utils.error(be.pos,"jml.message","Cannot chain comparisons that are in different directions");
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
     * Skips up to a EOF or up to and including a ENDJMLCOMMENT or right brace
     */
    public void skipThroughRightBrace() {
        while (token.kind != RBRACE && token.kind != EOF
                && jmlTokenKind() != JmlTokenKind.ENDJMLCOMMENT)
            nextToken();
        if (token.kind != EOF) nextToken();
    }

    /** Skips through an ENDJMLCOMMENT token, or up to EOF; 
     * used to recover from a parsing error in a JML comment */
    public void skipThroughEndOfJML() {
        while (token.ikind != ENDJMLCOMMENT && token.kind != EOF)
            nextToken();
        S.setJml(false); // Shouldn't the scanner set this appropriately?
        inJmlDeclaration = false;
        while (token.ikind == ENDJMLCOMMENT) nextToken();
    }
    
    /** Call this method wherever end-of-jml-comments are allowed; they need not be required.
     * For example, call at the end of a JML statement or clause in case it is the last one,
     * but it is allowed to combine multiple consecutive statements into a single comment, so
     * an end-of-jml marker is not required.
     */
    public boolean acceptEndJML() {
    	if (token.ikind != ENDJMLCOMMENT) return false;
    	while (token.ikind == ENDJMLCOMMENT) {
    		nextToken();
    	}
    	return true;
    }

    public boolean acceptStartJML() {
    	if (token.ikind != STARTJMLCOMMENT) return false;
    	nextToken();
    	return true;
        //while (jmlTokenClauseKind() == JmlOperatorKind.endjmlcommentKind) nextToken(); // FIXME - replace using this
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
        reportSyntaxError(pos, utils.errorKey(key, args));
        return toP(F.at(pos).Erroneous(errs));
    }

    // Just to make the visibility public
    public List<JCTypeParameter> typeParametersOpt() {
        return super.typeParametersOpt();
    }

    // Just to make the visibility public
    public void storeEnd(JCTree tree, int endpos) {
       super.storeEnd(tree, endpos);
    }

    // Just to make the visibility public
    public <T extends JCTree> T to(T t) {
        return super.to(t);
    }

    // Just to make the visibility public
    public <T extends JCTree> T toP(T t) {
        return super.toP(t);
    }



    // FIXME - check the use of Token.CUSTOM vs. null
    // FIXME - review the remaining uses of log.error vs. jmlerror
    // FIXME - refactor to better match the grammar as a top-down parser
    // FIXME - refactor for extension
    // FIXME - need to sort out the various modes - isJml isJmlDeclaration isLocalOrAnonClass...
}
