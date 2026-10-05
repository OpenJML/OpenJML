/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.code.Kinds.*;
import static com.sun.tools.javac.parser.Tokens.TokenKind.COLON;
import static com.sun.tools.javac.parser.Tokens.TokenKind.COMMA;
import static com.sun.tools.javac.parser.Tokens.TokenKind.RPAREN;
import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTree.JmlModifiers;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCInstanceOf;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCTypeCast;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.LetExpr;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

public class QuantifiedExpressions extends JmlExtension {

    public static class QuantifiedExpression extends IJmlClauseKind.ExpressionKind {
        public QuantifiedExpression(String keyword) { super(keyword); }

        @Override
        public JCExpression parse(JCModifiers mods, String keyword,
                IJmlClauseKind clauseType, JmlParser parser) {
            int pos = parser.pos();
            parser.nextToken();
            mods = parser.modifiersOpt();
            JCExpression t = parser.parseType(mods.annotations.isEmpty(), mods.annotations);
            if (t.getTag() == JCTree.Tag.ERRONEOUS) return t;
            if (mods.pos == -1) {
                mods.pos = t.pos; // set the beginning of the modifiers
                parser.storeEnd(mods,t.pos);
            }
                                                  // modifiers
            // to the beginning of the type, if there
            // are no modifiers
            ListBuffer<JCVariableDecl> decls = new ListBuffer<JCVariableDecl>();
            int idpos = parser.pos();
            Name id = parser.ident(); // FIXME JML allows dimensions after the ident
            decls.append(parser.toP(parser.maker().at(idpos).VarDef(mods, id, t, null)));
            while (parser.token().kind == COMMA) {
                parser.nextToken();
                idpos = parser.pos();
                id = parser.ident(); // FIXME JML allows dimensions after the ident
                decls.append(parser.toP(parser.maker().at(idpos).VarDef(mods, id, t, null)));
            }
            if (parser.token().kind != SEMI) {
                error(parser.context, parser.pos(), parser.endPos(), "jml.expected.semicolon.quantified");
                int p = parser.pos();
                parser.skipThroughRightParen();
                return parser.toP(parser.maker().at(p).Erroneous());
            }
            parser.nextToken();
            JCExpression range = null;
            JCExpression pred = null;
            if (parser.token().kind == SEMI) {
                // type id ; ; predicate
                // two consecutive semicolons is allowed, and means the
                // range is 'true' - continue
                parser.nextToken();
                pred = parser.parseExpression();
            } else {
                range = parser.parseExpression();
                if (parser.token().kind == SEMI) {
                    // type id ; range ; predicate
                    parser.nextToken();
                    pred = parser.parseExpression();
                } else if (parser.token().kind == RPAREN || parser.token().kind == COLON) {
                    // type id ; predicate
                    pred = range;
                    range = null;
                } else {
                    error(parser.context, parser.pos(), parser.endPos(),
                            "jml.expected.semicolon.quantified");
                    int p = parser.pos();
                    parser.skipThroughRightParen();
                    return parser.toP(parser.maker().at(p).Erroneous());
                }
            }
            List<JCExpression> triggers = null;
            if (parser.token().kind == COLON) {
                parser.accept(COLON);
                // triggers
                if (parser.token().kind != RPAREN) {
                    triggers = parser.parseExpressionList();
                }
            }
            JmlQuantifiedExpr q = parser.toP(parser.maker().at(pos).JmlQuantifiedExpr(this, decls.toList(),
                    range, pred));
            q.triggers = triggers;
            return parser.primaryTrailers(q, null); // FIXME - was primarySuffix
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> env) {
            com.sun.tools.javac.code.Symtab syms = attr.syms;
            JmlQuantifiedExpr that = (JmlQuantifiedExpr)tree;
            Env<AttrContext> localEnv = attr.envForExpr(that,env);
            
//            boolean b = ((JmlMemberEnter)attr.memberEnter).setInJml(true);
            for (JCVariableDecl decl: that.decls) {
                JmlModifiers mods = (JmlModifiers)decl.getModifiers();
                if (attr.utils.hasOnly(mods,0)!=0) Log.instance(attr.context).error(mods.pos,"jml.no.java.mods.allowed","quantified expression", TreeInfo.flagNames(mods.flags));
                attr.attribAnnotationTypes(mods.annotations,env);
                attr.annotationsToModifiers(mods, mods.annotations);
                attr.allAllowed(mods, attr.typeModifiers, "quantified expression");
//                if (utils.hasAny(mods,Flags.STATIC)) {
//                    log.error(that.pos,
//                            "mod.not.allowed.here", asFlagSet(Flags.STATIC));
//                }
//                //if (Resolve.isStatic(env)) mods.flags |= Flags.STATIC;  // FIXME - this is needed for variables declared in quantified expressions in invariants - will need to ignore this when pretty printing?
                attr.memberEnter.memberEnter(decl, localEnv);
                decl.type = decl.vartype.type; // FIXME not sure this is needed
                attr.localVariables.add(decl.sym);
            }
//            ((JmlMemberEnter)attr.memberEnter).setInJml(b);
            attr.quantifiedExprs.add(that);
            
            if (that.triggers != null && that.triggers.size() > 0) {
            	if (that.kind != qforallKind && that.kind != qexistsKind ) {
                    Utils.instance(attr.context).warning(that.triggers.get(0),"jml.message","Triggers only recognized in \\forall or \\exists quantified expressions");
                    that.triggers = null;
            	} else {
            		for (var t: that.triggers) t.type = attr.attribExpr(t, localEnv, Type.noType);
                    // FIXME - need to check well-formedness of triggers
            	}
            }
            Type resultType = syms.errType;
            Type valueType = null;
            var M = attr.jmlMaker;
            try {
                
                if (that.range != null) {
                	that.range.type = attr.attribExpr(that.range, localEnv, syms.booleanType);
                    attr.check(that.range, that.range.type, KindSelector.VAL, attr.new ResultInfo(KindSelector.VAL, syms.booleanType));
                }

                switch (this.keyword()) {
                    case qexistsID:
                    case qforallID:
                        valueType = syms.booleanType;
                        resultType = syms.booleanType;
                        break;

                    case qchooseID: {
                        valueType = syms.booleanType;
                        resultType = that.decls.head.type;
                        if (that.decls.tail.nonEmpty()) {
                            error(attr.context, that.decls.tail.head, "jml.message", "A \\choose quantifier may have only one variable declaration");
                        }
                        String tmpname = Strings.genPrefix + "found$" + that.pos;
                        that.founddef = (JmlVariableDecl)M.at(that).VarDef(M.at(that).Modifiers(0),attr.names.fromString(tmpname), 
                                    M.at(that).TypeIdent(TypeTag.BOOLEAN), attr.treeutils.falseLit);
                        attr.attribStat(that.founddef, localEnv);
                        break;
                    }
                    
                    case qchoosexID: {
                        // TODO -= check for strictness
                        valueType = Type.noType;
                        resultType = Type.noType;
                        strictCheck(attr.context, that,"\\choosex expression");
                        if (that.decls.tail.nonEmpty()) {
                            error(attr.context, that.decls.tail.head, "jml.message", "A \\choosex quantifier may have only one variable declaration");
                        }
                        if (that.value == null) {
                            error(attr.context, that, "jml.message", "A \\choosex xquantifier must have a value expression");
                        }
                        String tmpname = Strings.genPrefix + "found$" + that.pos;
                        that.founddef = (JmlVariableDecl)M.at(that).VarDef(M.at(that).Modifiers(0),attr.names.fromString(tmpname), 
                                    M.at(that).TypeIdent(TypeTag.BOOLEAN), attr.treeutils.falseLit);
                        attr.attribStat(that.founddef, localEnv);
                        break;
                    }

                    case qnumofID:
                        valueType = syms.booleanType;
                        resultType = JmlPrimitiveTypes.bigintTypeKind.getType(attr.context);
                        if (Utils.instance(attr.context).rac) resultType = syms.longType; // FIXME - or BigInteger
                        break;

                    case qmaxID:
                    case qminID:
                    	valueType = Type.noType;
                        resultType = that.value.type;
                        // FIXME - allow this for any Comparable type
                        //                if (!types.unboxedTypeOrType(resultType).isNumeric()) {
                        //                    log.error(that.value,"jml.internal", "The value expression of a sum or product expression must be a numeric type, not " + resultType.toString());
                        //                    resultType = types.createErrorType(resultType);
                        //                }
                        break;

                    case qsumID:
                    case qproductID:
                    	valueType = Type.noType;
                        resultType = that.value.type;
                        break;

                    default:
                        error(attr.context, that,"jml.unknown.construct", this.keyword(),"JmlAttr.visitJmlQuantifiedExpr");
                        break;
                }
                if (that.value != null) {
                    attr.attribExpr(that.value, localEnv, valueType);
                    if (valueType == Type.noType) resultType = that.value.type;
                    attr.check(that.value, that.value.type, KindSelector.VAL, attr.new ResultInfo(KindSelector.VAL, valueType));
                    if (keyword().equals(qsumID) || keyword().equals(qproductID)) {
                        if (!attr.jmltypes.isNumeric(attr.jmltypes.unboxedTypeOrType(resultType))) {
                            error(attr.context, that.value,"jml.bad.quantifer.expression", resultType.toString());
                            resultType = attr.jmltypes.createErrorType(resultType);
                        }
                    }
                }

                resultType = attr.check(that, resultType, KindSelector.VAL, attr.resultInfo);

                if (attr.utils.esc && (keyword().equals(qforallID) || keyword().equals(qexistsID))
                        && (that.triggers == null || that.triggers.isEmpty())) {
                    warnIfNoTrigger(attr, that, env);
                }

                if (attr.utils.rac) {
                    Type saved = resultType;
                    try {
                        if (that.racexpr == null) attr.createRacExpr(that,localEnv,resultType);
                    } finally {
                        resultType = saved;
                    }
                }
            } finally {
                attr.quantifiedExprs.remove(attr.quantifiedExprs.size()-1);
                localEnv.info.scope().leave();
                for (JCVariableDecl decl: that.decls) {
                    attr.localVariables.remove(decl.sym);
                }

            }
            if (that.range != null && that.range.type.isErroneous()) resultType = that.type = that.range.type;
            return resultType;
        }

    };

    /** Warns (once per quantifier) when some bound variable of a \\forall or \\exists that has no
     * explicit trigger occurs only in arithmetic, comparisons and logical operations. Such a
     * quantifier offers the SMT solver no term to use as a trigger for that variable, so the solver
     * either ignores the quantifier or uses an arithmetic term as a trigger, which can make it
     * instantiate the quantifier without end (issue #997). A term that can serve as a trigger is
     * a method call (a function in the SMT translation), an array or field access, or an integer
     * division or remainder by a non-constant value (which are uninterpreted functions in
     * quantifier bodies). Quantifiers in library specifications are not checked. */
    static void warnIfNoTrigger(JmlAttr attr, JmlQuantifiedExpr that, Env<AttrContext> env) {
        if (env.enclClass == null || env.enclClass.sym == null) return;
        var classfile = env.enclClass.sym.classfile;
        if (classfile == null || classfile.getKind() != javax.tools.JavaFileObject.Kind.SOURCE) return;
        var bound = new java.util.HashSet<Symbol>();
        for (JCVariableDecl d: that.decls) if (d.sym != null) bound.add(d.sym);
        var occurring = new java.util.LinkedHashSet<Symbol>();
        var covered = new java.util.HashSet<Symbol>();
        // A \\let variable stands for its initializer (the SMT translation substitutes it), so a
        // trigger term mentioning it covers the bound variables its initializer mentions
        var letVars = new java.util.HashMap<Symbol, java.util.Set<Symbol>>();
        var scanner = new JmlTreeScanner() {
            int inTrigger = 0; // > 0 when inside a term that can serve as a trigger
            java.util.Set<Symbol> mentioned = null; // when non-null, collects the bound variables a \\let initializer mentions
            @Override
            public void visitIdent(JCIdent id) {
                var syms = bound.contains(id.sym) ? java.util.Set.of(id.sym) : letVars.get(id.sym);
                if (syms == null) return;
                if (mentioned != null) mentioned.addAll(syms);
                occurring.addAll(syms);
                if (inTrigger > 0) covered.addAll(syms);
            }
            @Override
            public void visitLetExpr(LetExpr let) {
                for (JCStatement def: let.defs) {
                    if (def instanceof JCVariableDecl d) {
                        var prev = mentioned;
                        mentioned = new java.util.HashSet<>();
                        try {
                            scan(d.init);
                            letVars.put(d.sym, mentioned);
                        } finally {
                            if (prev != null) prev.addAll(mentioned);
                            mentioned = prev;
                        }
                    } else {
                        scan(def);
                    }
                }
                scan(let.expr);
            }
            void trigger(Runnable r) {
                inTrigger++;
                try { r.run(); } finally { inTrigger--; }
            }
            @Override
            public void visitApply(JCMethodInvocation t) { trigger(() -> super.visitApply(t)); }
            @Override
            public void visitIndexed(JCArrayAccess t) { trigger(() -> super.visitIndexed(t)); }
            @Override
            public void visitSelect(JCFieldAccess t) { trigger(() -> super.visitSelect(t)); }
            @Override
            public void visitTypeTest(JCInstanceOf t) { trigger(() -> super.visitTypeTest(t)); }
            @Override
            public void visitBinary(JCBinary t) {
                // integer / and % by a non-constant are uninterpreted functions in a quantifier body; real ones are arithmetic
                if ((t.hasTag(JCTree.Tag.DIV) || t.hasTag(JCTree.Tag.MOD)) && t.type != null
                        && attr.jmltypes.isAnyIntegral(t.type) && !isConstant(t.rhs)) {
                    trigger(() -> super.visitBinary(t));
                } else {
                    super.visitBinary(t);
                }
            }
        };
        scanner.scan(that.range);
        scanner.scan(that.value);
        occurring.removeAll(covered);
        // The solver eliminates a variable v that is equated to a term not mentioning v, so v needs
        // no trigger: v == e as a conjunct of the range, or (for \\exists) of the value
        var conjuncts = new java.util.ArrayList<JCExpression>();
        addConjuncts(that.range, conjuncts);
        if (that.kind == qexistsKind) addConjuncts(that.value, conjuncts);
        for (JCExpression c: conjuncts) {
            if (c instanceof JCBinary b && b.hasTag(JCTree.Tag.EQ)) {
                for (var sides: java.util.List.of(java.util.List.of(b.lhs, b.rhs), java.util.List.of(b.rhs, b.lhs))) {
                    if (TreeInfo.skipParens(sides.get(0)) instanceof JCIdent id && bound.contains(id.sym)
                            && !mentions(sides.get(1), id.sym)) occurring.remove(id.sym);
                }
            }
        }
        if (occurring.isEmpty()) return;
        String key = env.toplevel.sourcefile.getName() + ":" + that.pos;
        if (!attr.quantifierTriggerWarnings.add(key)) return;
        String names = occurring.stream().map(sym -> sym.name.toString()).collect(java.util.stream.Collectors.joining(", "));
        attr.utils.warning(that, "jml.message",
                "No term in this quantified expression can serve as an SMT trigger for " + names
                + ": it is used only in arithmetic, comparisons or logical operations, so the solver may"
                + " not use the quantifier, or may instantiate it without end; consider stating the"
                + " property with a model function or pure method");
    }

    /** Adds to list the top-level conjuncts of e (nothing if e is null) */
    static void addConjuncts(JCExpression e, java.util.List<JCExpression> list) {
        if (e == null) return;
        e = TreeInfo.skipParens(e);
        if (e instanceof JCBinary b && b.hasTag(JCTree.Tag.AND)) {
            addConjuncts(b.lhs, list);
            addConjuncts(b.rhs, list);
        } else {
            list.add(e);
        }
    }

    /** Whether e mentions the variable sym */
    static boolean mentions(JCExpression e, Symbol sym) {
        boolean[] found = { false };
        new JmlTreeScanner() {
            @Override
            public void visitIdent(JCIdent id) { if (id.sym == sym) found[0] = true; }
        }.scan(e);
        return found[0];
    }

    /** Whether e is a constant: a literal or a compile-time constant, possibly negated or cast */
    static boolean isConstant(JCExpression e) {
        e = TreeInfo.skipParens(e);
        if (e instanceof JCLiteral) return true;
        if (e.type != null && e.type.constValue() != null) return true;
        if (e instanceof JCTypeCast c) return isConstant(c.expr);
        if (e instanceof JCUnary u && u.hasTag(JCTree.Tag.NEG)) return isConstant(u.arg);
        return false;
    }

    public static final String qforallID = "\\forall";
    public static final IJmlClauseKind qforallKind = new QuantifiedExpression(qforallID);
    public static final String qexistsID = "\\exists";
    public static final IJmlClauseKind qexistsKind = new QuantifiedExpression(qexistsID);
    public static final String qchooseID = "\\choose";
    public static final IJmlClauseKind qchooseKind = new QuantifiedExpression(qchooseID);
    public static final String qchoosexID = "\\choosex";
    public static final IJmlClauseKind qchoosexKind = new QuantifiedExpression(qchoosexID);
    public static final String qnumofID = "\\num_of";
    public static final IJmlClauseKind qnumofKind = new QuantifiedExpression(qnumofID);
    public static final String qsumID = "\\sum";
    public static final IJmlClauseKind qsumKind = new QuantifiedExpression(qsumID);
    public static final String qproductID = "\\product";
    public static final IJmlClauseKind qproductKind = new QuantifiedExpression(qproductID);
    // maxKind is not final because there are two uses of \max -- MiscExpressions disambiguates
    // but we can't have both of them being registered
    public static final String qmaxID = "\\max";
    public static       IJmlClauseKind qmaxKind = new QuantifiedExpression(qmaxID);
    public static final String qminID = "\\min";
    public static final IJmlClauseKind qminKind = new QuantifiedExpression(qminID);
    public static final String letID = "\\let";
    public static final IJmlClauseKind letKind = new QuantifiedExpression(letID) {
        
        public JCExpression parse(JCModifiers mods, String keyword,
                IJmlClauseKind clauseType, JmlParser parser) {
            ListBuffer<JCTree.JCStatement> vdefs = new ListBuffer<>();
            int pos = parser.pos(); // Position of keyword
            parser.nextToken(); // advance over keyword
            if (mods != null) {
            	Log.instance(parser.context).error(pos,"jml.internal.notsobad","Parse routine for \\let does not expect modifiers to be already parsed");
            }
            do {
                mods = parser.modifiersOpt();
                //Utils.instance(parser.context).setJML(mods);
                if (Utils.instance(parser.context).hasMod(mods, Modifiers.MODEL, Modifiers.GHOST)) {
                	Utils.instance(parser.context).error(Log.instance(parser.context).currentSourceFile(),mods.pos,"jml.message","ghost or model modifiers not permitted on an expression-local declaration");
                }
                int declpos = parser.pos(); // beginning of type
                JCExpression type = parser.parseType(mods.annotations.isEmpty(), mods.annotations);
                if (mods.pos == -1) {
                	mods.pos = declpos; // In case the mods are empty
                	parser.storeEnd(mods,declpos);
                }
                int p = parser.pos(); // beginning of name
                Name name = parser.ident();
                JCVariableDecl decl = parser.variableDeclaratorRest(p,mods,type,name,true,null,true,false);
                if (decl.init == null) parser.toP(decl);
                vdefs.add(decl);
                if (parser.token().kind != COMMA) break;
                parser.accept(COMMA);
            } while (true);
            parser.accept(SEMI);
            JCExpression expr = parser.parseExpression();
            LetExpr r = parser.jmlF.at(pos).JmlLetExpr(vdefs.toList(),expr,true);
            wrapup(parser, r, clauseType, false, false);
            return r;
        }
    };
}

