/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static org.jmlspecs.openjml.JmlTokenKind.BSPRE;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

/** This class handles expression extensions that take an argument list of JCExpressions.
 * Even if there are constraints on the number of arguments, it
 * is more robust to accept all of them and then issue an error in the typechecker
 * if the number of arguments is wrong.
 * 
 * @author David Cok
 *
 */// TODO: This extension is inappropriately named at present.  However, I expect that this 
// extension will be broken into individual extensions when type checking and
// RAC and ESC translation are added.
public class StateExpressions extends ExpressionExtension {

    public StateExpressions(Context context) {
        super(context);
    }

    public static class StateExpression extends IJmlClauseKind.ExpressionKind {
        public StateExpression(String keyword) { super(keyword); }
        @Override
        public JCExpression parse(JCModifiers mods, String keyword,
                IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            int p = parser.pos();
            JmlTokenKind jt = parser.jmlTokenKind();
            parser.nextToken();
            if (parser.token().kind != TokenKind.LPAREN) {
                return parser.syntaxError(p, null, "jml.args.required", name());
//            } else if (typeArgs != null && !typeArgs.isEmpty()) {
//                return parser.syntaxError(p, null, "jml.no.typeargs.allowed", jt.internedName());
            }
            int pp = parser.pos();
            List<JCExpression> args = parser.arguments();
            JmlMethodInvocation t = toP(parser.maker().at(pp).JmlMethodInvocation(this, args));
            t.startpos = p;
            t.token = jt;
            return parser.primarySuffix(t, null);
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            syms = attr.syms;
            JmlMethodInvocation tree = (JmlMethodInvocation)that;
            Name savedLabel = attr.currentEnvLabel;
            int n = tree.args.size();
            if (!(n == 1 || (tree.token != JmlTokenKind.BSPRE && n == 2))) {
                if (tree.token != JmlTokenKind.BSPRE) log.error(tree.pos(),"jml.wrong.number.args",name(),
                        "1 or 2",n);
                else log.error(tree.pos(),"jml.one.arg",name(),
                        n);
            }
            IJmlClauseKind currentClauseType = attr.currentClauseType;
            Type t = null;
            if (tree.token == BSPRE) {
                // pre
                if (!currentClauseType.preAllowed()) {
                    log.error(tree.pos+1, "jml.misplaced.old", "\\pre token", currentClauseType.name());
                    t = syms.errType;
                }
            } else if (n == 1) {
                // old with no label
                if (attr.currentClauseType == null) {
                    // OK
                } else if (!currentClauseType.oldNoLabelAllowed() && currentClauseType != MethodSimpleClauseExtensions.declClause) {
                    log.error(tree.pos+1, "jml.misplaced.old", "\\old token with no label", currentClauseType.name());
                    t = syms.errType;
                } else if (currentClauseType == MethodSimpleClauseExtensions.declClause && localEnv.enclMethod == null) {
                    log.error(tree.pos+1, "jml.misplaced.old", "\\old token with no label", currentClauseType.name());
                    t = syms.errType;
                }
            } else {
                // old with label
                if (!currentClauseType.preOrOldWithLabelAllowed() && currentClauseType != MethodSimpleClauseExtensions.declClause) {
                    attr.log.error(tree.pos+1, "jml.misplaced.old", "\\old token with a label", currentClauseType.name());
                    t = syms.errType;
                } else if (currentClauseType == MethodSimpleClauseExtensions.declClause && localEnv.enclMethod == null) {
                    attr.log.error(tree.pos+1, "jml.misplaced.old", "\\old token with a label", currentClauseType.name());
                    t = syms.errType;
                }
            }
            Name label = null;
            JCExpression labelarg = null;
            if (n == 2) {
                labelarg = tree.args.get(1);
                label = attr.checkLabel(labelarg);
                if (label == null) {
                    t = syms.errType;
                }
            }
            
            // FIXME - is it possible for a variable to have a different type at a previous label?
            
            // label == empty ==> pre state; label == null ==> current state
            attr.currentEnvLabel = label == null ? attr.names.empty : label;
            if (n == 0 || t == syms.errType) {
                t = syms.errType;
            } else if (localEnv.enclMethod == null) { // FIXME - what about types declared within methods
                // In an type clause
                attr.attribExpr(tree.args.get(0), localEnv, Type.noType);
                attr.attribTypes(tree.typeargs, localEnv);
                t = tree.args.get(0).type;
            } else {
                // in a method clause
                Env<AttrContext> oldenv = attr.envForLabel(labelarg, label, attr.savedMethodClauseOutputEnv);
                
                Env<AttrContext> qOldEnv = oldenv;
                for (JmlQuantifiedExpr qexpr: attr.quantifiedExprs) {

                    qOldEnv = attr.envForExpr(qexpr,qOldEnv);
                    Scope enclScope = attr.enter.enterScope(qOldEnv);

                    for (JCVariableDecl decl: qexpr.decls) {

                        // FIXME - do we need to do these checks?
//                        if (chk.checkUnique(tree.pos(), v, enclScope)) {
//                            chk.checkTransparentVar(tree.pos(), v, enclScope);
                            enclScope.enter(decl.sym);
//                        }
                    }
                }
                attr.attribExpr(tree.args.get(0), qOldEnv, Type.noType);
                attr.attribTypes(tree.typeargs, qOldEnv);
                t = tree.args.get(0).type;
                Scope scope = qOldEnv.info.scope();
                for (JmlQuantifiedExpr qexpr: attr.quantifiedExprs) {
                    scope = scope.leave();
                }
            }
            attr.currentEnvLabel = savedLabel;
            return t;
        }

    };

    public static final String oldID = "\\old";
    public static final IJmlClauseKind oldKind = new StateExpression(oldID);
    public static final String preID = "\\pre";
    public static final IJmlClauseKind preKind = new StateExpression(preID);
    public static final String pastID = "\\past";
    public static final IJmlClauseKind pastKind = new StateExpression(pastID);

    // FIXME - eventually remove these
    
    public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> localEnv) {
        return null;
    }

    @Override
    public void checkParse(JmlParser parser, JmlMethodInvocation e) {
        // TODO Auto-generated method stub
        
    }
}

