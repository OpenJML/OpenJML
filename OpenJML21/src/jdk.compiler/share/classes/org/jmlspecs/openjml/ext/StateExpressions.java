/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Scope.WriteableScope;
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
public class StateExpressions extends JmlExtension {

    public static class StateExpression extends IJmlClauseKind.ExpressionKind {
        public StateExpression(String keyword) { super(keyword); }
        @Override
        public JCExpression parse(JCModifiers mods, String keyword,
                IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            int p = parser.pos();
            var jt = parser.jmlTokenClauseKind();
            parser.nextToken();
            if (parser.token().kind != TokenKind.LPAREN) {
                return parser.syntaxError(p, null, "jml.args.required", keyword());
//            } else if (typeArgs != null && !typeArgs.isEmpty()) {
//                return parser.syntaxError(p, null, "jml.no.typeargs.allowed", jt.internedName());
            }
            int pp = parser.pos();
            List<JCExpression> args = parser.arguments();
            JmlMethodInvocation t = toP(parser.maker().at(pp).JmlMethodInvocation(this, args));
            t.startpos = p;
            t.kind = jt;
            return parser.primaryTrailers(t, null); // FIXME - was primarySuffix
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            JmlMethodInvocation tree = (JmlMethodInvocation)that;
            attr.jmlenv = attr.jmlenv.pushCopy();
            IJmlClauseKind clauseKind = attr.jmlenv.currentClauseKind;
            Type t = attr.syms.errType;
            Name label = null;
            int n = tree.args.size();
            if (!(n == 1 || (tree.kind != preKind && n == 2))) {
                if (tree.kind != preKind) error(tree,"jml.wrong.number.args",keyword(),
                        "1 or 2",n);
                else error(tree,"jml.one.arg",keyword(), n);
            } else if (tree.kind == preKind) {
                // pre
                if (!clauseKind.preAllowed()) {
                    log.error(tree.pos+1, "jml.misplaced.old", "\\pre token", clauseKind.keyword());
                } else {
                	label = attr.preLabel;
                	t = null;
                }
            } else if (n == 1) {
                // old with no label
                if (clauseKind == null) {
                    // OK
                	t = null;
                } else if (!clauseKind.oldNoLabelAllowed() && clauseKind != MethodSimpleClauseExtensions.declClause) {
                    log.error(tree.pos+1, "jml.misplaced.old", "\\old token with no label", clauseKind.keyword());
                } else if (clauseKind == MethodSimpleClauseExtensions.declClause && localEnv.enclMethod == null) {
                    log.error(tree.pos+1, "jml.misplaced.old", "\\old token with no label", clauseKind.keyword());
                } else {
                	label = attr.oldLabel;
                	t = null;
                }
            } else {
                // old with label
                if (!clauseKind.preOrOldWithLabelAllowed() && clauseKind != MethodSimpleClauseExtensions.declClause) {
                    log.error(tree.pos+1, "jml.misplaced.old", "\\old token with a label", clauseKind.keyword());
                } else if (clauseKind == MethodSimpleClauseExtensions.declClause && localEnv.enclMethod == null) {
                    log.error(tree.pos+1, "jml.misplaced.old", "\\old token with a label", clauseKind.keyword());
                } else {
                	label = attr.checkLabel(tree.args.get(1));
                	if (label != null) t = null;
                }
            }
            if (label == attr.hereLabel) label = null;
            if (label == attr.oldLabel) label = attr.jmlenv.currentOldLabel;

            //System.out.println("OLD " + label + " " + attr.jmlenv.currentOldLabel + " " + that);
            
            // FIXME - it is possible for a variable to have a different type at a previous label?
            
            // label == null ==> current state (Here)
            attr.jmlenv.currentLabel = label;
            if (t == null) {
            	if (localEnv.enclMethod == null) {
            		// In a type clause
            	} else if (clauseKind instanceof IJmlClauseKind.MethodSpecClauseKind) {
            		// In a specification case
            		// FIXME - need to distinguish beginning of spec case from current position
            	} else {
            		// In a method body
            		localEnv = attr.envForLabel(n==1?tree:tree.args.get(1), label, localEnv);
            	}
        		attr.attribExpr(tree.args.get(0), localEnv, Type.noType);
        		attr.attribTypes(tree.typeargs, localEnv);
        		t = tree.args.get(0).type;
            }
            attr.jmlenv = attr.jmlenv.pop();
            return t;
        }

    };

    public static final String oldID = "\\old";
    public static final IJmlClauseKind oldKind = new StateExpression(oldID);
    public static final String preID = "\\pre";
    public static final IJmlClauseKind preKind = new StateExpression(preID);
    public static final String pastID = "\\past";
    public static final IJmlClauseKind pastKind = new StateExpression(pastID);
}

