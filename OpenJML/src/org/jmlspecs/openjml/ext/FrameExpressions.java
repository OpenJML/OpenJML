/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.code.Kinds.TYP;
import static com.sun.tools.javac.code.Kinds.VAL;
import static org.jmlspecs.openjml.JmlTokenKind.BSPRE;
import static org.jmlspecs.openjml.ext.RequiresClause.requiresClauseKind;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlDefinitions;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.Attr.ResultInfo;
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
public class FrameExpressions implements JmlDefinitions {

    
    public static class FrameExpression extends IJmlClauseKind.Expression {
        public FrameExpression(String keyword) { super(keyword); }
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
            JmlMethodInvocation t = toP(parser.maker().at(pp).JmlMethodInvocation(jt, args));
            t.startpos = p;
            t.kind = this;
            return parser.primarySuffix(t, null);
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            syms = Symtab.instance(context);
            JmlMethodInvocation tree = (JmlMethodInvocation)that;
            ListBuffer<Type> argtypesBuf = new ListBuffer<>();
            attr.attribArgs(VAL, tree.args, localEnv, argtypesBuf);
            if (!attr.postClauses.contains(attr.currentClauseType)) {
                log.error(tree.pos, "jml.misplaced.token", tree.kind != null ? tree.kind.name() : tree.token.internedName(), attr.currentClauseType == null ? "jml declaration" : attr.currentClauseType.name());
            }
            return attr.syms.booleanType;
        }

    };

    public static final String onlyAssignedID = "\\only_assigned";
    public static final IJmlClauseKind onlyAssignedKind = new FrameExpression(onlyAssignedID);
    public static final String onlyAccessedID = "\\only_accessed";
    public static final IJmlClauseKind onlyAccessedKind = new FrameExpression(onlyAccessedID);
    public static final String onlyCapturedID = "\\only_captured";
    public static final IJmlClauseKind onlyCapturedKind = new FrameExpression(onlyCapturedID);
    public static final String notAssignedID = "\\not_assigned";
    public static final IJmlClauseKind notAssignedKind = new FrameExpression(notAssignedID);

    public static final String onlyCalledID = "\\only_called";
    public static final IJmlClauseKind onlyCalledKind = new FrameExpression(onlyCalledID) {
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
            List<JmlTree.JmlMethodSig> args = parser.parseMethodNameList();
            // FIXME - not implemented
            return toP(parser.maker().at(p).Erroneous());
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            syms = Symtab.instance(context);
            JmlMethodInvocation tree = (JmlMethodInvocation)that;
// FIXME - needs implementation
//            ListBuffer<Type> argtypesBuf = new ListBuffer<>();
//            attr.attribArgs(VAL, tree.args, localEnv, argtypesBuf);
            if (!attr.postClauses.contains(attr.currentClauseType)) {
                log.error(tree.pos+1, "jml.misplaced.token", tree.token.internedName(), attr.currentClauseType == null ? "jml declaration" : attr.currentClauseType.name());
            }
            return attr.syms.booleanType;
        }


    };

}

