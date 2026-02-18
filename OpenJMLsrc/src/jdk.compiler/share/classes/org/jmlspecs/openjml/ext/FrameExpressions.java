/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.code.Kinds.*;
import static com.sun.tools.javac.code.Kinds.Kind.*;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;

public class FrameExpressions extends JmlExtension {

    public static class FrameExpression extends IJmlClauseKind.ExpressionKind {
        public FrameExpression(String keyword) { super(keyword); }
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
            JmlMethodInvocation t = toP(parser.maker().at(pp).JmlMethodInvocation(jt, args));
            t.startpos = p;
            t.kind = this;
            return parser.primaryTrailers(t, null); // FIXME - was perimarySUffix
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            JmlMethodInvocation tree = (JmlMethodInvocation)that;
            ListBuffer<Type> argtypesBuf = new ListBuffer<>();
            attr.attribArgs(KindSelector.VAL, tree.args, localEnv, argtypesBuf);
            if (!attr.postClauses.contains(attr.jmlenv.currentClauseKind)) {
                log.error(tree.pos, "jml.misplaced.token", tree.kind != null ? tree.kind.keyword() : "?", attr.jmlenv.currentClauseKind == null ? "jml declaration" : attr.jmlenv.currentClauseKind.keyword());
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
            parser.nextToken();
            if (parser.token().kind != TokenKind.LPAREN) {
                return parser.syntaxError(p, null, "jml.args.required", keyword());
//            } else if (typeArgs != null && !typeArgs.isEmpty()) {
//                return parser.syntaxError(p, null, "jml.no.typeargs.allowed", jt.internedName());
            }
            int pp = parser.pos();
            List<JmlTree.JmlMethodSig> args = parseMethodNameList();
            // FIXME - not implemented
            return toP(parser.maker().at(p).Erroneous());
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            JmlMethodInvocation tree = (JmlMethodInvocation)that;
// FIXME - needs implementation
//            ListBuffer<Type> argtypesBuf = new ListBuffer<>();
//            attr.attribArgs(VAL, tree.args, localEnv, argtypesBuf);
            if (!attr.postClauses.contains(attr.jmlenv.currentClauseKind)) {
                log.error(tree.pos+1, "jml.misplaced.token", tree.kind.keyword(), attr.jmlenv.currentClauseKind == null ? "jml declaration" : attr.jmlenv.currentClauseKind.keyword());
            }
            return attr.syms.booleanType;
        }
    };
}

