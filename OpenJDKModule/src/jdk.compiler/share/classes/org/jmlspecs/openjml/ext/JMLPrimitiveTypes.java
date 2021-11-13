package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.ext.MiscExtensions.NoTypeMisc;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Kinds.KindSelector;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Enter;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.Attr.ResultInfo;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Names;

public class JMLPrimitiveTypes extends JmlExtension {
	
	abstract public static class JmlTypeKind extends IJmlClauseKind {
		public String typename; // expected to be in org.jmlspecs.lang
		Type type = null; // lazily filled in; depends on context; only  implemented for a single context
		
		public JmlTypeKind(String keyword, String typename) {
			super(keyword);
			this.typename = typename;
		}
		
		Type getType(Env<AttrContext> env) {
			if (type == null) {
				JCIdent id = JmlTree.Maker.instance(context).Ident(Names.instance(context).fromString(typename));
				type = JmlAttr.instance(context).attribType(id, env);
			}
			return type;
		}

		@Override
		public JCExpression parse(JCModifiers mods, String keyword, IJmlClauseKind clauseKind, JmlParser parser) {
			return null;
		}

		public static final String locsetId = "\\locset";
		
		public static final JmlTypeKind locsetType = new JmlTypeKind(locsetId,"locset") {
			@Override
			public JCExpression parse(JCModifiers mods, String keyword, IJmlClauseKind clauseKind, JmlParser parser) {
				// TODO Auto-generated method stub
				init(parser);
				JCIdent id = parser.maker().at(parser.pos()).Ident(keyword);
				int p = parser.pos();
				int ep = parser.endPos();
				parser.nextToken();
				if (parser.token().kind == TokenKind.LPAREN) { 
					if (!parser.inExprMode()) {
						utils.error(p, ep, "jml.message",
								"Did not expect a \\locset expression here");
						// But go on to treat it like a function-like expression
					}
					parser.nextToken();
					var list = parser.parseStoreRefList();
					if (parser.token().kind != TokenKind.RPAREN) {
						utils.error(p, ep, "jml.message",
								"Either an ill-formed expression or missing right-parenthesis");
					} else {
						parser.nextToken();
					}
					JmlMethodInvocation app = parser.maker().at(p).JmlMethodInvocation(id, list.toList());
					app.kind = clauseKind;
					return app;
				} else {
					if (!parser.inTypeMode()) {
						utils.error(p, ep, "jml.message",
								"Did not expect a type identifier here");
						// But go on to treat it like an identifier
					}
					return id;
				}
			}

			@Override
			public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> env) {
				if (tree instanceof JmlMethodInvocation) {
					var app = (JmlMethodInvocation)tree;
					app.args.stream().forEach(t -> {
						attr.attribExpr(t, env, Type.noType);
						if (t instanceof JCTree.JCFieldAccess) {}
						else if (t instanceof JCTree.JCArrayAccess) {}
						else if (t instanceof JCTree.JCIdent) {}
						else if (t instanceof JmlTree.JmlStoreRefArrayRange) {}
						else if (t instanceof JmlTree.JmlSingleton && ((JmlTree.JmlSingleton)t).kind instanceof LocSet) {}
						else utils.error(t.pos(), "jml.message", "Only location expressions may be arguments to \\locset: " + t + " (" + t.getClass() + ")");
					});
					JCIdent id = JmlTree.Maker.instance(attr.context).Ident(Names.instance(attr.context).fromString(typename));
					type = attr.attribType(id, env);
					tree.type = type;
					((JCIdent)app.meth).sym = id.sym;
					((JCIdent)app.meth).type = id.type; // FIXME - or should be a method type?
					return type;
				}
				// FIXME - internal error
				return null;
			}
		};

	}
	
    public static class LocSet extends IJmlClauseKind.SingletonKind {
        public LocSet(String name) { super(name); }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            return Type.noType; // FIXME - fix this
        }
    };

    public static final String nothingID = "\\nothing";
    public static final IJmlClauseKind nothingKind = new LocSet(nothingID);
    
    public static final String everythingID = "\\everything";
    public static final IJmlClauseKind everythingKind = new LocSet(everythingID);
    

}
