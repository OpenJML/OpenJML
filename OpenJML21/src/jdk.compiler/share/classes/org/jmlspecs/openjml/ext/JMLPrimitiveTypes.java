package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

public class JMLPrimitiveTypes extends JmlExtension {
    Context context;
    
    public JMLPrimitiveTypes(Context context) {
        this.context = context;
        stringTypeKind.initType(context);
    }
	
	public static class JmlTypeKind extends IJmlClauseKind {
		public String typename; // expected to be in org.jmlspecs.lang
		public com.sun.tools.javac.util.Name name;
		Type type = null; // lazily filled in; depends on context; only  implemented for a single context
		Type repType = null;
        Context context = null; // context for type -- need even though it shadows IJmlClauseKind.context
		
		public JmlTypeKind(String keyword, String typename) {
			super(keyword);
			this.typename = typename;
		}
		
		public void initType(Context context) { this.context = context; }
		
		public int numTypeArguments() { return 0; }
		
		public Type getType(Context context) {
			// Caching the type (which depends on context) for general use
			if (type == null || context != this.context) {
				this.context = context;
                JCExpression id = JmlTree.Maker.instance(context).QualIdent("org","jmlspecs","lang",typename);
                type = JmlAttr.instance(context).attribType(id, JmlEnter.instance(context).tlenv); // FIXME - this should be improved (and tlenv removed)
                id = JmlTree.Maker.instance(context).QualIdent("org","jmlspecs","lang",typename);
                repType = JmlAttr.instance(context).attribType(id, JmlEnter.instance(context).tlenv); // FIXME - this should be improved (and tlenv removed)
                this.name = Names.instance(context).fromString(typename);
			}
			return type;
		}
		
		public Type getRepType(Context context) {
		    getType(context);
		    return repType;
		}

		@Override
		public JCExpression parse(JCModifiers mods, String keyword, IJmlClauseKind clauseKind, JmlParser parser) {
            init(parser);
            if (name == null) name = parser.names.fromString(typename);
            JCIdent id = parser.maker().at(parser.pos()).Ident(keyword);
            int p = parser.pos();
            int ep = parser.endPos();
            parser.nextToken();
            if (parser.token().kind == TokenKind.LPAREN) { 
                utils.error(p, ep, "jml.message",
                            "An ill-formed type");
                parser.nextToken();
                return null;
            } else {
                JCExpression t = parser.typeArgumentsOpt(id);
                return t;
            }
		}
		@Override
		public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> env) {
			return null;
		}
	}
	
    public static final String seqId = "\\seq";

    public static final JmlTypeKind seqTypeKind = new JmlTypeKind(seqId,"seq") {
        @Override
        public int numTypeArguments() { return 1; }
    };

    public static final String setId = "\\set";

    public static final JmlTypeKind setTypeKind = new JmlTypeKind(setId,"set") {
        @Override
        public int numTypeArguments() { return 1; }
    };

    public static final String mapId = "\\map";

    public static final JmlTypeKind mapTypeKind = new JmlTypeKind(mapId,"map") {
        @Override
        public int numTypeArguments() { return 2; }
    };

    public static final String stringId = "\\string";

    public static final JmlTypeKind stringTypeKind = new JmlTypeKind(stringId,"string") {
        @Override
        public int numTypeArguments() { return 0; }

        public Type getType(Context context) {
            var t = super.getType(context);
            JmlTypes.instance(context).enterBinop("+", t, t, t);
            return t;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> env) {
            if (tree instanceof JmlTree.JmlVariableDecl vd) {
                if (vd.init == null) test(vd.init.type, attr, tree);
            } else if (tree instanceof JCTree.JCTypeCast tc) {
                test(tc.expr.type, attr, tree);
            } else if (tree instanceof JCTree.JCAssign as) {
                test(as.rhs.type, attr, tree);
            } else if (tree instanceof JCTree.JCAssignOp asop) {
                test(asop.rhs.type, attr, tree);
            }
            return null;
        }
        
        private void test(Type t, JmlAttr attr, DiagnosticPosition p) {
            JmlTypes types = JmlTypes.instance(context);
            if (types.isSameType(t, stringTypeKind.type) || types.isSameType(t, attr.syms.stringType)) return;
            utils.error(p, "jml.message", "Cannot convert " + t + "to \string");
        }

//        public void initType(Context context) {
//            Type t = getType(context);
//            JmlTypes.instance(context).enterBinop("+", t, t, t);
//        }
    };
    

	
	public static final String rangeID = "\\range";
	
	public static final JmlTypeKind rangeTypeKind = new JmlTypeKind(rangeID, "range") {
        @Override
        public int numTypeArguments() { return 0; }
		@Override
		public JCExpression parse(JCModifiers mods, String keyword, IJmlClauseKind clauseKind, JmlParser parser) {
			init(parser);
			return null;
		}
	};

	public static final String locsetId = "\\locset";

	public static final JmlTypeKind locsetTypeKind = new JmlTypeKind(locsetId,"locset") {
        @Override
        public int numTypeArguments() { return 0; }
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
				var list = parser.parseExpressionList();
				if (parser.token().kind != TokenKind.RPAREN) {
					utils.error(p, ep, "jml.message",
							"Either an ill-formed expression or missing right-parenthesis");
				} else {
					parser.nextToken();
				}
				JmlStoreRef sr = JmlTreeUtils.instance(parser.context).makeLocsetLiteral(list.head);
				return sr;
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
				System.out.println("TYPECHECKED " + tree + " AS " + type);
				return type;
			}
			// FIXME - internal error
			return null;
		}
	};

	
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
