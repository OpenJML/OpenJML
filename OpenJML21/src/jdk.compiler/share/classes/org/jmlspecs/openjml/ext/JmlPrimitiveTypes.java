package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.visitors.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.parser.JmlFactory;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

public class JmlPrimitiveTypes extends JmlExtension {
//    Context context;
//    
//    public JmlPrimitiveTypes(Context context) {
//        this.context = context;
//    }
    public JmlPrimitiveTypes(Context context) {
        // FIXME - why is this called so many times
        // And why do we have to clear a type to get it to reload its operators for a new context?
//        intmapTypeKind.clear();
//        setTypeKind.clear();
//        seqTypeKind.clear();
//        arrayTypeKind.clear();
//        realTypeKind.clear();
    }
    
    public static class JmlTypeKind extends IJmlClauseKind {
        private String typename; // flat or unqualified type name
        public com.sun.tools.javac.util.Name name;
        Symbol.ClassSymbol sym = null; // lazily filled in; depends on context; only  implemented for a single context
        Type type = null; // lazily filled in; depends on context; only  implemented for a single context
        Context context = null; // context for type -- need even though it shadows IJmlClauseKind.context

        public JmlTypeKind(String keyword, String typename) {
            super(keyword);
            this.typename = typename;
            
        }
        
        public void clear() {
            name = null;
            type = null;
            context = null;
            sym = null;
        }

//        public void initType(Context context) { this.context = context; }

        public int numTypeArguments() { return 0; }

        public Type getType(Context context) {
            getSymbol(context);
            return type;
        }
        
        public void init(Context context) {
            this.context = context;
            String fqname;
            if (typename.contains(".")) {
                fqname = typename;
            } else {
                fqname = "org.jmlspecs.lang." + typename;
            }
            //System.out.println("GETTING " + fqname + " " + type + " " + context.hashCode());
            var nm = Names.instance(context).fromString("java.base");
            com.sun.tools.javac.code.Symbol.ModuleSymbol moduleSym = com.sun.tools.javac.code.ModuleFinder.instance(context).findModule(nm);
            sym = com.sun.tools.javac.code.Symtab.instance(context).enterClass(moduleSym, Names.instance(context).fromString(fqname));
            //sym = JmlTypes.instance(context).createClass(fqname);
            if (sym == null) {
                System.out.println("FAILED TO GET SYM FOR " + fqname);
            }
            this.type = sym.type;
            //System.out.println("GOT " + fqname + " " + type.hashCode() + " " + sym.hashCode());
            if (this.sym != type.tsym) System.out.println("Primitive Symbols different: " + sym + " " + type.tsym);
            this.name = Names.instance(context).fromString(typename); // FIXME - is this OK if the name is fully-qualified?
            initOps();
        }
        
        public Symbol.ClassSymbol getSymbol(Context context) {
            // Caching the type (which depends on context) for general use
            if (type == null || context != this.context) {
                try {
                    initAll(context);
                } catch (Throwable e) {
                    e.printStackTrace(System.out);
                }
            }
            return sym;
        }
        
        public void initAll(Context context) {
            //System.out.println("INITING ALL " + context.hashCode());
            TYPETypeKind.init(context);
            bigintTypeKind.init(context);
            arrayTypeKind.init(context);
            datagroupTypeKind.init(context);
            intmapTypeKind.init(context);
            intsetTypeKind.init(context);
            locsetTypeKind.init(context);
            mapTypeKind.init(context);
            rangeTypeKind.init(context);
            realTypeKind.init(context);
            seqTypeKind.init(context);
            setTypeKind.init(context);
            stringTypeKind.init(context);
        }
        
        // FIXME - this does not get called unless the tool encounters an explicit \zzz for the given type -- and then operators are not found
        public void initOps() {
            //System.out.println("EQOPS " + type + " " + context.hashCode());
            JmlTypes jt = JmlTypes.instance(context);
            jt.enterBinop("==", type, type, jt.syms.booleanType);
            jt.enterBinop("!=", type, type, jt.syms.booleanType);
        }
        
        public String opName(JCTree.Tag optag) { 
            return optag == JCTree.Tag.EQ ? "eq" : 
                   optag == JCTree.Tag.NE ? "ne" : 
                                            "";
        }


//        public Type getRepType(Context context) {
//            getSymbol(context);
//            return repType;
//        }

        @Override
        public JCExpression parse(JCModifiers mods, String keyword, IJmlClauseKind clauseKind, JmlParser parser) {
            init(parser);
            if (name == null) name = parser.names.fromString(keyword);
            JCIdent id = parser.maker().at(parser.pos()).Ident(keyword);
            int p = parser.pos();
            int ep = parser.endPos();
            parser.nextToken();
            if (parser.token().kind == TokenKind.LPAREN) { 
                utils.error(p, ep, "jml.message", "An ill-formed type");
                parser.nextToken();
                return null;
            } else {
                var hasAngleBracket = parser.token().kind == TokenKind.LT;
                var expectedNumArgs = numTypeArguments();
                JCExpression typeExpr = parser.typeArgumentsOpt(id);
                if (hasAngleBracket) {
                    if (expectedNumArgs == 0) {
                        utils.error(parser.token().pos, parser.token().endPos, "jml.message",
                            "A " + keyword + " does not expect type arguments");
                        typeExpr = parser.maker().at(p).Erroneous();
                    } else if (((com.sun.tools.javac.tree.JCTree.JCTypeApply)typeExpr).arguments.size() != expectedNumArgs) {
                        utils.error(parser.token().pos, parser.token().endPos, "jml.message",
                                "A " + keyword + " expects " + expectedNumArgs + " type arguments");
                        typeExpr = parser.maker().at(p).Erroneous();
                    } else {
                        // OK
                    }
                } else {
                    if (expectedNumArgs != 0 ) {
                        utils.error(parser.token().pos, parser.token().endPos, "jml.message",
                            "A " + keyword + " must have type arguments");
                        typeExpr = parser.maker().at(p).Erroneous();
                    } else {
                        // typeExxpr is already just equal to id
                    }
                }
                typeExpr = parser.bracketsOpt(typeExpr);
                return typeExpr;
            }
		}
		@Override
		public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> env) {
			return null;
		}
	}
	
    public static final String bigintID = "\\bigint";

    public static final JmlTypeKind bigintTypeKind = new JmlTypeKind(bigintID,"org.jmlspecs.lang.internal.bigint") {
        
        public void initOps() {
            JmlTypes jt = JmlTypes.instance(context);
            jt.enterBinop("==", type, type, jt.syms.booleanType);
            jt.enterBinop("!=", type, type, jt.syms.booleanType);
            jt.enterBinop(">", type, type, jt.syms.booleanType);
            jt.enterBinop("<", type, type, jt.syms.booleanType);
            jt.enterBinop("<=", type, type, jt.syms.booleanType);
            jt.enterBinop(">=", type, type, jt.syms.booleanType);

            jt.enterUnop("+++", type, type); // unary plus // These operators are those used also in Symtab
            jt.enterUnop("---", type, type); // unary minus
            jt.enterUnop("++", type, type);
            jt.enterUnop("--", type, type);

            jt.enterBinop("+", type, type, type);
            jt.enterBinop("-", type, type, type);
            jt.enterBinop("*", type, type, type);
            jt.enterBinop("/", type, type, type);
            jt.enterBinop("%", type, type, type);
            jt.enterBinop("<<", type, type, type);
            jt.enterBinop(">>", type, type, type);
            jt.enterBinop("<<", type, jt.syms.longType, type);
            jt.enterBinop(">>", type, jt.syms.longType, type);
            // Assign-op operators are automatically defined based on the simple operator
            
            // bit operators
            jt.enterUnop("~", type, type); // bit complement
            jt.enterBinop("|", type, type, type);
            jt.enterBinop("&", type, type, type);
            jt.enterBinop("^", type, type, type);

        }
        
        @Override
        public String opName(JCTree.Tag optag) {
            return switch (optag) {
            case EQ -> "eq";
            case NE -> "ne";
            case PLUS -> "add";
            case MINUS -> "subtract";
            case MUL -> "multiply";
            case DIV -> "divide";
            case MOD -> "mod";
            case GE -> "ge";
            case GT -> "gt";
            case LE -> "le";
            case LT -> "lt";
            case SL -> "shiftLeft";
            case SR -> "shiftRight";
            case BITAND -> "and";
            case BITOR -> "or";
            case BITXOR -> "xor";
            default -> null;
            };
        }

    };

    public static final String realId = "\\real";

    public static final JmlTypeKind realTypeKind = new JmlTypeKind(realId,"real") {
        
        public void initOps() {
            JmlTypes jt = JmlTypes.instance(context);
            jt.enterBinop("==", type, type, jt.syms.booleanType);
            jt.enterBinop("!=", type, type, jt.syms.booleanType);
            jt.enterBinop(">", type, type, jt.syms.booleanType);
            jt.enterBinop("<", type, type, jt.syms.booleanType);
            jt.enterBinop("<=", type, type, jt.syms.booleanType);
            jt.enterBinop(">=", type, type, jt.syms.booleanType);

            jt.enterUnop("+++", type, type); // unary plus // These operators are those used also in Symtab
            jt.enterUnop("---", type, type); // unary minus
            jt.enterUnop("++", type, type);
            jt.enterUnop("--", type, type);

            jt.enterBinop("+", type, type, type);
            jt.enterBinop("-", type, type, type);
            jt.enterBinop("*", type, type, type);
            jt.enterBinop("/", type, type, type);
            jt.enterBinop("%", type, type, type);
        }
        
        @Override
        public String opName(JCTree.Tag optag) {
            return switch (optag) {
            case EQ -> "eq";
            case NE -> "ne";
            case PLUS -> "add";
            case MINUS -> "subtract";
            case MUL -> "multiply";
            case DIV -> "divide";
            case MOD -> "mod";
            case GE -> "ge";
            case GT -> "gt";
            case LE -> "le";
            case LT -> "lt";
            default -> "";
            };
        }
    };

    public static final String arrayId = "\\array";

    public static final JmlTypeKind arrayTypeKind = new JmlTypeKind(arrayId,"array") {
        @Override
        public int numTypeArguments() { return 1; }
    };

    public static final String seqId = "\\seq";

    public static final JmlTypeKind seqTypeKind = new JmlTypeKind(seqId,"seq") {
        @Override
        public int numTypeArguments() { return 1; }
        
        @Override
        public void initOps() {
            JmlTypes jt = JmlTypes.instance(context);
            jt.enterBinop("==", type, type, jt.syms.booleanType);
            jt.enterBinop("!=", type, type, jt.syms.booleanType);
            //jt.enterBinop(">", REALP, REALP, jt.syms.booleanType);
            //jt.enterBinop("<", REALP, REALP, jt.syms.booleanType);
            //jt.enterBinop("<=", REALP, REALP, jt.syms.booleanType);
            //jt.enterBinop(">=", REALP, REALP, jt.syms.booleanType);
            jt.enterBinop("+", type, type, type);
        }
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

    public static final String intmapId = "\\intmap";

    public static final JmlTypeKind intmapTypeKind = new JmlTypeKind(intmapId,"intmap") {
        @Override
        public int numTypeArguments() { return 1; }
        
        @Override
        public Symbol.ClassSymbol getSymbol(Context context) {
            //System.out.println("INTMAP " + context + " " + this.context + " " + type); Utils.dumpStack();
            return super.getSymbol(context);
        }
    };

    public static final String intsetId = "\\intset";

    public static final JmlTypeKind intsetTypeKind = new JmlTypeKind(intsetId,"intset");

    public static final String stringId = "\\string";

    public static final JmlTypeKind stringTypeKind = new JmlTypeKind(stringId,"string") {
        @Override
        public int numTypeArguments() { return 0; }

        @Override
        public void initOps() {
            JmlTypes jt = JmlTypes.instance(context);
            jt.enterBinop("==", type, type, jt.syms.booleanType);
            jt.enterBinop("!=", type, type, jt.syms.booleanType);
            jt.enterBinop("+", type, type, type);
            jt.enterBinop("+", type, jt.syms.charType, type);
        }

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
    

	
    public static final String TYPEID = "\\TYPE";
    
    public static final JmlTypeKind TYPETypeKind = new JmlTypeKind(TYPEID, "org.jmlspecs.lang.internal.TYPE") {
        
    };

    public static final String datagroupID = "\\datagroup";
    
    public static final JmlTypeKind datagroupTypeKind = new JmlTypeKind(datagroupID, "org.jmlspecs.lang.internal.datagroup") {
        @Override
        public int numTypeArguments() { return 0; }
        
        @Override
        public void initOps() {
            // intentionally no operations, not even ==
        }
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
				tree.type = type;
				// FIXME
//				((JCIdent)app.meth).sym = id.sym;
//				((JCIdent)app.meth).type = id.type; // FIXME - or should be a method type?
				System.out.println("TYPECHECKED " + tree + " AS " + type);
				return type;
			}
			// FIXME - internal error
			return null;
		}
	};

	
    public static class LocSet extends IJmlClauseKind.SingletonExpressionKind {
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
