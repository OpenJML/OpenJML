package org.jmlspecs.openjml;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import static com.sun.tools.javac.code.Type.*;
import com.sun.tools.javac.parser.JmlToken;

import com.sun.tools.javac.tree.JCTree;
import static com.sun.tools.javac.tree.JCTree.*;
import org.jmlspecs.openjml.JmlTree;
import static org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

import com.google.gson.*;
import com.google.gson.stream.*;

import java.io.IOException;

/** This class contains custom serializers (for the Gson library), enabling emitting Json representation of a Java/JML AST,
 *  with type information.
 *  <p>
 *  Generate output Json text using <code>new JmlJson(context).toJson(tree)</code>.
 *  <p>
 *  OpenJDK/OpenJML AST classes contain the information provided by parsing, but also other derived information, such as types
 *  and symbols, and also references to containers, so that the AST has circular references within the derived information.
 *  Also, symbol and type information refers to entities in an internal compilation context. Thus it is not possible to simple use
 *  a default translation to JSON that finds, by reflection, and serializes all fields within an AST class. With Gson, there are
 *  two possibilities:
 *  <p>
 *  A) Mark all fields that are to be written to JSON with @Expose. This permits choosing just the parsed fields, but does not allow 
 *  customizing the output to include, for example, the AST class being translated. It also requires adding annotations to OpenJDK classes.
 *  <P>
 *  B) Write a custom serializer for each of the AST classes and leaf properties (such as literal values and names). This permits 
 *  customization as needed. This is the design chosen here. 
 *  <p>
 *  In either case, custom deserializers must be written, if any such are ever needed.
 */
// TODO:
// - change unnecessary unicode to ASCII
// - specifications
// - fix serializing of Name
// - symbols
// - destination of output files
// - output only command-line files (or give a choice)
// - documentation of --show
// - all the rest of the adapters
// - a check for missing adapters
// - deserializers; serialize-deserialize test

public class JmlJson {
    
    final GsonBuilder builder;
    final Gson gson;
    final Context context;
    final Names names;
    
    public String toJson(JCTree tree) {
        return gson.toJson(tree);
    }
    
    public JmlJson(Context context) {
        this.context = context;
        this.names = Names.instance(context);
        
        this.builder = new GsonBuilder();
        builder.registerTypeAdapter(JmlToken.class, this.new JmlTokenAdapter());
        builder.registerTypeAdapter(Name.class, this.new NameAdapter());
        builder.registerTypeAdapter(Type.class, this.new PTypeAdapter());
        
        var prefix = "com.sun.tools.javac.tree.JCTree$";
        var prefixjml = "org.jmlspecs.openjml.JmlTree$";
        var suffix = "Adapter".length();

        for (Class<?> nestedClass : JmlJson.class.getDeclaredClasses()) {
            var adapter = nestedClass.toString();
            var astclass = adapter.substring(adapter.indexOf('$')+1, adapter.length()-suffix);
            try {
                // FIXME - need to get constructor for inner class, and call with outer object
                var cons = nestedClass.getDeclaredConstructors()[0];
                var adap = cons.newInstance(this);
                Class<?> cl = null;
                try {
                    cl = Class.forName(prefix + astclass);
                } catch (ClassNotFoundException e) {
                }
                if (cl == null) try {
                    cl = Class.forName(prefixjml + astclass);
                } catch (ClassNotFoundException e) {
                }
                if (cl == null) try {
                    cl = Class.forName("com.sun.tools.javac.util." + astclass);
                } catch (ClassNotFoundException e) {
                }
                if (cl == null) try {
                    cl = Class.forName("com.sun.tools.javac.code.Type$" + astclass);
                } catch (ClassNotFoundException e) {
                }
                if (cl != null) {
                    builder.registerTypeAdapter(cl, adap);
//                  System.out.println("OK " + cl.toString() + " " + adapter);
                } else {
                    if (astclass.equals("PType")) continue;
                    if (astclass.equals("JmlToken")) continue;
                    System.out.println("FAILURE " + astclass + " " + adapter);
                }
            } catch (Exception e) {
                System.out.println("FAILURE " + astclass + " " + adapter + " " + e);
            }
        }
        this.gson = builder.setPrettyPrinting().create();
    }
    
    private JsonObject newgson(JCTree tree) {
        var obj = new JsonObject();
        var clazz = tree.getClass().toString();
        obj.add("class", new JsonPrimitive(clazz.substring(clazz.indexOf('$'))));
        if (tree instanceof JCExpression ex) {
            obj.add("type", str(ex.type));
        }
        return obj;
    }

    private JsonElement str(Object s) {
        return new JsonPrimitive(java.util.Objects.toString(s)); // 's' might be null
    }

    private JsonElement str(String s) {
        return s == null ? JsonNull.INSTANCE : new JsonPrimitive(s);
    }
    
    private JsonElement name(Name n) { // FIXME - why can't we use context.serialize(n) for names
        return n == null ? null : str(n.toString());
    }
    
    /***************************************************/

    class JCAnnotatedTypeAdapter implements JsonSerializer<JCAnnotatedType> {
        @Override
        public JsonElement serialize(JCAnnotatedType src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("annotations", str(src.annotations));
            obj.add("underlyingType", context.serialize(src.underlyingType));
            return obj;
        }
    }

    class JmlAnnotationAdapter implements JsonSerializer<JmlAnnotation> {
        @Override
        public JsonElement serialize(JmlAnnotation src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("annotationType", str(src.annotationType));
            obj.add("args", context.serialize(src.args));
            return obj;
        }
    }


    // TODO: JCAnyPattern

    class JCArrayAccessAdapter implements JsonSerializer<JCArrayAccess> {
        @Override
        public JsonElement serialize(JCArrayAccess src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("indexed", context.serialize(src.indexed));
            obj.add("index", context.serialize(src.index));
            return obj;
        }
    }

    class JCArrayTypeTreeAdapter implements JsonSerializer<JCArrayTypeTree> {
        @Override
        public JsonElement serialize(JCArrayTypeTree src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("elemtype", context.serialize(src.elemtype));
            return obj;
        }
    }
    
    class JCAssertAdapter implements JsonSerializer<JCAssert> {
        @Override
        public JsonElement serialize(JCAssert src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("cond", context.serialize(src.cond));
            obj.add("detail", context.serialize(src.detail));
            return obj;
        }
    }

    class JCAssignAdapter implements JsonSerializer<JCAssign> {
        @Override
        public JsonElement serialize(JCAssign src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("lhs", context.serialize(src.lhs));
            obj.add("rhs", context.serialize(src.rhs));
            return obj;
        }
    }

    class JCAssignOpAdapter implements JsonSerializer<JCAssignOp> {
        @Override
        public JsonElement serialize(JCAssignOp src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("lhs", context.serialize(src.lhs));
            obj.add("opcode", str(src.getTag()));
            obj.add("rhs", context.serialize(src.rhs));
            return obj;
        }
    }

    // TODO?: JMLBB?

    class JCBinaryAdapter implements JsonSerializer<JCBinary> {
        @Override
        public JsonElement serialize(JCBinary src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("lhs", context.serialize(src.lhs));
            obj.add("opcode", str(src.getTag()));
            obj.add("rhs", context.serialize(src.rhs));
            return obj;
        }
    }

    class JmlBinaryAdapter implements JsonSerializer<JmlBinary> {
        @Override
        public JsonElement serialize(JmlBinary src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("lhs", context.serialize(src.lhs));
            obj.add("op", str(src.op));
            obj.add("rhs", context.serialize(src.rhs));
            return obj;
        }
    }
    
    // TODO: JCBindingPattern

    class JmlBlockAdapter implements JsonSerializer<JmlBlock> {
        @Override
        public JsonElement serialize(JmlBlock src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("flags", str(Flags.toString(src.flags & Flags.StandardFlags)));
            obj.add("stats", context.serialize(src.stats));
            return obj;
        }
    }
    
    class JCBreakAdapter implements JsonSerializer<JCBreak> {
        @Override
        public JsonElement serialize(JCBreak src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("label", name(src.label));
            return obj;
        }
    }
    

    // TODO: JmlCase
    // TODO: JCCaseLabel
    // TODO: JCCatch
    // TODO: JmlChained
    // TODO: JmlChoose

    class JmlClassDeclAdapter implements JsonSerializer<JmlClassDecl> {
        @Override
        public JsonElement serialize(JmlClassDecl src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("mods", context.serialize(src.mods));
            obj.add("name", name(src.name));
            obj.add("typarams", context.serialize(src.typarams));
            obj.add("extending", context.serialize(src.extending));
            obj.add("implementing", context.serialize(src.implementing));
            obj.add("permitting", context.serialize(src.permitting));
            obj.add("defs", context.serialize(src.defs));
            return obj;
        }
    }

    class JmlCompilationUnitAdapter implements JsonSerializer<JmlCompilationUnit> {
        @Override
        public JsonElement serialize(JmlCompilationUnit src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("sourcefile", str(src.sourcefile.getName()));
            obj.add("pid", context.serialize(src.pid));
            obj.add("defs", context.serialize(src.defs));
            return obj;
        }
    }
    
    class JCConditionalAdapter implements JsonSerializer<JCConditional> {
        @Override
        public JsonElement serialize(JCConditional src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("cond", context.serialize(src.cond));
            obj.add("truepart", context.serialize(src.truepart));
            obj.add("falsepart", context.serialize(src.falsepart));
            return obj;
        }
    }
    
    // TODO: JCConstantCaseLabel

    class JCContinueAdapter implements JsonSerializer<JCContinue> {
        @Override
        public JsonElement serialize(JCContinue src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("label", name(src.label));
            return obj;
        }
    }
    
    // TODO: JCDefaultCaselabel
    // abstract - JCDirective
    // TODO: JmlDoWhileLoop
    // TODO: JmlEnhancedForLoop
    // TODO: JCErroneous
    // TODO: JCExports
    // abstract - JCExpression

    class JCExpressionStatementAdapter implements JsonSerializer<JCExpressionStatement> {
        @Override
        public JsonElement serialize(JCExpressionStatement src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("expr", context.serialize(src.expr));
            return obj;
        }
    }

    class JCFieldAccessAdapter implements JsonSerializer<JCFieldAccess> {
        @Override
        public JsonElement serialize(JCFieldAccess src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("selected", context.serialize(src.selected));
            obj.add("name", name(src.name));
            return obj;
        }
    }
    
    class JmlForLoopAdapter implements JsonSerializer<JmlForLoop> {
        @Override
        public JsonElement serialize(JmlForLoop src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("loopSpecs", context.serialize(src.loopSpecs)); // TODO
            obj.add("split", context.serialize(src.split));
            obj.add("init", context.serialize(src.init));
            obj.add("cond", context.serialize(src.cond));
            obj.add("step", context.serialize(src.step));
            obj.add("body", context.serialize(src.body));
            return obj;
        }
    }
    // TODO: JCFunctionalExpression
    // TODO: JmlGroupName
    
    class JCIdentAdapter implements JsonSerializer<JCIdent> {
        @Override
        public JsonElement serialize(JCIdent src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("name", name(src.name));
            return obj;
        }
    }
    
    class JmlIfStatementAdapter implements JsonSerializer<JmlIfStatement> {
        @Override
        public JsonElement serialize(JmlIfStatement src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("cond", context.serialize(src.cond));
            obj.add("thenpart", context.serialize(src.thenpart));
            obj.add("elsepart", context.serialize(src.elsepart));
            return obj;
        }
    }

    class JmlImportAdapter implements JsonSerializer<JmlImport> {
        @Override
        public JsonElement serialize(JmlImport src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("qualid", context.serialize(src.qualid));
            obj.add("staticImport", context.serialize(src.staticImport));
            obj.add("isModel", context.serialize(src.isModel));
            return obj;
        }
    }
    
    // TODO: JmlInlinedLoop
    // TODO: JCInstanceOf
    // TODO: JmlLabeledStatement
    // TODO: JmlLambda
    // TODO: JmlLblExpression
    // TODO: JmlLetExpr
    
    class JCLiteralAdapter implements JsonSerializer<JCLiteral> {
        @Override
        public JsonElement serialize(JCLiteral src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("typetag", str(src.typetag));
            obj.add("value", str(src.value));
            return obj;
        }
    }
    
    // TODO: JmlMatchExpression
    // TODO: JCMemberReference
    // TODO: JmlMethodClauseBehaviors
    // TODO: JmlMethodClauseCallable
    // TODO: JmlMethodClauseConditional
    // TODO: JmlMethodClauseDecl
    // TODO: JmlMethodClauseExpr
    class JmlMethodClauseExprAdapter implements JsonSerializer<JmlMethodClauseExpr> {
        @Override
        public JsonElement serialize(JmlMethodClauseExpr src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("clauseType", str(src.clauseKind));
            obj.add("name", name(src.name));
            obj.add("expression", context.serialize(src.expression));
            return obj;
        }
    }

    // TODO: JmlMethodClauseGroup
    // TODO: JmlMethodClauseInvariants
    // TODO: JmlMethodClauseSignals
    // TODO: JmlMethodClauseSignalsOnly
    // TODO: JmlMethodClauseStoreRef

    class JmlMethodDeclAdapter implements JsonSerializer<JmlMethodDecl> {
        @Override
        public JsonElement serialize(JmlMethodDecl src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("mods", context.serialize(src.mods));
            obj.add("name", name(src.name));
            obj.add("restype", context.serialize(src.restype));
            obj.add("typarams", context.serialize(src.typarams));
            obj.add("recvparam", context.serialize(src.recvparam));
            obj.add("params", context.serialize(src.params));
            obj.add("thrown", context.serialize(src.thrown));
            obj.add("methodSpecs", context.serialize(src.methodSpecs));
            obj.add("body", context.serialize(src.body));
            obj.add("defaultValue", context.serialize(src.defaultValue));
            return obj;
        }
    }
    
    class JCMethodInvocationAdapter implements JsonSerializer<JCMethodInvocation> {
        @Override
        public JsonElement serialize(JCMethodInvocation src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("typeargs", context.serialize(src.typeargs));
            obj.add("meth", context.serialize(src.meth));
            obj.add("args", context.serialize(src.args));
            obj.add("varargsElement", context.serialize(src.varargsElement));
            //obj.add("polyKind", context.serialize(src.polyKind)); // FIXME - add this
            return obj;
        }
    }
    
    class JmlMethodInvocationAdapter implements JsonSerializer<JmlMethodInvocation> {
        @Override
        public JsonElement serialize(JmlMethodInvocation src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("name", str(src.name));
            obj.add("kind", str(src.kind));
            obj.add("args", context.serialize(src.args)); // FIXME - more - ?
            return obj;
        }
    }
    
    // TODO: JmlMethodSig

    class JmlMethodSpecsAdapter implements JsonSerializer<JmlMethodSpecs> {
        @Override
        public JsonElement serialize(JmlMethodSpecs src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("cases", context.serialize(src.cases)); // FIXME - more - both cases and behaviors?
            return obj;
        }
    }
        
// TODO: JmlModelProgramStatement

    class JmlModifiersAdapter implements JsonSerializer<JmlModifiers> {
        @Override
        public JsonElement serialize(JmlModifiers src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("annotations", context.serialize(src.annotations));
            obj.add("flags", str(Flags.toString(src.flags & Flags.StandardFlags)));
            obj.add("jmlmods", context.serialize(src.jmlmods));
            return obj;
        }
    }
    
    // TODO: JCModuleDecl

    class JCNewArrayAdapter implements JsonSerializer<JCNewArray> {
        @Override
        public JsonElement serialize(JCNewArray src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("elemtype", context.serialize(src.elemtype)); // FIXME - needs more fields
            obj.add("dims", context.serialize(src.dims));
            obj.add("elems", context.serialize(src.elems));
            return obj;
        }
    }

    class JmlNewClassAdapter implements JsonSerializer<JmlNewClass> {
        @Override
        public JsonElement serialize(JmlNewClass src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("encl", context.serialize(src.encl)); // FIXME - needs more fields
            obj.add("clazz", context.serialize(src.clazz));
            obj.add("args", context.serialize(src.args));
            obj.add("def", context.serialize(src.def));
            return obj;
        }
    }
    
    // TODO: JCOpens
    // abstract - JCOperatorExpression
    
    class JCPackageDeclAdapter implements JsonSerializer<JCPackageDecl> {
        @Override
        public JsonElement serialize(JCPackageDecl src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("annotations", context.serialize(src.annotations));
            obj.add("pid", context.serialize(src.pid));
            return obj;
        }
    }

    class JCParensAdapter implements JsonSerializer<JCParens> {
        @Override
        public JsonElement serialize(JCParens src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("expr", context.serialize(src.expr));
            return obj;
        }
    }
    
    // abstract JCPattern
    // TODO: JCPatternCaseLabel
    // TODO: JCPolyExpression

    class JCPrimitiveTypeTreeAdapter implements JsonSerializer<JCPrimitiveTypeTree> {
        @Override
        public JsonElement serialize(JCPrimitiveTypeTree src, java.lang.reflect.Type type, JsonSerializationContext context) {
            return str(src);
        }
    }
    
    class JmlPrimitiveTypeTreeAdapter implements JsonSerializer<JmlPrimitiveTypeTree> {
        @Override
        public JsonElement serialize(JmlPrimitiveTypeTree src, java.lang.reflect.Type type, JsonSerializationContext context) {
            return str(src);
        }
    }
    
    // TODO: JCProvides

    class JmlQuantifiedExprAdapter implements JsonSerializer<JmlQuantifiedExpr> {
        @Override
        public JsonElement serialize(JmlQuantifiedExpr src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("kind", str(src.kind));
            obj.add("decls", context.serialize(src.decls));
            obj.add("range", context.serialize(src.range));
            obj.add("value", context.serialize(src.value));
            obj.add("triggers", context.serialize(src.triggers));
            obj.add("failure", context.serialize(src.failure)); // TODO ???
            return obj;
        }
    }

    // TODO: JmlRange
    class JmlRangeAdapter implements JsonSerializer<JmlRange> {
        @Override
        public JsonElement serialize(JmlRange src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("lo", context.serialize(src.lo));
            obj.add("hi", context.serialize(src.hi));
            obj.add("hiExclusive", context.serialize(src.hiExclusive));
            return obj;
        }
    }
    
    // TODO: JCRecordPattern
    // TODO: JCRequires

    class JCReturnAdapter implements JsonSerializer<JCReturn> {
        @Override
        public JsonElement serialize(JCReturn src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("expr", context.serialize(src.expr));
            return obj;
        }
    }
    
    // TODO: JmlSetComprehension

    class JmlSingletonAdapter implements JsonSerializer<JmlSingleton> {
        @Override
        public JsonElement serialize(JmlSingleton src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("kind", str(src.kind));
            return obj;
        }
    }
    

    class JCSkipAdapter implements JsonSerializer<JCSkip> {
        @Override
        public JsonElement serialize(JCSkip src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            return obj;
        }
    }
    

    class JmlSpecificationCaseAdapter implements JsonSerializer<JmlSpecificationCase> {
        @Override
        public JsonElement serialize(JmlSpecificationCase src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("also", str(src.also));
            //obj.add("code", str(src.code)); // FIXME - change to a token
            obj.add("clauses", context.serialize(src.clauses));
            return obj;
        }
    }
    
    // abstract - JCStatement
    // TODO: JmlStatementDecls
    
    class JmlStatementExprAdapter implements JsonSerializer<JmlStatementExpr> {
        @Override
        public JsonElement serialize(JmlStatementExpr src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("keyword", str(src.keyword));
            obj.add("expression", context.serialize(src.expression));
            obj.add("optionalExpression", context.serialize(src.optionalExpression));
            return obj;
        }
    }

    // TODO: JmlStatementHavoc
    // TODO: JmlStatementLoop
    // TODO: JmlStatementLoopExpr

    class JmlStatementLoopExprAdapter implements JsonSerializer<JmlStatementLoopExpr> {
        @Override
        public JsonElement serialize(JmlStatementLoopExpr src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("name", str(src.name));
            obj.add("clauseType", str(src.clauseType));
            obj.add("expression", context.serialize(src.expression));
            return obj;
        }
    }

    class JmlStatementLoopModifiesAdapter implements JsonSerializer<JmlStatementLoopModifies> {
        @Override
        public JsonElement serialize(JmlStatementLoopModifies src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("name", str(src.name));
            obj.add("clauseType", str(src.clauseType));
            obj.add("source", str(src.source));
            obj.add("expression", context.serialize(src.storerefs));
            return obj;
        }
    }
// TODO: JmlStatementLoopModifies
    // TODO: JmlStatementShow
    // TODO: JmlStatementSpec
    // TODO: JmlStoreRef
    // TODO: JmlStoreRefArrayRange
    // TODO: JmlStoreRefKeyword
    // TODO: JmlStoreRefListExpression
    // TODO: JCStringTemplate
    // TODO: JmlSwitchStatement
    // TODO: JCSwitchExpression
    // TODO: JCSynchronized

    class JCSynchronizedAdapter implements JsonSerializer<JCSynchronized> {
        @Override
        public JsonElement serialize(JCSynchronized src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("lock", context.serialize(src.lock));
            obj.add("body", context.serialize(src.body));
            return obj;
        }
    }

    class JCThrowAdapter implements JsonSerializer<JCThrow> {
        @Override
        public JsonElement serialize(JCThrow src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("expr", context.serialize(src.expr));
            return obj;
        }
    }
    
    // TODO: JCTry
    // TODO: JmlTuple
    // TODO: JCTypeApply

    class JCTypeApplyAdapter implements JsonSerializer<JCTypeApply> {
        @Override
        public JsonElement serialize(JCTypeApply src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("clazz", str(src.clazz));
            obj.add("arguments", context.serialize(src.arguments));
            return obj;
        }
    }

    // TODO: JCTypeCast
    // TODO: JmlTypeClauseConditional
    // TODO: JmlTypeClauseConstraint
    // TODO: JmlTypeClauseDecl
    
    class JmlTypeClauseExprAdapter implements JsonSerializer<JmlTypeClauseExpr> {
        @Override
        public JsonElement serialize(JmlTypeClauseExpr src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("clauseType", str(src.clauseType));
            obj.add("name", name(src.name));
            obj.add("expression", context.serialize(src.expression));
            return obj;
        }
    }
    // TODO: JmlTypeClauseIn
    // TODO: JmlTypeClauseInitializer
    // TODO: JmlTypeClauseMaps
    // TODO: JmlTypeClauseMonitorsFor
    // TODO: JmlTypeClauseRepresents
    // TODO: JCTypeIntersection
    // TODO: JCTypeParameter
    // TODO: JCTypeUnion

    class JCUnaryAdapter implements JsonSerializer<JCUnary> {
        @Override
        public JsonElement serialize(JCUnary src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("opcode", str(src.getTag()));
            obj.add("arg", context.serialize(src.arg));
            return obj;
        }
    }
    
    // TODO: JCUses
    
    class JmlVariableDeclAdapter implements JsonSerializer<JmlVariableDecl> {
        @Override
        public JsonElement serialize(JmlVariableDecl src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("mods", context.serialize(src.mods));
            obj.add("name", name(src.name));
            obj.add("vartype", context.serialize(src.vartype));
            obj.add("init", context.serialize(src.init));
            return obj;
        }
    }
    
    class JCPrimitiveTypeAdapter implements JsonSerializer<Type.JCPrimitiveType> {
        @Override
        public JsonElement serialize(Type.JCPrimitiveType src, java.lang.reflect.Type type, JsonSerializationContext context) {
            return str(src);
        }
    }
    
    class JCVoidTypeAdapter implements JsonSerializer<Type.JCVoidType> {
        @Override
        public JsonElement serialize(Type.JCVoidType src, java.lang.reflect.Type type, JsonSerializationContext context) {
            return str(src);
        }
    }
    
    class JmlWhileLoopAdapter implements JsonSerializer<JmlWhileLoop> {
        @Override
        public JsonElement serialize(JmlWhileLoop src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("loopSpecs", context.serialize(src.loopSpecs));
            obj.add("cond", context.serialize(src.cond));
            obj.add("body", context.serialize(src.body));
            return obj;
        }
    }

// TODO: JCWildcard
    // TODO: JCYield
    // TODO: LetExpr
    // TODO: TypeBoundKind
    
    /**************************/

    class NameAdapter implements JsonSerializer<Name>, JsonDeserializer<Name> {
        @Override
        public JsonElement serialize(Name src, java.lang.reflect.Type type, JsonSerializationContext context) {
            return new JsonPrimitive(src.toString());
        }
        @Override
        public Name deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            return names.fromString(json.getAsJsonPrimitive().getAsString());
        }
    }
    
    class JmlTokenAdapter implements JsonSerializer<JmlToken> {
        @Override
        public JsonElement serialize(JmlToken src, java.lang.reflect.Type type, JsonSerializationContext context) {
            return new JsonPrimitive(src.toString());
        }
    }
    
   class PTypeAdapter extends TypeAdapter<Type> {
        public Type read(JsonReader reader) throws IOException {
          if (reader.peek() == JsonToken.NULL) {
            reader.nextNull();
            return null;
          }
          return null;
        }
        public void write(JsonWriter writer, Type value) throws IOException {
          if (value == null) {
            writer.nullValue();
            return;
          }
          String xy = value.toString() ;
          writer.value(xy);
        }
    }

}
