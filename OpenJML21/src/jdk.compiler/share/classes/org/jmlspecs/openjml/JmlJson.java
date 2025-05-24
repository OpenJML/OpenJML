package org.jmlspecs.openjml;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import static com.sun.tools.javac.code.Type.*;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.parser.JmlToken;

import com.sun.tools.javac.tree.JCTree;
import static com.sun.tools.javac.tree.JCTree.*;
import org.jmlspecs.openjml.JmlTree;
import static org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.file.JavacFileManager;

import javax.tools.JavaFileObject;

import com.google.gson.*;
import com.google.gson.stream.*;

import java.io.IOException;

// TODO:
// Update discussion below
// Fix serialization of JavaFileObject
// Record positions?
// Lots more classes to fixup and corresponding tests
// Capture comments?

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
    final JmlTree.JmlFactory M;
    final Log log;
    
    public String toJson(JCTree tree) {
        return gson.toJson(tree);
    }
    
    public JsonElement toJsonTree(JCTree tree) {
        return gson.toJsonTree(tree);
    }

    public final static String prefix = "com.sun.tools.javac.tree.JCTree$";
    public final static String prefixjml = "org.jmlspecs.openjml.JmlTree$";
    public final static String suffix = "Adapter";

    public JmlJson(Context context) {
        this.context = context;
        this.names = Names.instance(context);
        this.M = JmlTree.Maker.instance(context);
        this.log = Log.instance(context);
        
        // Register all the adapters
        this.builder = new GsonBuilder();
        builder.registerTypeAdapter(JmlToken.class, this.new JmlTokenAdapter());
        builder.registerTypeAdapter(names.fromString("").getClass(), this.new NameAdapter());
        builder.registerTypeAdapter(Type.class, this.new PTypeAdapter());
        builder.registerTypeAdapter(TypeTag.class, this.new TypeTagAdapter());
        builder.registerTypeAdapter(JCTree.Tag.class, this.new OpTagAdapter());
        builder.registerTypeAdapter(JavaFileObject.class, this.new JavaFileObjectAdapter());
        builder.registerTypeAdapter(new JavacFileManager(context,false,null).getJavaFileObject("Z").getClass(), this.new JavaFileObjectAdapter());

        for (Class<?> nestedClass : JmlJson.class.getDeclaredClasses()) {
            var adapter = nestedClass.toString();
            var astclass = adapter.substring(adapter.indexOf('$')+1, adapter.length()-suffix.length());
            if (astclass.isEmpty()) continue;
            try {
                var cons = nestedClass.getDeclaredConstructors()[0];
                var adap = cons.newInstance(this);
                Class<?> cl = null;
                try {
                    cl = Class.forName(prefix + astclass);
                } catch (ClassNotFoundException e) {
                    // continue
                }
                if (cl == null) try {
                    cl = Class.forName(prefixjml + astclass);
                } catch (ClassNotFoundException e) {
                    // continue
                }
                if (cl == null) try {
                    cl = Class.forName("com.sun.tools.javac.util." + astclass);
                } catch (ClassNotFoundException e) {
                    // continue
                }
                if (cl != null) {
                    builder.registerTypeAdapter(cl, adap);
//                } else {
//                    System.out.println("No AST class found for adapter " + adapter);
                }
            } catch (Exception e) {
                log.error("jml.internal","Exception attempting to find an AST class corresponding to adapter " + adapter + " : " + e);
            }
        }
        // Set the string output of Json construction to be pretty-printed
        this.gson = builder.setPrettyPrinting().serializeNulls().create();
    }
    
    /** Serializes a class name in a way that is readily deserializable */
    private String formatClass(Class<?> clazz) {
        var s = clazz.toString();
        int k = s.indexOf(' ');
        s = s.substring(k+1); // remove the 'class ' or 'enum ' prefix
        return s;
    }
    
    /** Creates JSON for a primitive type value, in a way that is self-deserializable*/
    private JsonObject primitive(Class<?> clazz, Object o) {
        var obj = new JsonObject();
        obj.add("class", new JsonPrimitive(formatClass(clazz)));
        obj.add("primitive", str(o));
        return obj;
    }
    
    /** Creates an initial JsonObject, including the class of the object and, if a JCTree, its type and sourcefile, if relevant. */
    private JsonObject newgson(Object o, JsonSerializationContext context) {
        var clazz = o.getClass();
        var obj = new JsonObject();
        obj.add("class", new JsonPrimitive(formatClass(clazz)));
        if (o instanceof JCExpression ex) {
            obj.add("type", str(ex.type)); // FIXME - proper encoding
        }
        if (o instanceof JmlSource sr) {
            var src = sr.source();
            obj.add("sourcefile", context.serialize(src));
        }
        return obj;
    }

    private JsonElement str(Object s) {
        return s == null ? JsonNull.INSTANCE : new JsonPrimitive(java.util.Objects.toString(s)); // 's' might be null
    }

    /** Entry point to convert a String representation of JSON into a JML/Java AST */
    public void toJava(String s) {
        @SuppressWarnings("deprecation")
        var res = new JsonParser().parse(s);
        var tree = toJava(res);
        System.out.println(tree);
    }
    
    /** Entry point to convert a JsonElement into a JML/Java AST */
    public Object toJava(JsonElement j) {
        return gson.fromJson(j, JmlCompilationUnit.class); // FIXME - change this to not need class parameter
    }

    
    /** Gets a Field by reflection in the given class or any superclass or interface, recursively */
    java.lang.reflect.Field getField(Class<?> clazz, String key) {
        java.lang.reflect.Field field = null;
        try {
            field = clazz.getDeclaredField(key);
        } catch (Exception e) {
            var sp = clazz.getSuperclass();
            if (sp != null) field = getField(sp, key);
            if (field == null) for (var iface: clazz.getInterfaces()) {
                field = getField(iface, key);
                if (field != null) break;
            }
        }
        return field;
    }
    
    // FIXME - is this actually used??
    Object fromJsonElement(JsonElement f) {
        if (f == null) {
            return null;
        } else if (f.isJsonObject()) {
            return fromJsonObject(f.getAsJsonObject());
        } else if (f.isJsonPrimitive()) {
            System.out.println("PRIMITIVE FOR " + f.getAsJsonPrimitive());
            return null;
        } else if (f.isJsonNull()) {
            return null;
        } else if (f.isJsonArray()) {
            var list = new com.sun.tools.javac.util.ListBuffer<Object>();
            for (JsonElement elem: f.getAsJsonArray()) {
                list.add(fromJsonElement(elem));
            }
            return list.toList();
        } else {
            // ERROR
            return null;
        }
    }

    /** Converts a JsonObject to an element of an OpenJML AST, using the JsonObject's "class" field 
     * as the type of the target object.
     */
    Object fromJsonObject(JsonObject json) {
        String s = json.get("class").getAsJsonPrimitive().getAsString();
        try {
            Class<?> cl = Class.forName(s);
            return gson.fromJson((JsonElement)json,cl);
        } catch (Exception e) {
            if ("long".equals(s)) {
                return json.get("primitive").getAsJsonPrimitive().getAsLong();
            } else if ("boolean".equals(s)) {
                return Boolean.valueOf(json.get("primitive").getAsJsonPrimitive().getAsString());                
            } else {
                log.error("jml.message","Failed to create an object for a given Json object, with class field \"" + s + "\": " + e);
                System.out.println(json);
                e.printStackTrace(System.out);
                return null;
            }
        }
    }
    
    /** Converts a List<Object> to a List<T> (using unchecked casts of list elements) */
    @SuppressWarnings("unchecked")
    public static <T> List<T> toList(Object list) {
        if (list == null) return null;
        ListBuffer<T> newlist = new ListBuffer<T>();
        for (var elem: (List<Object>)list) newlist.add((T)elem);
        return newlist.toList();
    }
    
    class Adapter<T> implements JsonSerializer<T>, JsonDeserializer<T> {
        /** Retrieves the String[] that is the 'fields' class of the dynamic type of 'this' */
        public String[] fields() { 
            try {
                return (String[])this.getClass().getDeclaredField("fields").get(this);
            } catch (Exception e) {
                Log.instance(JmlJson.this.context).error("jml.internal", "Failed to find the 'fields' array in class " + this.getClass());
                return new String[0];
            }
        }
        
        /** Returns an array of values, the same length as the 'fields' array, where each returned element is the 
         * Object produced by deserializing the corresponding element of the input json object */
        public Object[] getFieldValues(JsonObject json) {
            var fields = fields();
            var values = new Object[fields.length];
            int i = 0;
            for (var fieldName: fields) {
                values[i++] = fromJsonElement(json.get(fieldName));
            }
            return values;
        }
        
         /** Default serializing routine for all values of JCTree subclasses */
        public JsonElement serialize(T src, java.lang.reflect.Type type, JsonSerializationContext context) {
            try {
                if (src instanceof JCTree t) {
                    var obj = newgson(t, context);
                    for (var s: fields()) {
                        java.lang.reflect.Field f = getField(t.getClass(), s);
                        if (f == null) {
                            // Likely a field name in the 'fields' list that does not agree with the class declaration
                            log.error("jml.internal","Invalid field name " + t.getClass() + " " + s);
                            obj.add(s, context.serialize(null));
                            continue;
                        }
                        Object value = f.get(t);
                        if (f.getType().isPrimitive() || f.getType() == String.class) {
                            obj.add(s, primitive(f.getType(), value));
                        } else {
                            obj.add(s, context.serialize(value));
                        }
                    }
                    return obj;
                } else {
                    Log.instance(JmlJson.this.context).error("jml.internal", "Failure to serialize an input of type " + src.getClass() + " (not a JCTree subclass)");
                }
            } catch (Exception e) {
                Log.instance(JmlJson.this.context).error("jml.internal", "Failure to serialize an input of type " + src.getClass() + ": " + e);
                e.printStackTrace(System.out);
            }
            return null;
        }
        
        /** Default deserializing routine -- all JCTree subclasses must override this because they each have their own
         * factory method to produce a new AST element. 
         */
        public T deserialize(JsonElement src, java.lang.reflect.Type type, JsonDeserializationContext context) {
            Log.instance(JmlJson.this.context).error("jml.internal","NO DESERIALIZER: " + this.getClass() + " " + type);
            return null;
        }
    }
    
    /***************************************************/

    class JCAnnotatedTypeAdapter extends Adapter<JCAnnotatedType> {
        public static final String[] fields = { "annotations", "underlyingType" };
        public JCAnnotatedType deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            //var result = (JCExpression)values[1];  // FIXME - need a constructor for an AnnotatedType
            return null;
        }
    }

    class JmlAnnotationAdapter extends Adapter<JmlAnnotation> {
        public static final String[] fields = { "annotationType", "args" };
        public JmlAnnotation deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.Annotation(
                    (JCTree)values[0], 
                    JmlJson.<JCExpression>toList(values[1])
                    );
            return result;
        }
    }


    // TODO: JCAnyPattern

    class JCArrayAccessAdapter extends Adapter<JCArrayAccess> {
        public static final String[] fields = { "indexed", "index" };

        public JCArrayAccess deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.Indexed(
                    (JCExpression)values[0], 
                    (JCExpression)values[1]
                    );
            return result;
        }
}

    class JCArrayTypeTreeAdapter extends Adapter<JCArrayTypeTree> {
        public static final String[] fields = { "indexed", "index" };
    }
    
    class JCAssertAdapter extends Adapter<JCAssert> {
        public static final String[] fields = { "cond", "detail" };
    }

    class JCAssignAdapter extends Adapter<JCAssign> {
        public static final String[] fields = { "lhs", "rhs" };
    }

    class JCAssignOpAdapter extends Adapter<JCAssignOp> {
        public static final String[] fields = { "lhs", "opcode", "rhs" };
       @Override
        public JsonElement serialize(JCAssignOp src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src, context);
            obj.add("lhs", context.serialize(src.lhs));
            obj.add("opcode", str(src.getTag()));
            obj.add("rhs", context.serialize(src.rhs));
            return obj;
        }
    }

    // TODO?: JMLBB?

    class JCBinaryAdapter extends Adapter<JCBinary> {
        public static final String[] fields = { "lhs", "opcode", "rhs" };
        @Override
        public JCBinary deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.Binary((JCTree.Tag)values[1], (JCExpression)values[0], (JCExpression)values[2]);
            return result;
        }
    }

    class JmlBinaryAdapter extends Adapter<JmlBinary> {
        public static final String[] fields = { "lhs", "op", "rhs" };
        @Override
        public JsonElement serialize(JmlBinary src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src, context);
            obj.add("lhs", context.serialize(src.lhs));
            obj.add("op", str(src.op));   // FIXME - proper serializing
            obj.add("rhs", context.serialize(src.rhs));
            return obj;
        }
    }
    
    // TODO: JCBindingPattern

    class JmlBlockAdapter extends Adapter<JmlBlock> {
        public static final String[] fields = { "flags", "stats" };

        public JmlBlock deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.Block(
                    (long)values[0], 
                    JmlJson.<JCStatement>toList(values[1])
                    );
            return result;
        }
    }
    
    class JCBreakAdapter extends Adapter<JCBreak> {
        public static final String[] fields = { "label" };

        public JCBreak deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.Break((Name)values[0]);
            return result;
        }
     }
    

    // TODO: JmlCase
    // TODO: JCCaseLabel
    // TODO: JCCatch
    // TODO: JmlChained
    // TODO: JmlChoose

    class JmlClassDeclAdapter extends Adapter<JmlClassDecl> {
        public static final String[] fields = {"mods", "name", "typarams", "extending", "implementing", "permitting", "defs"};
        @Override
        public JmlClassDecl deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            JCClassDecl result = M.ClassDef(
                    (JCModifiers)values[0], 
                    (Name)values[1], 
                    JmlJson.<JCTypeParameter>toList(values[2]),
                    (JCExpression)values[3],
                    JmlJson.<JCExpression>toList(values[4]),
                    JmlJson.<JCTree>toList(values[6])
                    );
            result.permitting = JmlJson.<JCExpression>toList(values[5]);
            return (JmlClassDecl)result;
        }
    }

    class JmlCompilationUnitAdapter extends Adapter<JmlCompilationUnit> {
        public static final String[] fields = { "pid", "defs"};
        @Override
        public JmlCompilationUnit deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            JmlCompilationUnit result = (JmlCompilationUnit)M.TopLevel(JmlJson.<JCTree>toList(values[1]));
            result.pid = (JCPackageDecl)values[0];
            return result;
        }
    }
    
    class JCConditionalAdapter extends Adapter<JCConditional> {
        public static final String[] fields = { "cond", "truepart", "falsepart" };

        public JCConditional deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.Conditional((JCExpression)values[0],(JCExpression)values[1],(JCExpression)values[2]);
            return result;
        }
    }
    
    // TODO: JCConstantCaseLabel

    class JCContinueAdapter extends Adapter<JCContinue> {
        public static final String[] fields = { "label" };

        public JCContinue deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.Continue((Name)values[0]);
            return result;
        }
    }
    
    // TODO: JCDefaultCaselabel
    // abstract - JCDirective
    // TODO: JmlDoWhileLoop
    // TODO: JmlEnhancedForLoop
    // TODO: JCErroneous
    // TODO: JCExports
    // abstract - JCExpression

    class JCExpressionStatementAdapter extends Adapter<JCExpressionStatement> {
        public static final String[] fields = { "expr" };

        public JCExpressionStatement deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.Exec((JCExpression)values[0]);
            return result;
        }
    }

    class JCFieldAccessAdapter extends Adapter<JCFieldAccess> {
        public static final String[] fields = { "selected", "name" };
        
        @Override
        public JCFieldAccess deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            JCFieldAccess result = M.Select((JCExpression)values[0], (Name)values[1]);
            return result;
        }

    }
    
    class JmlForLoopAdapter extends Adapter<JmlForLoop> {
        public static final String[] fields = { "loopSpecs", "split", "init", "cond", "step", "body" };
    }
    // TODO: JCFunctionalExpression
    // TODO: JmlGroupName
    
    class JCIdentAdapter extends Adapter<JCIdent> {
        public static final String[] fields = { "name" };

        @Override
        public JCIdent deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var name = fromJsonElement(json.getAsJsonObject().get("name"));
            JCIdent result = M.Ident((Name)name);
            return result;
        }
}
    
    class JmlIfStatementAdapter extends Adapter<JmlIfStatement> {
        public static final String[] fields = { "cond", "thenpart", "elsepart" };

        @Override
        public JmlIfStatement deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = (JmlIfStatement)M.If((JCExpression)values[0], (JCStatement)values[1], (JCStatement)values[2]);
            return result;
        }
    }

    class JmlImportAdapter extends Adapter<JmlImport> {
        public static final String[] fields = { "qualid", "staticImport", "isModel" };
        
        @Override
        public JmlImport deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            JmlImport result = M.JmlImport((JCFieldAccess)values[0], (boolean)values[1], (boolean)values[2]);
            return result;
        }
    }
    
    // TODO: JmlInlinedLoop
    
    class JCInstanceOfAdapter extends Adapter<JCInstanceOf> {
        public static final String[] fields = { "pattern", "expr" };// FIXME - what about allowNulls

        @Override
        public JCInstanceOf deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.TypeTest((JCExpression)values[0], (JCExpression)values[1]);
            return result;
        }
}

    class JmlLabeledStatementAdapter extends Adapter<JmlLabeledStatement> {
        public static final String[] fields = { "label", "body" };

        @Override
        public JmlLabeledStatement deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = (JmlLabeledStatement)M.Labelled((Name)values[0], (JCStatement)values[1]);
            return result;
        }
    }

    class JmlLambdaAdapter extends Adapter<JmlLambda> {
        public static final String[] fields = { "paramKind", "param", "body" };
        @Override
        public JsonElement serialize(JmlLambda src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src, context);
            obj.add("paramKind", str(src.paramKind));
            obj.add("params", context.serialize(src.params));
            obj.add("body", context.serialize(src.body));
            return obj;
        }
    }
    // TODO: JmlLblExpression
    // TODO: JmlLetExpr
    
    class JCLiteralAdapter extends Adapter<JCLiteral> {
        public static final String[] fields = { "typetag", "value" };
        @Override
        public JsonElement serialize(JCLiteral src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src, context);
            obj.add("typetag", context.serialize(src.typetag));
            obj.add("value", str(src.value));
            return obj;
        }
        @Override
        public JCLiteral deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            TypeTag typetag = (TypeTag)fromJsonElement(json.getAsJsonObject().get("typetag"));
            JsonPrimitive pr = json.getAsJsonObject().get("value").getAsJsonPrimitive();
            Object v = null;
            switch (typetag) {
            case INT:
                v = pr.getAsInt();
                break;
            case BOOLEAN:// JCLiterals hold boolean literals as Integer (0 or 1)
                v = pr.getAsInt();
                break;
            case CLASS:
                v = pr.getAsString();
                break;
            case LONG:
                v = pr.getAsLong();
                break;
            case CHAR:
                v = pr.getAsInt(); // JCLiterals hold character literals as Integer
                break;
            case FLOAT:
                v = pr.getAsFloat();
                break;
            case DOUBLE:
                v = pr.getAsDouble();
                break;
            case SHORT:
                v = pr.getAsShort();
                break;
            case BYTE:
                v = pr.getAsByte();
                break;
            default:
                System.out.println("UNKNOWN LITERAL VALUE FOR TAG " + typetag + " " + pr);
            }
            JCLiteral result = M.Literal(typetag, v);
            return result;
        }
    }
    
    // TODO: JmlMatchExpression

    class JCMemberReferenceAdapter extends Adapter<JCMemberReference> {
        public static final String[] fields = { "mode", "name", "expr", "typeaargs" };
        @Override
        public JsonElement serialize(JCMemberReference src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src, context);
            obj.add("mode", str(src.mode)); // FIXME
            obj.add("name", context.serialize(src.name));
            obj.add("expr", context.serialize(src.expr));
            obj.add("typeargs", context.serialize(src.typeargs));
            return obj;
        }
    }
    
    // TODO: JmlMethodClauseBehaviors
    // TODO: JmlMethodClauseCallable
    // TODO: JmlMethodClauseConditional
    // TODO: JmlMethodClauseDecl
    // TODO: JmlMethodClauseExpr
    class JmlMethodClauseExprAdapter extends Adapter<JmlMethodClauseExpr> {
        public static final String[] fields = { "keyword", "name", "clauseType", "expression", "exception" };
        @Override
        public JsonElement serialize(JmlMethodClauseExpr src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src, context);
            obj.add("clauseType", str(src.clauseKind)); // FIXME
            obj.add("name", context.serialize(src.name));
            obj.add("expression", context.serialize(src.expression));
            return obj;
        }
        @Override
        public JmlMethodClauseExpr deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.JmlMethodClauseExpr(
                    (String)values[0],        // keyword
                    (IJmlClauseKind)values[1], // clauseType // FIXME????
                    (JCExpression)values[2] // expression
                    );
            //result.exception = FIXME???
            return result;
        }
    }

    // TODO: JmlMethodClauseGroup
    // TODO: JmlMethodClauseInvariants
    // TODO: JmlMethodClauseSignals
    // TODO: JmlMethodClauseSignalsOnly
    // TODO: JmlMethodClauseStoreRef

    class JmlMethodDeclAdapter extends Adapter<JmlMethodDecl> {
        public static final String[] fields = { "mods", "name", "restype", "typarams", "recvparam", "params", "thrown", "methodSpecs", "body", "defaultValue" };
        @Override
        public JmlMethodDecl deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = (JmlMethodDecl)M.MethodDef(
                    (JCModifiers)values[0], // mods
                    (Name)values[1],        // name
                    (JCExpression)values[2],// restype
                    JmlJson.<JCTypeParameter>toList(values[3]), // typarams
                    (JCVariableDecl)values[4], // recvparam
                    JmlJson.<JCVariableDecl>toList(values[5]), // params
                    JmlJson.<JCExpression>toList(values[6]), // thrown
                    (JCBlock)values[8],// body
                    (JCExpression)values[9] // defaultValue
                    );
                    // FIXME - meethod specs
            return result;
        }
    }
    
    class JCMethodInvocationAdapter extends Adapter<JCMethodInvocation> {
        String[]fields = { "typeargs", "meth", "args" }; // FIXME - varargs? polyKind
        @Override
        public JCMethodInvocation deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.Apply(JmlJson.<JCExpression>toList(values[0]), (JCExpression)values[1], JmlJson.<JCExpression>toList(values[2]));
            return result;
        }
    }
    
    class JmlMethodInvocationAdapter extends Adapter<JmlMethodInvocation> {
        public static final String[] fields = { "typeargs", "meth", "kind", "name", "args" };
        @Override
        public JsonElement serialize(JmlMethodInvocation src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src, context);
            obj.add("typeargs", context.serialize(src.typeargs));
            obj.add("meth", context.serialize(src.meth));
            obj.add("kind", str(src.kind)); // IJmlClauseKind
            obj.add("name", primitive(String.class, src)); // a String
            obj.add("args", context.serialize(src.args)); // FIXME - more - ?
            return obj;
        }
    }
    
    // TODO: JmlMethodSig

    class JmlMethodSpecsAdapter extends Adapter<JmlMethodSpecs> {
        public static final String[] fields = { "cases", "behaviors", "impliesThatCases", "forExampleCases" }; // FIXME - decl, desugared, feasible ?
        @Override
        public JmlMethodSpecs deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.JmlMethodSpecs(JmlJson.<JmlSpecificationCase>toList(values[0]));
            result.behaviors = JmlJson.<JmlMethodClauseBehaviors>toList(values[1]);
            result.impliesThatCases = JmlJson.<JmlSpecificationCase>toList(values[2]);
            result.forExampleCases = JmlJson.<JmlSpecificationCase>toList(values[3]);
            return result;
        }
    }
        
// TODO: JmlModelProgramStatement

    class JmlModifiersAdapter extends Adapter<JmlModifiers> {
        public static final String[] fields = { "annotations", "flags", "jmlmods" };
        
        @Override
        public JmlModifiers deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            JmlModifiers result = (JmlModifiers)M.Modifiers(
                    (long)values[1],
                    JmlJson.<JCAnnotation>toList(values[0])
                    );
            result.jmlmods = JmlJson.<JmlToken>toList(values[2]);
            return result;
        }

    }
    
    // TODO: JCModuleDecl

    class JCNewArrayAdapter extends Adapter<JCNewArray> {
        public static final String[] fields = { "elemtype", "dims", "elems" }; // FIXME - needs more fields
    }

    class JmlNewClassAdapter extends Adapter<JmlNewClass> {
        public static final String[] fields = { "encl", "clazz", "args", "def"}; // FIXME - needs more fields
    }
    
    // TODO: JCOpens
    // abstract - JCOperatorExpression
    
    class JCPackageDeclAdapter extends Adapter<JCPackageDecl> {
        public static final String[] fields = { "annotations", "pid" };
        @Override
        public JCPackageDecl deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.PackageDecl(JmlJson.<JCAnnotation>toList(values[0]), (JCExpression)values[1]);
            return result;
        }
    }

    class JCParensAdapter extends Adapter<JCParens> {
        public static final String[] fields = { "expr" };
        public JCParens deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.Parens((JCExpression)values[0]);
            return result;
        }
    }
    
    // abstract JCPattern
    // TODO: JCPatternCaseLabel
    // TODO: JCPolyExpression
    
    class JCPrimitiveTypeTreeAdapter extends Adapter<JCPrimitiveTypeTree> {
        public static final String[] fields = { "typetag" };
        public JCPrimitiveTypeTree deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.TypeIdent((TypeTag)values[0]);
            return result;
        }
        
    }

    class JmlPrimitiveTypeTreeAdapter extends Adapter<JmlPrimitiveTypeTree> {
        public static final String[] fields = { "typetag", "jmlclausekind", "typeName" };
        @Override
        public JsonElement serialize(JmlPrimitiveTypeTree src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src, context);
            obj.add("typetag", context.serialize(src.typetag));
            obj.add("jmlclausekind", str(src.jmlclausekind)); // FIXME - how to deserialize this
            obj.add("typeName", context.serialize(src.typeName));
            return obj;
        }
        public JmlPrimitiveTypeTree deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = (JmlPrimitiveTypeTree)M.TypeIdent((TypeTag)values[0]); // FIXME - needs fixing
            return result;
        }
    }
    
    // TODO: JCProvides

    class JmlQuantifiedExprAdapter extends Adapter<JmlQuantifiedExpr> {
        public static final String[] fields = { "kind", "decls", "range", "value", "triggers", "failure" };
        @Override
        public JsonElement serialize(JmlQuantifiedExpr src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src, context);
            obj.add("kind", str(src.kind)); // FIXME
            obj.add("decls", context.serialize(src.decls));
            obj.add("range", context.serialize(src.range));
            obj.add("value", context.serialize(src.value));
            obj.add("triggers", context.serialize(src.triggers));
            obj.add("failure", context.serialize(src.failure)); // TODO ???
            return obj;
        }
    }

    // TODO: JmlRange
    class JmlRangeAdapter extends Adapter<JmlRange> {
        public static final String[] fields = { "lo", "hi", "hiExclusive" };
    }
    
    // TODO: JCRecordPattern
    // TODO: JCRequires

    class JCReturnAdapter extends Adapter<JCReturn> {
        public static final String[] fields = { "expr" };
        public JCReturn deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.Return((JCExpression)values[0]);
            return result;
        }
    }
    
    // TODO: JmlSetComprehension

    class JmlSingletonAdapter extends Adapter<JmlSingleton> {
        public static final String[] fields = { "kind" };
        @Override
        public JsonElement serialize(JmlSingleton src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src, context);
            obj.add("kind", str(src.kind)); // FIXME
            return obj;
        }
    }
    

    class JCSkipAdapter extends Adapter<JCSkip> {
        public static final String[] fields = {};
        public JCSkip deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            return M.Skip();
        }
    }
    

    class JmlSpecificationCaseAdapter extends Adapter<JmlSpecificationCase> {
        public static final String[] fields = { "also", "modifiers", "token", "callee_only", "clauses" };  // FIXME - more?

        @Override
        public JmlSpecificationCase deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.JmlSpecificationCase(
                    (JmlModifiers)values[1], // mods
                    false,    // code
                    (IJmlClauseKind)values[2],    // t
                    (IJmlClauseKind)values[0],    // also
                    JmlJson.<JmlMethodClause>toList(values[4]), // clauses
                    (JCBlock)null     // block
                    );
            return result;
        }
}
    
    // abstract - JCStatement
    // TODO: JmlStatementDecls
    
    class JmlStatementExprAdapter extends Adapter<JmlStatementExpr> {
        public static final String[] fields = { "keyword", "expression", "optionalExpression" };
//        @Override
//        public JsonElement serialize(JmlStatementExpr src, java.lang.reflect.Type type, JsonSerializationContext context) {
//            var obj = newgson(src, context);
//            obj.add("keyword", str(src.keyword));  // FIXME
//            obj.add("expression", context.serialize(src.expression));
//            obj.add("optionalExpression", context.serialize(src.optionalExpression));
//            return obj;
//        }
    }

    // TODO: JmlStatementHavoc
    // TODO: JmlStatementLoop
    // TODO: JmlStatementLoopExpr

    class JmlStatementLoopExprAdapter extends Adapter<JmlStatementLoopExpr> {
        public static final String[] fields = { "name", "clauseType", "expression" };
        @Override
        public JsonElement serialize(JmlStatementLoopExpr src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src, context);
            obj.add("name", context.serialize(src.name));
            obj.add("clauseType", str(src.clauseType));  // FIXME
            obj.add("expression", context.serialize(src.expression));
            return obj;
        }
    }

    class JmlStatementLoopModifiesAdapter extends Adapter<JmlStatementLoopModifies> {
        public static final String[] fields = { "name", "clauseType", "expression" };
        @Override
        public JsonElement serialize(JmlStatementLoopModifies src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src, context);
            obj.add("name", context.serialize(src.name));
            obj.add("clauseType", str(src.clauseType));  // FIXME
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

    class JCSynchronizedAdapter extends Adapter<JCSynchronized> {
        public static final String[] fields = { "lock", "body" };
        @Override
        public JCSynchronized deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.Synchronized((JCExpression)values[0], (JCBlock)values[1]);
            return result;
        }
    }

    class JCThrowAdapter extends Adapter<JCThrow> {
        public static final String[] fields = { "expr" };
        public JCThrow deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.Throw((JCExpression)values[0]);
            return result;
        }
    }
    
    // TODO: JCTry
    // TODO: JmlTuple
    // TODO: JCTypeApply

    class JCTypeApplyAdapter extends Adapter<JCTypeApply> {
        public static final String[] fields = { "clazz", "arguments" };
        public JCTypeApply deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.TypeApply((JCExpression)values[0], JmlJson.<JCExpression>toList(values[1]));
            return result;
        }
    }

    class JCTypeCastAdapter extends Adapter<JCTypeCast> {
        public static final String[] fields = { "clazz", "expr" };
        public JCTypeCast deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.TypeCast((JCTree)values[0], (JCExpression)values[1]);
            return result;
        }
    }

    // TODO: JmlTypeClauseConditional
    // TODO: JmlTypeClauseConstraint
    // TODO: JmlTypeClauseDecl
    
    class JmlTypeClauseExprAdapter extends Adapter<JmlTypeClauseExpr> {
        public static final String[] fields = { "clauseType", "name", "expression" };
        @Override
        public JsonElement serialize(JmlTypeClauseExpr src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src, context);
            obj.add("clauseType", str(src.clauseType)); // FIXME
            obj.add("name", context.serialize(src.name));
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
    
    class JCTypeParameterAdapter extends Adapter<JCTypeParameter> {
        public static final String[] fields = { "name", "bounds", "annotations" };
        public JCTypeParameter deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            @SuppressWarnings("unchecked")
            var result = M.TypeParameter((Name)values[0], JmlJson.<JCExpression>toList(values[1]));
            result.annotations = JmlJson.<JCAnnotation>toList(values[2]);
            return result;
        }
    }
    // TODO: JCTypeUnion

    class JCUnaryAdapter extends Adapter<JCUnary> {
        public static final String[] fields = { "opcode", "arg" };
        public JCUnary deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            var result = M.Unary((JCTree.Tag)values[0], (JCExpression)values[1]);
            return result;
        }
    }
    
    // TODO: JCUses
    
    class JmlVariableDeclAdapter extends Adapter<JmlVariableDecl> {
        public static final String[] fields = { "mods", "name", "vartype", "init" };
        @Override
        public JmlVariableDecl deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var values = getFieldValues(json.getAsJsonObject());
            @SuppressWarnings("unchecked")
            var result = (JmlVariableDecl)M.VarDef((JCModifiers)values[0], (Name)values[1], (JCExpression)values[2], (JCExpression)values[3]);
            return result;
        }
    }
        
    class JmlWhileLoopAdapter extends Adapter<JmlWhileLoop> {
        public static final String[] fields = { "loopSpecs", "cond", "body" };
//        public JmlVariableDecl deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
//                throws JsonParseException {
//            var values = getFieldValues(json.getAsJsonObject());
//            @SuppressWarnings("unchecked")
//            var result = (JmlVariableDecl)M.VarDef((JCModifiers)values[0], (Name)values[1], (JCExpression)values[2], (JCExpression)values[3]);
//            return result;
//        }
    }

// TODO: JCWildcard
    // TODO: JCYield
    // TODO: LetExpr
    // TODO: TypeBoundKind
    
    /**************************/

    /** An adapter for Name */
    class NameAdapter implements JsonSerializer<Name>, JsonDeserializer<Name> {
        @Override
        public JsonElement serialize(Name src, java.lang.reflect.Type type, JsonSerializationContext context) {
            return primitive(Name.class, src);
        }
        @Override
        public Name deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var str = json.getAsJsonObject().get("primitive").getAsJsonPrimitive().getAsString();
            Name n = names.fromString(str);
            return n;
        }
    }
    
    /** An adapter for JmlToken */
    class JmlTokenAdapter implements JsonSerializer<JmlToken>, JsonDeserializer<JmlToken> {
        @Override
        public JsonElement serialize(JmlToken src, java.lang.reflect.Type type, JsonSerializationContext context) {
            return new JsonPrimitive(src.toString());
        }
        @Override
        public JmlToken deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            System.out.println("READING " + this.getClass() + " " + json);
            var str = json.getAsJsonObject().get("primitive").getAsJsonPrimitive().getAsString();
            var scanner = new com.sun.tools.javac.parser.JmlScanner.JmlScannerFactory(JmlJson.this.context).newScanner(str);
            scanner.nextToken();
            var token = scanner.jmlToken();
            System.out.println("JMLTOKEN " + token + " " + (token == null ? "" : token.getClass().toString()));
            return token;
        }
    }
    
    /** An adapter for TypeTag */
    class TypeTagAdapter implements JsonSerializer<TypeTag>, JsonDeserializer<TypeTag> {
        @Override
        public JsonElement serialize(TypeTag src, java.lang.reflect.Type type, JsonSerializationContext context) {
            return primitive(TypeTag.class, src);
        }
        @Override
        public TypeTag deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var str = json.getAsJsonObject().get("primitive").getAsJsonPrimitive().getAsString();
            var typetag = TypeTag.valueOf(str);
            return typetag;
        }
    }
    
    /** An adapter for JavaFileObject */
    class JavaFileObjectAdapter implements JsonSerializer<JavaFileObject>, JsonDeserializer<JavaFileObject> {
        @Override
        public JsonElement serialize(JavaFileObject src, java.lang.reflect.Type type, JsonSerializationContext context) {
            return primitive(JavaFileObject.class, src.getName());
        }
        // FIXME - what about 'kind'
        @Override
        public JavaFileObject deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var str = json.getAsJsonObject().get("primitive").getAsJsonPrimitive().getAsString();
            System.out.println("DESERIALIZING " + json + " " + typeOfT + " " + str);
            // FIXME - how to deserialize a JavaFileObject
            var jfo = new JavacFileManager(JmlJson.this.context,false,null).getJavaFileObject(str);
            return jfo;
        }
    }
    
    /** An adapter for JCTree.Tag */
    class OpTagAdapter implements JsonSerializer<JCTree.Tag>, JsonDeserializer<JCTree.Tag> {
        @Override
        public JsonElement serialize(JCTree.Tag src, java.lang.reflect.Type type, JsonSerializationContext context) {
            return primitive(JCTree.Tag.class, src);
        }
        @Override
        public JCTree.Tag deserialize(JsonElement json, java.lang.reflect.Type typeOfT, JsonDeserializationContext context)
                throws JsonParseException {
            var str = json.getAsJsonObject().get("primitive").getAsJsonPrimitive().getAsString();
            var tag = JCTree.Tag.valueOf(str);
            return tag;
        }
    }
    
    // FIXME - are we still using this -- is it for recording the attributed types?
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
