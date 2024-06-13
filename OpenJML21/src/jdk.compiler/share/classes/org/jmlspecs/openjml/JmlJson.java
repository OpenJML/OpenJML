package org.jmlspecs.openjml;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.Env;

import com.sun.tools.javac.tree.JCTree;
import static com.sun.tools.javac.tree.JCTree.*;

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
 */
// TODO:
// - fix serialization of flags
// - output only command-line files (or give a choice)
// - documentation of --show
// - all the rest of the adapters
// - a check for missing adapters
// - remove @Expose annotations
// - deserializers; serialize-deserialize test
// - auto registration of adapters

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
        builder.registerTypeAdapter(Name.class, new NameAdapter());
        builder.registerTypeAdapter(Type.class, new PTypeAdapter());
        builder.registerTypeAdapter(Symbol.class, new SymbolAdapter());
        builder.registerTypeAdapter(Symbol.PackageSymbol.class, new SymbolAdapter());
        builder.registerTypeAdapter(com.sun.tools.javac.util.Names.class, new NamesAdapter());
        builder.registerTypeAdapter(com.sun.tools.javac.util.JavacMessages.class, new JavacMessagesAdapter());
        builder.registerTypeAdapter(Type.JCVoidType.class, new JCVoidTypeAdapter());
        builder.registerTypeAdapter(JCAnnotation.class, new JCAnnotationAdapter());
        builder.registerTypeAdapter(Env.class, new EnvAdapter());
        builder.registerTypeAdapter(JCPackageDecl.class, new JCPackageDeclAdapter());

//        builder.registerTypeAdapter(JCBinary.class, new JCBinaryAdapter());
//        builder.registerTypeAdapter(JCConditional.class, new JCConditionalAdapter());
//        builder.registerTypeAdapter(JCLiteral.class, new JCLiteralAdapter());
//        builder.registerTypeAdapter(JCParens.class, new JCParensAdapter());
//        builder.registerTypeAdapter(JCUnary.class, new JCUnaryAdapter());
       // builder.registerTypeAdapter(JmlCompilationUnit.class, new JmlCompilationUnitAdapter());
        
        var prefix = "com.sun.tools.javac.tree.JCTree$";
        var suffix = "Adapter".length();
        var constructors = JCBinaryAdapter.class.getDeclaredConstructors();
        for (var constructor : constructors)
            System.out.println("PARAMS " + java.util.Arrays.toString(constructor.getParameterTypes()));
        for (Class<?> nestedClass : JmlJson.class.getDeclaredClasses()) {
            var adapter = nestedClass.toString();
            var astclass = adapter.substring(adapter.indexOf('$')+1, adapter.length()-suffix);
            try {
                // FIXME - need to get constructor for inner class, and call with outer object
                var cons = nestedClass.getDeclaredConstructors()[0];
                var adap = cons.newInstance(this);
                builder.registerTypeAdapter(Class.forName(prefix + astclass), adap);
                System.out.println((prefix + astclass) + " " + adapter);
            } catch (Exception e) {
                System.out.println("FAILURE " + e);
                System.out.println((prefix + astclass) + " " + adapter);
            }
        }
        this.gson = builder.excludeFieldsWithoutExposeAnnotation().setPrettyPrinting().create();
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
        return new JsonPrimitive(s);
    }

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

    class JCLiteralAdapter implements JsonSerializer<JCLiteral> {
        @Override
        public JsonElement serialize(JCLiteral src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("typetag", str(src.typetag));
            obj.add("value", str(src.value));
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

    class JCUnaryAdapter implements JsonSerializer<JCUnary> {
        @Override
        public JsonElement serialize(JCUnary src, java.lang.reflect.Type type, JsonSerializationContext context) {
            var obj = newgson(src);
            obj.add("opcode", str(src.getTag()));
            obj.add("arg", context.serialize(src.arg));
            return obj;
        }
    }
    
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
    static class PTypeAdapter extends TypeAdapter<Type> {
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
    static class JCVoidTypeAdapter extends TypeAdapter<Type.JCVoidType> {
        public Type.JCVoidType read(JsonReader reader) throws IOException {
          if (reader.peek() == JsonToken.NULL) {
            reader.nextNull();
            return null;
          }
          return null;
        }
        public void write(JsonWriter writer, Type.JCVoidType value) throws IOException {
          if (value == null) {
            writer.nullValue();
            return;
          }
          writer.value("void");
        }
    }
    static class JavacMessagesAdapter extends TypeAdapter<com.sun.tools.javac.util.JavacMessages> {
        public com.sun.tools.javac.util.JavacMessages read(JsonReader reader) throws IOException {
          if (reader.peek() == JsonToken.NULL) {
            reader.nextNull();
            return null;
          }
          return null;
        }
        public void write(JsonWriter writer, com.sun.tools.javac.util.JavacMessages value) throws IOException {
          writer.nullValue();
        }
    }
    static class SymbolAdapter extends TypeAdapter<Symbol> {
        public Symbol read(JsonReader reader) throws IOException {
          if (reader.peek() == JsonToken.NULL) {
            reader.nextNull();
            return null;
          }
          return null;
        }
        public void write(JsonWriter writer, Symbol value) throws IOException {
          if (value == null) {
            writer.nullValue();
            return;
          }
          String xy = value.toString() ;
          writer.value(xy);
        }
    }
    static class NamesAdapter extends TypeAdapter<com.sun.tools.javac.util.Names> {
        public com.sun.tools.javac.util.Names read(JsonReader reader) throws IOException {
          if (reader.peek() == JsonToken.NULL) {
            reader.nextNull();
            return null;
          }
          return null;
        }
        public void write(JsonWriter writer, com.sun.tools.javac.util.Names value) throws IOException {
          writer.nullValue();
        }
    }
    static class JCAnnotationAdapter extends TypeAdapter<JCAnnotation> {
        public JCAnnotation read(JsonReader reader) throws IOException {
          if (reader.peek() == JsonToken.NULL) {
            reader.nextNull();
            return null;
          }
          return null;
        }
        public void write(JsonWriter writer, JCAnnotation value) throws IOException {
          writer.value(value.toString());
        }
    }
    static class EnvAdapter extends TypeAdapter<Env<com.sun.tools.javac.comp.AttrContext>> {
        public Env<com.sun.tools.javac.comp.AttrContext> read(JsonReader reader) throws IOException {
          if (reader.peek() == JsonToken.NULL) {
            reader.nextNull();
            return null;
          }
          return null;
        }
        public void write(JsonWriter writer, Env<com.sun.tools.javac.comp.AttrContext> value) throws IOException {
          writer.nullValue();
        }
    }
    static class JCPackageDeclAdapter extends TypeAdapter<JCPackageDecl> {
        public JCPackageDecl read(JsonReader reader) throws IOException {
          if (reader.peek() == JsonToken.NULL) {
            reader.nextNull();
            return null;
          }
          return null;
        }
        public void write(JsonWriter writer, JCPackageDecl value) throws IOException {
          writer.value(value.toString());
        }
    }
//    class JmlCompilationUnitAdapter extends TypeAdapter<JmlCompilationUnit> {
//        public JmlCompilationUnit read(JsonReader reader) throws IOException {
//          if (reader.peek() == JsonToken.NULL) {
//            reader.nextNull();
//            return null;
//          }
//          return null;
//        }
//        public void write(JsonWriter writer, JmlCompilationUnit value) throws IOException {
//            for (JCTree d: value.defs) {
//                writer.value(gson.toJson(d));
//                
//            }
//        }
//    }

}
