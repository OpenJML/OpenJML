package org.jmlspecs.openjml.esc;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.Set;

import javax.lang.model.element.Modifier;

import com.fasterxml.jackson.annotation.JsonAutoDetect.Visibility;
import com.fasterxml.jackson.annotation.JsonIdentityInfo;
import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonIgnoreType;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.fasterxml.jackson.annotation.JsonTypeInfo;
import com.fasterxml.jackson.annotation.JsonTypeInfo.As;
import com.fasterxml.jackson.annotation.JsonTypeInfo.Id;
import com.fasterxml.jackson.annotation.ObjectIdGenerators;
import com.fasterxml.jackson.annotation.PropertyAccessor;
import com.fasterxml.jackson.core.JsonGenerator;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.SerializationFeature;
import com.fasterxml.jackson.databind.SerializerProvider;
import com.fasterxml.jackson.databind.jsontype.TypeSerializer;
import com.fasterxml.jackson.databind.module.SimpleModule;
import com.fasterxml.jackson.databind.ser.std.StdSerializer;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.voodoodyne.jackson.jsog.JSOGGenerator;

public class JmlToJson {

    /**
     * The key used to register an instance of JmlEsc in the compilation context
     */
    protected static final Context.Key<JmlToJson> toJsonKey = new Context.Key<JmlToJson>();

    /**
     * The method used to obtain the singleton instance of JmlEsc for this
     * compilation context
     */
    public static JmlToJson instance(Context context) {
        JmlToJson instance = context.get(toJsonKey);
        if (instance == null) {
            instance = new JmlToJson();
            context.put(toJsonKey, instance);
        }
        return instance;
    }

    private final class DontSerializer<T> extends StdSerializer<T> {
        private static final long serialVersionUID = 1L;

        private DontSerializer(Class<T> t) {
            super(t);
        }

        @Override
        public void serialize(T obj, JsonGenerator json,
                SerializerProvider serializer) throws IOException {
            json.writeString(obj.toString());
        }

        @Override
        public void serializeWithType(T obj, JsonGenerator json,
                SerializerProvider provider, TypeSerializer serializer)
                throws IOException {
            serialize(obj, json, provider);
        }
    }

    @JsonIgnoreProperties(value = { "lineMap", "endPositions", "file",
            "sourceFile", "sourceMap", "sourcefile", "classfile", "context",
            "parser", "scanner", "log", "reader", "metadata",
            "members_field", "syms", "source", "starImportScope"})
    @JsonTypeInfo(use = Id.NAME, include = As.PROPERTY, property = "@class")
    @JsonIdentityInfo(generator = JSOGGenerator.class, property = "@id")
    private class DefaultMixin {
    }
    
    @JsonIgnoreType
    private class IgnoreMixin {
    }

    @JsonIdentityInfo(generator = ObjectIdGenerators.None.class)
    @JsonTypeInfo(use = Id.NONE)
    private class SimpleMixin {
    }
    
    private interface ModifiersMixin {
        @JsonProperty("flags")
        public Set<Modifier> getFlags();        
    }
    
    void dumpJson(Object node, File file) {
        SimpleModule nameModule = new SimpleModule()
                .addSerializer(Name.class, new DontSerializer<Name>(Name.class))
                .addSerializer(Names.class, new DontSerializer<Names>(Names.class));
        ObjectMapper objectMapper = new ObjectMapper()
                .registerModule(nameModule)
                .addMixIn(Object.class, DefaultMixin.class)
                .addMixIn(Collection.class, SimpleMixin.class)
                .addMixIn(TypeTag.class, SimpleMixin.class)
                .addMixIn(JCModifiers.class, ModifiersMixin.class)
                .addMixIn(Env.class, IgnoreMixin.class)
                .setVisibility(PropertyAccessor.FIELD, Visibility.ANY)
                .setVisibility(PropertyAccessor.GETTER, Visibility.NONE)
                .setVisibility(PropertyAccessor.IS_GETTER, Visibility.NONE)
                .enable(SerializationFeature.WRITE_ENUMS_USING_TO_STRING);
        objectMapper.getSerializerProvider()
                .setNullKeySerializer(new StdSerializer<Object>(Object.class) {
                    private static final long serialVersionUID = 1L;

                    @Override
                    public void serialize(Object arg0, JsonGenerator json,
                            SerializerProvider arg2) throws IOException {
                        json.writeFieldName("");
                    }
                });
        try {
            objectMapper.writeValue(file, node);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public void toJson(JCCompilationUnit node) {
        File file = new File(node.sourcefile.getName()+".json");
        dumpJson(node, file);
        System.out.println("AST dumped to " + file);
        System.exit(0);
    }
}
