package org.jmlspecs.openjml.esc;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.annotation.Annotation;
import java.lang.reflect.Field;
import java.net.URL;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.reflections.Reflections;
import org.reflections.scanners.SubTypesScanner;
import org.reflections.util.ClasspathHelper;
import org.reflections.util.ConfigurationBuilder;

import com.fasterxml.jackson.annotation.JsonAutoDetect.Visibility;
import com.fasterxml.jackson.annotation.JsonIdentityInfo;
import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
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
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;
import com.voodoodyne.jackson.jsog.JSOGGenerator;

public class JmlToJson {

    /** The key used to register an instance of JmlEsc in the compilation context */
    protected static final Context.Key<JmlToJson> toJsonKey =
        new Context.Key<JmlToJson>();
    

    /** The method used to obtain the singleton instance of JmlEsc for this compilation context */
    public static JmlToJson instance(Context context) {
        JmlToJson instance = context.get(toJsonKey);
        if (instance == null) {
            instance = new JmlToJson();
            context.put(toJsonKey,instance);
        }
        return instance;
    }

    
    @JsonIgnoreProperties(value = { "owner", "toplevel", "scope", "env", "topLevelEnv", "namedImportScope", "starImportScope", "lineMap", "endPositions",
            "members_field", "refiningSpecDecls", "file", "outer_field", "associatedSource",
            "interface", "sourceFile", "source", "sourceMap", "sourcefile", "metadata",
            "classfile", "context", "parser", "scanner", "log", "reader", "syms", "pos" })
    @JsonTypeInfo(use = Id.NAME, include = As.PROPERTY, property = "@class")
    @JsonIdentityInfo(generator = JSOGGenerator.class, property = "@id")
    public class DefaultMixin {
    }

    @JsonIdentityInfo(generator = ObjectIdGenerators.None.class)
    @JsonTypeInfo(use = Id.NONE)
    public class SimpleMixin {   
    }
//
//    @JsonIgnoreProperties({"table"})
//    @JsonAutoDetect(fieldVisibility=Visibility.NONE, getterVisibility=Visibility.NONE, isGetterVisibility=Visibility.NONE, setterVisibility=Visibility.NONE)
//    public class NameMixin extends AllMixin {
//        @JsonProperty
//        public String getName() { return toString(); }
//    }

    class MyDtoNullKeySerializer extends StdSerializer<Object> {
        private static final long serialVersionUID = 1L;

        public MyDtoNullKeySerializer() {
            this(null);
        }

        public MyDtoNullKeySerializer(Class<Object> t) {
            super(t);
        }

        @Override
        public void serialize(Object nullKey, JsonGenerator jsonGenerator,
                SerializerProvider unused) throws IOException {
            jsonGenerator.writeFieldName("");
        }
    }

    void dumpJson(Object node, File file) {
        SimpleModule nameModule = new SimpleModule()
                .addSerializer(Name.class, new StdSerializer<Name>(Name.class) {
                    private static final long serialVersionUID = 1L;
                    @Override
                    public void serialize(Name obj, JsonGenerator json,
                            SerializerProvider serializer) throws IOException {
                        json.writeString(obj.toString());
                    }
                    @Override
                    public void serializeWithType(Name obj, JsonGenerator json, SerializerProvider provider,
                            TypeSerializer serializer)
                        throws IOException {
                        serialize(obj, json, provider);
                    }
                });
        ObjectMapper objectMapper = new ObjectMapper()
                .registerModule(nameModule)
                .addMixIn(Object.class, DefaultMixin.class)
                .addMixIn(Collection.class, SimpleMixin.class)
                .addMixIn(TypeTag.class, SimpleMixin.class)
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
    
    private Map<Class<?>, Set<Class<?>>> getSubclasses(Class<?> rootClass) {
        Collection<URL> urls = new HashSet<>(ClasspathHelper.forPackage("com.sun.tools.javac"));
        urls.addAll(ClasspathHelper.forPackage("org.jmlspecs.openjml"));
        ConfigurationBuilder config = new ConfigurationBuilder()
                .setUrls(urls)
                .setScanners(new SubTypesScanner());
        Reflections r = new Reflections(config);
        System.out.println("Subclasses of "+rootClass);
        Map<Class<?>, Set<Class<?>>> subclasses = new HashMap<>();
        for (Class<?> clazz1 : r.getSubTypesOf(rootClass)) {
            Class<?> super1 = clazz1.getSuperclass();
            if (!subclasses.containsKey(super1))
                subclasses.put(super1, new HashSet<>());
            subclasses.get(super1).add(clazz1);
        }
        return subclasses;
    }
    
    String indent(int depth) {
        StringBuilder sb = new StringBuilder();
        for (int i=0; i<depth; i++)
            sb.append("  ");
        return sb.toString();
    }

    String[] jsonIgnoreProperties() {
        for (Annotation annotation: DefaultMixin.class.getAnnotations()) 
            if (annotation instanceof JsonIgnoreProperties) {
                JsonIgnoreProperties ignore = (JsonIgnoreProperties) annotation;
                return ignore.value();
            }
        throw new RuntimeException("Couldn't find ignore properties");
    }
    
    private void dumpHierarchy(Class<?> clazz, Map<Class<?>, Set<Class<?>>> subclasses, Collection<String> ignoreProperties, int depth, PrintStream out) {
        String indent = indent(depth);
        out.println(indent + "- name: " + clazz.getSimpleName());
        out.println(indent + "  fields:");
        for (Field field: clazz.getFields())
            if (!ignoreProperties.contains(field.getName()))
                out.println(indent + "  - {type: " + field.getType().getSimpleName() + ", name: " + field.getName() + "}");
        if (subclasses.containsKey(clazz)) {
            out.println(indent + "  subclasses:");
            for (Class<?> subclass: subclasses.get(clazz))
                dumpHierarchy(subclass, subclasses, ignoreProperties, depth+1, out);
        }
    }
    
//    void dumpTypes(Map<Class<?>, Set<Class<?>>> subclasses, PrintStream out) {
//        for (Class<?> clazz: subclasses.keySet()) {
//            out.println("type "+clazz.getSimpleName() + " =");
//            for (Class<?> subclass: subclasses.get(clazz)) {
//                if (subclasses.containsKey(subclass))
//                    out.println("  | "+subclass.getSimpleName());
//                else {
//                    out.print("  | "+subclass.getSimpleName()+" of ");
//                    for (Field field: )
//                }
//            }
//        }
//    }
    
    public void toJson(JCCompilationUnit node) {

        File file = new File(node.sourcefile.getName().replace(".java", ".json"));
//        if (file.exists())
//            System.out.println("Not dumping AST to "+file+", file exists");
//        else {
            System.out.println("Dumping AST to "+file);
            dumpJson(node, file);
            System.exit(0);
//        }
    }

    public void toJson(JCClassDecl node) {
//        for (StackTraceElement stackTrace : Thread.currentThread().getStackTrace())
//            System.out.println(stackTrace);
//        System.out.println("############ OVERHERE ###############");

//        Map<Class<?>, Set<Class<?>>> subclasses = getSubclasses(JCTree.class);
//        try {
//            OutputStream writer = Files.newOutputStream(Paths.get("classes-jctree.yaml"), StandardOpenOption.CREATE);
//            dumpHierarchy(JCTree.class, subclasses, Arrays.asList(jsonIgnoreProperties()), 0, new PrintStream(writer));
//        } catch (IOException e) {
//            e.printStackTrace();
//        }
        
//        try {
//            OutputStream writer= Files.newOutputStream(Paths.get("types.ml"), StandardOpenOption.WRITE);
//            dumpTypes(subclasses, new PrintStream(writer));

        File file = new File(node.name.toString()+".json");
//        if (file.exists())
//            System.out.println("Not dumping AST to "+file+", file exists");
//        else {
            System.out.println("Dumping AST to "+file);
            dumpJson(node, file);
            System.exit(0);
//        }
    }
}
