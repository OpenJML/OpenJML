/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.lang.annotation.Annotation;
import java.lang.reflect.Field;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.OpenOption;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.Arrays;
import java.util.Collection;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.IAPI;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.ProverResult;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;
import org.reflections.Reflections;
import org.reflections.scanners.SubTypesScanner;
import org.reflections.util.ClasspathHelper;
import org.reflections.util.ConfigurationBuilder;

import com.fasterxml.jackson.annotation.JsonAutoDetect.Visibility;
import com.fasterxml.jackson.annotation.JsonIdentityInfo;
import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
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
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.PropagatedException;
import com.voodoodyne.jackson.jsog.JSOGGenerator;

/**
 * This class is the main driver for executing ESC on a Java/JML AST. It
 * formulates the material to be proved, initiates the proofs, and obtains and
 * reports the results. The class is also a TreeScanner so that it can easily
 * walk the tree to find all class and method declarations.
 * <P>
 * To use, instantiate an instance of JmlEsc, and then call either visitClassDef
 * or visitMethodDef; various options from JmlOptions will be used. In particular,
 * the -boogie option affects which implementation of ESC is used,
 * and the -prover and -exec options (and the openjml.prover... properties)
 * determine which prover is used.
 * 
 * @author David R. Cok
 */
public class JmlEsc extends JmlTreeScanner {

    /** The key used to register an instance of JmlEsc in the compilation context */
    protected static final Context.Key<JmlEsc> escKey =
        new Context.Key<JmlEsc>();

    /** The method used to obtain the singleton instance of JmlEsc for this compilation context */
    public static JmlEsc instance(Context context) {
        JmlEsc instance = context.get(escKey);
        if (instance == null) {
            instance = new JmlEsc(context);
            context.put(escKey,instance);
        }
        return instance;
    }
    
//    public IAPI.IProofResultListener proofResultListener = null;
    
    /** The compilation context, needed to get common tools, but unique to this compilation run*/
    @NonNull Context context;

    /** Used to obtain cached symbols, such as basic types */
    @NonNull Symtab syms;
    
    /** The tool to log problem reports */ 
    @NonNull Log log;
    
    /** The OpenJML utilities object */
    @NonNull Utils utils;
    
    /** true if compiler options are set to a verbose mode */
    boolean verbose;
    
    /** Just for debugging esc */
    public static boolean escdebug = false; // May be set externally to enable debugging while testing
    
    /** The assertion adder instance used to translate */
    public JmlAssertionAdder assertionAdder;
    
    /** The JmlEsc constructor, which initializes all the tools and other fields. */
    public JmlEsc(Context context) {
        this.context = context;
        this.syms = Symtab.instance(context);
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        
    }

    /** Initializes assertionAdder and proverToUse and translates the argument */
    public void check(JCTree tree) {
        this.verbose = escdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
                || utils.jmlverbose >= Utils.JMLVERBOSE;
        this.assertionAdder = new JmlAssertionAdder(context, true, false);
        try {
            // We convert the whole tree first
        	assertionAdder.convert(tree); // get at the converted tree through the map
        	// And then we walk the tree to see which items are to be proved
        	tree.accept(this);
        } catch (PropagatedException | Main.JmlCanceledException e) {
        	// Canceled
    		Main.instance(context).canceled = true;
    		count(IProverResult.ERROR);
    		throw e;
        } catch (Exception e) {
            // No further error messages needed - FIXME - is this true?
            count(IProverResult.ERROR);
            String info = "";
            if (tree instanceof JCClassDecl) info = "class " + ((JCClassDecl)tree).name.toString();
            if (tree instanceof JCCompilationUnit) info = "compilation unit " + (((JCCompilationUnit)tree).sourcefile.toString());
            log.error("jml.internal","Should not be catching an exception in JmlEsc.check: "+ e.toString() + " while translating " + info);
            e.printStackTrace();
        } catch (Throwable e) {
            // No further error messages needed - FIXME - is this true?
            count(IProverResult.ERROR);
            String info = "";
            if (tree instanceof JCClassDecl) info = "class " + ((JCClassDecl)tree).name.toString();
            if (tree instanceof JCCompilationUnit) info = "compilation unit " + (((JCCompilationUnit)tree).sourcefile.toString());
            log.error("jml.internal","Should not be catching a Java error in JmlEsc.check: "+ e.toString() + " while translating " + info);
            e.printStackTrace();
        }
    }
    
    @JsonIgnoreProperties(value = { "owner", "toplevel", "scope", "env",
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

    void dumpJson(JCClassDecl node, File file) {
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
    
    /** Visit a class definition */
    @Override
    public void visitClassDef(JCClassDecl node) {
        
        Map<Class<?>, Set<Class<?>>> subclasses = getSubclasses(JCTree.class);
        try {
            OutputStream writer = Files.newOutputStream(Paths.get("classes-jctree.yaml"), StandardOpenOption.CREATE);
            dumpHierarchy(JCTree.class, subclasses, Arrays.asList(jsonIgnoreProperties()), 0, new PrintStream(writer));
        } catch (IOException e) {
            e.printStackTrace();
        }
        
//        try {
//            OutputStream writer= Files.newOutputStream(Paths.get("types.ml"), StandardOpenOption.WRITE);
//            dumpTypes(subclasses, new PrintStream(writer));

        File file = new File(node.name.toString()+".json");
        if (file.exists())
            System.out.println("Not dumping AST to "+file+", file exists");
        else {
            System.out.println("Dumping AST to "+file);
            dumpJson(node, file);
            System.exit(0);
        }

        boolean savedMethodsOK = allMethodsOK;
        allMethodsOK = true;
        Main.instance(context).pushOptions(node.mods);

        // The super class takes care of visiting all the methods
        utils.progress(0,1,"Proving methods in " + utils.classQualifiedName(node.sym) ); //$NON-NLS-1$
        long classStart = System.currentTimeMillis();
        boolean doDefsInSortedOrder = true;
        if (doDefsInSortedOrder && !Utils.testingMode) { // Don't sort in tests because too many golden outputs were created before sorting
            scan(node.mods);
            scan(node.typarams);
            scan(node.extending);
            scan(node.implementing);
            JCTree[] arr = node.defs.toArray(new JCTree[node.defs.size()]);
            Arrays.sort(arr, new java.util.Comparator<JCTree>() { public int compare(JCTree o, JCTree oo) { 
                Name n = o instanceof JCClassDecl ? ((JCClassDecl)o).name : o instanceof JCMethodDecl ? ((JCMethodDecl)o).getName() : null;
                Name nn = oo instanceof JCClassDecl ? ((JCClassDecl)oo).name : oo instanceof JCMethodDecl ? ((JCMethodDecl)oo).getName() : null;
                return n == nn ? 0 : n == null ? -1 : nn == null ? 1 : n.toString().compareToIgnoreCase(nn.toString());
            	} });
            for (JCTree d: arr) {
            	scan(d);
            }
        } else {
            super.visitClassDef(node);
        }
        long classDuration = System.currentTimeMillis() - classStart;
        utils.progress(0,1,"Completed proving methods in " + utils.classQualifiedName(node.sym) +  //$NON-NLS-1$
                (Utils.testingMode ? "" : String.format(" [%4.2f secs]", (classDuration/1000.0)))); //$NON-NLS-1$
        if (utils.isModel(node.sym)) classesModel++; 
        else {
            classes++;
            if (allMethodsOK) classesOK++;
        }
        allMethodsOK = savedMethodsOK;
        Main.instance(context).popOptions();
    }

    /** When we visit a method declaration, we translate and prove the method;
     * we do not walk into the method any further from this call, only through
     * the translation mechanism.  
     */
    @Override
    public void visitMethodDef(@NonNull JCMethodDecl decl) {
        if (decl.sym.isConstructor() && decl.sym.owner.isAnonymous()) {
            // Constructors for anonymous classes are not explicit. They are checked
            // in the course of instantiating the anonymous object.
            return;
        }

        Main.instance(context).pushOptions(decl.mods);
        IProverResult res = null;
        if (decl.body == null) return; // FIXME What could we do with model methods or interfaces, if they have specs - could check that the preconditions are consistent
        if (!(decl instanceof JmlMethodDecl)) {
            JCDiagnostic d = (log.factory().warning(log.currentSource(), decl.pos(), "jml.internal","Unexpected non-JmlMethodDecl in JmlEsc - not checking " + utils.qualifiedMethodSig(decl.sym)));
            log.report(d);
            //log.warning(decl.pos(),"jml.internal","Unexpected non-JmlMethodDecl in JmlEsc - not checking " + utils.qualifiedMethodSig(decl.sym)); //$NON-NLS-2$
            res = new ProverResult("",ProverResult.ERROR,decl.sym).setOtherInfo(d);
            return;
        }
        JmlMethodDecl methodDecl = (JmlMethodDecl)decl;

        // Do any nested classes and methods first (which will recursively call
        // this method)
        super.visitMethodDef(methodDecl);

        if (skip(methodDecl)) {
            markMethodSkipped(methodDecl," (excluded by skipesc)"); //$NON-NLS-1$
            return;
        }

        if (!utils.filter(methodDecl,true)) {
            markMethodSkipped(methodDecl," (excluded by -method)"); //$NON-NLS-1$ // FIXME excluded by -method or -exclude
            return;
        }

        try {
    	    res = doMethod(methodDecl);
        } catch (PropagatedException e) {
            IAPI.IProofResultListener proofResultListener = context.get(IAPI.IProofResultListener.class);
            if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, new ProverResult("",IProverResult.CANCELLED,methodDecl.sym));
            throw e;
        }
        Main.instance(context).popOptions();
        return;        
    }
    
    public static boolean skip(JmlMethodDecl methodDecl) {
        if (methodDecl.mods != null) {
            for (JCTree.JCAnnotation a : methodDecl.mods.annotations) {
                if (a != null && a.type.toString().equals("org.jmlspecs.annotation.SkipEsc")) { // FIXME - do this without converting to string
                    return true;
                }
            }
        }
        return false;
    }
    
    // FIXME - perhaps shoud not be in JmlEsc
    public static boolean skipRac(JmlMethodDecl methodDecl) {
        if (methodDecl.mods != null) {
            for (JCTree.JCAnnotation a : methodDecl.mods.annotations) {
                if (a != null && a.type.toString().equals("org.jmlspecs.annotation.SkipRac")) { // FIXME - do this without converting to string
                    return true;
                }
            }
        }
        return false;
    }
    
    public IProverResult markMethodSkipped(JmlMethodDecl methodDecl, String reason) {
        if (JmlOption.isOption(context, JmlOption.SKIPPED)) utils.progress(1,1,"Skipping proof of " + utils.qualifiedMethodSig(methodDecl.sym) + reason); //$NON-NLS-1$ //$NON-NLS-2$
        
        // FIXME - this is all a duplicate from MethodProverSMT
        IProverResult.IFactory factory = new IProverResult.IFactory() {
            @Override
            public IProverResult makeProverResult(MethodSymbol msym, String prover, IProverResult.Kind kind, java.util.Date start) {
                ProverResult pr = new ProverResult(prover,kind,msym);
                pr.methodSymbol = msym;
                if (start != null) {
                    pr.accumulateDuration((pr.timestamp().getTime()-start.getTime())/1000.);
                    pr.setTimestamp(start);
                }
                return pr;
            }
        };
        IProverResult res = factory.makeProverResult(methodDecl.sym,"",IProverResult.SKIPPED,new java.util.Date());
        IAPI.IProofResultListener proofResultListener = context.get(IAPI.IProofResultListener.class);
        if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, res);
        count(IProverResult.SKIPPED, methodDecl.sym);
        return res;
    }
    
    /** Returns the prover specified by the options. */
    public String pickProver() {
        // Pick a prover to use
        String proverToUse = JmlOption.value(context,JmlOption.PROVER);
        if (proverToUse == null || proverToUse.isEmpty()) proverToUse = Options.instance(context).get(Strings.defaultProverProperty);
        if (proverToUse == null || proverToUse.isEmpty() || proverToUse.equals("z3")) {
            proverToUse = "z3_4_3";
        }
        return proverToUse;
    }
    
    // FIXME _ need synchronizatipon on this field
    MethodProverSMT currentMethodProver = null;

    public void abort() {
        if (currentMethodProver != null) currentMethodProver.abort();
    }
    
    /** Do the actual work of proving the method */
    protected IProverResult doMethod(@NonNull JmlMethodDecl methodDecl) {
        boolean printPrograms = this.verbose || JmlOption.includes(context, JmlOption.SHOW, "translated") || JmlOption.includes(context, JmlOption.SHOW, "program");
        
        if (skip(methodDecl)) {
            return markMethodSkipped(methodDecl," (because of SkipEsc annotation)");
        }
        
        String proverToUse = pickProver();
        
        utils.progress(0,1,"Starting proof of " + utils.qualifiedMethodSig(methodDecl.sym) + " with prover " + (Utils.testingMode ? "!!!!" : proverToUse)); //$NON-NLS-1$ //$NON-NLS-2$
        long methodStart = System.currentTimeMillis();
        log.resetRecord();
//        int prevErrors = log.nerrors;

        IAPI.IProofResultListener proofResultListener = context.get(IAPI.IProofResultListener.class);
        if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, new ProverResult(proverToUse,IProverResult.RUNNING,methodDecl.sym));

        // The code in this method decides whether to attempt a proof of this method.
        // If so, it sets some parameters and then calls proveMethod
        
        boolean isConstructor = methodDecl.sym.isConstructor();
        boolean doEsc = ((methodDecl.mods.flags & (Flags.SYNTHETIC|Flags.ABSTRACT|Flags.NATIVE)) == 0);
            // TODO: Could check that abstract or native methods have consistent specs

        // Don't do ESC on the constructor of Object
        // FIXME - why?  (we don't have the source anyway, so how would we get here?)
        if (methodDecl.sym.owner == syms.objectType.tsym && isConstructor) doEsc = false;
        if (!doEsc) return null; // FIXME - SKIPPED?

        // print the body of the method to be proved
        if (printPrograms) {
            PrintWriter noticeWriter = log.getWriter(WriterKind.NOTICE);
            noticeWriter.println(Strings.empty);
            noticeWriter.println("--------------------------------------"); //$NON-NLS-1$
            noticeWriter.println(Strings.empty);
            noticeWriter.println("STARTING PROOF OF " + utils.qualifiedMethodSig(methodDecl.sym)); //$NON-NLS-1$
            noticeWriter.println(JmlSpecs.instance(context).getDenestedSpecs(methodDecl.sym).toString());
            noticeWriter.println(JmlPretty.write(methodDecl.body));
        }
        
        IProverResult res = null;
        try {
            if (JmlOption.isOption(context, JmlOption.BOOGIE)) {
                res = new MethodProverBoogie(this).prove(methodDecl);
            } else {
                currentMethodProver = new MethodProverSMT(this);
                res = currentMethodProver.prove(methodDecl,proverToUse);
                currentMethodProver = null;
            }
            long duration = System.currentTimeMillis() - methodStart;
            utils.progress(1,1,"Completed proof of " + utils.qualifiedMethodSig(methodDecl.sym)  //$NON-NLS-1$ 
                    + " with prover " + (Utils.testingMode ? "!!!!" : proverToUse)  //$NON-NLS-1$ 
                    + " - "
                    + (  res.isSat() ? "with warnings" 
                       : res.result() == IProverResult.UNSAT ? "no warnings"
                               : res.result().toString())
                    + (Utils.testingMode ? "" : String.format(" [%4.2f secs]", (duration/1000.0)))
                    );
            count(res.result(), methodDecl.sym);
            
//            if (log.nerrors != prevErrors) {
//                res = new ProverResult(proverToUse,IProverResult.ERROR,methodDecl.sym);
//            }

        } catch (Main.JmlCanceledException | PropagatedException e) {
            res = new ProverResult(proverToUse,ProverResult.CANCELLED,methodDecl.sym); // FIXME - I think two ProverResult.CANCELLED are being reported
           // FIXME - the following will throw an exception because progress checks whether the operation is cancelled
            utils.progress(1,1,"Proof CANCELLED of " + utils.qualifiedMethodSig(methodDecl.sym)  //$NON-NLS-1$ 
            + " with prover " + (Utils.testingMode ? "!!!!" : proverToUse)  //$NON-NLS-1$ 
            + " - exception"
            );
            throw (e instanceof Main.JmlCanceledException) ? new PropagatedException(e) : e;
        } catch (Throwable e) {
            JCDiagnostic d;
            if (e instanceof SMTTranslator.JmlBVException) {
                d = log.factory().error(log.currentSource(), methodDecl, "jml.message", "Proof aborted because bit-vector operations are not supported. Use option -escBV=true");
            } else {
                d = log.factory().error(log.currentSource(), null, "jml.internal","Prover aborted with exception: " + e.toString());
                e.printStackTrace(System.out);
            }
            log.report(d);
            count(IProverResult.ERROR);

            res = new ProverResult(proverToUse,ProverResult.ERROR,methodDecl.sym).setOtherInfo(d);
            //log.error("jml.internal","Prover aborted with exception: " + e.getMessage());
            utils.progress(1,1,"Proof ABORTED of " + utils.qualifiedMethodSig(methodDecl.sym)  //$NON-NLS-1$ 
                    + " with prover " + (Utils.testingMode ? "!!!!" : proverToUse)  //$NON-NLS-1$ 
                    + " - exception"
                    );
            // FIXME - add a message? use a factory?
        } finally {
        	if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, res);
        	if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, new ProverResult(proverToUse,IProverResult.COMPLETED,methodDecl.sym));
        }
        return res;
    }
        
    public Map<IProverResult.Kind,Integer> counts = new HashMap<>();
    public Map<IProverResult.Kind,Integer> modelcounts = new HashMap<>();
    public int classes;
    public int classesOK;
    public int classesModel;
    public int methodsModel;
    public boolean allMethodsOK;
    
    private long startTime;
    
    public void initCounts() {
        classes = classesOK = classesModel = methodsModel = 0;
        counts.clear();
        modelcounts.clear();
        startTime = System.currentTimeMillis();
    }
    
    public void count(IProverResult.Kind r, MethodSymbol sym) {
        if (utils.isModel(sym) || utils.isModel(sym.owner)) {
            modelcounts.put(r, modelvalue(r) + 1);
        } else {
            count(r);
        }
    }
    public void count(IProverResult.Kind r) {
        counts.put(r,  value(r) + 1);
        if (r != IProverResult.UNSAT) allMethodsOK = false;
    }
    
    public int value(IProverResult.Kind r) {
        Integer i = counts.get(r);
        return i == null ? 0 : i;
    }
    
    public int modelvalue(IProverResult.Kind r) {
        Integer i = modelcounts.get(r);
        return i == null ? 0 : i;
    }
    
    public int allmodelvalue() {
        int sum = 0;
        for (Integer i: modelcounts.values()) {
            if (i == null) i = 0;
            sum += i;
        }
        return sum;
    }
    
    public int allvalue() {
        int sum = 0;
        for (Integer i: counts.values()) {
            sum += i;
        }
        return sum;
    }
    
    public String reportCounts() {
        StringBuilder s = new StringBuilder();
        int t = 0; int tt;
        s.append("Summary:" + Strings.eol);
        s.append("  Valid:        " + (tt=value(IProverResult.UNSAT)) + Strings.eol);
        t += tt;
        s.append("  Invalid:      " + (tt=value(IProverResult.SAT)+value(IProverResult.POSSIBLY_SAT)+value(IProverResult.UNKNOWN)) + Strings.eol);
        t += tt;
        s.append("  Infeasible:   " + (tt=value(IProverResult.INFEASIBLE)) + Strings.eol);
        t += tt;
        s.append("  Timeout:      " + (tt=value(IProverResult.TIMEOUT)) + Strings.eol);
        t += tt;
        s.append("  Error:        " + (tt=value(IProverResult.ERROR)) + Strings.eol);
        t += tt;
        s.append("  Skipped:      " + (tt=value(IProverResult.SKIPPED)) + Strings.eol);
        t += tt;
        s.append(" TOTAL METHODS: " + t + Strings.eol);
        if (t != allvalue()) s.append("  DISCREPANCY " + t + " vs. " + allvalue() + Strings.eol);
        s.append(" Classes:       " + classesOK + " proved of " + classes + Strings.eol);
        s.append(" Model Classes: " + classesModel + Strings.eol);
        s.append(" Model methods: " + modelvalue(IProverResult.UNSAT) + " proved of " + allmodelvalue() + Strings.eol);
        long duration = System.currentTimeMillis() - startTime;
        s.append(" DURATION: " + String.format("%12.1f",(duration/1000.0)) + " secs" + Strings.eol);
        return s.toString();
    }
    
//    // FIXME - move these away from being globals
//    
//    static public IProverResult mostRecentProofResult = null;
    
    
}

