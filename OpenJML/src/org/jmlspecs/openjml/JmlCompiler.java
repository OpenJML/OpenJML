/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
// FIXME - do a review
package org.jmlspecs.openjml;

import static com.sun.tools.javac.util.ListBuffer.lb;

import java.util.Queue;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;
import org.jmlspecs.openjml.esc.JmlEsc;

import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.comp.Resolve;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Pair;

/**
 * This class extends the JavaCompiler class in order to find and parse
 * specification files when a Java source file is parsed.
 * 
 * @author David Cok
 */
public class JmlCompiler extends JavaCompiler {

    /** Registers a factory for producing JmlCompiler tools.
     * There is one instance for each instance of context.  
     * @param context the compilation context used for tools
     */
    public static void preRegister(final Context context) {
        context.put(compilerKey, new Context.Factory<JavaCompiler>() {
            public JmlCompiler make(Context context) {
                return new JmlCompiler(context);  // registers itself
            }
        });
    }
    
    /** A cached value indicating the verbosity level of tracing information. */
    protected boolean verbose;

    /** Cached value of the class loader */
    protected JmlResolve resolver;
    
    /** Cached value of the utilities object */
    protected Utils utils;
    
    /** A constructor for this tool, but do not use it directly - use instance()
     * instead to get a unique instance of this class for the context.
     * @param context the compilation context for which this instance is being created
     */
    protected JmlCompiler(Context context) {
        super(context);
        //shouldStopPolicy = CompileState.GENERATE;
        this.context = context;
        this.utils = Utils.instance(context);
        this.verbose = utils.jmlverbose >= Utils.JMLVERBOSE;
        this.resolver = JmlResolve.instance(context);
    }
    
    /** A flag that controls whether to get specs during a parse or not (if false 
     * then do, if true then do not).  This should be left in a false state
     * after being used to preclude parsing specs.
     */
    public boolean inSequence = false;
    
    /** This method is overridden in order to parse specification files along 
     * with parsing a Java file.  Note that it is called directly from 
     * JavaCompiler.complete and JavaCompiler.parse to do the actual parsing.
     * Thus when parsing an individual file (such as a spec file) it is also 
     * called (through parse).  Consequently we have to do this little trick 
     * with the "inSequence" field to avoid trying to parse the specifications
     * of specification files. [I'm not sure when, if ever, JavaCompiler.complete 
     * is called.  If it did not ever call this method here, we could override 
     * JavaCompiler.parse(JavaFileObject) instead, and avoid this
     * trickery with inSequence.]
     * <P>
     * <UL>
     * <LI>If inSequence is false, then this method parses the given content and associated specs.
     * The JmlCompilationUnit for the specs is assigned to the specsCompilationUnit field of the
     * JmlCompilationUnit for the .java file.
     * <LI>If inSequence is true, then this method parses just the given content.
     * <LI>In either case a JmlCompilationUnit is returned.
     * However, see the FIXME below regarding adding the .java file into an empty specs list.
     * </UL>
     */
    // TODO - when called from JavaCompiler.complete it seems that the end position information is not recorded
    // in the way that happens when called from JavaCompiler.parse.  Is this a problem in the Javac compiler?
    @Override
    public JCCompilationUnit parse(JavaFileObject fileobject, CharSequence content) {
        // TODO: Use a TaskEvent and a TaskListener here?
        if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(0,2,"parsing " + fileobject.toUri() );
        JCCompilationUnit cu = super.parse(fileobject,content);
        if (inSequence) {
            return cu;
        }
        if (cu instanceof JmlCompilationUnit) {
            JmlCompilationUnit jmlcu = (JmlCompilationUnit)cu;
            if (fileobject.getKind() == JavaFileObject.Kind.SOURCE) { // A .java file
                jmlcu.mode = JmlCompilationUnit.JAVA_SOURCE_PARTIAL;
                JavaFileObject specsFile = findSpecs(jmlcu,true);
                // FIXME - this comparison is not robust, though is usually working
                // we use it to avoid parsing a file twice (which would also give
                // duplicate error messages) - what does JavaCompiler do?
                //log.noticeWriter.println(f.toUri().normalize().getPath() + " VS " + javaCU.getSourceFile().toUri().normalize().getPath());
                if (specsFile != null && specsFile.equals(jmlcu.getSourceFile())) {
                    if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("The java file is its own specs for " + specsFile);
                    jmlcu.specsCompilationUnit = jmlcu;
                } else {
                    jmlcu.specsCompilationUnit = parseSingleFile(specsFile);
                }

                if (jmlcu.specsCompilationUnit == null) {
                    // If there are no specs, that means that not even the .java file is
                    // on the specification path.  That may well be something to warn
                    // about.  For now (and for the sake of the tests), we will be
                    // helpful and add the .java file to the specs sequence despite it
                    // not being on the specification path.
                    // TODO log.warning("jml.no.specs",filename.getName());
                    jmlcu.specsCompilationUnit = jmlcu;
                } else {
                    JmlCompilationUnit jcu = jmlcu.specsCompilationUnit;
                    if (jcu != cu) jcu.mode = JmlCompilationUnit.SPEC_FOR_SOURCE;
                }
                // Only need dependencies in interactive situations - Eclipse and programmatic api
                // Needs to be false for testing or we run out of memory
                if (false) {
                    JmlCompilationUnit jcu = jmlcu.specsCompilationUnit;
                    //log.noticeWriter.println(jmlcu.sourcefile + " depends on " + jcu.sourcefile);
                    Dependencies.instance(context).dependsOn(jmlcu.sourcefile,jcu.sourcefile);
                }
            } else {
                jmlcu.mode = JmlCompilationUnit.SPEC_FOR_SOURCE;
                JavaFileObject javaFile = findSpecs(jmlcu,false); // look for corresponding java file
                JmlCompilationUnit javacu = parseSingleFile(javaFile);
                if (javacu != null) {
                    javacu.specsCompilationUnit = jmlcu; 
                    javacu.mode = JmlCompilationUnit.JAVA_SOURCE_PARTIAL;
                    cu = javacu;
                } else {
                    log.warning("jml.no.java.file",jmlcu.sourcefile);
                }
                // Only need dependencies in interactive situations - Eclipse and programmatic api
                // Needs to be false for testing or we run out of memory
                if (false) {
                    JmlCompilationUnit jcu = jmlcu.specsCompilationUnit;
                    //log.noticeWriter.println(jmlcu.sourcefile + " depends on " + jcu.sourcefile);
                    Dependencies.instance(context).dependsOn(jmlcu.sourcefile,jcu.sourcefile);
                }
            }
        } else {
            log.error("jml.internal",
                    "JmlCompiler.parse expects to receive objects of type JmlCompilationUnit, but it found a " 
                            + cu.getClass() + " instead, for source " + cu.getSourceFile().toUri().getPath());
        }
        try {
            if (cu.endPositions != null) { // FIXME - is this ever non-null? and why only of we are in the mode of parsing multiple files
                JavaFileObject prev = log.useSource(fileobject);
                log.setEndPosTable(fileobject,cu.endPositions);
                log.useSource(prev);
            }
        } catch (Exception e) {
        	// End-position table set twice - so for just encountered this when a class name is used but is not defined in the file by that name
            log.error("jml.file.class.mismatch",fileobject.getName());
        }
        return cu;
    }
    
    /** Finds the specs file for a given compilation unit.
     * @param jmlcu The compilation unit of the Java source, if any
     * @param specs if true, looks for any specs file; if false, looks for Java file
     * @return the source object of the specifications
     */
    /*@ nullable */
    public JavaFileObject findSpecs(JmlCompilationUnit jmlcu, boolean specs) {
        JCTree.JCExpression pkgName = jmlcu.getPackageName();
        String pack = pkgName == null ? null : pkgName.toString();
        String filepath = jmlcu.getSourceFile().getName();
        // In the following, we need a name as the prefix to look for the specs.
        // That is supposed to be the same as the name of the public class within
        // the file, and thus the same as the name of the file itself.
        // However, a file may have no public classes within it - so 
        // the best indication of the spec file name is the name of the
        // java file just parsed.
        // (TODO) Unfortunately, there is no guarantee as to what getName()
        // will return.  It would be safer, but a pain, to dismember the 
        // associated URI. (getName is even deprecated within some subclasses)
        int i = filepath.lastIndexOf('/');
        int ii = filepath.lastIndexOf('\\');
        if (i < ii) i = ii;
        int k = filepath.lastIndexOf(".");
        String rootname = k >= 0 ? filepath.substring(i+1,k) : filepath.substring(i+1);
        JavaFileObject f;
        if (specs) {
            f = JmlSpecs.instance(context).findAnySpecFile(pack == null ? rootname : (pack + "." + rootname));
        } else {
            rootname = rootname + Strings.javaSuffix;
            f = JmlSpecs.instance(context).findSpecificSourceFile(pack == null ? rootname : (pack + "." + rootname));
        }
        return f;
    }
    
    /** Parses the specs for a class - used when we need the specs corresponding to a binary file;
     * this may only be called for public top-level classes (the specs for non-public or
     * nested classes are part of the same file with the corresponding public class)
     * @param typeSymbol the symbol of the type whose specs are sought
     * @return the possibly null parsed compilation unit, as an AST
     */
    /*@Nullable*/
    public JmlCompilationUnit parseSpecs(Symbol.TypeSymbol typeSymbol) {
        String typeName = typeSymbol.flatName().toString();
        JavaFileObject f = JmlSpecs.instance(context).findAnySpecFile(typeName);
        /*@Nullable*/ JmlCompilationUnit speccu = parseSingleFile(f);
        if (speccu != null) speccu.packge = (Symbol.PackageSymbol)typeSymbol.outermostClass().getEnclosingElement();
        return speccu;
    }
    
    /** Parses the given specification file. The compilation unit to which it
     * belongs is an argument because if the specification source is the same
     * as the Java source, the input is not reparsed.
     * @param f the file object to parse, if any
     * @param javaCU the compilation unit that provoked this parsing, if any
     * @return the possibly empty list of parsed compilation units, as ASTs
     */
    //@ nullable
    public JmlCompilationUnit parseSingleFile(/*@ nullable*/JavaFileObject f) {
        inSequence = true;
        try {
            if (f != null) {
                JCCompilationUnit result = parse(f);
                if (result instanceof JmlCompilationUnit) {
                    return (JmlCompilationUnit)result;
                } else {
                    log.error("jml.internal","The result of a parse is a JCCompilationUnit instead of a JmlCompilationUnit");
                    return null;
                }
            } else {
                return null;
            }
        } finally {
            inSequence = false;
        }
    }
    
    @Override
    public List<JCCompilationUnit> parseFiles(Iterable<JavaFileObject> fileObjects) {
        List<JCCompilationUnit> list = super.parseFiles(fileObjects);
        for (JCCompilationUnit cu: list) {
            ((JmlCompilationUnit)cu).mode = JmlCompilationUnit.JAVA_SOURCE_FULL;
        }
        return list;
    }
    
    private int nestingLevel = 0;

    /** Parses and enters specs for binary classes, given a ClassSymbol.  This is 
     * called when a name is resolved to a binary type; the Java type itself is
     * loaded (and symbols entered) by the conventional Java means.  Here we need
     * to add to that by parsing the specs and entering any new declarations
     * into the scope tables (via JmlEnter and JmlMemberEnter).  This method is
     * also called when during type attribution a new unattributed type is found
     * that does not have any specs associated with it.  We call this to get the
     * specs.  If ever a Java file is loaded by conventional means and gets its
     * source file through parsing, the specs will be obtained using parse()
     * above.
     * 
     * @param env the environment representing the source for the given class;
     *      may be null for a PUBLIC top-level class  
     * @param csymbol the class whose specs are wanted
     */  // FIXME - what should we use for env for non-public binary classes
    public void loadSpecsForBinary(Env<AttrContext> env, ClassSymbol csymbol) {
        // Don't load over again
        
        if (JmlSpecs.instance(context).get(csymbol) != null) return;
        // FIXME - need to figure out what the environment should be

        // This nesting level is used to be sure we queue up a whole set of 
        // classes, do their 'enter' processing to record any types before we
        // do their member processing to record all their members.  We need the
        // types recorded so that we can look up types for the members (e.g. do
        // method resolution).  This is the same two-phase processing as the
        // Java handling uses, we just don't use the same todo list.
        nestingLevel++;
        loadSuperSpecs(env,csymbol);
        
        // It can happen that the specs are loaded during the loading of the super class 
        // since complete() may be called on the class in order to fetch its superclass
        JmlSpecs.TypeSpecs tspecs = JmlSpecs.instance(context).get(csymbol);
        JmlCompilationUnit speccu;
        if (JmlSpecs.instance(context).get(csymbol) != null) {
            speccu = tspecs.decl.toplevel;
        } else {
            speccu = parseSpecs(csymbol);
            if (verbose && speccu == null) {
                log.noticeWriter.println("No specs for " + csymbol);
            }
        }
        // FIXME - not sure env or mode below are still used
        if (speccu != null) {
            env = enter.getTopLevelEnv(speccu);
            //enter.visitTopLevel(specSequence.get(0));  // Does imports
            csymbol.flags_field |= Flags.UNATTRIBUTED;
        }
        if (speccu != null) {
            if (speccu.sourcefile.getKind() == JavaFileObject.Kind.SOURCE) speccu.mode = JmlCompilationUnit.JAVA_AS_SPEC_FOR_BINARY;
            else speccu.mode = JmlCompilationUnit.SPEC_FOR_BINARY;
        }
        if (utils.jmlverbose >= Utils.JMLDEBUG) if (speccu == null) log.noticeWriter.println("   LOADED CLASS " + csymbol + " FOUND NO SPECS");
        else log.noticeWriter.println("   LOADED CLASS " + csymbol + " PARSED SPECS");
        ((JmlEnter)enter).enterSpecsForBinaryClasses(csymbol,speccu);
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("NEST " + nestingLevel + " " + csymbol);
        if (nestingLevel==1) ((JmlMemberEnter)JmlMemberEnter.instance(context)).completeBinaryTodo();
        nestingLevel--;
     }
    
    /** Makes sure that the super classes and interfaces of the given symbol
     * are loaded, including specs.
     * @param csymbol the class whose super types are wanted
     */
    public void loadSuperSpecs(Env<AttrContext> env, ClassSymbol csymbol) {
        // We have a ClassSymbol, but the super classes and interfaces
        // are not necessarily loaded, completed or have their
        // specs read
        Resolve resolve = JmlResolve.instance(context);
        Type t = csymbol.getSuperclass();
        if (t != null && t.tsym != null) {
            resolve.loadClass(env,((ClassSymbol)t.tsym).flatname);
        }
        for (Type tt: csymbol.getInterfaces()) {
            resolve.loadClass(env,((ClassSymbol)tt.tsym).flatname);
        }
    }
    
    /** Overridden in order to put out some information about stopping */
    @Override
    protected  <T> List<T> stopIfError(CompileState cs, List<T> list) {
        if (errorCount() != 0) {
            if (JmlOption.isOption(context,JmlOption.STOPIFERRORS)) {
                if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(0,1,"Stopping because of parsing errors");
                return List.<T>nil();
            } else {
                if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(0,1,"Continuing bravely despite parsing errors");
            }
        }
        return list;
    }

    /** Overridden so that we do either (1) ESC or (2) RAC prep followed 
     * by desugaring and code generation.
     */
    @Override
    protected void desugar(Env<AttrContext> env, Queue<Pair<Env<AttrContext>, JCClassDecl>> results) {
        // Note super.desugar() translates generic Java to non-generic Java and perhaps does other stuff.
        
        // Note - we do not want translation for jmldoc (neither ESC nor RAC)
        
        if (utils.check || utils.doc) {
            // Stop here // FIXME - use stopping policy?
            return;
        }
        
        if (utils.esc) {
            esc(env);
            
            // nothing has been put in results, so no further compilation 
            // phases will be performed
        }
        if (utils.rac) {
            JCTree t = env.tree;
            env = rac(env);
            if (env == null) return;
            // Continue with the usual compilation phases
            
            if (utils.jmlverbose >= Utils.PROGRESS) 
                context.get(Main.IProgressListener.class).report(0,2,"desugar " + todo.size() + " " + 
                    (t instanceof JCTree.JCCompilationUnit ? ((JCTree.JCCompilationUnit)t).sourcefile:
                        t instanceof JCTree.JCClassDecl ? ((JCTree.JCClassDecl)t).name : t.getClass()));
            super.desugar(env,results);
        }
        
        // FIXME - continue with usual Java compilation?
    }
    
//    public CountMethodInvocation counter = new CountMethodInvocation();

//    /** Initiates type attribution for the given class; overridden in order
//     * 
//     */
//    public Env<AttrContext> attribute(Env<AttrContext> env) {
//        // FIXME - I think this can go away.  Test some time.
//        env = super.attribute(env);
//        //counter.scan(env.tree == null ? env.toplevel : env.tree);
//        return env;
//
//    }
    
    /** This is overridden so that if attribute() returns null, processing continues (instead of crashing). */
    @Override
    public Queue<Env<AttrContext>> attribute(Queue<Env<AttrContext>> envs) {
        ListBuffer<Env<AttrContext>> results = lb();
        while (!envs.isEmpty()) {
            Env<AttrContext> env = attribute(envs.remove());
            if (env != null) results.append(env);
        }
        return stopIfError(CompileState.ATTR, results);
    }

    
    // FIXME - the following control flow is a bit convoluted and needsd to be explained and cleaned up

    /** Overridden to remove binary/spec entries from the list of Envs after processing */
    @Override
    protected void flow(Env<AttrContext> env, Queue<Env<AttrContext>> results) {
        if (env.toplevel.sourcefile.getKind() != JavaFileObject.Kind.SOURCE) unconditionallyStop = true;
        super.flow(env,results);
    }
    
    // FIXME - this design prevents flow from running on spec files - we want actually to stop after the spec files are processed
    @Override
    protected boolean shouldStop(CompileState cs) {
        if (unconditionallyStop) { unconditionallyStop = false; return true; }
        return super.shouldStop(cs);
    }

    protected boolean unconditionallyStop = false;
    
    /** Overridden simply to do a sanity check that annotation processing does not produce a JavaCompiler instead of a JmlCompiler. */
    @Override
    public JavaCompiler processAnnotations(List<JCCompilationUnit> roots, List<String> classnames) {
        JavaCompiler result = super.processAnnotations(roots,classnames);
        if (!(result instanceof JmlCompiler)) {
            log.error("jml.internal","annotation processing produced a new instance of JavaCompiler, disabling further JML processing");
        }
        return result;
    }
    
    /** Does the RAC processing on the argument. */
    protected Env<AttrContext> rac(Env<AttrContext> env) {
        JCTree tree = env.tree;
        
        if (tree instanceof JCClassDecl) {
            JmlTree.Maker M = JmlTree.Maker.instance(context);
            JCClassDecl that = (JCClassDecl)tree;
            // The class named here must match that in org.jmlspecs.utils.Utils.isRACCompiled
            Name n = names.fromString("org.jmlspecs.annotation.RACCompiled");
            ClassSymbol sym = ClassReader.instance(context).enterClass(n);
            Attribute.Compound ac = new Attribute.Compound(sym.type, List.<Pair<Symbol.MethodSymbol,Attribute>>nil());
            that.sym.attributes_field = that.sym.attributes_field.append(ac);
        }


//        if (!JmlCompilationUnit.isJava(((JmlCompilationUnit)env.toplevel).mode)) {
//            // TODO - explain why we remove these from the symbol tables
//            if (env.tree instanceof JCClassDecl) {
//                Symbol c = ((JCClassDecl)env.tree).sym;
//                //((JmlEnter)enter).remove(c);
//            } else if (env.toplevel instanceof JCCompilationUnit) {
//                for (JCTree t : ((JCCompilationUnit)env.toplevel).defs) {
//                    if (t instanceof JCClassDecl) ((JmlEnter)enter).remove(((JCClassDecl)t).sym);
//                }
//            } else {
//                // This is a bug, but we can probably get by with just not instrumenting
//                // whatever this is.
//                log.warning("jml.internal.notsobad","Did not expect to encounter this option in JmlCompiler.rac: " + env.tree.getClass());
//            }
//            return null;
//        }
        // Note that if env.tree is a class, we translate just that class.  
        // We have to adjust the toplevel tree accordingly.  Presumably other
        // class declarations in the compilation unit will be translated on 
        // other calls.
        if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(0,1,"RAC-Compiling " + utils.envString(env));
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("rac " + utils.envString(env));
        
        if (env.tree instanceof JCClassDecl) {
            JCTree newtree;
            if (JmlOption.isOption(context,JmlOption.SHOW)) {
                log.noticeWriter.println("ORIGINAL");
                log.noticeWriter.println(JmlPretty.write(env.tree,true));
                log.noticeWriter.println("");
            }
            newtree = new JmlAssertionAdder(context,false,true).convert(env.tree);
            if (JmlOption.isOption(context,JmlOption.SHOW)) {
                log.noticeWriter.println("TRANSLATED RAC");
                log.noticeWriter.println(JmlPretty.write(newtree,true));
            }

                
            // When we do the RAC translation, we create a new instance
            // of the JCClassDecl for the class.  So we have to find where
            // it is kept in the JCCompilationUnit and replace it there.
            // If there is more than one class in the compilation unit, we are
            // presuming that each one that is to be translated will be 
            // separately called - so we just translate each one when it comes.
            List<JCTree> t = env.toplevel.defs;
            while (t.head != null) {
                if (t.head == env.tree) {
                    env.tree = newtree;
                    //reattribute(env);
                    t.head = newtree;
                    break;
                }
                t = t.tail;
            }
        } else {
            // FIXME - does this happen?
            JCCompilationUnit newtree = new JmlAssertionAdder(context,false,true).convert(env.toplevel);
            env.toplevel = newtree;
        }
        //       flow(env);  // FIXME - give a better explanation if this produces errors.
        // IF it does, it is because we have done the RAC translation wrong.
        return env;
    }
    
    /** Does the ESC processing for the given class
     * 
     * @param env the env for a class
     */ // FIXME - check that we always get classes, not CUs and adjust the logic accordingly
    protected void esc(Env<AttrContext> env) {
        if (((JmlCompilationUnit)env.toplevel).mode != JmlCompilationUnit.JAVA_SOURCE_FULL) return;
//        if (Options.instance(context).get("-custom") != null) {
//            new JmlTranslator(context).translate(env);
//        }
        //log.noticeWriter.println(JmlPretty.write(env.tree));

        JmlEsc esc = JmlEsc.instance(context);
        esc.check(env.tree);

        return;
    }

//    // FIXME - this statement no longer applies - what happens instead?
//    /** This overrides JavaCompiler.compile simply to load java.lang.Object
//     * explicitly.  The parsing/entering logic will prompt for class or source
//     * file loading of any class explicitly mentioned in the source files.  But
//     * Object is the default super class and is not explicitly mentioned; though
//     * it could, Enter and MemberEnter do not explicitly load it.  The class 
//     * does get loaded at a later point.  As a result, the class is not put on
//     * the todo list for attribution until after other classes.  This is not a
//     * problem for Java because Object is a binary class and there is no source
//     * code to attribute.  However, for JML, the result is that the specs
//     * for Object do not get attributed early enough.  We could fix this by
//     * changing the logic in Enter to explicitly process a default super type;
//     * however, it is easier (and less invasive) to simply force the class 
//     * loading as the first thing that happens in the compilation.  It does have
//     * the side-effect of processing all the classes referenced by Object's
//     * specs before the parsing of command-line files begins (however, this would
//     * happen on the first file processed anyway).
//     */
//    public void compile(List<JavaFileObject> sourceFileObjects,
//            List<String> classnames,
//            Iterable<? extends Processor> processors) {
////        Runtime rt = Runtime.getRuntime();
//        //log.noticeWriter.println("    ....... Memory free=" + rt.freeMemory() + "  max="+rt.maxMemory() + "  total="+rt.totalMemory());
//// FIXME - do we keep these preloadings?
// //       JmlResolve.instance(context).loadClass(null,Symtab.instance(context).objectType.tsym.flatName());
////        JmlResolve.instance(context).loadClass(null,Names.instance(context).fromString("org.jmlspecs.lang.JMLList"));
//        
//        // The following class contains utility functions that have specs and implementations
//        // for built-in functionality, such as the behavior of JML expressions
//        // (e.g. \type or \typeof).  Here we make sure that Utils is loaded and
//        // its specs are read, so that they get typechecked along with everything else.
//        //JmlResolve.instance(context).loadClass(null,Names.instance(context).fromString("org.jmlspecs.utils.Utils"));
//
//        super.compile(sourceFileObjects,classnames,processors);
//    }
    
    // TODO - need some explanation here
    protected void compile2(CompilePolicy compPolicy) {
        //super.compile2(CompilePolicy.BY_TODO);
        super.compile2(CompilePolicy.SIMPLE);
    }
    
//    protected void flow(Env<AttrContext> env, ListBuffer<Env<AttrContext>> results) {
//        results.append(env);
//    }
    
//    public class CountMethodInvocation extends JmlTreeScanner {
//        
//        public java.util.Map<String,Integer> counter =
//            new java.util.HashMap<String,Integer>();
//
//        public int classes = 0;
//        
//        public CountMethodInvocation() {
//        }
//        
//        public void scan(JCTree t) {
//            if (t == null) return;
//            if (t instanceof JCTree.JCClassDecl) classes++;
//            
//            if (t instanceof JCTree.JCMethodInvocation) {
//                JCTree.JCMethodInvocation m = (JCTree.JCMethodInvocation)t;
//                Symbol sym = null;
//                if (m.meth instanceof JCTree.JCIdent) {
//                    sym = ((JCTree.JCIdent)m.meth).sym;
//                } else if (m.meth instanceof JCTree.JCFieldAccess) {
//                    sym = ((JCTree.JCFieldAccess)m.meth).sym;
//                } else if (t instanceof JmlTree.JmlMethodInvocation){
//                } else {
//                    System.out.println("NOT COUNTED");
//                }
//                String ms = null;
//                if (sym != null) {
//                    if (sym instanceof MethodSymbol) {
//                        MethodSymbol msym = (MethodSymbol)sym;
//                        if (msym.owner != null) {
//                            ms = msym.owner.getQualifiedName() + "." + msym;
//                        }
//                    } else if (sym instanceof ClassSymbol) {
//                        ms = ((ClassSymbol)sym).getQualifiedName().toString();
//                    }
//                    //log.noticeWriter.println("COUNTING " + ms);
//                    if (ms != null) {
//                        Integer i = counter.get(ms);
//                        if (i == null) i = new Integer(0);
//                        counter.put(ms,i+1);
//                    }
//                }
//            }
//            super.scan(t);
//        }
//        
//        public java.util.Iterator<java.util.Map.Entry<String,Integer>> iterator() {
//            java.util.SortedSet<java.util.Map.Entry<String,Integer>> set =
//                new java.util.TreeSet<java.util.Map.Entry<String,Integer>>(
//                        new java.util.Comparator<java.util.Map.Entry<String,Integer>>() {
//                            public boolean equals(Object oo) {
//                                return this == oo;
//                            }
//                            public int compare(java.util.Map.Entry<String,Integer> o,
//                                    java.util.Map.Entry<String,Integer> oo) {
//                                int i = oo.getValue().compareTo(o.getValue());
//                                if (i == 0) {
//                                    i = oo.getKey().compareTo(o.getKey());
//                                }
//                                return i;
//                            }
//                            
//                        }
//                        );
//            set.addAll(counter.entrySet());
//            
//            return set.iterator();
//        }
//    }
    
    public void reattribute(Env<AttrContext> env) {
        compileStates.put(env,null);
        (new ClearAttributes()).scan(env.tree);
        attribute(env);
    }
    
    public class ClearAttributes extends JmlTreeScanner {
        @Override
        public void visitJmlClassDecl(JmlTree.JmlClassDecl that) {
            that.mods.flags |= Flags.UNATTRIBUTED;
            that.sym.flags_field |= Flags.UNATTRIBUTED;
            super.visitJmlClassDecl(that);
        }
        
        @Override
        public void visitIdent(JCTree.JCIdent that) {
            that.sym = null;
            super.visitIdent(that);
        }
    }
}
