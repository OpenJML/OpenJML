/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
// FIXME - do a review
package org.jmlspecs.openjml;

import java.io.PrintWriter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
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
import com.sun.tools.javac.comp.CompileStates.CompileState;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCImport;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log.WriterKind;
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
     * of specification files. 
     * <P>
     * <UL>
     * <LI>If inSequence is false, then this method parses the given content and associated specs.
     * The JmlCompilationUnit for the specs is assigned to the specsCompilationUnit field of the
     * JmlCompilationUnit for the .java file.
     * <LI>If inSequence is true, then this method parses just the given content.
     * <LI>In either case a JmlCompilationUnit is returned.
     * However, see the FIXME below regarding adding the .java file into an empty specs list.
     * </UL>
     * <p>
     * THis method is eventually called for (1) source files specified on the command-line,
     * through Enter.main and (2) classes referenced in other files that need to be compiled
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
                JavaFileObject specsFile = JmlSpecs.instance(context).findSpecs(jmlcu,true);
                if (specsFile != null && Utils.ifSourcesEqual(specsFile, jmlcu.getSourceFile())) {
                    if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("The java file is its own specs for " + specsFile);
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
                    if (jcu != cu) {
                        jcu.mode = JmlCompilationUnit.SPEC_FOR_SOURCE;
                        // Insert import statements
                        // FIXME - This is not the best solution - since it adds imports to the Java compilation unit, which may make it invalid
                        Map<String,JCImport> map = new HashMap<String,JCImport>();
                        ListBuffer<JCTree> extras = new ListBuffer<JCTree>();
                        for (JCImport imp: jmlcu.getImports()) map.put(imp.qualid.toString(),imp);
                        for (JCImport def: jcu.getImports()) {
                            JCImport imp = map.get(def.qualid.toString());
                            if (imp == null) extras.add(def);
                        }
                        cu.defs = cu.defs.appendList(extras);
                    }
                }
                
                // FIXME - record dependencies
            } else {
                // Parsing a specification file
                jmlcu.mode = JmlCompilationUnit.SPEC_FOR_SOURCE;
                JavaFileObject javaFile = JmlSpecs.instance(context).findSpecs(jmlcu,false); // look for corresponding java file
                JmlCompilationUnit javacu = parseSingleFile(javaFile);
                if (javacu != null) {
                    javacu.specsCompilationUnit = jmlcu; 
                    javacu.mode = JmlCompilationUnit.JAVA_SOURCE_PARTIAL;
                    cu = javacu;
                } else {
                    log.warning("jml.no.java.file",jmlcu.sourcefile);
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
        	// End-position table set twice - so far just encountered this when a class name is used but is not defined in the file by that name
            log.error("jml.file.class.mismatch",fileobject.getName());
        }
        return cu;
    }
    
    
    /** Parses the specs for a class - used when we need the specs corresponding to a binary file;
     * this may only be called for public top-level classes (the specs for non-public or
     * nested classes are part of the same file with the corresponding public class).
     * Returns null if no specifications file is found.
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
    
    /** Parses the given file as a JmlCompilationUnit (either Java source or JML specifications);
     * does not seek any specification file. Retruns a best guess compilation unit if there are parse errors.
     * @param f the file object to parse, if any
     * @param javaCU the compilation unit that provoked this parsing, if any
     * @return the possibly empty list of parsed compilation units, as ASTs; possibly returns null
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
    
    /** Parses the list of file objects (using parse(fileobject)), returning a list of JmlCompilationUnits;
     * parsing a source file will cause a search for and parsing of the specification file */
    @Override
    public List<JCCompilationUnit> parseFiles(Iterable<JavaFileObject> fileObjects) {
        List<JCCompilationUnit> list = super.parseFiles(fileObjects);
        for (JCCompilationUnit cu: list) {
            ((JmlCompilationUnit)cu).mode = JmlCompilationUnit.JAVA_SOURCE_FULL;  // FIXME - does this matter? is it right? there could be jml files on the command line
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
    // FIXME - move this to JmlResolve
    public void loadSpecsForBinary(Env<AttrContext> env, ClassSymbol csymbol) {
        // The binary Java class itself is already loaded - it is needed to produce the classSymbol itself
        
        // Don't load specs over again
        if (JmlSpecs.instance(context).get(csymbol) != null) return;
 //       if (csymbol.toString().equals("java.lang.Object")) Utils.stop();
 //       if (csymbol.toString().equals("java.io.File")) Utils.stop();
        
        // FIXME - need to figure out what the environment should be

        if (!binaryEnterTodo.contains(csymbol)) {
            nestingLevel++;
            try {

                if (csymbol.getSuperclass() != Type.noType) loadSpecsForBinary(env, (ClassSymbol)csymbol.getSuperclass().tsym);
                for (Type t: csymbol.getInterfaces()) {
                    loadSpecsForBinary(env, (ClassSymbol)t.tsym);  // FIXME - env is not necessarily the tree for the classSymbol
                }

                // It can happen that the specs are loaded during the loading of the super class 
                // since complete() may be called on the class in order to fetch its superclass
                JmlSpecs.TypeSpecs tspecs = JmlSpecs.instance(context).get(csymbol);
                if (tspecs == null) {
                    // Note: classes and interfaces may be entered in this queue multiple times. The check for specs at the beginning of this method
                    // does not prevent unloaded classes from begin added to the queue more than once, because the specs are not loaded until completeBinaryEnterTodo
                    if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("QUEUING BINARY ENTER " + csymbol);
                    binaryEnterTodo.prepend(csymbol);
                }

            } finally {
                nestingLevel --;
            }
        }

        // This nesting level is used to be sure we queue up a whole set of 
        // classes, do their 'enter' processing to record any types before we
        // do their member processing to record all their members.  We need the
        // types recorded so that we can look up types for the members (e.g. do
        // method resolution).  This is the same two-phase processing as the
        // Java handling uses, we just don't use the same todo list.
        if (nestingLevel==0) completeBinaryEnterTodo();
            
     }
    
    ListBuffer<ClassSymbol> binaryEnterTodo = new ListBuffer<ClassSymbol>();
    
    // FIXME - do we really need this deferred processing?
    public void completeBinaryEnterTodo() {
        while (!binaryEnterTodo.isEmpty()) {
            ClassSymbol csymbol = binaryEnterTodo.remove();
            if (JmlSpecs.instance(context).get(csymbol) != null) continue;
            
//            if (csymbol.toString().contains("Throwable")) Utils.stop();

            // Record default specs just to show they are in process
            // If there are actual specs, they will be recorded later
            // We do this, in combination with the check above, to avoid recursive loops
            ((JmlEnter)enter).recordEmptySpecs(csymbol);
            
            JmlCompilationUnit speccu = parseSpecs(csymbol);
            if (speccu != null) {
//                csymbol.flags_field |= Flags.UNATTRIBUTED;

                if (speccu.sourcefile.getKind() == JavaFileObject.Kind.SOURCE) speccu.mode = JmlCompilationUnit.JAVA_AS_SPEC_FOR_BINARY;
                else speccu.mode = JmlCompilationUnit.SPEC_FOR_BINARY;

                //if (speccu.sourcefile.toString().contains("File")) Utils.stop();
                nestingLevel++;
                try {
                    boolean ok = ((JmlEnter)enter).binaryEnter(speccu);
 //                   ((JmlEnter)enter).binaryEnvs.add(speccu);
                    
                    // specscu.defs is empty if nothing was declared or if all class declarations were removed because of errors
                    if (ok) {
                        for (JCTree d: speccu.defs) {
                            if (d instanceof JmlClassDecl) todo.append(((JmlClassDecl)d).env);
                        }
                    }
//                    memberEnter.enterSpecsForBinaryClasses(csymbol,List.<JCTree>of(speccu));
                } finally {
                    nestingLevel--;
                }
            }
        }
    }
    
    /** Overridden in order to put out some information about stopping */
    @Override
    public  <T> List<T> stopIfError(CompileState cs, List<T> list) {
        if (shouldStop(cs)) {
            if (JmlOption.isOption(context,JmlOption.STOPIFERRORS)) {
                if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(0,1,"Stopping because of parsing errors");
                return List.<T>nil();
            } else {
                if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(0,1,"Continuing bravely despite parsing errors");
            }
        }
        return list;
    }

    /** We override this method instead of the desugar method that does one
     * env because we have to do all the rac before any of the desugaring
     */
    @Override
    public Queue<Pair<Env<AttrContext>, JCClassDecl>> desugar(Queue<Env<AttrContext>> envs) {
        ListBuffer<Pair<Env<AttrContext>, JCClassDecl>> results = new ListBuffer<>();

        if (utils.check || utils.doc) {
            // Stop here
            return results; // Empty list - do nothng more
        } else if (utils.esc) {
            for (Env<AttrContext> env: envs)
                esc(env);
            return results; // Empty list - Do nothing more
        } else if (utils.rac) {
            for (Env<AttrContext> env: envs) {
                JCTree t = env.tree;
                env = rac(env);
                if (env == null) continue; // FIXME - error? just keep oroginal env?
                
                if (utils.jmlverbose >= Utils.PROGRESS) 
                    context.get(Main.IProgressListener.class).report(0,2,"desugar " + todo.size() + " " + 
                        (t instanceof JCTree.JCCompilationUnit ? ((JCTree.JCCompilationUnit)t).sourcefile:
                            t instanceof JCTree.JCClassDecl ? ((JCTree.JCClassDecl)t).name : t.getClass()));
            }
            // Continue with the usual compilation phases
            for (Env<AttrContext> env: envs)
                desugar(env, results);
            
        } else {
            for (Env<AttrContext> env: envs)
                desugar(env, results);
        }
        return stopIfError(CompileState.FLOW, results);
    }

    /** This is overridden so that if attribute() returns null, processing continues (instead of crashing). */
    // FIXME - why might it return null, and should we stop if it does?
    @Override
    public Queue<Env<AttrContext>> attribute(Queue<Env<AttrContext>> envs) {
        ListBuffer<Env<AttrContext>> results = new ListBuffer<>();
        while (!envs.isEmpty()) {
            Env<AttrContext> env = attribute(envs.remove());
            if (env != null) results.append(env);
        }
        ((JmlAttr)attr).completeTodo();
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
    
    // FIXME _ review
    /** Does the RAC processing on the argument. */
    protected Env<AttrContext> rac(Env<AttrContext> env) {
        JCTree tree = env.tree;
        PrintWriter noticeWriter = log.getWriter(WriterKind.NOTICE);
        
        // TODO - will sourcefile always exist? -- JLS
        String currentFile = env.toplevel.sourcefile.getName();
        
        if (tree instanceof JCClassDecl) {
            JmlTree.Maker M = JmlTree.Maker.instance(context);
            JCClassDecl that = (JCClassDecl)tree;
            
            if (((JmlAttr)attr).hasAnnotation(that.sym,JmlTokenKind.SKIP_RAC)) {
                utils.progress(1,1,"Skipping RAC of " + that.name.toString() + " (SkipRac annotation)");
                return env;
            }
            
            // The class named here must match that in org.jmlspecs.utils.Utils.isRACCompiled
            Name n = names.fromString("org.jmlspecs.annotation.RACCompiled");
            ClassSymbol sym = ClassReader.instance(context).enterClass(n);
            Attribute.Compound ac = new Attribute.Compound(sym.type, List.<Pair<Symbol.MethodSymbol,Attribute>>nil());
            that.sym.appendAttributes(List.<Attribute.Compound>of(ac));
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
        utils.progress(0,1,"RAC-Compiling " + utils.envString(env));
        if (utils.jmlverbose >= Utils.JMLDEBUG) noticeWriter.println("rac " + utils.envString(env));
        
        if (env.tree instanceof JCClassDecl) {
            JCTree newtree;
            if (JmlOption.isOption(context,JmlOption.SHOW)) {
                // FIXME - these are not writing out during rac, at least in debug in development, to the console
                noticeWriter.println(String.format("[jmlrac] Translating: %s", currentFile));
                noticeWriter.println(
                            JmlPretty.toFancyLineFormat(
                                    currentFile,
                                    JmlPretty.racFormatter,            // the formatter 
                                    JmlPretty.write(env.toplevel,true) // the source to format
                                    ));
                noticeWriter.println("");
            }
            newtree = new JmlAssertionAdder(context,false,true).convert(env.tree);
                
            // When we do the RAC translation, we create a new instance
            // of the JCClassDecl for the class.  So we have to find where
            // it is kept in the JCCompilationUnit and replace it there.
            // If there is more than one class in the compilation unit, we are
            // presuming that each one that is to be translated will be 
            // separately called - so we just translate each one when it comes.
            for (List<JCTree> l = env.toplevel.defs; l.nonEmpty(); l = l.tail) {
                if(l.head == env.tree){
                    env.tree = newtree;
                    l.head = newtree;
                    break;
                }
            }
            
            // it's not enough to update the toplevels. If you have nested classes, you must 
            // update the type envs, otherwise the wrong typeenv gets selected during the desugaring phase
            if(newtree instanceof JmlClassDecl){
                updateTypeEnvs((JmlClassDecl)newtree);
            }
            
            // After adding the assertions, we will need to add the OpenJML libraries 
            // to the import directives.             

            // Add the Import: import org.jmlspecs.utils.*;
            
            if (JmlOption.isOption(context,JmlOption.SHOW)) { 
                noticeWriter.println(String.format("[jmlrac] RAC Transformed: %s", currentFile));
                // this could probably be better - is it OK to modify the AST beforehand? JLS
                noticeWriter.println(
                        JmlPretty.toFancyLineFormat(
                            currentFile,
                            JmlPretty.racFormatter,            // the formatter 
                            "import org.jmlspecs.utils.*;",    // a header prefix to print
                            JmlPretty.write(env.toplevel,true) // the source to format
                            ));
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
    
    // FIXME - review
    /** Recursively updates nested class declarations */
    protected void updateTypeEnvs(JmlClassDecl tree){
        
        enter.getEnv(tree.sym).tree = tree;
        
        for(List<JCTree> l = tree.defs; l.nonEmpty(); l=l.tail){
            if(l.head instanceof JmlClassDecl){
                updateTypeEnvs((JmlClassDecl)l.head);
            }
        }
    }
    
    /** Does the ESC processing for the given class
     * 
     * @param env the env for a class
     */ // FIXME - check that we always get classes, not CUs and adjust the logic accordingly
    protected void esc(Env<AttrContext> env) {
        // Only run ESC on source files
        if (((JmlCompilationUnit)env.toplevel).mode != JmlCompilationUnit.JAVA_SOURCE_FULL) return;

        JmlEsc esc = JmlEsc.instance(context); // FIXME - get this once at initialization?
        esc.check(env.tree);

        return;
    }

    // FIXME - we are overriding to only allow SIMPLE compile policy
    protected void compile2(CompilePolicy compPolicy) {
        //super.compile2(CompilePolicy.BY_TODO);
        super.compile2(CompilePolicy.SIMPLE);
    }
    
}
