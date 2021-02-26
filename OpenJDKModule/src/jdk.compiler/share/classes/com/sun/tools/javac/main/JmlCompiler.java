/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
// FIXME - do a review
package com.sun.tools.javac.main;

import static com.sun.tools.javac.code.Flags.UNATTRIBUTED;
import static com.sun.tools.javac.main.Option.PROC;

import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import javax.annotation.processing.Processor;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.IJmlClauseKind.ModifierKind;
//import org.jmlspecs.openjml.JmlClearTypes;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.Maker;
import org.jmlspecs.openjml.Main.Cmd;
import org.jmlspecs.openjml.Main.IProgressListener;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;
import org.jmlspecs.openjml.esc.JmlEsc;
import org.jmlspecs.openjml.ext.Modifiers;
import org.jmlspecs.openjml.visitors.JmlUseSubstitutions;

import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.CompileStates;
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
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Pair;
import com.sun.tools.javac.util.PropagatedException;

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
    
    public static JmlCompiler instance(Context context) {
    	return (JmlCompiler)JavaCompiler.instance(context);
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
        this.context = context;
        this.utils = Utils.instance(context);
        this.verbose |= utils.jmlverbose >= Utils.JMLVERBOSE; // Only used in JavaCompiler
        this.resolver = JmlResolve.instance(context);
    }
    
    public void init() {
        JmlAttr.instance(context).init();
        org.jmlspecs.openjml.JmlTreeUtils.instance(context).init();
    }
    
    public List<JCCompilationUnit> enterTrees(List<JCCompilationUnit> roots) {
    	// init must be called before the trees are entered because entering trees invokes
    	// type resolution, which requires the init() call
    	// (If we do this initialization during tool creation, we get circular instantiation)
    	init();
    	return super.enterTrees(roots);
    }
    
//    /** A flag that controls whether to get specs during a parse or not (if false 
//     * then do, if true then do not).  This should be left in a false state
//     * after being used to preclude parsing specs.
//     */
//    public boolean inSequence = false;
    
//    /** 
//     * This method is eventually called for (1) source files specified on the command-line,
//     * through Enter.main and (2) classes referenced in other files that need to be compiled
//     */
//    @Override
//    public JmlCompilationUnit parse(JavaFileObject fileobject, CharSequence content) {
//        if (fileobject == null) return null;
//        if (utils.jmlverbose >= Utils.JMLVERBOSE) context.get(Main.IProgressListener.class).report(2,"parsing " + fileobject.toUri() );
//        
//        try {
//        	JCCompilationUnit cu = super.parse(fileobject,content);
//        	if (cu instanceof JmlCompilationUnit) return (JmlCompilationUnit)cu;
//        	log.error("jml.internal",
//        			"JmlCompiler.parse expects to receive objects of type JmlCompilationUnit, but it found a " 
//        					+ cu.getClass() + " instead, for source " + cu.getSourceFile().toUri().getPath());
//        	return null;
//        } catch (Exception e) {
//        	Scanner S = getScanner();
//        	S.tokenizer.getCharacters(S.tokenizer.position()-10, S.tokenizer.position()+50);
//        	throw e;
//        }
//    }
    
    
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
        if (f == null) return null;
        /*@Nullable*/ JmlCompilationUnit speccu = (JmlCompilationUnit)parse(f);
        if (speccu == null) return null;
        Symbol.PackageSymbol p = typeSymbol.packge();
        String specpid = speccu.pid == null ? "unnamed package" : speccu.pid.getPackageName().toString();
        if (!p.toString().equals(specpid)) {
        	utils.error(speccu.sourcefile,speccu.pid == null ? 1 : speccu.pid.pos,
        			"jml.mismatched.package",
        			specpid,
        			p.toString());
        	speccu = null;
        } else {
        	if (specpid.startsWith("java.") || specpid.startsWith("org.")) {
        		JCExpression pp = speccu.pid.getPackageName();
        		while (pp instanceof JCFieldAccess && ((JCFieldAccess)pp).selected instanceof JCFieldAccess) {
        			pp = ((JCFieldAccess)pp).selected;
        		}
        		JCFieldAccess fa = (JCFieldAccess)pp;
        		Maker m = Maker.instance(context).at(fa.pos);
        		fa.selected = m.Select(
        				m.Ident(names.fromString("specs")),
        				((JCIdent)fa.selected).name);
        		specpid = specpid + ".*";
        		JCTree t = m.Import(utils.nametree(pp.pos,  pp.pos, specpid, null), false);
    			if (speccu.defs.head instanceof JCPackageDecl) {
    				JCTree tt = speccu.defs.head;
    				speccu.defs = speccu.defs.tail.prepend(t).prepend(tt);
    			} else {
    				speccu.defs = speccu.defs.prepend(t);
    			}
        		// FIXME speccu.packge ??
        	} else {
        		speccu.packge = p;
        	}
        }
        return speccu;
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
                    // does not prevent unloaded classes from being added to the queue more than once, because the specs are not loaded until completeBinaryEnterTodo
                    if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("QUEUING BINARY ENTER " + csymbol);
                    binaryEnterTodo.prepend(csymbol);
                }

                for (Symbol t: csymbol.getEnclosedElements()) {
                    if (t.isPrivate()) continue;
                    if (t instanceof ClassSymbol) {
                        //if (((ClassSymbol)t).getTypeParameters().size() != 0) continue; // FIXME - crashes on type parameters
                        loadSpecsForBinary(env, (ClassSymbol)t);  // FIXME - env is not necessarily the tree for the classSymbol
                    }
                }

                if (tspecs == null) {
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
        JmlSpecs specs = JmlSpecs.instance(context);
        while (!binaryEnterTodo.isEmpty()) {
            ClassSymbol csymbol = binaryEnterTodo.remove();
            if (csymbol.type instanceof Type.ErrorType) {
                continue; // A bad type causes crashes later on
            }
            if (specs.get(csymbol) != null) continue;
            
            // Record default specs just to show they are in process
            // If there are actual specs, they will be recorded later
            // We do this, in combination with the check above, to avoid recursive loops
            ((JmlEnter)enter).recordEmptySpecs(csymbol);
            csymbol.flags_field |= UNATTRIBUTED;
            
            
            JmlCompilationUnit speccu = parseSpecs(csymbol);
            if (speccu != null) {
            	speccu.sourceCU = null;
            	speccu.modle = syms.unnamedModule; // csymbol.packge().modle;

//                if (speccu.sourcefile.getKind() == JavaFileObject.Kind.SOURCE) speccu.mode = JmlCompilationUnit.JAVA_AS_SPEC_FOR_BINARY;
//                else speccu.mode = JmlCompilationUnit.SPEC_FOR_BINARY;

                nestingLevel++;
                try {
                    boolean ok = ((JmlEnter)enter).binaryEnter(speccu);
//                    // specscu.defs is empty if nothing was declared or if all class declarations were removed because of errors
//                    if (ok) {
//                        for (JCTree d: speccu.defs) {
//                            if (d instanceof JmlClassDecl) {
//                                JmlClassDecl jd = (JmlClassDecl)d;
//                                Env<AttrContext> outerEnv = jd.env;
//                                todo.append(outerEnv);
//                                //specs.combineSpecs(jd.sym, jd, jd); // This is a repeat of the top-level definitions
//                                for (JCTree dd: jd.defs) { // TODO: Needs full recursiveness, not just the next level
//                                    if (dd instanceof JmlClassDecl) {
//                                        JmlClassDecl jdd = (JmlClassDecl)dd;
//                                        if (jdd.env == null) jdd.env = enter.classEnv(jdd, outerEnv);
//                                        jdd.specsDecl = jdd;
//                                        todo.append(jdd.env);
//                                        //specs.combineSpecs(jdd.sym, jdd, jdd);
//                                    }
//                                }
//                            }
//                        }
//                    }
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
                if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(1,"Stopping because of parsing errors");
                return List.<T>nil();
            } else {
                if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(1,"Continuing bravely despite parsing errors");
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
        
        if (envs.isEmpty()) {
        	if (utils.esc) context.get(Main.IProgressListener.class).report(1,"Operation not performed because of parse or type errors");
        	return results;
        }
        
        JmlUseSubstitutions subst = new JmlUseSubstitutions(context);
        for (Env<AttrContext> env: envs) {
            env.tree = subst.translate(env.tree);
        }

        // TODO _ dependencies
//        if (utils.cmd == Main.Cmd.DEP) {
//            MethodDependencies.find(context, envs);
//            return results;
//        }
        
        if (utils.check || utils.doc) {
            // Stop here
            return results; // Empty list - do nothing more
        } else if (utils.esc) {
            JmlEsc esc = JmlEsc.instance(context);
        	try {
                esc.initCounts();
        	    for (Env<AttrContext> env: envs) esc(env); // Transforms and proves
        	} catch (PropagatedException e) {
        		// cancelation
        	} finally {
                String summary = esc.reportCounts();
                if (utils.jmlverbose >= Utils.PROGRESS && !Utils.testingMode) utils.note(false,summary);
        	}
    		return results; // Empty list - Do nothing more
        } else if (utils.infer) {
            for (Env<AttrContext> env: envs)
                infer(env);
            return results;
        } else if (utils.rac) {
            for (Env<AttrContext> env: envs) {
                JCTree t = env.tree;
                env = rac(env); // Transforms tree in place (within the env)
                if (env == null) continue; // Error reported; cocmntinue with other trees
                
                if (utils.jmlverbose >= Utils.JMLVERBOSE) 
                    context.get(Main.IProgressListener.class).report(2,"desugar " + todo.size() + " " + 
                        (t instanceof JCTree.JCCompilationUnit ? ((JCTree.JCCompilationUnit)t).sourcefile:
                            t instanceof JCTree.JCClassDecl ? ((JCTree.JCClassDecl)t).name : t.getClass()));
            }
            // Continue with the usual compilation phases
            for (Env<AttrContext> env: envs)
                desugar(env, results);
            
        } else {
        	// No JML operation. Continue with regular compiler processing
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
        while (!envs.isEmpty())
            results.append(attribute(envs.remove()));
        ((JmlAttr)attr).completeTodo();
        
//        // TODO: Review the following
//        if (rerunForTesting)  {
//            if (results != null) {
//                ListBuffer<JCCompilationUnit> list = new ListBuffer<JCCompilationUnit>();
//                ListBuffer<Env<AttrContext>> list2 = new ListBuffer<Env<AttrContext>>();
//
//                for (Env<AttrContext> env: results.toList()) {
//                    if (env.tree instanceof JmlClassDecl) {
//                        JmlClassDecl d = (JmlClassDecl)env.tree;
//                        if (d.sym != null && d.sym.flatname.toString().startsWith("java.")) continue;
//                    }
//                    if (!list.contains(env.toplevel)) {
//                        list.add(env.toplevel);
//                        list2.add(env);
//                    }
//                }
//                JmlClearTypes.clear(context, list2.toList());
//                com.sun.tools.javac.processing.JavacProcessingEnvironment.cleanTrees(list.toList());
//                JavaCompiler delegateCompiler =
//                        processAnnotations(
//                            enterTreesIfNeeded(list.toList()),
//                            List.<String>nil());
//
//                    //delegateCompiler.compile2(compilePolicy);  // OPENJML - passed in the argument, to make it more convenient to use in derived classes
//                    ListBuffer<Env<AttrContext>> results2 = new ListBuffer<>();
//                    while (!envs.isEmpty()) {
//                        Env<AttrContext> env = attribute(envs.remove());
//                            
//                        if (env != null) results2.append(env);
//                    }
//                    ((JmlAttr)attr).completeTodo();
//
//            }
//        }

        return stopIfError(CompileState.ATTR, results);
    }

    /** Overridden to remove binary/spec entries from the list of Envs after processing */
    @Override
    protected void flow(Env<AttrContext> env, Queue<Env<AttrContext>> results) {
        if (env.toplevel.sourcefile.getKind() != JavaFileObject.Kind.SOURCE) {
//            // FIXME - not sure why this is needed for rac but causes esc tests to fail
            if (utils.rac) CompileStates.instance(context).put(env,CompileState.FLOW);
            return;
        }
        super.flow(env,results);
    }
    
    
    @Override
    public void initProcessAnnotations(Iterable<? extends Processor> processors,
            Collection<? extends JavaFileObject> initialFiles,
            Collection<String> initialClassNames) {
        // Annotation processors are not necessarily compatible with OpenJML so 
        // they are disabled (e.g. lombok is not)
        if (!JmlOption.isOption(context, JmlOption.USEJAVACOMPILER)) {
            options.put(PROC.primaryName + "none", "none");
        }
        super.initProcessAnnotations(processors, initialFiles, initialClassNames);
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
            
            if (((JmlAttr)attr).hasAnnotation(that.sym,Modifiers.SKIPRAC)) {
                utils.progress(1,1,"Skipping RAC of " + that.name.toString() + " (SkipRac annotation)");
                return env;
            }
            
            // The class named here must match that in org.jmlspecs.utils.Utils.isRACCompiled
            Name n = names.fromString("org.jmlspecs.annotation.RACCompiled");
            ClassSymbol sym = ClassReader.instance(context).enterClass(n); // FIXME use modToAnnotationSymbol
            Attribute.Compound ac = new Attribute.Compound(sym.type, List.<Pair<Symbol.MethodSymbol,Attribute>>nil());
            that.sym.appendAttributes(List.<Attribute.Compound>of(ac));
        }

        // Note that if env.tree is a class, we translate just that class.  
        // We have to adjust the toplevel tree accordingly.  Presumably other
        // class declarations in the compilation unit will be translated on 
        // other calls.
        utils.progress(0,1,"RAC-Compiling " + utils.envString(env));
        if (utils.jmlverbose >= Utils.JMLDEBUG) noticeWriter.println("rac " + utils.envString(env));
        
        if (env.tree instanceof JCClassDecl) {
            JCTree newtree;
            if (JmlOption.includes(context,JmlOption.SHOW,"translated")) {
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
            
            if (JmlOption.includes(context,JmlOption.SHOW,"translated")) {
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
//        if (((JmlCompilationUnit)env.toplevel).mode != JmlCompilationUnit.JAVA_SOURCE_FULL) return;
    	if (env.toplevel.sourcefile.getKind() != JavaFileObject.Kind.SOURCE) return;
    	
        JmlEsc esc = JmlEsc.instance(context); // FIXME - get this once at initialization?
        esc.check(env.tree);

        return;
    }
    
    // FIXME - fix up or delete inference
    protected void infer(Env<AttrContext> env) {
//        if (((JmlCompilationUnit)env.toplevel).mode != JmlCompilationUnit.JAVA_SOURCE_FULL) return;
//
//        JmlInfer infer;        
//        String currentFile = env.toplevel.sourcefile.getName();
//        
//        if (InferenceType.valueOf(JmlOption.value(context, org.jmlspecs.openjml.ext.OptionsInfer.INFER))==InferenceType.POSTCONDITIONS){
//            infer = JmlInferPostConditions.instance(context);
//        } else {
//            // NOT DONE YET!
//            log.error("jml.internal","Precondition inference is not available yet.");
//            return;
//        }
//
//        infer.check(env.tree);
//        
//        if ((infer.persistContracts || infer.weaveContracts) && env.tree instanceof JmlClassDecl){
//            infer.flushContracts(currentFile, (JmlClassDecl)env.tree);
//        }
    }


}
