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
import org.jmlspecs.openjml.JmlCheckSpecs;
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
import com.sun.tools.javac.comp.Attr;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.CompileStates;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.comp.Resolve;
import com.sun.tools.javac.comp.Todo;
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
    	JmlEnter.instance(context).hold();
    	var list = super.enterTrees(roots);
    	JmlEnter.instance(context).release();
    	JmlEnter.instance(context).flush();
    	return list;
    }
    
    
    /** Parses the specs for a class - used when we need the specs corresponding to a binary file;
     * this may only be called for public top-level classes (the specs for non-public or
     * nested classes are part of the same file with the corresponding public class).
     * Returns null if no specifications file is found.
     * @param typeSymbol the symbol of the type whose specs are sought
     * @return the possibly null parsed compilation unit, as an AST
     */
    /*@Nullable*/
    public JmlCompilationUnit parseSpecs(Symbol.ClassSymbol typeSymbol) {
        JavaFileObject f = JmlSpecs.instance(context).findSpecFile(typeSymbol);
        if (utils.verbose()) utils.note("Found spec " + typeSymbol + " " + f);
        if (f == null) return null;
        /*@Nullable*/ JmlCompilationUnit speccu = (JmlCompilationUnit)parse(f);
        if (speccu == null) return null;
        Symbol.PackageSymbol p = typeSymbol.packge();
        String ps = p.toString();
        String specpid = speccu.pid == null ? "unnamed package" : speccu.pid.getPackageName().toString();
        if (!ps.equals(specpid)) {
        	if (!ps.isEmpty()) {
        		utils.error(speccu.sourcefile,speccu.pid == null ? 1 : speccu.pid.pos,
        				"jml.mismatched.package",
        				specpid,
        				p.toString());
        		return null;
        	} else {
        		speccu.packge = syms.rootPackage;
        	}
        } else {
        	speccu.packge = p;
        }
        speccu.modle = p.modle;
        return speccu;
    }
        
    
    /** Overridden in order to put out some progress information about stopping */
    @Override
    public  <T> List<T> stopIfError(CompileState cs, List<T> list) {
    	if (shouldStop(cs) && JmlOption.isOption(context,JmlOption.STOPIFERRORS)) {
    		if (utils.progress()) context.get(Main.IProgressListener.class).report(1,"Stopping because of parsing errors");
    		return List.<T>nil();
    	}
        return super.stopIfError(cs, list);
    }

    /** We override this method instead of the desugar method that does one
     * env because we have to do all the rac before any of the desugaring
     */
//    @Override
//    public Queue<Pair<Env<AttrContext>, JCClassDecl>> desugar(Queue<Env<AttrContext>> envs) {
//    	{ System.out.println("DESUGAR ON " + envs.size() + " " + (System.getenv("NOJML") == null)); Utils.dumpStack(); }
//        ListBuffer<Pair<Env<AttrContext>, JCClassDecl>> results = new ListBuffer<>();
//        
//
//        // TODO _ dependencies
////        if (utils.cmd == Main.Cmd.DEP) {
////            MethodDependencies.find(context, envs);
////            return results;
////        }
//        
//        if (utils.check) {
//        	//JmlCheckSpecs.instance(context).check();
//            return results; // Empty list - do nothing more
//        } else if (utils.doc) {
//            return results; // Empty list - do nothing more
//        } else if (utils.esc) {
//            JmlEsc esc = JmlEsc.instance(context);
//        	try {
//                esc.initCounts();
//        	    for (Env<AttrContext> env: envs) esc(env); // Transforms and proves
//        	} catch (PropagatedException e) {
//        		// cancelation - catch and continue
//        	} finally {
//                String summary = esc.reportCounts();
//                if (utils.jmlverbose >= Utils.PROGRESS && !Utils.testingMode) utils.note(false,summary);
//        	}
//    		return results; // Empty list - Do nothing more
//        } else if (utils.infer) {
//            for (Env<AttrContext> env: envs)
//                infer(env);
//            return results;
//        } else if (utils.rac) {
//        	Queue<Env<AttrContext>> newenvs = new ListBuffer<>();
//            for (Env<AttrContext> env: envs) {
//                JCTree t = env.tree;
//                if (t instanceof JmlClassDecl && ((JmlClassDecl)t).sourcefile.getKind() != JavaFileObject.Kind.SOURCE) {
////                	newenvs.add(env);
//                	System.out.println("SKIPPING " + ((JmlClassDecl)t).name + " " + ((JmlClassDecl)t).sourcefile);
//                	continue;
//                }
//            	System.out.println("ABOUT TO RAC " + ((JmlClassDecl)t).name + " " + ((JmlClassDecl)t).sourcefile);
//                env = rac(env); // Transforms tree in place (within the env)
//                if (env == null) continue; // Error reported; continue with other trees
//            	System.out.println("ADDING NEWENV " + ((JmlClassDecl)t).name + " " + ((JmlClassDecl)t).sourcefile);
//                newenvs.add(env);
//                if (utils.jmlverbose >= Utils.JMLVERBOSE) 
//                    context.get(Main.IProgressListener.class).report(2,"desugar " + todo.size() + " " + 
//                        (t instanceof JCTree.JCCompilationUnit ? ((JCTree.JCCompilationUnit)t).sourcefile:
//                            t instanceof JCTree.JCClassDecl ? ((JCTree.JCClassDecl)t).name : t.getClass()));
//            }
//            // Continue with the usual compilation phases
//            for (Env<AttrContext> env: envs) {
//            	System.out.println("ENV " + ((JCClassDecl)env.tree).name);
//            }
//            for (Env<AttrContext> env: newenvs) {
//            	System.out.println("NEWENV " + ((JCClassDecl)env.tree).name);
//            }
//
//            envs.clear();
//            envs.addAll(newenvs);
//            for (Env<AttrContext> env: envs) {
//            	System.out.println("ENVZ " + ((JCClassDecl)env.tree).name);
//            }
//            for (Env<AttrContext> env: envs) {
//            	System.out.println("DESUGAR " + ((JmlClassDecl)env.tree).sourcefile);
//                desugar(env, results);
//            }
//            for (var p: results) {
//            	System.out.println("RESULTS " + ((JCClassDecl)p.fst.tree).name + " " + p.snd.name);
//            }
//            System.out.println("RESULTS " + results.size());
//            
//        } else {
//        	// No JML operation. Continue with regular compiler processing
//            for (Env<AttrContext> env: envs)
//                desugar(env, results);
//        }
//    	if (System.getenv("NOJML") == null) System.out.println("DESUGAR OUT " + results.size());
//        return stopIfError(CompileState.FLOW, results);
//    }

    /** This is overridden so that if attribute() returns null, processing continues (instead of crashing). */
    // FIXME - why might it return null, and should we stop if it does?
    @Override
    public Queue<Env<AttrContext>> attribute(Queue<Env<AttrContext>> envs) {
        ListBuffer<Env<AttrContext>> results = new ListBuffer<>();
        while (!envs.isEmpty()) {
            results.append(attribute(envs.remove()));
        }
        ((JmlAttr)attr).completeTodo();
        
        if (org.jmlspecs.openjml.Main.useJML) {
        	envs = results;
        	JmlSpecs specs = JmlSpecs.instance(context);
        	results = new ListBuffer<>();
        	while (!envs.isEmpty()) {
        		var env = envs.remove();
        		switch (env.tree.getTag()) {
        		case MODULEDEF:
        		case PACKAGEDEF:
        			break;
        		case TOPLEVEL:
        			for (var def : env.toplevel.defs) {
        				if (def instanceof JmlClassDecl) {
                        	//System.out.println("ATTRIBUTING SPECS of " + ((JmlClassDecl)def).sym);
        					JmlAttr.instance(context).attribClassBodySpecs(((JmlClassDecl)def));
        				}
        			}
        			break;
        		default:
        			JmlAttr.instance(context).attribClassBodySpecs((JmlClassDecl)env.enclClass);
        		}
        		results.append(env);
        	}
        }
      
        
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

    public Queue<Env<AttrContext>> flow(Queue<Env<AttrContext>> envs) {
        envs = super.flow(envs);
        ListBuffer<Env<AttrContext>> results = new ListBuffer<>();
        if (envs.isEmpty()) {
        	if (utils.esc) context.get(Main.IProgressListener.class).report(1,"Operation not performed because of parse or type errors");
        	return results;
        }
        
        if (utils.esc || utils.rac) {
        	JmlUseSubstitutions subst = new JmlUseSubstitutions(context);
            for (Env<AttrContext> env: envs) {
                env.tree = subst.translate(env.tree);
            }
        }
        if (utils.check) {
        	//JmlCheckSpecs.instance(context).check();
            return results; // Empty list - do nothing more
        } else if (utils.doc) {
            return results; // Empty list - do nothing more
        } else if (utils.esc) {
            JmlEsc esc = JmlEsc.instance(context);
        	try {
                esc.initCounts();
        	    for (Env<AttrContext> env: envs) esc(env); // Transforms and proves
        	} catch (PropagatedException e) {
        		// cancelation - catch and continue
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
        	for (var env: envs) {
        		var t = env.tree;
        		if (t instanceof JmlClassDecl && ((JmlClassDecl)t).sourcefile.getKind() != JavaFileObject.Kind.SOURCE) continue;
        		env = rac(env);
        		if (env == null) continue;
        		results.add(env);
        	}
        	return results;
        } else {
        	return envs;
        }
    }

    @Override
    protected void flow(Env<AttrContext> env, Queue<Env<AttrContext>> results) {
//        if (env.toplevel.sourcefile.getKind() != JavaFileObject.Kind.SOURCE) {
////            // FIXME - not sure why this is needed for rac but causes esc tests to fail
//            if (utils.rac) CompileStates.instance(context).put(env,CompileState.FLOW);
//            return;
//        }
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
            
            // The class named here must match that in org.jmlspecs.runtime.Utils.isRACCompiled
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
            JCTree newtree= null;
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

//            if (tree instanceof JmlClassDecl) {
//            	JmlClassDecl d = ((JmlClassDecl)tree);
//                if (d.sourcefile.getKind() != JavaFileObject.Kind.SOURCE) newtree = tree;
//            }
            {
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

                // Add the Import: import org.jmlspecs.runtime.*;
                
                if (JmlOption.includes(context,JmlOption.SHOW,"translated")) {
                    noticeWriter.println(String.format("[jmlrac] RAC Transformed: %s", currentFile));
                    // this could probably be better - is it OK to modify the AST beforehand? JLS
                    noticeWriter.println(
                            JmlPretty.toFancyLineFormat(
                                currentFile,
                                JmlPretty.racFormatter,            // the formatter 
                                "",  // a header prefix to print
                                JmlPretty.write(env.toplevel,true) // the source to format
                                ));
                }
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
    	if (env.toplevel.sourcefile.getKind() != JavaFileObject.Kind.SOURCE) return;
    	
        JmlEsc esc = JmlEsc.instance(context);
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
