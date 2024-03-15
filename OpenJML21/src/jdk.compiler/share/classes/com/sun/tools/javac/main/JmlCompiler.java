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
import org.jmlspecs.openjml.JmlOptions;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlAstPrinter;
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
import com.sun.tools.javac.comp.CompileStates.CompileState;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.comp.Resolve;
import com.sun.tools.javac.comp.Todo;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.main.JavaCompiler.InitialFileParser;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Abort;
import com.sun.tools.javac.util.Assert;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Pair;
import com.sun.tools.javac.util.PropagatedException;

import static com.sun.tools.javac.parser.Tokens.*;

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
    	// (If we do this initialization during tool registration, we get circular instantiation)
    	init();
    	JmlEnter.instance(context).hold();
    	var list = super.enterTrees(roots);
    	JmlEnter.instance(context).release();
    	JmlEnter.instance(context).flush();
    	return list;
    }
    
    static boolean debugParse2 = org.jmlspecs.openjml.Utils.debug("parse+");
    static boolean debugParse = debugParse2 || org.jmlspecs.openjml.Utils.debug("parse");
    
    // This bit of complexity/hackery is due to the following problem. JML states that if there is a .jml file, all the specs in
    // the .jml file supersede anything in the .java file. So, in that case, any JML annotations in the .java file are ignored;
    // in fact they are not even required to be parsable. So we need to know whether there is a .jml file to know how to parse
    // the .java file (since we want to do that in one pass -- not just collect all the JML comments and then parse them later if
    // they are needed). However, to find the .jml file we need to know what package it is in, and for that we need to find and
    // interpret the package declaration in the .java file. So we do just enough reading of the .java source (without processing
    // any JML) to find the package, look for a corresponding .jml file. If there is one, we parse the .java without JML annotations
    // (except JML annotations in method and initialization bodies).
    // If there is no .jml file, we parse the .java with the annotations as the specs.
    //@ nullable
    JavaFileObject checkForSpecsFile(JavaFileObject filename, CharSequence charSeq) {
        var charBuf = charSeq instanceof java.nio.CharBuffer cb ? cb : java.nio.CharBuffer.wrap(charSeq);
    	JmlScanner.JmlScannerFactory fac = (JmlScanner.JmlScannerFactory)JmlScanner.JmlScannerFactory.instance(context);
        var tokenizer = new com.sun.tools.javac.parser.JmlTokenizer(fac, charBuf, true);
        Token t;
    	String name = "";
        outer:{
        	while ((t=tokenizer.readToken()) != null) {
        		if (t.kind == TokenKind.PACKAGE) break ;
        		if (t.kind == TokenKind.IMPORT) break outer;
        		if (t.kind == TokenKind.CLASS) break outer;
        		if (t.kind == TokenKind.LBRACE) break outer;
        		if (t.kind == TokenKind.EOF) break outer;
        	}
    		t = tokenizer.readToken();
    		if (t.kind != TokenKind.IDENTIFIER) return null; // Bad package declaration -- report as no jml file; the error will be reported on the real parsing of the .java file
    		name += t.name();
    		t = tokenizer.readToken();
        	while (t.kind != TokenKind.SEMI) {
        		if (t.kind != TokenKind.DOT) return null; // Bad package declaration
        		name += ".";
        		t = tokenizer.readToken();
        		if (t.kind != TokenKind.IDENTIFIER) return null; // Bad package declaration
        		name += t.name();
        		t = tokenizer.readToken();
        	}
        	name += ".";
        }
    	String s = filename.toUri().getPath();
    	int k = s.lastIndexOf('/');
    	s = s.substring(k+1);
    	k = s.indexOf('.');
    	s = s.substring(0,k); // filename without suffix or directory
    	name += s; // fully qualified class name
    	if (debugParse) System.out.println("parser: Seeking specfile for " + name);
    	return JmlSpecs.instance(context).findSpecFile(name); // returns null if not found
    }
    
    /** Overridden to emit debug information */
    @Override
    public void compile(Collection<JavaFileObject> sourceFileObjects,
                            Collection<String> classnames,
                            Iterable<? extends Processor> processors,
                            Collection<String> addModules) {
        if (Utils.debug("paths")) {
        	// TODO - what output writer to use?
            System.out.println("sourcepath: " + Utils.join(":",JmlSpecs.instance(context).getSourcePath()));
            System.out.println("specspath:  " + Utils.join(":",JmlSpecs.instance(context).getSpecsPath()));
        }
        if (Utils.debug("options")) JmlOptions.instance(context).dumpOptions();
        super.compile(sourceFileObjects, classnames, processors, addModules);
    }
    
    @Override
    public List<JCCompilationUnit> parseFiles(Iterable<JavaFileObject> fileObjects) {
    	try {
    		return super.parseFiles(fileObjects);
    	} catch (AssertionError e) {
    		// Some parse errors cause an AssertionError. This catches it and converts it to 
    		// the empty list, which is the usual way to communicate that the chain of compiler phases
    		// is to be aborted.
        	return List.<JCCompilationUnit>nil();
    	}
    }
 
    public JCTree.JCCompilationUnit parse(JavaFileObject filename) {
        JavaFileObject prev = log.useSource(filename);
        JavaFileObject specFile = null;
        noJML = false;
        var charSeq = readSource(filename);
        try {
        	if (filename.getKind() == JavaFileObject.Kind.SOURCE) {
        		specFile = checkForSpecsFile(filename, charSeq);
        		noJML = specFile != null; // Using the noJML field to pass a parameter to the scanner factory is a hack and precludes parallel parsing within a context
        	}
        	// This block of code is inlined (twice) from super.parse(filename) in order to avoid rereading the source file
        	JmlCompilationUnit javaCU = (JmlCompilationUnit)parse(filename, charSeq);
        	if (javaCU.endPositions != null) log.setEndPosTable(filename, javaCU.endPositions);
        	JmlCompilationUnit specCU = null;
        	if (specFile != null) {
        		noJML = false;
        		log.useSource(specFile);
        		charSeq = readSource(specFile);
        		specCU = (JmlCompilationUnit)parse(specFile, charSeq);
        		if (specCU.endPositions != null) log.setEndPosTable(specFile, specCU.endPositions);
                javaCU.specsCompilationUnit = specCU;
                specCU.specsCompilationUnit = specCU;
                specCU.sourceCU = javaCU;
                javaCU.sourceCU = javaCU;
        	} else {
        		javaCU.specsCompilationUnit = javaCU;
                javaCU.sourceCU = javaCU;
        	}
        	if (debugParse) System.out.println("parser: Parsed " + filename + " " + specFile + " " + " Classes: " + Utils.join(" ",javaCU.defs.stream().filter(d->d instanceof JmlClassDecl).map(d->((JmlClassDecl)d).name.toString())));
            if (debugParse && filename.toString().contains("Object")) { System.out.println(specCU.toString()); }
            org.jmlspecs.openjml.visitors.JmlCheckParsedAST.check(context, javaCU, filename);
            if (specCU != null) org.jmlspecs.openjml.visitors.JmlCheckParsedAST.check(context, specCU, specFile);
            if (javaCU != null && JmlOptions.instance(context).isSet(JmlOption.SHOW)) {
                String ss = JmlOption.value(context, JmlOption.SHOW);
                if (ss.contains("ast") && filename.toString().contains("Test.java")) { // FIXME - fix this to show user-designated file
                    System.out.println(JmlAstPrinter.print(javaCU, context));
                    if (specCU != null) {
                        System.out.println(JmlAstPrinter.print(specCU, context));
                    }
                }
            }

        	return javaCU;
        	// FIXME - are javaCU and specCU always non-null?
        	// FIXME - do we need to check/set the module and package in the specs file? (like we do in parseSpecs)
        } finally {
            noJML = false;
            log.useSource(prev);
        }
    }
    
    /** This flag determines whether JML annotations are being parsed -- it is a bit of a hack to communicate with the scanner */
    public boolean noJML = false;
    
    /** Parses the specs for a class - used when we need the specs corresponding to a binary file;
     * this may only be called for public top-level classes (the specs for non-public or
     * nested classes are part of the same file with the corresponding public class).
     * Returns null if no specifications file is found.
     * @param typeSymbol the symbol of the type whose specs are sought
     * @return the possibly null parsed compilation unit, as an AST
     */
    /*@Nullable*/
    public JmlCompilationUnit parseSpecs(ClassSymbol typeSymbol) {
    	// TODO - what output writer to use?
        if (debugParse) System.out.println("parser: Seeking specfile for " + typeSymbol);
        JavaFileObject specFile = JmlSpecs.instance(context).findSpecFile(typeSymbol);
    	if (debugParse) System.out.println("parser: Parsing specs " + typeSymbol + " " + specFile);
        if (specFile == null) return null;

        var specCU = (JmlCompilationUnit)super.parse(specFile);

    	if (debugParse && specCU == null) System.out.println("parser: Parsing failed: " + specFile);
        if (specCU == null) return null;
        
        // Successful parse. Check that the package is correct.
        // Also set the module and package symbols in the CU
        Symbol.PackageSymbol p = typeSymbol.packge();
        String ps = p.toString();
        String specpid = specCU.pid == null ? "unnamed package" : specCU.pid.getPackageName().toString();
        if (!ps.equals(specpid)) {
        	if (!ps.isEmpty()) {
        		utils.error(specCU.sourcefile, specCU.pid == null ? 1 : specCU.pid.pos,
        				"jml.mismatched.package",
        				specpid,
        				p.toString());
                specCU.packge = p; // FIXME: Trying to continue causes cascading errors; at least need to fix the pid as well
        		return null; // Report as no specs
        	} else {
        		specCU.packge = syms.rootPackage;
        	}
        } else {
        	specCU.packge = p;
        }
        specCU.modle = p.modle;
        specCU.specsCompilationUnit = specCU;
        specCU.sourceCU = null;
        org.jmlspecs.openjml.visitors.JmlCheckParsedAST.check(context, specCU, specFile);
        if (debugParse) System.out.println("parser: Parsed specs " + typeSymbol + " " + specFile);
        return specCU;
    }

    /** This is overridden to do the JML attribution (via completeTodo) */
    // FIXME - review the reason for this override
    @Override
    public Queue<Env<AttrContext>> attribute(Queue<Env<AttrContext>> envs) {
        ListBuffer<Env<AttrContext>> results = new ListBuffer<>();
        while (!envs.isEmpty()) {
            results.append(attribute(envs.remove()));
        }
        ((JmlAttr)attr).completeTodo();
        
//        if (org.jmlspecs.openjml.Main.useJML) {
//        	envs = results;
//        	JmlSpecs specs = JmlSpecs.instance(context);
//        	results = new ListBuffer<>();
//        	while (!envs.isEmpty()) {
//        		var env = envs.remove();
//        		switch (env.tree.getTag()) {
//        		case MODULEDEF:
//        		case PACKAGEDEF:
//        			break;
//        		case TOPLEVEL:
////        			for (var def : env.toplevel.defs) {
////        				if (def instanceof JmlClassDecl) {
////        					JmlAttr.instance(context).attribClassBodySpecs(((JmlClassDecl)def));
////        				}
////        			}
////        			break;
//        		default:
//        			//JmlAttr.instance(context).attribClassBodySpecs((JmlClassDecl)env.enclClass);
//        		}
//        		results.append(env);
//        	}
//        }

        return stopIfError(CompileState.ATTR, results);
    }

    /** Overridden in order to insert ESC and RAC (or other) processing */
    @Override
    public Queue<Env<AttrContext>> flow(Queue<Env<AttrContext>> envsin) {
    	Assert.check(compilePolicy == CompilePolicy.SIMPLE); // FIXME - only works for SIMPLE at present
    	var noresults = new java.util.LinkedList<Env<AttrContext>>();
        if (envsin.isEmpty()) {
        	if (!utils.check) context.get(Main.IProgressListener.class).report(1,"Operation not performed because of parse or type errors");
        	return noresults;
        }
    	var envs = super.flow(envsin);
        if (utils.esc || utils.rac) {
        	JmlUseSubstitutions subst = new JmlUseSubstitutions(context);
            for (Env<AttrContext> env: envs) {
                env.tree = subst.translate(env.tree);
            }
        }
        if (utils.check) {
        	if (JmlOption.includes(context,JmlOption.SHOW,"program")) { 
        		envs.stream().forEach(e->System.out.println(e.toplevel.toString()));
        	}
            return noresults; // Empty list - do nothing more
        } else if (utils.doc) {
            return noresults; // Empty list - do nothing more
        } else if (utils.esc) {
            JmlEsc esc = JmlEsc.instance(context);
        	try {
                esc.initCounts();
        	    for (Env<AttrContext> env: envs) esc(env); // Transforms and proves
        	} catch (PropagatedException e) {
        		// cancellation or error in specifications parsed on demand - catch and continue // TODO: Review
        	} finally {
                String summary = esc.reportCounts();
                if (utils.jmlverbose >= Utils.PROGRESS && !Utils.testingMode && JmlOption.isOption(context, JmlOption.SHOW_SUMMARY)) utils.note(false,summary);
        	}
    		return noresults; // Empty list - Do nothing more
        } else if (utils.infer) {
            for (Env<AttrContext> env: envs)
                infer(env);
            return noresults;
        } else if (utils.rac) {
        	var results = new java.util.LinkedList<Env<AttrContext>>();
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
    public void initProcessAnnotations(Iterable<? extends Processor> processors,
            Collection<? extends JavaFileObject> initialFiles,
            Collection<String> initialClassNames) {
        // Annotation processors are not necessarily compatible with OpenJML so 
        // they are disabled (e.g. lombok is not compatible)
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
        // Only run ESC on source files (.jml files are Kind.OTHER)
    	if (env.toplevel.sourcefile.getKind() != JavaFileObject.Kind.SOURCE) return;
    	
        JmlEsc esc = JmlEsc.instance(context);
        esc.check(env.tree);
        
        shouldStopPolicyIfNoError = CompileState.TRANSTYPES;
        shouldStopPolicyIfError = CompileState.TRANSTYPES;

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
