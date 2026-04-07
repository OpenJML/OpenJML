/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
// FIXME - do a review
package com.sun.tools.javac.main;

import static com.sun.tools.javac.main.Option.PROC;

import java.io.PrintWriter;
import java.util.Collection;
import java.util.Queue;

import javax.annotation.processing.Processor;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlAstPrinter;
import org.jmlspecs.openjml.JmlJson;
//import org.jmlspecs.openjml.JmlClearTypes;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.Dir;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;
import org.jmlspecs.openjml.esc.JmlEsc;
import org.jmlspecs.openjml.ext.Modifiers;
import org.jmlspecs.openjml.visitors.JmlUseSubstitutions;

import com.google.gson.JsonElement;
import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.CompileStates.CompileState;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.util.Assert;
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

    static boolean debugParse2 = org.jmlspecs.openjml.Utils.debug("parse+");
    static boolean debugParse = debugParse2 || org.jmlspecs.openjml.Utils.debug("parse");
        
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
    
    /** Returns the singleton instanceof JmlCOMpiler for the given context, creating one if needed */
    // If the cast fails, then this method is being called before preRegister above has been called
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
        if (!org.jmlspecs.openjml.JmlOptions.instance(context).optionsAllSet) {  // FIXME - get this test to work
            utils.error("jml.internal", "JavaCompiler is being instantiated before all options are read");
            Utils.dumpStack();
        }
        this.verbose |= utils.jmlverbose >= Utils.JMLVERBOSE; // Only used in JavaCompiler // FIXME - options not yet set???
        this.resolver = JmlResolve.instance(context);
        this.noJML = !JmlOption.JML.isSet(context); // If this is true, we have JML capability in the tool, but we are ignoring all JML 
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
        var list = super.enterTrees(roots);
        var any = JmlEnter.instance(context).flush(); // FIXME - not sure this is needed
        //if (any) System.out.println("JmlCompiler - flush is needed");
        return list;
    }
    
//    @Override
//    public int errorCount() {
//        if (log.nerrors == 0 && options.isSet(Option.WERROR) &&
//                (log.nwarnings > 0 || ("0".equals(JmlOption.EXITVERIFY.value(context)) && Utils.instance(context).verifyWarnings > 0))) {
//            log.error(Errors.WarningsAndWerror);
//        }
//        return log.nerrors;
//    }

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
        //System.out.println("FIND SPEC FOR SOURCE " + filename);
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
        if (debugParse) System.out.println("parser: Seeking specfile for name: " + name);
        var specFile = JmlSpecs.instance(context).findSpecFile(name); // returns null if not found
        if (specFile == null) {
            // No spec file on specspath. Last resort is to look for a sibling of the source file.
            var path = java.nio.file.Paths.get(filename.toUri().getPath());
            //JmlSpecs.instance(context);
            specFile = JmlSpecs.withMockOverride(
                    new Dir.FileSystemDir(path.getParent().toString()).findFile(path.getFileName().toString().replace(".java",".jml"), context),
                    context);
        }
        if (debugParse) System.out.println("parser:     Found " + specFile);
        return specFile;
    }
    
    /** Overridden to emit debug information */
    @Override
    public void compile(Collection<JavaFileObject> sourceFileObjects,
                            Collection<String> classnames,
                            Iterable<? extends Processor> processors,
                            Collection<String> addModules) {
        if (Utils.debug("paths")) {
            System.out.println("classpath:  " + Utils.join(":",JmlSpecs.instance(context).getClassPath()));
            System.out.println("sourcepath: " + Utils.join(":",JmlSpecs.instance(context).getSourcePath()));
            System.out.println("specspath:  " + Utils.join(":",JmlSpecs.instance(context).getSpecsPath()));
        }
        super.compile(sourceFileObjects, classnames, processors, addModules);
    }
    
    /** Parses all the given files, producing a list of JmlCompilationUnit ASTs */
    @Override
    public List<JCCompilationUnit> parseFiles(Iterable<JavaFileObject> fileObjects) {
        try {
            var compunits = super.parseFiles(fileObjects);
            if (JmlOption.SHOW.includes(context,"ast")) {
                for (var cu: compunits) {
                    System.out.println(JmlAstPrinter.print(cu, context));
                    //                        if (specCU != null) {
                    //                            System.out.println(JmlAstPrinter.print(specCU, context));
                    //                        }
                }
            }

            if (JmlOption.SHOW.includes(context,"json")) {
                writeJson(compunits, false);
            }

            if (org.jmlspecs.openjml.Utils.instance(context).cmd == org.jmlspecs.openjml.Main.Cmd.PARSE) {
                // empty out the list of ASTs so that there is no further action in compilation
                compunits  = List.<JCCompilationUnit>nil();
            }
            return compunits;
        } catch (AssertionError e) {
            // Some parse errors cause an AssertionError. This catches it and converts it to 
            // the empty list, which is the usual way to communicate that the chain of compiler phases
            // is to be aborted. An error message is presumed to have been emitted when the AssertionError is thrown.
            return List.<JCCompilationUnit>nil();
        }
    }
    
    /** Write JSON files for the given Env objects, which are presumed to hold JmlCompilationUnits */
    public void writeJson(ListBuffer<Env<AttrContext>> results, boolean includeTypeInfo) {
        ListBuffer<JCCompilationUnit> cus = new ListBuffer<>();
        for (var env: results) {
            if (utils.isSpecFile(((JmlCompilationUnit)env.toplevel).source())) continue; // FIXME - when spec files are processed take care that the library specs are not processed
            cus.add(env.toplevel);
        }
        writeJson(cus.toList(), includeTypeInfo);
    }
    
    /** Write JSON fgiles for the given JCCompilationUnits */
    public void writeJson(List<JCCompilationUnit> compunits, boolean includeTypeInfo) {
        String dest = options.get("-d");
        if (dest != null && !dest.equals("-") && !new java.io.File(dest).exists() && !new java.io.File(dest).mkdirs()) {
            utils.error("jml.message", "Failed to create output directories: " + dest);
            return;
        }

        var json = new org.jmlspecs.openjml.JmlJson(context);
        for (var cu: compunits) {
            //System.out.println("JSON FOR " + includeTypeInfo + " " + cu.sourcefile);
            writeJson(dest, json, cu, null, includeTypeInfo);
        }
    }
    
    private static final int span = 100;
    private String formatLongString(String s) {
        if (s.length() <= span) return s;
        else return s.substring(0,span) + "\n" + formatLongString(s.substring(span));
    }

    private String writeJson(String dest, JmlJson json, JCTree decl, String name, boolean includeTypeInfo) {
        String sourcepath = decl instanceof JmlTree.JmlSource s ? s.source().getName() : "?";
        String out = null;
        JsonElement outtree = null;
        var stdout = context.get(Log.outKey);
        try {
            //json.clearIds();
            out = json.toJson(decl, includeTypeInfo); // serializes to a pretty-printed string
            // If we do both of these, we need to clear the cache of ids in between, but then we can't share ids between classes
            //json.clearIds();
            //outtree = json.toJsonTree(decl, includeTypeInfo); // serializes to an in-memory JSON tree
        } catch (Throwable e) {
            utils.error("jml.internal", "Failed translate to json (" + sourcepath + "): "+ e);
            e.printStackTrace(stdout);
            return null;
        }
        try {
//            // Checking the output by reparsing it and comparing string representations
//            @SuppressWarnings("deprecation")
//            var res = new JsonParser().parse(out);
//            if (!outtree.equals(res)) {
//                utils.error("jml.internal", "Reparsed JSON tree does not match the original tree: " + sourcepath);
//            }
//            // Parsed tree interprets unicode sequences
//            var rereadString = res.toString();
//            var treeString = outtree.toString();
//            // Serialized tree has unicode sequences
//            var nowsOut = out.replaceAll("[ \t\n]+","");
//            // Compare string version of parsed version of output text generated tree to string version of generated tree
//            if (!rereadString.equals(treeString)) { 
//                utils.error("jml.message", "Generated and reread json tree structures are different:\n"
//                        + formatLongString(rereadString)  + "\n\nVS.\n\n" + formatLongString(treeString));
//              System.out.println("Lengths " + rereadString.length() + " " + treeString.length());
//              for (int i = 0; i < treeString.length(); ++i) {
//                  if (rereadString.charAt(i) != treeString.charAt(i)) {
//                      System.out.println("   DIFF " + i + " " + rereadString.charAt(i) + " " + treeString.charAt(i));
//                      break;
//                  }
//              }
//            }
//            // Compare string version of parsed version of output text generated tree to directly generated json text
//            // These differ in unicode representations
//            if (!rereadString.equals(nowsOut)) { 
//                utils.error("jml.message", "Generated and reread json string structures (removing whitespace) are different:\n"
//                        + formatLongString(rereadString) + "\n\nVS.\n\n" + formatLongString(nowsOut));
//                System.out.println("Lengths " + rereadString.length() + " " + nowsOut.length());
//                for (int i = 0; i < nowsOut.length(); ++i) {
//                    if (rereadString.charAt(i) != nowsOut.charAt(i)) {
//                        System.out.println("   DIFF " + i + " " + rereadString.charAt(i) + " " + nowsOut.charAt(i));
//                        break;
//                    }
//                }
//            }
            // Check the output by deserializing the output text back into an AST
            if (JmlOption.JMLTESTING.isSet(context)) {
                // In testing mode, recreate a source AST from the output JSON text
                Object obj = json.toJava(out);
                JmlPretty p = new JmlPretty(stdout, true); p.printSourceInfo = true;
                if (!(obj instanceof JCTree tree)) {
                    stdout.println("Input and output ASTs differ");
                    stdout.println(obj.toString());
                    stdout.println(p.toString(decl));
                } else if (!p.toString(tree).equals(p.toString(decl))) {
                    stdout.println("Input and output ASTs differ");
                    stdout.println(p.toString(tree));
                    stdout.println(p.toString(decl));
                }
            }
        } catch (Throwable e) {
            utils.error("jml.message", "Failed read generated json (" + sourcepath + "): "+ e);            
        }
        if (dest == null) {
            // FIXME - cleanup name calculation
            // Write to file as sibling of input
            String path = sourcepath + ".json";
            if (name != null) {
                int k = sourcepath.lastIndexOf("/");
                path = sourcepath.substring(0, k+1) + name + ".json";
            }
            try {
                new java.io.File(path).delete();
                new java.io.File(path).createNewFile();
                try ( var fw = new java.io.FileWriter(path); ) {
                    fw.append(out);
                    fw.append("\n");
                } finally {}
            } catch (java.io.IOException e) {
                utils.error("jml.message", "Failed to delete or write to output: " + path + ": " + e);
            }
        } else if (dest.equals("-")) {
            // Write all files consecutively to standard out
            stdout.println(out);
        } else {
            // Write files using 'dest' as package root
            String pdecl = "";
            if (decl instanceof JmlCompilationUnit ccu) {
                pdecl = ccu.pid == null ? "" : ccu.pid.pid.toString().replace('.','/') + "/";
            } else if (decl instanceof JmlClassDecl cd) {
                pdecl = cd.sym.fullname.toString();
                int k = pdecl.lastIndexOf('.');
                pdecl = k < 0 ? "" : pdecl.substring(0,k).replace('.','/');
            }
            String pid = pdecl;
            String path = sourcepath;
            if (name == null) {
                int k = path.lastIndexOf('/');
                path = path.substring(k+1);
            } else {
                path = "/" + name;
            }
            var dir = dest + "/" + pid;
            path = dir + path + ".json";
            try {
                new java.io.File(path).delete();
                if (!new java.io.File(dir).exists() && !new java.io.File(dir).mkdirs()) {
                    utils.error("jml.message", "Failed to create output directories: " + dir);
                    return out;
                }
                if (!new java.io.File(path).createNewFile()) {
                    utils.error("jml.message", "Failed to create output file: " + path);
                    return out;
                }
                try ( var fw = new java.io.FileWriter(path); ) {
                    fw.append(out);
                    fw.append("\n");
                } finally {}
            } catch (Throwable e) {
                utils.error("jml.message", "Failed to delete or write to output: " + path + ": " + e);
            }
        }
        return out;
    }
 
    /** Parse the given file */
    public JCTree.JCCompilationUnit parse(JavaFileObject filename) {
        if (inputFiles.contains(filename)) {
            utils.error(filename, -1, "jml.message",  // FIXME - use the no position name
                    "Parsing failed because there is an attempt to parse the file " + filename.getName() + " twice, likely indicating that the file does not actually declare the desired class");
            var tree = (JmlCompilationUnit)make.TopLevel(List.<JCTree>nil());
            tree.sourcefile = filename;
            tree.specsCompilationUnit = tree;
            return tree;
        }
        JavaFileObject prev = log.useSource(filename);
        JavaFileObject specFile = null;
        boolean jmlOption = JmlOption.JML.isSet(context);
        noJML = !jmlOption;
        var charSeq = readSource(filename);
        try {
            if (debugParse) System.out.println("parser: About to parse: " + filename + (noJML?" (ignoring JML)":""));
            if (filename.getKind() == JavaFileObject.Kind.SOURCE) {
                // If the file is a source file and there is a specs file, we ignore any JML in the source file
                // We also always ignore the JML if -no-jml has been set
                specFile = checkForSpecsFile(filename, charSeq);
                noJML = specFile != null || !jmlOption;
            }
            // This block of code is inlined (twice) from super.parse(filename) in order to avoid rereading the source file
            JmlCompilationUnit javaCU = (JmlCompilationUnit)parse(filename, charSeq);
            if (javaCU.endPositions != null) log.setEndPosTable(filename, javaCU.endPositions);
            JmlCompilationUnit specCU = null;
            if (specFile != null && jmlOption) {
                noJML = !jmlOption;
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
            
        	org.jmlspecs.openjml.visitors.JmlCheckParsedAST.check(context, javaCU, filename);
            if (specCU != null) org.jmlspecs.openjml.visitors.JmlCheckParsedAST.check(context, specCU, specFile);
            String ss = JmlOption.SHOW.value(context);
            if (javaCU != null && ss != null) {
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
            noJML = !jmlOption;
            log.useSource(prev);
        }
    }
    
    /** This flag determines whether JML annotations are being parsed -- it is a bit of a hack to communicate with the scanner */
    private boolean noJML = false;
    public boolean disableJML() { return noJML; }
    public void disableJML(boolean b) { noJML = b; }
    
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
        if (debugParse) System.out.println("parser: Seeking specfile for type symbol: " + typeSymbol + " " + typeSymbol.hashCode());
        JavaFileObject specFile = JmlSpecs.instance(context).findSpecFile(typeSymbol);
    	if (debugParse) System.out.println("parser: Parsing specs " + typeSymbol + " " + specFile);
        if (specFile == null) return null;

        JmlCompilationUnit specCU = null;
        if (log.getSource(specFile).getEndPosTable() != null) {
            // An obscure situation in which the file has already been parsed, likely because there is an attempt to compile
            // a class that duplicates a binary class in a library, and consequently there are two class symbols for the "same"
            // class, but the same specs file is found for both of them.
            // For now, we just declare this a failure
            utils.error(specFile, -1, "jml.message",  // FIXME - use the no position name
                    "Parsing failed because there is an attempt to parse a spec file twice, likely indicating that there are two instances of a class, one binary and one in source: " + typeSymbol);
            if (typeSymbol.toString().equals("java.lang.Object")) {
                // In case this is java.lang.Object, we will have a big trail of errors, so we just abort
                throw new PropagatedException(new org.jmlspecs.openjml.JmlInternalAbort());
            }
        } else {
            specCU = (JmlCompilationUnit)super.parse(specFile);
        }

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

        if (JmlOption.SHOW.includes(context, "typed-ast")) {
            for (var env: results) if (((JmlCompilationUnit)env.toplevel).sourcefile.toString().contains(".java")) System.out.println(JmlAstPrinter.print(env.toplevel, context));
        }

        if (JmlOption.SHOW.includes(context, "typed-json")) {
            writeJson(results, true);
        }
        

        return stopIfError(CompileState.ATTR, results);
    }
    
    public Env<AttrContext> attribute(Env<AttrContext> env) {
        try {
            return super.attribute(env);
        } finally {
            if (!env.toplevel.sourcefile.toString().contains(".jml")) {
                synchronized (org.openjml.API.astListeners) { 
                    for (var listener: org.openjml.API.astListeners) {
                        listener.notify(context, env.toplevel.sourcefile, (JmlCompilationUnit)env.toplevel);
                    }
                }
            }
        }
    }


    /** Overridden in order to insert ESC and RAC (or other) processing after the OpenJDK flow processing */
    @Override
    public Queue<Env<AttrContext>> flow(Queue<Env<AttrContext>> envsin) {
    	Assert.check(compilePolicy == CompilePolicy.SIMPLE); // FIXME - only works for SIMPLE at present
    	var noresults = new java.util.LinkedList<Env<AttrContext>>();
        if (envsin.isEmpty()) {
        	if (!utils.check) utils.progress(0,Utils.PROGRESS,"Operation not performed because of parse or type errors");
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
            if (JmlOption.SHOW.includes(context,"program","all")) { 
                //envs.stream().forEach(e->System.out.println(e.toplevel.sourcefile));
                envs.stream().filter(e->e.toplevel.sourcefile.getKind() == JavaFileObject.Kind.SOURCE).forEach(e->System.out.println(e.toplevel.toString()));
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
                if (utils.jmlverbose >= Utils.PROGRESS && !utils.testingMode && JmlOption.SHOW_SUMMARY.isSet(context)) utils.note(false,summary);
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
                if (utils.isSpecFile(((JmlTree.JmlSource)t).source())) continue;
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
        if (!JmlOption.USEJAVACOMPILER.isSet(context)) {
            options.put(PROC.primaryName + "none", "none");
        }
        super.initProcessAnnotations(processors, initialFiles, initialClassNames);
    }
    
    // FIXME _ review
    /** Does the RAC processing on the argument. */
    protected Env<AttrContext> rac(Env<AttrContext> env) {
        if (debugCompiler) System.out.println("Starting rac");
        JCTree tree = env.tree;
        PrintWriter noticeWriter = log.getWriter(WriterKind.NOTICE);
        //System.out.println("RACING " + env.tree.getClass() + " " + env.toplevel.sourcefile);
        
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
        utils.progress(0,Utils.PROGRESS,"RAC-Compiling " + utils.envString(env));
        if (utils.jmlverbose >= Utils.JMLDEBUG) noticeWriter.println("rac " + utils.envString(env));
        
        if (env.tree instanceof JCClassDecl) {
            JCTree newtree= null;
            if (JmlOption.SHOW.includes(context,"translated","all")) {
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
                
                if (JmlOption.SHOW.includes(context,"translated","all")) {
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
        if (debugCompiler) System.out.println("[compiler] Starting esc");
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
