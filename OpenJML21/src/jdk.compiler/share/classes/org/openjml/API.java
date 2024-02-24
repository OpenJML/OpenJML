/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.openjml;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.net.URI;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;

import javax.tools.DiagnosticListener;
import javax.tools.JavaFileManager;
import javax.tools.JavaFileObject;
import javax.tools.SimpleJavaFileObject;

import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.esc.BasicBlocker2;
import org.jmlspecs.openjml.esc.BasicProgram;
import org.jmlspecs.openjml.esc.JmlEsc;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;

import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.Attr;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Enter;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.file.JavacFileManager;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.main.JmlCompiler;
import com.sun.tools.javac.comp.CompileStates;
import com.sun.tools.javac.comp.CompileStates.CompileState;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.Pretty;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.Position;

import org.jmlspecs.openjml.Main;

/** This class is a wrapper and publicly published API for the OpenJML tool 
 * functionality.  In principle, any external programmatic interaction with
 * openjml would go through methods in this class.  [In practice some internal
 * classes are exposed as well.]
 * <P>
 * The class is used as follows.  The user creates a new API object and makes
 * calls to it; each distinct API object encapsulates a completely separate
 * compilation context.  What would ordinarily be command-line options are
 * specified on creation of the API object; for the most part they are not
 * changeable after the compilation context has been created (where change is
 * allowed, a method call is provided).
 * <P>
 * There are also static methods, named execute, that are public entry points to the
 * various tools (jml checker, jmldoc, ...) that openjml provides.  It performs 
 * a one-time processing of files, without making the classes and ASTs available,
 * just like a command-line execution would do.
 * <P>
 * The public API consists of the methods with public visibility in this 
 * compilation unit.
 *
 * @author David Cok
 */
public class API implements IAPI {

    /** The encapsulated org.jmlspecs.openjml.Main object */
    private Main main = null;
//    //@ initially main != null;
//    
//    /** The listener for diagnostic messages */
//    protected DiagnosticListener<? extends JavaFileObject> diagListener = null;
//    
////    /** The listener for proof results */
////    protected IProofResultListener proofResultListener;
//    
//
    /** Creates a new compilation context, initialized with given command-line options;
     * use Factory.makeAPI to create new API objects.
     * Output is sent to System.out; no diagnostic listener is used (so errors
     * and warnings are sent to System.out). 
     * @param args the command-line options and initial set of files with which
     * to load the compilation environment
     */
    //@ ensures isOpen;
    protected API()  {
//        try {
//            main = new org.jmlspecs.openjml.Main("openjml", new PrintWriter(System.out));
//        } catch (Exception e) {
//            // FAILURE
//        }
    }
//    
//    /** Creates an API that will send informational output to the
//     * given PrintWriter and diagnostic output to the given listener; no
//     * operations are initiated however;
//     * use Factory.makeAPI to create new API objects - don't call the constructor directly.
//     * @param writer destination of non-diagnostic output (null means System.out)
//     * @param listener receiver for diagnostic output
//     * @param options the set of options to use, or null to mean default initialization
//     * @param args files and additional options (as command-line arguments)
//     */
//    //@ ensures isOpen;
//    protected API(/*@nullable*/ PrintWriter writer, 
//            /*@nullable*/ DiagnosticListener<? extends JavaFileObject> listener, 
//            /*@nullable*/ Options options,
//            /*@non_null*/ String... args) throws java.io.IOException {
//        if (writer == null) {
//            writer = new PrintWriter(System.out);
//        }
//        main = new Main(Strings.applicationName,writer);
//        this.diagListener = listener;
//        // FIXME - handle options and args
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#context()
//     */
//    @Override
//    //@ ensures \result == main.context;
//    /*@pure*/
//    public /*@nullable*/ Context context() {
//        return main == null ? null : main.context;
//    }
//
//    /** Returns the compiler object for this context. */
//    @Override /*@pure*/ /*@nullable*/
//    public Main main() { return main; }
//
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#setProgressReporter(org.jmlspecs.openjml.Main.IProgressReporter)
//     */
//    @Override
//    public void setProgressListener(/*@ nullable */ Main.IProgressListener p) {
//        if (main.progressDelegator != null) {
//            p.setContext(context());
//            Main.progressListener = () -> p;
//        }
//    }
//    
//    IProofResultListener prl;
//    
//    @Override 
//    public IProofResultListener setProofResultListener(/*@nullable*/ IProofResultListener p) {
//    	prl = p;
//    	return context().get(IProofResultListener.class).setListener(p);
//    }
//    
//    /** Returns the string describing the version of OpenJML that is this
//     * set of classes.
//     * @return the version of this instance of OpenJML
//     */
//    @Override
//    public /*@non_null*/ String version() {
//        return JavaCompiler.version();
//    }
//    
//    // See comment in parent interface
//    @Override
//    public void initOptions(/*@non_null*/ Options options, /*@non_null*/ String ... args) {
//    	Context c = context();
//    	Options.instance(c).putAll(options);
//    	Main.instance(c).addOptions(args);
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#setOption(java.lang.String, java.lang.String)
//     */
//    //@ requires isOpen;
//    //@ ensures isOpen;
//    @Override
//    public void addOptions(String... args) {
//        main.addOptions(args);
//    }
//    
//    @Override
//    public void addUncheckedOption(String arg) {
//        main.addUncheckedOption(arg);
//    }
//
//
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getOption(java.lang.String)
//     */
//    @Override
//    public /*@nullable*/ String getOption(String name) {
//        return Options.instance(context()).get(name);
//    }
//    
//    // Expected to be called in a different thread
//    @Override
//    public void abort() {
//       if (main != null) JmlEsc.instance(main.context()).abort();
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#execute(Options, String[])
//     */
//    @Override
//    public int execute(/*@nullable*/ Options options, /*@non_null*/ String ... args) {
//        int ret = main.executeNS(main.out(), diagListener, prl, options, args);
//        return ret;
//    }
//    
    /* (non-Javadoc)
     * @see org.jmlspecs.openjml.IAPI#execute(PrintWriter, DiagnosticListener<JavaFileObject>, Options, String[])
     */
    private int execute(/*@non_null*/ PrintWriter writer, /*@nullable*/ DiagnosticListener<JavaFileObject> diagListener, /*@nullable*/ Options options, /*@non_null*/ String ... args) {
        int ret = Main.execute(writer, diagListener, null, args);
        return ret;
    }
    
    @Override
    public int execute(/*@non_null*/ String ... args) {
        return execute(null, null, null, args);
    }

    @Override
    public int execute(
            /*@non_null*/ PrintWriter writer, 
            /*@non_null*/ String ... args) {
        return execute(writer, null, null, args);
    }

    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#jmldoc(String[])
//     */
//    public int jmldoc(/*@non_null*/ String... args) {
//        return 4; // FIXME - org.jmlspecs.openjml.jmldoc.Main.execute(args);
//    }
//    
//    @Override
//    public boolean isTypechecked(ClassSymbol csym) {
//        Env<AttrContext> env = Enter.instance(context()).getEnv(csym);
//        if (env == null) return false;
//        return env.tree.type != null;
//    }
//
//    @Override
//    public boolean isTypechecked(String qualifiedName) {
////        ClassSymbol csym = Symtab.instance(context()).classes.get(Names.instance(context()).fromString(qualifiedName));
////        if (csym == null) return false;
////        return isTypechecked(csym);
//    	return false; // FIXME
//    }
//    
//    @Override
//    public void clearTypes(Collection<? extends JCCompilationUnit> trees) {
//        //for (JCCompilationUnit t: trees) new JmlClearTypes(context).scan(t);
//    }
//
//
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#enterAndCheck(org.jmlspecs.openjml.JmlTree.JmlCompilationUnit[])
//     */
//    @Override
//    public int typecheck(/*@non_null*/ JmlCompilationUnit... trees) throws IOException {
//        if (context() == null) {
//            throw new NullPointerException("There is no valid compilation context");
//        }
//        if (trees == null) {
//            throw new IllegalArgumentException("Argument 'trees' of API.enterAndCheck is null");
//        }
//        ListBuffer<JCCompilationUnit> list = new ListBuffer<JCCompilationUnit>();
//        list.appendArray(trees);
//        return typecheck(list.toList());
//    }
//
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#typecheck(java.util.Collection<? extends JmlCompilationUnit>)
//     */
//    @Override
//    public int typecheck(/*@non_null*/ Collection<? extends JmlCompilationUnit> trees) throws java.io.IOException {
//        if (context() == null) {
//            throw new NullPointerException("There is no valid compilation context");
//        }
//        if (trees == null) {
//            throw new IllegalArgumentException("Argument 'trees' of API.enterAndCheck is null");
//        }
//        ListBuffer<JCCompilationUnit> list = new ListBuffer<JCCompilationUnit>();
//        list.addAll(trees);
//        return typecheck(list.toList());
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#typecheck(java.util.List<? extends JmlCompilationUnit>)
//     */
//    @Override
//    public int typecheck(/*@non_null*/ List<? extends JCCompilationUnit> list) throws IOException {
//        Context context = context();
//        JmlCompiler jcomp = JmlCompiler.instance(context);
//        JmlTree.Maker maker = JmlTree.Maker.instance(context);
////        for (JCCompilationUnit jcu: list) {
////            for (JCTree t: jcu.defs) {
////                if (t instanceof JmlClassDecl && ((JmlClassDecl)t).typeSpecs == null) JmlParser.filterTypeBodyDeclarations((JmlClassDecl)t,context,maker);
////            }
//////            for (JmlClassDecl t: ((JmlCompilationUnit)jcu).parsedTopLevelModelTypes) {
//////                if (t.typeSpecs == null) JmlParser.filterTypeBodyDeclarations(t,context, maker);
//////            }
////        }
//
//        ListBuffer<JCCompilationUnit> jlist = new ListBuffer<JCCompilationUnit>();
//        jlist.addAll(list);
//        
//        // FIXME
//        // The following statements are a subset of the compilation tool chain from JavaCompiler
////        JavaCompiler dc =
////            jcomp.processAnnotations(
////                    jcomp.enterTrees(jcomp.stopIfError(CompileState.PARSE, jlist.toList())),
////                com.sun.tools.javac.util.List.<String>nil()); // TODO - someday incorporate annotation processors
////        dc.flow(dc.attribute(dc.todo));
//        int errs = Log.instance(context()).nerrors;
//        Log.instance(context()).nerrors = 0;
//        return errs;
//    }
//
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#parseFiles(java.io.File[])
//     */
//    @Override
//    public /*@ non_null */ java.util.List<JmlCompilationUnit> parseFiles(/*@non_null*/ File... files) {
//        JmlCompiler c = JmlCompiler.instance(context());
//        Log log = Log.instance(context());
//        Iterable<? extends JavaFileObject> fobjects = ((JavacFileManager)context().get(JavaFileManager.class)).getJavaFileObjects(files);
//        ArrayList<JmlCompilationUnit> trees = new ArrayList<JmlCompilationUnit>();
//        for (JavaFileObject fileObject : fobjects) {
//        	JavaFileObject prev = log.useSource(fileObject);
//        	var tab = log.currentSource().getEndPosTable();
//        	log.useSource(prev);
//            if (tab != null) continue; // File object already parsed
//            trees.add((JmlCompilationUnit)c.parse(fileObject));
//        }
//        return trees;
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#parseFiles(String[])
//     */
//    @Override
//    public /*@ non_null */ java.util.List<JmlCompilationUnit> parseFiles(/*@non_null*/ String... filenames) {
//        File[] files = new File[filenames.length];
//        for (int i=0; i<filenames.length; i++) {
//            files[i] = new File(filenames[i]);
//        }
//        return parseFiles(files);
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#parseFiles(javax.tools.JavaFileObject[])
//     */
//    @Override
//    public /*@ non_null */ java.util.List<JmlCompilationUnit> parseFiles(/*@non_null*/ JavaFileObject... inputs) {
//        JmlCompiler c = JmlCompiler.instance(context());
//        ArrayList<JmlCompilationUnit> trees = new ArrayList<JmlCompilationUnit>();
//        for (JavaFileObject fileObject : inputs)
//            trees.add((JmlCompilationUnit)c.parse(fileObject));
//        return trees;
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#parseFiles(java.util.Collection)
//     */
//    @Override
//    public /*@ non_null */ java.util.List<JmlCompilationUnit> parseFiles(/*@non_null*/ Collection<? extends JavaFileObject> inputs) {
//        JmlCompiler c = JmlCompiler.instance(context());
//        ArrayList<JmlCompilationUnit> trees = new ArrayList<JmlCompilationUnit>();
//        for (JavaFileObject fileObject : inputs)
//            trees.add((JmlCompilationUnit)c.parse(fileObject));
//        return trees;
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#parseSingleFile(java.io.File)
//     */
//    @Override
//    public /*@non_null*/ JmlCompilationUnit parseSingleFile(/*@non_null*/ String filename) {
//        return parseSingleFile(makeJFOfromFilename(filename));
//    }
//    
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#parseSingleFile(java.io.File)
//     */
//    @Override
//    public /*@non_null*/ JmlCompilationUnit parseSingleFile(/*@non_null*/ JavaFileObject jfo) {
//        JmlCompiler c = JmlCompiler.instance(context());
//        JmlCompilationUnit specscu = (JmlCompilationUnit)c.parse(jfo);
//        return specscu;
//    }
//
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#parseString(java.lang.String, java.lang.String)
//     */
//    @Override
//    public /*@non_null*/ JmlCompilationUnit parseString(/*@non_null*/ String name, /*@non_null*/ String content) throws Exception {
//        if (name == null || name.length() == 0) throw new IllegalArgumentException();
//        JmlCompiler c = JmlCompiler.instance(context());
//        JavaFileObject file = makeJFOfromString(name,content);
//        Iterable<? extends JavaFileObject> fobjects = List.<JavaFileObject>of(file);
//        JmlCompilationUnit jcu = ((JmlCompilationUnit)c.parse(fobjects.iterator().next()));
//        if (name.endsWith(".java")) jcu.specsCompilationUnit = jcu;
//        return jcu;
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#parseExpression(java.lang.CharSequence, boolean)
//     */
//    @Override
//    public JCExpression parseExpression(CharSequence text,boolean isJML) {
//        JmlCompiler.instance(context());
//        JmlParser p = ((com.sun.tools.javac.parser.JmlFactory)com.sun.tools.javac.parser.JmlFactory.instance(context())).newParser(text,true,true,true,isJML);
//        return p.parseExpression();
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#parseStatement(java.lang.CharSequence, boolean)
//     */
//    @Override
//    public JCStatement parseStatement(CharSequence text,boolean isJML) {
//        JmlCompiler.instance(context());
//        JmlParser p = ((com.sun.tools.javac.parser.JmlFactory)com.sun.tools.javac.parser.JmlFactory.instance(context())).newParser(text,true,true,true,isJML);
//        return p.parseStatement();
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#parseAndCheck(java.io.File)
//     */
//    @Override
//    public void parseAndCheck(File... files) throws java.io.IOException {
//        typecheck(parseFiles(files));
//    }
//
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#findSpecs(JmlCompilationUnit)
//     */
//    @Override public /*@nullable*/
//    JavaFileObject findSpecs(JmlCompilationUnit jmlcu) {
//        return JmlSpecs.instance(context()).findSpecs(jmlcu,true);
//    }
//
//
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#attachSpecs(JmlCompilationUnit,JmlCompilationUnit)
//     */
//    @Override
//    public void attachSpecs(JmlCompilationUnit javaSource, JmlCompilationUnit specsSource) {
//        javaSource.specsCompilationUnit = specsSource == null ? javaSource: specsSource;
//    }
//    
//
//    /** Creates a JavaFileObject instance from a pseudo filename and given content
//     * @param name the name to give the 'file'
//     * @param content the content to give the file
//     * @return the resulting JavaFileObject
//     */
//    @Override
//    public JavaFileObject makeJFOfromString(String name, String content) throws Exception {
//        return new StringJavaFileObject(name,content);
//    }
//    
//    /** Creates a JavaFileObject instance from a real file, by name
//     * @param filepath the path to the file, either absolute or relative to the current working directory
//     * @return the resulting JavaFileObject
//     */
//    @Override
//    public JavaFileObject makeJFOfromFilename(String filepath) {
////        JavacFileManager dfm = (JavacFileManager)context().get(JavaFileManager.class);
////        return dfm.getFileForInput(filepath);
//    	return null; // FIXME
//    }
//    
//    /** Creates a JavaFileObject instance from a File object
//     * @param file the file to wrap
//     * @return the resulting JavaFileObject
//     */
//    @Override
//    public JavaFileObject makeJFOfromFile(File file) {
////        JavacFileManager dfm = (JavacFileManager)context().get(JavaFileManager.class);
////        return dfm.getJavaFileForInput(file);
//    	return null; // FIXME
//    }
//    
//    // TODO: need an easier way to find out if there are errors from parseAndCheck or enterAndCheck
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getPackageSymbol(java.lang.String)
//     */
//    @Override
//    public /*@nullable*/ PackageSymbol getPackageSymbol(/*@non_null*/ String qualifiedName) {
////        Name n = Names.instance(context()).fromString(qualifiedName);
////        return Symtab.instance(context()).packages.get(n);
//    	return null; // FIXME
//    }
//
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getClassSymbol(java.lang.String)
//     */
//    //@ requires isOpen;
//    //@ ensures isOpen;
//    @Override
//    public /*@nullable*/ ClassSymbol getClassSymbol(/*@non_null*/ String qualifiedName) {
////        Name n = Names.instance(context()).fromString(qualifiedName);
////        return Symtab.instance(context()).classes.get(n);
//    	return null; // FIXME
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getClassSymbol(com.sun.tools.javac.code.Symbol.ClassSymbol, java.lang.String)
//     */
//    @Override
//    public /*@nullable*/ ClassSymbol getClassSymbol(/*@non_null*/ ClassSymbol csym, /*@non_null*/ String name) {
//        var it = csym.members().getSymbolsByName(Names.instance(context()).fromString(name));
//        for (Symbol sym: it) {
//            if (sym instanceof ClassSymbol) return (ClassSymbol)sym;
//        }
//        return null;
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getMethodSymbol(com.sun.tools.javac.code.Symbol.ClassSymbol, java.lang.String)
//     */
//    @Override
//    public /*@nullable*/ MethodSymbol getMethodSymbol(/*@non_null*/ ClassSymbol csym, /*@non_null*/ String name) {
//        var it = csym.members().getSymbolsByName(Names.instance(context()).fromString(name));
//        for (Symbol sym: it) {
//            if (sym instanceof MethodSymbol) return (MethodSymbol)sym;
//        }
//        return null;
//    } // FIXME - need a way to handle multiple methods with the same name
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getVarSymbol(com.sun.tools.javac.code.Symbol.ClassSymbol, java.lang.String)
//     */
//    @Override
//    public /*@nullable*/ VarSymbol getVarSymbol(/*@non_null*/ ClassSymbol csym, /*@non_null*/ String name) {
//        var it = csym.members().getSymbolsByName(Names.instance(context()).fromString(name));
//        for (Symbol sym: it) {
//            if (sym instanceof VarSymbol) return (VarSymbol)sym;
//        }
//        return null;
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getSymbol(org.jmlspecs.openjml.JmlTree.JmlClassDecl)
//     */
//    @Override
//    public /*@nullable*/ ClassSymbol getSymbol(/*@non_null*/ JmlClassDecl decl) {
//        return decl.sym;
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getSymbol(org.jmlspecs.openjml.JmlTree.JmlMethodDecl)
//     */
//    @Override
//    public /*@nullable*/ MethodSymbol getSymbol(/*@non_null*/ JmlMethodDecl decl) {
//        return decl.sym;
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getSymbol(org.jmlspecs.openjml.JmlTree.JmlVariableDecl)
//     */
//    @Override
//    public /*@nullable*/ VarSymbol getSymbol(/*@non_null*/ JmlVariableDecl decl) {
//        return decl.sym;
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getClassDecl(java.lang.String)
//     */
//    //@ requires isOpen;
//    //@ ensures isOpen;
//    @Override
//    public /*@non_null*/ JmlClassDecl getClassDecl(/*@non_null*/ String qualifiedName) {
//        return getClassDecl(getClassSymbol(qualifiedName));
//    }
//        
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getClassDecl(com.sun.tools.javac.code.Symbol.ClassSymbol)
//     */
//    //@ requires isOpen;
//    //@ ensures isOpen;
//    @Override
//    public JmlClassDecl getClassDecl(ClassSymbol csym) {
//        JCTree tree = JmlEnter.instance(context()).getClassEnv(csym).tree;
//        return (JmlClassDecl)tree;
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getMethodDecl(com.sun.tools.javac.code.Symbol.MethodSymbol)
//     */
//    //@ requires isOpen;
//    //@ ensures isOpen;
//    @Override
//    public /*@nullable*/ JmlMethodDecl getMethodDecl(MethodSymbol msym) {
//        JmlClassDecl cdecl = getClassDecl((ClassSymbol)msym.owner);
//        for (JCTree t: cdecl.defs) {
//            if (t instanceof JmlMethodDecl && ((JmlMethodDecl)t).sym == msym) {
//                return (JmlMethodDecl)t;
//            }
//        }
//        return null;
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getVarDecl(com.sun.tools.javac.code.Symbol.VarSymbol)
//     */
//    //@ requires isOpen;
//    //@ ensures isOpen;
//    @Override
//    public /*@nullable*/ JmlVariableDecl getVarDecl(VarSymbol vsym) {
//        JmlClassDecl cdecl = getClassDecl((ClassSymbol)vsym.owner);
//        for (JCTree t: cdecl.defs) {
//            if (t instanceof JmlVariableDecl && ((JmlVariableDecl)t).sym == vsym) {
//                return (JmlVariableDecl)t;
//            }
//        }
//        return null;
//    }
//    
//    
//    /** A cached object to search parse trees (not thread safe since it is static) */
//    static protected Finder finder = new Finder();
//    
//    /** A class that searches parse trees for nodes with a given position range.
//     * This class presumes that the AST nodes have start and end position information
//     * for which (a) each node has an end position at or after the start position,
//     * (b) sibling nodes have disjoint position ranges, ordered in the order the
//     * nodes are visited, and (c) a node's range includes the ranges of its
//     * children. This condition is true of a AST produced by parsing, but is
//     * not necessarily true of an AST produced by translation or other AST edits. */
//    public static class Finder extends JmlTreeScanner {
//    	public Finder() { super(null); }
//    	
//        /** Find the node within the given tree that encompasses the given
//         * start and end position.
//         * @param tree the root of the tree
//         * @param startpos the starting char position (from begining of file)
//         * @param endpos the ending position
//         * @return the best matching node
//         */
//        public JCTree find(JmlCompilationUnit tree, int startpos, int endpos) {
//            this.startpos = startpos;
//            this.endpos = endpos;
//            this.tree = tree;
//            this.scanMode = AST_JML_MODE;
//            scan(tree);
//            return found;
//        }
//        
//        int startpos;
//        int endpos;
//        JmlCompilationUnit tree;
//        public JCTree found = null;
//        public JmlMethodDecl parentMethod = null;
//        
//        /** Called for each node as the tree is visited - do not call directly - use find() */
//        public void scan(JCTree node) {
//            if (node == null) return;
//            int sp = node.getStartPosition();
//            if (sp == Position.NOPOS && node instanceof JmlMethodInvocation) sp = ((JmlMethodInvocation)node).pos;
//            int ep = node.getEndPosition(tree.endPositions);
//            // Do this specially because the range of a MethodDecl node does not include the specs
//            if (node instanceof JmlMethodDecl) {
//                JCTree ftree = found;
//                super.scan(node);
//                if (found != ftree) parentMethod = (JmlMethodDecl)node;
//            } else if (node instanceof JmlVariableDecl) {
//                JCTree ftree = found;
//                super.scan(node);
//                if (found == ftree && sp <= startpos && endpos <= ep) {
//                    found = node;
//                }
//            } else if (sp <= startpos && endpos <= ep) {
//                found = node;
//                //System.out.println(startpos + " " + endpos + " " + sp + " " + ep + " " + node.getClass());
//                super.scan(node);  // Call this to scan child nodes
//            } // If the desired range is not within the node's range, we
//              // don't even process the children
//        }
//    }
//
//    /** Finds the minimal (lowest) node in the AST that includes the given character position range
//     * @param tree the compilation unit to search (must have endPositions set)
//     * @param startpos the starting character position
//     * @param endpos the ending character position
//     * @return the node identified
//     */
//    protected JCTree findNode(JmlCompilationUnit tree, int startpos, int endpos) {
//        return finder.find(tree,startpos,endpos);
//    }
//    
////    /** The method on which ESC was run most recently */
////    protected MethodSymbol mostRecentProofMethod = null;
////    
////    protected BasicProgram mostRecentProgram = null; // FIXME - document; perhaps get rid of, and mostRecentProofMethod
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getCEValue(int, int, java.lang.String, java.lang.String)
//     */
//    @Override  // TODO: REVIEW THIS - get the info through the IProverResult
//    public String getCEValue(int pos, int end, String text, String fileLocation) {
////        fileLocation = fileLocation.replace('\\','/');
//////        if (mostRecentProofMethod == null) {
//////            return "No proof in which to evaluate the selection";
//////        }
////        JmlCompilationUnit tree = null; //(JmlCompilationUnit)Enter.instance(context()).getEnv((TypeSymbol)mostRecentProofMethod.owner).toplevel;
////        if (!tree.sourcefile.getName().replace('\\','/').equals(fileLocation)) {
////            //System.out.println("Did not match " + tree.sourcefile.toString());
////            boolean found = false;
////            {
////                JmlCompilationUnit stree = tree.specsCompilationUnit;
////                if (stree.sourcefile.getName().replace('\\','/').equals(fileLocation)) {
////                    tree = stree;
////                    found = true;
////                }
////                //System.out.println("Did not match " + stree.sourcefile.toString());
////            }
////            if (!found) {
////                // TODO _ make a proper error to the right destination
////                System.out.println("No Match for " + tree.specsCompilationUnit.sourcefile.getName());
////            }
////        }
////        JCTree node = findNode(tree,pos,end);
////        JmlMethodDecl parentMethod = finder.parentMethod;
//////        if (parentMethod.sym != mostRecentProofMethod) {
//////            return "Selected text is not within the method of the most recent proof (which is " + mostRecentProofMethod + ")";
//////        }
////        String out;
////        if (node instanceof JmlVariableDecl) {
////            // This happens when we have selected a method parameter or the variable within a declaration
////            // continue
////            out = text == null ? null : ("Found declaration: " + ((JmlVariableDecl)node).name.toString() + "\n");
////        } else if (!(node instanceof JCTree.JCExpression)) {
////            return text == null ? null : ("Selected text is not an expression (" + node.getClass() + "): " + text);
////        } else {
////            if (text == null) out = node.toString().replace("<", "&lt;") + " <B>is</B> ";
////            else    out = "Found expression node: " + node.toString() + "\n";
////        }
////        
////        if (JmlEsc.mostRecentProofResult != null) {
////            String value = JmlEsc.mostRecentProofResult.counterexample().get(node);
////            if (value != null) {
////                if (text == null) out = out + value;
////                else out = out + "Value " + node.type + " : " + value;
////                if (node.type.tag == TypeTags.CHAR) {
////                    try {
////                        out = out + " ('" + (char)Integer.parseInt(value) + "')"; 
////                    } catch (NumberFormatException e) {
////                        // ignore
////                    }
////                }
////            }
////            else out = text == null ? null : (out + "Value is unknown (type " + node.type + ")");
////            return out;
////        }
//        return "No counterexample information available";
//        
//    }
//    @Override  // TODO: REVIEW THIS - get the info through the IProverResult
//    public Finder findMethod(JmlCompilationUnit tree, int pos, int end, String text, String fileLocation) {
//        fileLocation = fileLocation.replace('\\','/');
////        if (mostRecentProofMethod == null) {
////            return "No proof in which to evaluate the selection";
////        }
//        if (!tree.sourcefile.getName().replace('\\','/').equals(fileLocation)) {
//            //System.out.println("Did not match " + tree.sourcefile.toString());
//            boolean found = false;
//            {
//                JmlCompilationUnit stree = tree.specsCompilationUnit;
//                if (stree.sourcefile.getName().replace('\\','/').equals(fileLocation)) {
//                    tree = stree;
//                    found = true;
//                }
//                //System.out.println("Did not match " + stree.sourcefile.toString());
//            }
//            if (!found) {
//                // TODO _ make a proper error to the right destination
//                System.out.println("No Match for " + tree.specsCompilationUnit.sourcefile.getName());
//            }
//        }
//        JCTree node = findNode(tree,pos,end);
//        return finder;
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#doESC(com.sun.tools.javac.code.Symbol.MethodSymbol)
//     */
//    @Override
//    public IProverResult doESC(MethodSymbol msym) {
//        JmlMethodDecl decl = getMethodDecl(msym);
//        JmlEsc esc = JmlEsc.instance(context());
//        class L implements IProofResultListener { 
//        	public L(IProofResultListener chained) { this.chained = chained; }
//        	public IProofResultListener chained;
//        	public IProverResult result; 
//        	public void reportProofResult(MethodSymbol msym, IProverResult result) { 
//                if (result.result() == IProverResult.COMPLETED) return;
//                if (result.result() == IProverResult.RUNNING) return;
//        		this.result = result; 
//        		if (chained != null) chained.reportProofResult(msym, result);
//        	}
//        };
//        
//        IProofResultListener p = setProofResultListener(null);
//        L l = new L(p);
//        setProofResultListener(l);
//        esc.check(decl);
//        setProofResultListener(p);
//        return l.result; 
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#doESC(com.sun.tools.javac.code.Symbol.ClassSymbol)
//     */
//    @Override
//    public void doESC(ClassSymbol csym) {
//        //if (!isTypechecked(csym)) typecheck(csym);
////        mostRecentProofMethod = null;
////        mostRecentProgram = null;
//        JmlClassDecl decl = getClassDecl(csym);
//        JmlEsc.instance(context()).check(decl);
//    }
//    
////    /* (non-Javadoc)
////     * @see org.jmlspecs.openjml.IAPI#getProofResult(com.sun.tools.javac.code.Symbol.MethodSymbol)
////     */
////    //@ requires isOpen;
////    //@ ensures isOpen;
////    @Override
////    public /*@nullable*/ IProverResult getProofResult(MethodSymbol msym) {
////        return JmlEsc.instance(context()).proverResults.get(msym);
////    }
////    
////    @Override
////    public /*@nullable*/ Map<MethodSymbol,IProverResult> getProofResults() {
////        return JmlEsc.instance(context()).proverResults;
////    }
//    
//    // TODO - move these two methods to Utils?
//    /** Adds the given class and all its supertypes (recursively) to the given list,
//     * ordered with parent classes first.
//     * @param csym the class or interface in question
//     * @param list the list to add to
//     */
//    //@ requires isOpen;
//    //@ ensures isOpen;
//    protected void collectSuperTypes(/*@non_null*/ ClassSymbol csym, java.util.List<ClassSymbol> list) {
//        Type tt = csym.getSuperclass();
//        if (tt != null && tt != Type.noType) {
//            ClassSymbol s = (ClassSymbol)tt.tsym;  // super classes are always ClassSymbols
//            collectSuperTypes(s,list);
//        }
//        for (Type t: csym.getInterfaces()) {
//            ClassSymbol c = (ClassSymbol)t.tsym; // interfaces are ClassSymbols
//            if (!list.contains(c)) {
//                collectSuperTypes(c,list);  // c and any super interfaces are added here
//            }
//        }
//        list.add(csym);
//    }
//    
//    /** Adds the method and all the methods it overrides (in classes or interfaces)
//     * to the given list
//     * @param msym the method in question
//     * @param list the list to add the methods to
//     */
//    //@ requires isOpen;
//    //@ ensures isOpen;
//    protected void collectSuperMethods(/*@non_null*/ MethodSymbol msym, java.util.List<MethodSymbol> list) {
//        java.util.List<ClassSymbol> clist = new ArrayList<ClassSymbol>();
//        collectSuperTypes(msym.enclClass(),clist);
//        for (ClassSymbol c: clist) {
//            // find a method matching msym in c
//            var it = c.members().getSymbolsByName(msym.getSimpleName());
//            for (Symbol sym: it) {
//                if (!(sym instanceof MethodSymbol)) continue;
//                MethodSymbol mmsym = (MethodSymbol)sym;
//                if (!msym.overrides(mmsym,msym.enclClass(),Types.instance(context()),false)) continue;
//                list.add(mmsym);
//                break;
//            } // FIXME - there must be a utility somewhere that does this already
//        }
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getSpecs(com.sun.tools.javac.code.Symbol.ClassSymbol)
//     */
//    @Override
//    public /*@non_null*/ TypeSpecs getSpecs(/*@non_null*/ ClassSymbol sym) {
//        return JmlSpecs.instance(context()).getAttrSpecs(sym);
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getAllSpecs(com.sun.tools.javac.code.Symbol.ClassSymbol)
//     */
//    @Override
//    public java.util.List<TypeSpecs> getAllSpecs(/*@non_null*/ ClassSymbol sym) {
//        java.util.List<ClassSymbol> list = new ArrayList<ClassSymbol>();
//        collectSuperTypes(sym,list);
//        JmlSpecs specs = JmlSpecs.instance(context());
//        java.util.List<TypeSpecs> tslist = new ArrayList<TypeSpecs>(list.size());
//        for (ClassSymbol c: list) tslist.add(specs.getAttrSpecs(c));
//        return tslist;
//    }
//
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getSpecs(com.sun.tools.javac.code.Symbol.MethodSymbol)
//     */
//    @Override
//    public /*@ non_null */ JmlSpecs.MethodSpecs getSpecs(/*@non_null*/ MethodSymbol sym) {
//        return JmlSpecs.instance(context()).getAttrSpecs(sym);
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getAllSpecs(com.sun.tools.javac.code.Symbol.MethodSymbol)
//     */
//    @Override
//    public java.util.List<JmlSpecs.MethodSpecs> getAllSpecs(/*@non_null*/ MethodSymbol msym) {
//        java.util.ArrayList<JmlSpecs.MethodSpecs> tslist = new ArrayList<JmlSpecs.MethodSpecs>();
//        if (msym.isStatic() || msym.isConstructor()) {
//            tslist.add(getSpecs(msym));
//            return tslist;
//        }
//        java.util.List<MethodSymbol> list = new ArrayList<MethodSymbol>();
//        collectSuperMethods(msym,list);
//        tslist.ensureCapacity(list.size());
//        JmlSpecs specs = JmlSpecs.instance(context());
//        for (MethodSymbol c: list) tslist.add(specs.getAttrSpecs(c));
//        return tslist;
//    }
//    
//    // FIXME - should this be inherited specs; what about parameter name renaming?
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getDenestedSpecs(com.sun.tools.javac.code.Symbol.MethodSymbol)
//     */
//    @Override
//    public /*@ nullable*/ JmlMethodSpecs getDenestedSpecs(/*@non_null*/ MethodSymbol sym) {
//        return JmlSpecs.instance(context()).getDenestedSpecs(sym);
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#getSpecs(com.sun.tools.javac.code.Symbol.VarSymbol)
//     */
//    @Override
//    public /*@non_null*/ FieldSpecs getSpecs(/*@non_null*/ VarSymbol sym) {
//        return JmlSpecs.instance(context()).getAttrSpecs(sym);
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#nodeFactory()
//     */
//    //@ requires isOpen;
//    //@ ensures isOpen;
//    @Override
//    public /*@ non_null */ JmlTree.Maker nodeFactory() {
//        JmlAttr.instance(context());  // Avoids circular tool registration problems
//        return JmlTree.Maker.instance(context());
//    }
//    
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#prettyPrint(com.sun.tools.javac.tree.JCTree)
//     */ // FIXME - allow the option of showing composite specs?
//    @Override
//    public /*@non_null*/ String prettyPrint(/*@non_null*/ JCTree ast) throws java.io.IOException {
//        StringWriter s = new StringWriter();
//        Pretty p = JmlPretty.instance(s,true);
//        if (ast instanceof JCTree.JCExpressionStatement) p.printStat(ast);
//        else ast.accept(p);
//        return s.toString();
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#prettyPrintJML(com.sun.tools.javac.tree.JCTree)
//     */
//    @Override
//    public /*@non_null*/ String prettyPrintJML(/*@non_null*/ JCTree ast) throws java.io.IOException {
//        StringWriter s = new StringWriter();
//        Pretty p = JmlPretty.instance(s,false);
//        if (ast instanceof JCTree.JCExpressionStatement) p.printStat(ast);
//        else ast.accept(p);
//        return s.toString();
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#prettyPrint(java.util.List, boolean, java.lang.String)
//     */
//    //@ requires isOpen;
//    //@ ensures isOpen;
//    @Override
//    public /*@non_null*/ String prettyPrint(/*@ non_null */ java.util.List<? extends JCTree> astlist, /*@non_null*/ String sep) throws java.io.IOException {
//        StringWriter s = new StringWriter();
//        boolean isFirst = true;
//        for (JCTree ast: astlist) {
//            if (!isFirst) { s.append(sep); } else { isFirst = false; }
//            JmlPretty.instance(s,true).print(ast);
//        }
//        return s.toString();
//    }
//    
//    /* (non-Javadoc)
//     * @see org.jmlspecs.openjml.IAPI#close()
//     */
//    //@ requires isOpen;
//    //@ assignable isOpen;
//    //@ ensures !isOpen;
//    @Override
//    public void close() {
//        JmlCompiler.instance(context()).close();
//        main.context = null;
//        main = null;
//    }
//    
//    /** This class encapsulates a String as a JavaFileObject, making it a pseudo-file
//     */
//    protected static class StringJavaFileObject extends SimpleJavaFileObject {
//        
//        /** The content of the mock file */
//        //@ non_null
//        protected String content;
//        
//        /** A fake file name, used when the user does not want to be bothered
//         * supplying one.  We have to make and cache this because it is a pain to
//         * deal with exceptions in constructors.
//         */
//        //@ non_null
//        static final protected URI uritest = makeURI();
//        
//        /** A utility method to make the URI, so it can handle the exceptions. 
//         * We don't try to recover gracefully if the exception occurs - this is
//         * just used in testing anyway. */
//        private static URI makeURI() {
//            try {
//                return new URI("file:///TEST.java");
//            } catch (Exception e) {
//                System.err.println("CATASTROPHIC EXIT - FAILED TO CONSTRUCT A MOCK URI");
//                System.exit(3);
//                return null;
//            }
//        }
//
//
//        /** Constructs a new JavaFileObject of kind SOURCE or OTHER depending on the
//         * filename extension
//         * @param filename the filename to use (no leading slash) (null indicates to
//         *          use the internal fabricated filename)
//         * @param content the content of the pseudo file
//         * @throws Exception if a URI cannot be created
//         */ // FIXME - sort out the package part of the path
//        public StringJavaFileObject(/*@ nullable */String filename, /*@ non_null */String content) throws Exception {
//            // This takes three slashes because the filename is supposed to be absolute.
//            // In our case this is not a real file anyway, so we pretend it is absolute.
//            super(filename == null ? uritest : new URI("file:///" + filename),
//                    filename == null || filename.endsWith(Strings.javaSuffix) ? Kind.SOURCE : Kind.OTHER);
//            this.content = content;
//        }
//
//        /** Overrides the parent to provide the content directly from the String
//         * supplied at construction, rather than reading the file.  This is called
//         * by the system.
//         */
//        @Override
//        public CharSequence getCharContent(boolean ignoreEncodingErrors) {
//            return content;
//        }
//        
//        /** Overrides the parent method to allow name compatibility between 
//         * pseudo files of different kinds.
//         */
//        // Don't worry about whether the kinds match, just the file extension
//        @Override
//        public boolean isNameCompatible(String simpleName, Kind kind) {
//            String s = uri.getPath();
//            if (kind == Kind.OTHER) {
//                int i = s.lastIndexOf('/');
//                s = s.substring(i+1);
//                return s.startsWith(simpleName);
//            } else {
//                String baseName = simpleName + kind.extension;
//                return s.endsWith("/" + baseName);
//            }
//        }
//        
//        /** Returns true if the receiver and argument are the same object */
//        @Override
//        public boolean equals(Object o) {
//            return o == this;
//        }
//        
//        /** A definition of hashCode, since we have a definition of equals */
//        @Override
//        public int hashCode() {
//            return super.hashCode();
//        }
//    }
}
