package org.jmlspecs.openjml;

import java.io.IOException;

import javax.annotation.processing.Processor;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.esc.JmlEsc;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.comp.JmlRac;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Pair;

/**
 * This class extends the JavaCompiler class in order to find and parse
 * specification files when a Java source file is parsed.
 * 
 * @author David Cok
 */
public class JmlCompiler extends JavaCompiler {

    /** Registers a factory for producing parsers.  We use a fresh parser for
     * each file parsed.
     * @param context the compilation context used for tools
     */
    public static void preRegister(final Context context) {
        context.put(compilerKey, new Context.Factory<JavaCompiler>() {
            public JmlCompiler make() {
                return new JmlCompiler(context);  // registers itself
            }
        });
    }
    
    /** A cached value indicating the verbosity level of tracing information. */
    protected boolean verbose;

    /** Cached value of the class loader */
    protected JmlResolve resolver;
    
    /** A constructor for this tool, but do not use it directly - use instance()
     * instead to get a unique instance of this class for the context.
     * @param context the compilation context for which this instance is being created
     */
    protected JmlCompiler(Context context) {
        super(context);
        this.context = context;
        this.verbose = JmlOptionName.isOption(context,"-verbose") ||
                        JmlOptionName.isOption(context,JmlOptionName.JMLVERBOSE) || 
                        Utils.jmldebug;
        this.resolver = (JmlResolve)JmlResolve.instance(context);
    }
    
    /** A flag that controls whether to get specs during a parse or not (if false 
     * then do, if true then do not).  This should be left in a false state
     * after being used to preclude parsing specs.
     */
    boolean inSequence = false;
    
    /** This method is overridden in order to parse specification files along with parsing a Java file.  Note
     * that it is called directly from JavaCompiler.complete and JavaCompiler.parse to do the actual parsing.
     * Thus when parsing an individual file (such as a spec file) it is also called (through parse).  Consequently
     * we have to do this little trick with the "inSequence" field to avoid trying to parse the specifications
     * of specification files. [I'm not sure when, if ever, JavaCompiler.complete is called.  If it did not ever 
     * call this method here, we could override JavaCOmpiler.parse(JavaFileObject) instead, and avoid this
     * trickery with inSequence.]
     * <P>
     * <UL>
     * <LI>If inSequence is false, then this method parses the given content and associated specs.
     * <LI>If inSequence is true, then this method parses just the given content.
     * <LI>In either case a JmlCompilationUnit is returned.  The specsSequence field
     * contains a non-null, but possibly empty, list of the specification files for this class.
     * However, see the FIXME below regarding adding the .java file into an empty specs list.
     * </UL>
     */
    // TODO - when called from JavaCompiler.complete it seems that the end position information is not recorded
    // in the way that happens when called from JavaCompiler.parse.  Is this a problem in the Javac compiler?
    @Override
    public JCCompilationUnit parse(JavaFileObject filename, CharSequence content) {
        if (verbose) System.out.println("parsing " + filename.toUri().getPath());
        JCCompilationUnit cu = super.parse(filename,content);
        if (inSequence) {
            return cu;
        }
        if (cu instanceof JmlCompilationUnit) {
            JmlCompilationUnit jmlcu = (JmlCompilationUnit)cu;
            jmlcu.mode = JmlCompilationUnit.JAVA_SOURCE_FULL;
            JCTree.JCExpression e = jmlcu.getPackageName();
            // In the following, we need a name as the prefix to look for the specs.
            // That is supposed to be the same as the name of the public class within
            // the file, and thus the same as the name of the file itself.
            // However, a file may have no public classes within it - in which case 
            // the best indication of the spec file name is the name of the
            // java file just parsed.
            // FIXME - unfortunately, there is no guarantee as to what getName()
            // will return.  It would be safer, but a pain, to dismember the 
            // associated URI. (getName is even deprecated within some subclasses)
            jmlcu.specsSequence = parseSpecs(jmlcu,e == null ? null : e.toString(),jmlcu.getSourceFile().getName());
            if (jmlcu.specsSequence.size() == 0) {
                // If there are no specs, that means that not even the .java file is
                // on the specification path.  That may well be something to warn
                // about.  For now (and for the sake of the tests), we will be
                // helpful and add the .java file to the specs sequence despite it
                // not being on the specification path.
                // FIXME log.warning("jml.no.specs",filename.getName());
                java.util.List<JmlCompilationUnit> list = new java.util.LinkedList<JmlCompilationUnit>();
                list.add(jmlcu);
                jmlcu.specsSequence = list;
            } else {
                for (JmlCompilationUnit jcu: jmlcu.specsSequence) {
                    if (jcu != cu) jcu.mode = JmlCompilationUnit.SPEC_FOR_SOURCE;
                }
            }
        } else {
            log.error("jml.internal",
                    "JmlCompiler.parse expects to receive objects of type JmlCompilationUnit, but it found a " 
                    + cu.getClass() + " instead, for source " + cu.getSourceFile().toUri().getPath());
        }
        return cu;
    }
    
    /** Parses the entire refinement chain of  specification files
     * @param javaCU the Java compilation unit on whose behalf we are parsing specs, or null if none; this is supplied so that if
     * the Java file is part of the refinement sequence, the file is not parsed over again
     * @param pack a dot-separated path name for the package in which the class resides, or null for the default package
     * @param file the class name whose specs are being sought (without any suffix)
     * @return the possibly empty list of parsed compilation units, as ASTs
     */
    //@ non_null
    public java.util.List<JmlCompilationUnit> parseSpecs(/*@ nullable*/JmlCompilationUnit javaCU, /*@ nullable*/String pack, /*@ non_null */String file) {
        int i = file.lastIndexOf('/');
        int k = file.lastIndexOf(".");
        if (k >= 0) file = file.substring(i+1,k);
        JavaFileObject f = JmlSpecs.instance(context).findLeadingSpecFile(pack == null ? file : (pack + "." + file));
        return parseSpecs(f,javaCU);
    }

    /** Parses the entire refinement chain of  specification files
     * @param typeSymbol the symbol of the type whose specs are sought
     * @return the possibly empty list of parsed compilation units, as ASTs
     */
    //@ non_null
    public java.util.List<JmlCompilationUnit> parseSpecs(Symbol.TypeSymbol typeSymbol) {
        String typeName = typeSymbol.flatName().toString();
        String path = typeName.replace('.','/');
        JavaFileObject f = JmlSpecs.instance(context).findLeadingSpecFile(path);
        java.util.List<JmlCompilationUnit> list = parseSpecs(f,null);
        return list;
    }
    
    /** Initiates the actual parsing of the refinement chain.  Note that in the
     * end we want to consolidate the specs sequence into one declaration file
     * with all replicated declarations identified together and specifications
     * combined.  However, we cannot do that until we can do type matching, so
     * that has to wait until the enter phase is completed.
     * @param f the file object to parse, if any
     * @param javaCU the compilation unit that provoked this parsing, if any
     * @return the possibly empty list of parsed compilation units, as ASTs
     */
    //@ non_null
    public java.util.List<JmlCompilationUnit> parseSpecs(/*@ nullable*/JavaFileObject f, /*@ nullable*/JmlCompilationUnit javaCU) {
        inSequence = true;
        java.util.List<JmlCompilationUnit> list = new java.util.LinkedList<JmlCompilationUnit>();
        while (f != null) {
            JmlCompilationUnit jmlcu;
            // FIXME - this comparison is not robust, though is usually working
            // we use it to avoid parsing a file twice (which would also give
            // duplicate error messages)
            //System.out.println(f.toUri().normalize().getPath() + " VS " + javaCU.getSourceFile().toUri().normalize().getPath());
            if (javaCU != null && f.equals(javaCU.getSourceFile())) {
                if (Utils.jmldebug) System.out.println("REFOUND " + f);
                jmlcu = javaCU;
            } else {
                jmlcu = (JmlCompilationUnit)parse(f);
            }
            list.add(jmlcu);
            JCTree.JCExpression packTree = jmlcu.getPackageName();
            if (jmlcu.refinesClause == null) break;
            String file = jmlcu.refinesClause.filename;
            String fullname = packTree == null ? file : (packTree.toString().replace('.','/') + "/" + file);
            f = JmlSpecs.instance(context).findSpecFile(fullname);
        }
        inSequence = false;
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
        // This nesting level is used to be sure we queue up a whole set of 
        // classes, do their 'enter' processing to record any types before we
        // do their member processing to record all their members.  We need the
        // types recorded so that we can look up types for the members (e.g. do
        // method resolution).  This is the same two-phase processing as the
        // Java handling uses, we just don't use the same todo list.
        nestingLevel++;
        loadSuperSpecs(env,csymbol);
        java.util.List<JmlCompilationUnit> specSequence = parseSpecs(csymbol);
        if (verbose && specSequence.isEmpty()) System.out.println("No specs for " + csymbol);
        for (JmlCompilationUnit cu: specSequence) {
            if (cu.sourcefile.toString().endsWith(".java")) cu.mode = JmlCompilationUnit.JAVA_AS_SPEC_FOR_BINARY;
            else cu.mode = JmlCompilationUnit.SPEC_FOR_BINARY;
        }
        if (Utils.jmldebug) if (specSequence.isEmpty()) System.out.println("   LOADED CLASS " + csymbol + " FOUND NO SPECS");
                            else System.out.println("   LOADED CLASS " + csymbol + " PARSED SPECS");
        ((JmlEnter)enter).enterTopLevelSpecClassesForBinary(csymbol,specSequence);
        if (Utils.jmldebug) System.out.println("NEST " + nestingLevel + " " + csymbol);
        if (nestingLevel==1) ((JmlMemberEnter)JmlMemberEnter.instance(context)).completeBinaryTodo();
        nestingLevel--;
     }
    
    /** Makes sure that the super classes and interfaces of the given symbol
     * are loaded, including specs.
     * @param csymbol the class whose super types are wanted
     */
    public void loadSuperSpecs(Env<AttrContext> env, ClassSymbol csymbol) {
        // We have a ClassSymbol,
        // but they are not necessarily loaded, completed or have their
        // specs read
        Type t = csymbol.getSuperclass();
        if (t != null && t.tsym != null) {
            JmlResolve.instance(context).loadClass(env,((ClassSymbol)t.tsym).flatname);
        }
        for (Type tt: csymbol.getInterfaces()) {
            JmlResolve.instance(context).loadClass(env,((ClassSymbol)tt.tsym).flatname);
        }
    }
    
    /** Overridden in order to put out some information about stopping */
    protected  <T> List<T> stopIfError(List<T> list) {
        if (errorCount() != 0) {
            if (JmlOptionName.isOption(context,JmlOptionName.STOPIFERRORS)) {
                log.note("jml.stop");
                return List.<T>nil();
            } else {
                if (verbose) log.note("jml.continue");
            }
        }
        return list;
    }

    /** Overridden so that we do either (1) ESC or (2) RAC prep followed 
     * by desugaring and code generation.
     */
    protected void desugar(Env<AttrContext> env, ListBuffer<Pair<Env<AttrContext>, JCClassDecl>> results) {
        // Note super.desugar() translates generic Java to non-generic Java and perhaps does other stuff.
        if (JmlOptionName.isOption(context,JmlOptionName.ESC)) {
            esc(env);
            // nothing put in results, so no further compilation phases are performed
        }
        if (JmlOptionName.isOption(context,JmlOptionName.RAC)) {
            JCTree t = env.tree;
            env = rac(env);
            if (env == null) return;
            // Continue with the usual compilation phases
            if (verbose) System.out.println("desugar " + todo.size() + " " + 
                    (t instanceof JCTree.JCCompilationUnit ? ((JCTree.JCCompilationUnit)t).sourcefile:
                        t instanceof JCTree.JCClassDecl ? ((JCTree.JCClassDecl)t).name : t.getClass()));
            super.desugar(env,results);
        }
    }

    /** Initiates type attribution for the given class; overridden in order
     * 
     */
    public Env<AttrContext> attribute(Env<AttrContext> env) {
        // FIXME - I think this can go away.  Test some time.
//        int n = todo.size();
//        while ((--n) >= 0) {
//            if (compilePolicy != CompilePolicy.BY_TODO) break;
//            if (!desugarLater(env)) break;
////            System.out.println("deferring " + Utils.envString(env)
////                    + " for " + (savedSupers.iterator().next()));
//            todo.append(env);
//            env = todo.next();
//        }
        
        
//        System.out.println("ATTRIBUTE MODE " + ((JmlCompilationUnit)env.toplevel).mode + " " + env.enclClass.sym);
//        if (env.toplevel instanceof JmlCompilationUnit) {
//            int m = ((JmlCompilationUnit)env.toplevel).mode;
//            if ((m&JmlCompilationUnit.SPEC_FOR_BINARY)==JmlCompilationUnit.SPEC_FOR_BINARY) {
//                // need to attribute the binary
//            }
//        }
        return super.attribute(env);
    }
    
//    public boolean desugarLater(final Env<AttrContext> env) {
//        if (compilePolicy == CompilePolicy.BY_FILE)
//            return false;
////        if (!devVerbose && deferredSugar.contains(env))
////            // guarantee that compiler terminates
////            return false;
//        class ScanNested extends TreeScanner {
//            Set<Symbol> externalSupers = new HashSet<Symbol>();
//            public void visitClassDef(JCClassDecl node) {
//                if (node.sym != null) { // node.sym==null for unattributed anonymous classes
//                    Type st = types.supertype(node.sym.type);
//                    if (st.tag == TypeTags.CLASS) {
//                        ClassSymbol c = st.tsym.outermostClass();
//                        Env<AttrContext> stEnv = enter.getEnv(c);
//                        if (stEnv != null && env != stEnv)
//                            externalSupers.add(st.tsym);
//                    }
//                }
//                super.visitClassDef(node);
//            }
//        }
//        ScanNested scanner = new ScanNested();
//        scanner.scan(env.tree);
//        if (scanner.externalSupers.isEmpty())
//            return false;
////        if (!deferredSugar.add(env) && devVerbose) {
////            throw new AssertionError(env.enclClass.sym + " was deferred, " +
////                                     "second time has these external super types " +
////                                     scanner.externalSupers);
////        }
//        savedSupers = scanner.externalSupers;
//        return true;
//    }
//    
//    Set<Symbol> savedSupers = null;


//    /** Overridden just to put out tracking information in verbose mode */
//    @Override
//    protected void flow(Env<AttrContext> env, ListBuffer<Env<AttrContext>> results) {
//        JCTree t = env.tree;
//        if (verbose) System.out.println("flow checks " +  
//                (t instanceof JCTree.JCCompilationUnit ? ((JCTree.JCCompilationUnit)t).sourcefile:
//                    t instanceof JCTree.JCClassDecl ? ((JCTree.JCClassDecl)t).name : t.getClass()));
//        super.flow(env,results);
//    }
    
    int oldsize = -1;
    
    /** Does the RAC processing on the argument. */
    // FIXME - the argument is probably a class, not a CU; are we going to get
    // an env for each class if there are more than one in a CU?
    protected Env<AttrContext> rac(Env<AttrContext> env) {
        JCTree tree = env.tree;
        if (!JmlCompilationUnit.isJava(((JmlCompilationUnit)env.toplevel).mode)) {
            // TODO - explain why we remove these from the symbol tables
            if (env.tree instanceof JCClassDecl) {
                Symbol c = ((JCClassDecl)tree).sym;
                ((JmlEnter)enter).remove(c);
            } else if (env.tree instanceof JCCompilationUnit) {
                for (JCTree t : ((JCCompilationUnit)tree).defs) {
                    if (t instanceof JCClassDecl) ((JmlEnter)enter).remove(((JCClassDecl)t).sym);
                }
            } else {
                // This is a bug, but we can probably get by with just not instrumenting
                // whatever this is.
                log.warning("jml.internal.notsobad","Did not expect to encounter this option in JmlCompiler.rac: " + env.tree.getClass());
            }
            return null;
        }
        // Note that if env.tree is a class, we translate just that class.  
        // We have to adjust the toplevel tree accordingly.  Presumably other
        // class declarations in the compilation unit will be translated on 
        // other calls.
        if (verbose) System.out.println("rac " + todo.size() + " " + Utils.envString(env));
        JmlRac rac = new JmlRac(context,env);  // FIXME - use a factory
        if (env.tree instanceof JCClassDecl) {
            // When we do the RAC translation, we create a new instance
            // of the JCClassDecl for the class.  So we have to find where
            // it is kept in the JCCompilationUnit and replace it there.
            // If there is more than one class in the compilation unit, we are
            // presuming that each one that is to be translated will be 
            // separately called - so we just translate each one when it comes.
            List<JCTree> t = env.toplevel.defs;
            while (t.head != null) {
                if (t.head == env.tree) {
                    JCTree newtree = rac.translate(env.tree);
                    env.tree = newtree;
                    t.head = newtree;
                    break;
                }
                t = t.tail;
            }
        } else {
            env.toplevel = rac.translate(env.toplevel);
        }
//        System.out.println("TRANSLATED RAC");
//        System.out.println(env.tree);
        //flow(env);  // FIXME - give a better explanation if this produces errors.
                // IF it does, it is because we have done the RAC translation wrong.
        return env;
    }
    
    /** Does the ESC processing for the given class
     * 
     * @param env the env for a class
     */ // FIXME - check that we always get classes, not CUs and adjust the logic accordingly
    protected void esc(Env<AttrContext> env) {
        JCTree tree = env.tree;
        if (!JmlCompilationUnit.isJava(((JmlCompilationUnit)env.toplevel).mode)) {
            if (env.tree instanceof JCClassDecl) {
                Symbol c = ((JCClassDecl)tree).sym;
                ((JmlEnter)enter).remove(c);
            } else if (env.tree instanceof JCCompilationUnit) {
                for (JCTree t : ((JCCompilationUnit)tree).defs) {
                    if (t instanceof JCClassDecl) ((JmlEnter)enter).remove(((JCClassDecl)t).sym);
                }
            } else {
                // FIXME - unknown
                System.out.println("UNKNOWN - esc");
            }
            return;
        }
        
        JmlEsc esc = JmlEsc.instance(context);
        env.tree.accept(esc);

        return;
    }

    /** This overrides JavaCompiler.compile simply to load java.lang.Object
     * explicitly.  The parsing/entering logic will prompt for class or source
     * file loading of any class explicitly mentioned in the source files.  But
     * Object is the default super class and is not explicitly mentioned; though
     * it could, Enter and MemberEnter do not explicitly load it.  The class 
     * does get loaded at a later point.  As a result, the class is not put on
     * the todo list for attribution until after other classes.  This is not a
     * problem for Java because Object is a binary class and there is no source
     * code to a attribute.  However, for JML, the result is that the specs
     * for Object do not get attributed early enough.  We could fix this by
     * changing the logic in Enter to explicitly process a default super type;
     * however, it is easier (and less invasive) to simply force the class 
     * loading as the first thing that happens in the compilation.  It does have
     * the side-effect of processing all the classes referenced by Object's
     * specs before the parsing of command-line files begins.
     */
    public void compile(List<JavaFileObject> sourceFileObjects,
            List<String> classnames,
            Iterable<? extends Processor> processors) throws IOException {
        Runtime rt = Runtime.getRuntime();
        //System.out.println("    ....... Memory free=" + rt.freeMemory() + "  max="+rt.maxMemory() + "  total="+rt.totalMemory());
        JmlResolve.instance(context).loadClass(null,Symtab.instance(context).objectType.tsym.flatName());
        super.compile(sourceFileObjects,classnames,processors);
    }
    
    protected void compile2(CompilePolicy compPolicy) {
        super.compile2(CompilePolicy.SIMPLE);
    }
}
