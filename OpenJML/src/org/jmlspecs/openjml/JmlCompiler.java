package org.jmlspecs.openjml;

import java.util.HashSet;
import java.util.Set;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.esc.JmlEsc;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.comp.JmlMemberEnter;
import com.sun.tools.javac.comp.JmlRac;
import com.sun.tools.javac.main.JavaCompiler;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeScanner;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Pair;

/** This class extends the JavaCompiler class in order to find and parse
 * specification files when a java source file is parsed.
 * @author David Cok
 *
 */
public class JmlCompiler extends JavaCompiler {


    public static void preRegister(final Context context) {
        context.put(compilerKey, new Context.Factory<JavaCompiler>() {
            public JmlCompiler make() {
                return new JmlCompiler(context);  // registers itself
            }
        });
    }
    
    /** The compilation context for this tool */
    protected Context context;

    /** A cached value indicating the verbosity level of tracing information. */
    boolean verbose;

    
    /** A constructor for this tool, but do not use it directly - use instance()
     * instead to get a unique instance of this class for the context.
     * @param context the compilation context for which this instance is being created
     */
    public JmlCompiler(Context context) {
        super(context);
        this.context = context;
        this.verbose = JmlOptionName.isOption(context,"-verbose") ||
                        JmlOptionName.isOption(context,JmlOptionName.JMLVERBOSE) || 
                        Utils.jmldebug;
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
     * of specification files.
     * <P>
     * If inSequence is false, then this method parses the given content and associated specs
     * If inSequence is true, then this method parses just the given content
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
    public java.util.List<JmlCompilationUnit> parseSpecs(/*@ nullable*/JmlCompilationUnit javaCU, /*@ nullable*/String pack, String file) {
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
    
    /** Initiates the actual parsing of the refinement chain
     * @param f the file object to parse
     * @param javaCU the compilation unit that provoked this parsing, if any
     * @return the possibly empty list of parsed compilation units, as ASTs
     */
    //@ non_null
    public java.util.List<JmlCompilationUnit> parseSpecs(JavaFileObject f, /*@ nullable*/JmlCompilationUnit javaCU) {
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
            JCTree.JCExpression e = jmlcu.getPackageName();
            if (jmlcu.refinesClause == null) break;
            String file = jmlcu.refinesClause.filename;
            String pack = e == null ? null : e.toString();
            String fullname = pack == null ? file : (pack.replace('.','/') + "/" + file);
            f = JmlSpecs.instance(context).findSpecFile(fullname);
        }
        inSequence = false;
        return list;
    }
    
    private int nestingLevel = 0;

    public void loadSpecsForBinary(ClassSymbol csymbol) {
        if (JmlSpecs.instance(context).get(csymbol) != null) return;
        nestingLevel++;
        java.util.List<JmlCompilationUnit> specSequence = parseSpecs(csymbol);
        for (JmlCompilationUnit cu: specSequence) {
            if (cu.sourcefile.toString().endsWith(".java")) cu.mode = JmlCompilationUnit.JAVA_AS_SPEC_FOR_BINARY;
            else cu.mode = JmlCompilationUnit.SPEC_FOR_BINARY;
        }
        if (Utils.jmldebug) if (specSequence == null) System.out.println("   LOADED CLASS " + csymbol + " FOUND NO SPECS");
                            else System.out.println("   LOADED CLASS " + csymbol + " PARSED SPECS");
        ((JmlEnter)enter).enterTopLevelSpecClassesForBinary(csymbol,specSequence);
        loadSuperSpecs(csymbol);
        if (Utils.jmldebug) System.out.println("NEST " + nestingLevel + " " + csymbol);
        if (nestingLevel==1) ((JmlMemberEnter)JmlMemberEnter.instance(context)).completeBinaryTodo();
        nestingLevel--;
     }
    
    public void loadSuperSpecs(ClassSymbol csymbol) {
        Type t = csymbol.getSuperclass();
        if (t != null && t.tsym != null) {
            loadSpecsForBinary((ClassSymbol)t.tsym);
        }
        for (Type tt: csymbol.getInterfaces()) {
            loadSpecsForBinary((ClassSymbol)tt.tsym);
        }
    }
    
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

    /** Overridden to stop the processing at this point - no code generation unless rac is enabled */
    @Override
    protected void desugar(Env<AttrContext> env, ListBuffer<Pair<Env<AttrContext>, JCClassDecl>> results) {
        // Note super.desugar() translates generic Java to non-generic Java and perhaps does other stuff.
        // TODO - decide whether this should be executed before doing ESC or RAC
        if (JmlOptionName.isOption(context,JmlOptionName.ESC)) {
            esc(env);
        }
        if (JmlOptionName.isOption(context,JmlOptionName.RAC)) {
            JCTree t = env.tree;
            env = rac(env);
            if (env == null) return;
            if (verbose) System.out.println("desugaring " + errorCount() + " " + 
                    (t instanceof JCTree.JCCompilationUnit ? ((JCTree.JCCompilationUnit)t).sourcefile:
                        t instanceof JCTree.JCClassDecl ? ((JCTree.JCClassDecl)t).name : t.getClass()));

            super.desugar(env,results);
        }
    }

    public Env<AttrContext> attribute(Env<AttrContext> env) {
        int n = todo.size();
        while ((--n) >= 0) {
            if (compilePolicy != CompilePolicy.BY_TODO) break;
            if (!desugarLater(env)) break;
//            System.out.println("deferring " + Utils.envString(env)
//                    + " for " + (savedSupers.iterator().next()));
            todo.append(env);
            env = todo.next();
        }
        return super.attribute(env);
    }
    
    public boolean desugarLater(final Env<AttrContext> env) {
        if (compilePolicy == CompilePolicy.BY_FILE)
            return false;
//        if (!devVerbose && deferredSugar.contains(env))
//            // guarantee that compiler terminates
//            return false;
        class ScanNested extends TreeScanner {
            Set<Symbol> externalSupers = new HashSet<Symbol>();
            public void visitClassDef(JCClassDecl node) {
                if (node.sym != null) { // node.sym==null for unattributed anonymous classes
                    Type st = types.supertype(node.sym.type);
                    if (st.tag == TypeTags.CLASS) {
                        ClassSymbol c = st.tsym.outermostClass();
                        Env<AttrContext> stEnv = enter.getEnv(c);
                        if (stEnv != null && env != stEnv)
                            externalSupers.add(st.tsym);
                    }
                }
                super.visitClassDef(node);
            }
        }
        ScanNested scanner = new ScanNested();
        scanner.scan(env.tree);
        if (scanner.externalSupers.isEmpty())
            return false;
//        if (!deferredSugar.add(env) && devVerbose) {
//            throw new AssertionError(env.enclClass.sym + " was deferred, " +
//                                     "second time has these external super types " +
//                                     scanner.externalSupers);
//        }
        savedSupers = scanner.externalSupers;
        return true;
    }
    
    Set<Symbol> savedSupers = null;

    
    /** Overridden to stop the processing at this point - no code generation unless rac is enabled */
    @Override
    public List<Pair<Env<AttrContext>, JCClassDecl>> desugar(List<Env<AttrContext>> envs) {
        if (JmlOptionName.isOption(context,JmlOptionName.RAC) ||
                JmlOptionName.isOption(context,JmlOptionName.ESC)) {
            return super.desugar(envs);
        }
        return List.<Pair<Env<AttrContext>, JCClassDecl>>nil();
    }
    
    @Override
    protected void flow(Env<AttrContext> env, ListBuffer<Env<AttrContext>> results) {
        JCTree t = env.tree;
        if (verbose) System.out.println("flow checks " +  
                (t instanceof JCTree.JCCompilationUnit ? ((JCTree.JCCompilationUnit)t).sourcefile:
                    t instanceof JCTree.JCClassDecl ? ((JCTree.JCClassDecl)t).name : t.getClass()));
        super.flow(env,results);
    }

    protected Env<AttrContext> rac(Env<AttrContext> env) {
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
                System.out.println("UNKNOWN - rac");
            }
            return null;
        }
        // Note that if env.tree is a class, we translate just that class.  
        // We have to adjust the toplevel tree accordingly.  Presumably other
        // class declarations in the compilation unit will be translated on 
        // other calls.
        if (verbose) System.out.println("rac " + errorCount() + " " + Utils.envString(env));
        JmlRac rac = new JmlRac(context,env);  // FIXME - use a factory
        if (env.tree instanceof JCClassDecl) {
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
        //flow(env);  // FIXME - give a better explanation if this produces errors.
                // IF it does, it is because we have done the RAC translation wrong.
        return env;
    }
    
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
        // Note that if env.tree is a class, we translate just that class.  
        // Presumably other
        // class declarations in the compilation unit will be translated on 
        // other calls.
        if (true||verbose) System.out.println("esc " + Utils.envString(env));
        
        JmlEsc esc = new JmlEsc(context,env);  // FIXME - use a factory
        env.tree.accept(esc);
        //        if (env.tree instanceof JCClassDecl) {
//            esc.translate((JCClassDecl)env.tree);
//        } else {
//            esc.translate(env.toplevel);
//        }
        return;
    }
    

//    public int errorCount() {
//        return 0;
//    }
}
