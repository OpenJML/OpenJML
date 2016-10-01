/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.comp;


import java.util.Collection;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.code.Type.TypeVar;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;

/** 
 * This class extends Enter, which has the job of creating symbols for all the
 * types mentioned in a set of parse trees. JmlEnter adds to that functionality
 * to create symbols for all JML types (i.e., model classes) that are present in
 * the parse trees.  In addition it links each class declaration to declarations
 * containing that class's specifications.
 * <P>
 * JmlEnter expects that a compilation unit knows its specification files 
 * (via its specsCompilationUnit field). It
 * walks those specification files, matching classes in the specification file
 * to the corresponding classes in the Java file, making links from the Java
 * classes to their specifications.  JmlEnter also expects that the parse 
 * tree contains JmlClassDecl nodes instead of JCClassDecl nodes, even where
 * no additional specs are present.
 * <P>
 * Per the current version of JML, specifications for a .java file are taken from 
 * just one file (previously, the specifications were a combination of specifications
 * from a sequence of specification files). The one file may be the .java file containing
 * the Java definition of the class or it may be a different (e.g., .jml) file. The file used
 * is the one attached to the JmlCompilationUnit.specsCompilationUnit field (which may be
 * but is not necessarily the AST for the .java file itself).
 * <P>
 * Note that classes referenced in the set of compilation unit trees passed to Enter.main
 * are not processed until later (during MemberEnter or Attribution). If those classes
 * exist as .java files they will be parsed and their specifications attached as usual.
 * If the referenced classes are only binary, the specifications still need to be obtained
 * and attached to the class symbol.
 * <P>
 * The process of entering a CU does these things:
 * <UL>
 * <LI> packages are completed by entering all the classes in the package
 * <LI> classes: a class symbol is defined; a completer is attached to the symbol
 * <LI> type parameters: recorded in the Env associated with the class
 * <LI> initiates the MemberEnter processing, which adds the members of a class
 * to its Env (its scope); this can have the side-effect of uncovering more
 * classes that need to be loaded (by either parsing or finding the binary class)
 * and entered.
 * </UL>
 * Also typeEnvs is a map that gives an Env<AttrContext> object for each class,
 * to be used when attributing types and resolving references within the class.
 * The enter process creates and stores this Env.  JmlEnter does the same for
 * model classes and for the specifications corresponding to binary classes.
 * 
 * @author David Cok
 */
/* FIXME - REVIEW THE FOLLOWING
 * Relationships that need to be set up (for binary classes as well)
 *   class symbol:          ClassSymbol csym
 *   class environment :    Env<AttrContext> classenv
 *   class specs:           TypeSpecs cspecs
 *   class declaration:     JmlClassDecl cdecl
 *   
 *   classenv = getEnv(csym) ; classenv created by classEnv(cdecl, topLevelEnv)
 *   csym = cdecl.sym
 *   cspecs = specs.get(csym)
 *   
 *   cdecl.typeSpecsCombined = cspecs (only for Java declaration)
 *   cdecl.typeSpecs = specifications from this cdecl only, not combined [Set by filterTypeBodyDeclarations() ]
 *   cdecl.toplevel = not reliably set ??? FIXME
 *   cdecl.sourcefile = toplevel.sourcefile    [ Set by JmlParser ]
 *   cdecl.specsDecls = list of JmlClassDecls, including cdecl if class is binary [ Set in JmlEnter, during matching of specs to class symbols ]
 *   cdecl.sym = csym [For Java files, assigned when class dfinition is entered;
 *                      for binary files, assigned in JmlEnter during matching of specs to class symbols ]
 *   
 *   cspecs.refiningSpecDecls = list of specifications declarations
 *   cspecs.csymbol = csym
 *   cspecs.file = file for Java declaration; if binary, file for most refined specs file (can be used for modifiers)
 *   cspecs.decl = decl for Java declaration; if binary, decl for most refined specs file
 *   cspecs.modifiers = accumulated modifiers, so from most refined specs file, else from symbol
 *   [ JmlParser sets up the individual cdecl.sourcefile, cdecl.typeSpecs field
 *       and the cdecl.typeSpecs.modifiers, file, decl fields ]
 *   
 *   csym.sourcefile = file for Java declaration; if binary, file for most refined specs file (or null?)
 */
public class JmlEnter extends Enter {

    /** This registers a factory so that we do not have to prematurely
     * create an instance of Enter, but the factory only produces a singleton
     * instance per context.
     * @param context the context in which to register
     */
    public static void preRegister(final Context context) {
        context.put(enterKey, new Context.Factory<Enter>() {
            Enter instance = null;
            public Enter make(Context context) {
                return instance != null ? instance 
                        : (instance = new JmlEnter(context));
            }
        });
    }

    /** The context in which this instance was created. */
    @NonNull
    final protected Context context;

    /** A cached value of the specs tool for this compilation context */
    @NonNull
    final protected JmlSpecs specs;
    
    /** A cached value of the Utils tool */
    @NonNull
    final protected Utils utils;

    // FIXME _ document - do we need this?
    public ListBuffer<JmlCompilationUnit> binaryEnvs = new ListBuffer<JmlCompilationUnit>();
    
    /** Creates an instance of the JmlEnter tool in the given context; note that
     * any options must be already set in Options prior to creating the tool.
     * @param context the compilation context to use for this tool
     */
    //@ assignable this.*;
    public JmlEnter(Context context) {
        super(context); // automatically registers the new object
        this.context = context;
        this.utils = Utils.instance(context);
        this.specs = JmlSpecs.instance(context);
    }
    
    /** The env (scope) to be used within specifications corresponding to the env for Java, as passed internally
     * from visitTopLevel to classEnter.
     */
    private Env<AttrContext> specTopEnv;
    
    /** This method visits the designated compilation unit; first it matches
     * class declarations in the specification files to class declarations in
     * Java; then it calls the super class visitTopLevel method to initiate
     * walking the tree; overriding methods in JmlEnter will be called when visiting
     * class declarations, so that a class can register in the symbol table
     * any model classes that are declared within it.  As classes are visited,
     * the specs for that class are extracted from the specification sequence
     * and attached to the class.  We also take care of secondary top-level 
     * class declarations and top-level model declarations.
     */
    public void visitTopLevel(JCCompilationUnit tree) {
        if (!(tree instanceof JmlCompilationUnit)) {
            log.warning("jml.internal.notsobad","Encountered an unexpected JCCompilationUnit instead of a JmlCompilationUnit in JmlEnter.visitTopeLevel");
            super.visitTopLevel(tree);
            return;
        }
        JmlCompilationUnit jmltree = (JmlCompilationUnit)tree;

        if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(0,2,"entering " + jmltree.sourcefile.getName());

        // Fill in the toplevel field for each class definition
        for (JCTree t: tree.defs) {
            if (t instanceof JmlClassDecl) ((JmlClassDecl)t).toplevel = jmltree;  // FIXME - this is already done, at lesat for parsed files?
        }
        
        // FIXME - a problem here is that the specs and the model fields/classes/methods will be attributed using the set of imports from the Java source file

        // Match specifications to the corresponding Java class
        if (jmltree.specsCompilationUnit != null) {
            tree.defs = matchClasses(tree.defs, jmltree.specsCompilationUnit.defs, tree.sourcefile.toString());
        }

        jmltree.topLevelEnv = null;
        if (jmltree.specsCompilationUnit == null) {
            specTopEnv = null;
        } else {
            JmlCompilationUnit specscu = jmltree.specsCompilationUnit;
            for (JCTree t: specscu.defs) {
                if (t instanceof JmlClassDecl) ((JmlClassDecl)t).toplevel = specscu;
            }
            // This if-else statement copied from Enter
            if (specscu.pid != null) {
                specscu.packge = reader.enterPackage(TreeInfo.fullName(specscu.pid));
//                if (specscu.packageAnnotations.nonEmpty()
//                        || pkginfoOpt == PkgInfo.ALWAYS
//                        || specscu.docComments != null) {
//                    if (specscu.packageAnnotations.nonEmpty()){
//                        log.error(specscu.packageAnnotations.head.pos(),
//                                  "pkg.annotations.sb.in.package-info.java");
//                    }
//                }
            } else {
                specscu.packge = syms.unnamedPackage;
            }
            specscu.packge.complete(); // Find all classes in package.
            specTopEnv = topLevelEnv(specscu);
            specscu.topLevelEnv = specTopEnv;
        }

        // Then do all the regular Java registering of packages and types
        super.visitTopLevel(jmltree);

        // Checking that the specs and the java source declare the same package 
        if (jmltree.specsCompilationUnit != null && jmltree.specsCompilationUnit != jmltree) {

            JmlCompilationUnit specscu = jmltree.specsCompilationUnit; 
            if (specscu.packge != jmltree.packge) {
//            if (((jmltree.pid == null) != (specscu.pid == null)) || 
//                    (jmltree.pid != null && specscu.pid != null && !jmltree.pid.toString().equals(specscu.pid.toString()))) {
                utils.error(specscu.sourcefile,specscu.getPackageName().pos,"jml.internal","The package in " + specscu.sourcefile.getName() + " is " + (specscu.pid == null ? "<default>" : specscu.pid.toString() + ", which does not match the .java file: " + jmltree.packge.toString()));
                String s = utils.locationString(specscu.getPackageName().pos, specscu.sourcefile);
                utils.error(jmltree.getSourceFile(), jmltree.getPackageName().pos,"jml.associated.decl.cf",s);
            }
//            specscu.packge = jmltree.packge;
        }
        if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(0,2,"  completed entering " + jmltree.sourcefile.getName());
    }

    public void visitTopLevelBinary(JCCompilationUnit tree) {
        if (!(tree instanceof JmlCompilationUnit)) {
            log.warning("jml.internal.notsobad","Encountered an unexpected JCCompilationUnit instead of a JmlCompilationUnit in JmlEnter.visitTopeLevel");
            super.visitTopLevel(tree);
            return;
        }
        JmlCompilationUnit specscu = (JmlCompilationUnit)tree;

        if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(0,2,"entering " + specscu.sourcefile.getName());

        // Fill in the toplevel field for each class definition
        for (JCTree t: specscu.defs) {
            if (t instanceof JmlClassDecl) ((JmlClassDecl)t).toplevel = specscu;  // FIXME - this is already done, at lesat for parsed files?
        }
        
        // FIXME - a problem here is that the specs and the model fields/classes/methods will be attributed using the set of imports from the Java source file

        if (specscu.pid != null) {
            specscu.packge = reader.enterPackage(TreeInfo.fullName(specscu.pid));
//            if (specscu.packageAnnotations.nonEmpty()
//                    || pkginfoOpt == PkgInfo.ALWAYS
//                    || specscu.docComments != null) {
//                if (specscu.packageAnnotations.nonEmpty()){
//                    log.error(specscu.packageAnnotations.head.pos(),
//                              "pkg.annotations.sb.in.package-info.java");
//                }
//            }
        } else {
            specscu.packge = syms.unnamedPackage;
        }
        specscu.packge.complete(); // Find all classes in package.
        specTopEnv = topLevelEnv(specscu);
        specscu.topLevelEnv = specTopEnv;

        // Checking that the specs and the java source declare the same package  -- FIXME
//        if (jmltree.specsCompilationUnit != null && jmltree.specsCompilationUnit != jmltree) {
//
//            if (specscu.packge != specscu.packge) {
////            if (((jmltree.pid == null) != (specscu.pid == null)) || 
////                    (jmltree.pid != null && specscu.pid != null && !jmltree.pid.toString().equals(specscu.pid.toString()))) {
//                utils.error(specscu.sourcefile,specscu.getPackageName().pos,"jml.internal","The package in " + specscu.sourcefile.getName() + " is " + (specscu.pid == null ? "<default>" : specscu.pid.toString() + ", which does not match the .java file: " + jmltree.packge.toString()));
//                String s = utils.locationString(specscu.getPackageName().pos, specscu.sourcefile);
//                utils.error(jmltree.getSourceFile(), jmltree.getPackageName().pos,"jml.associated.decl.cf",s);
//            }
////            specscu.packge = jmltree.packge;
//        }

        // Match specifications to the corresponding Java class
        {
            String owner = (specscu.packge == syms.unnamedPackage?"":(specscu.packge.flatName()+"."));
            matchClassesForBinary(owner, specscu.defs, null, null);
        }


        if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(0,2,"  completed entering " + specscu.sourcefile.getName());
    }

    /** This routine matches class declarations in the specifications ('specsDefs' list) with Java declarations ('defs' list).
     * Note that these may be top-level declarations in corresponding files; they may also be lists of nested declaration
     * from corresponding nested locations. The composite list of declarations (to replace 'defs') is returned. Any duplicate
     * orphan declarations are warned about.
     */
    public List<JCTree> matchClasses(List<JCTree> defs, List<? extends JCTree> specsDefs, String javasource) {
        ListBuffer<JCTree> newdefs = new ListBuffer<JCTree>();
        for (JCTree tt: defs) { // Iterate over the Java classes 
            if (tt instanceof JmlClassDecl) {
                JmlClassDecl javaDecl = (JmlClassDecl)tt;
                if (utils.isJML(javaDecl.mods)) continue; // Ignore JML (model) classes in the Java declaration
            }
            newdefs.add(tt); // We have to leave everything else in, because the java and specs lists might be shared
                            // and we can't match everything else up and produce the specs structures until JmlMemberEnter
        }
        for (JCTree specDecl: specsDefs) {  // Iterate over the classes in the specification
            if (!(specDecl instanceof JmlClassDecl)) continue;
            JmlClassDecl specsClass = (JmlClassDecl)specDecl;
            // The declaration 'specsClass' is in a specification file.
            // We need to find the Java declaration that it matches
            // There must be one, and there should only be one declaration in the specsDefs list
            // that matches a particular java declaration.
            // A Java declaration need not have a match
            Name name = specsClass.name;
            JmlClassDecl matched = null;
            for (JCTree tt: newdefs) { // Iterate over the Java classes 
                if (!(tt instanceof JmlClassDecl)) continue;
                JmlClassDecl javaDecl = (JmlClassDecl)tt;
                if (name.equals(javaDecl.name)) {
                    matched = javaDecl;
                    if (javaDecl.specsDecls == null) {
                        javaDecl.specsDecls = specsClass; // Attach the specification to the matching Java AST
                        if (utils.isJML(specsClass.mods)) {
                            // A model class (in the specs) matches a java class - error
                            utils.error(specsClass.source(), specsClass.pos,
                                    "jml.duplicate.model",
                                    specsClass.name,javasource);
                            String s = utils.locationString(specsClass.pos, specsClass.source());
                            utils.error(javaDecl.source(), javaDecl.pos,"jml.associated.decl.cf",s);
                        }
                    } else {  // Duplicate
                        utils.error(specsClass.source(), specsClass.pos,"jml.duplicate.jml.class.decl",specsClass.name);
                        utils.error(javaDecl.specsDecls.source(), javaDecl.specsDecls.pos,"jml.associated.decl.cf",
                        		utils.locationString(specsClass.pos, specsClass.source()));
                    }
                    break;
                }
            }
            if (matched == null) {
                if (!utils.isJML(specsClass.mods)) {
                    utils.error(specsClass.source(), specsClass.pos,
                            "jml.orphan.jml.class.decl",
                            specsClass.name,javasource);
                }
                
                // This specification file is not matched, so it is like a
                // model class declaration. Pretend it is one.
                
                specsClass.specsDecls = specsClass;
                newdefs.add(specsClass);
            }
        }
        return newdefs.toList();
    }

    public void matchClassesForBinary(String owner, List<JCTree> specsDefs, Collection<JmlClassDecl> unmatchedTypesList, String javasource) {
        for (JCTree specDecl: specsDefs) {  // Iterate over the classes in the specification
            if (!(specDecl instanceof JmlClassDecl)) continue;
            JmlClassDecl specsClass = (JmlClassDecl)specDecl;
            // The declaration 'specsClass' is in a specification file.
            // We need to find the Java declaration that it matches
            // There must be one, and there should only be one declaration in the specsDefs list
            // that matches a particular java declaration.
            // A Java declaration need not have a match

            ClassSymbol c = reader.enterClass( names.fromString( owner + specsClass.name.toString()));

            if (c != null) {
                specsClass.sym = c;
                specs.combineSpecs(c,null,specsClass);
                if (utils.isJML(specsClass.mods)) {
                    // A model class (in the specs) matches a java class - error
                    // FIXME _ fix this error message
                    utils.error(specsClass.source(), specsClass.pos,
                            "jml.duplicate.model",
                            specsClass.name,javasource);
                    String s = utils.locationString(specsClass.pos, specsClass.source());
                    utils.error(specsClass.source(), specsClass.pos,"jml.associated.decl.cf",s);
                }
//            } else {  // Duplicate
//                utils.error(specsClass.source(), specsClass.pos,"jml.duplicate.jml.class.decl",specsClass.name);
//                utils.error(javaDecl.specsDecls.source(), javaDecl.specsDecls.pos,"jml.associated.decl.cf",
//                        utils.locationString(specsClass.pos, specsClass.source()));
//            }
//        }
            }
            if (c == null) {
                if (!utils.isJML(specsClass.mods)) {
                    // FIXME - fix error
                    utils.error(specsClass.source(), specsClass.pos,
                            "jml.orphan.jml.class.decl",
                            specsClass.name,javasource);
                }
                
                // This specification file is not matched, so it is like a
                // model class declaration. Pretend it is one.
                
                // FIXME - enter the class
            }
        }
    }

    // Overridden to use the specTopEnv when appropriate
    @Override
    public <T extends JCTree> List<Type> classEnter(List<T> trees, Env<AttrContext> env) { 
        ListBuffer<Type> ts = new ListBuffer<Type>();
        for (List<T> l = trees; l.nonEmpty(); l = l.tail) {
            T clazz = l.head; 
//            if (specTopEnv != null && clazz instanceof JmlClassDecl && utils.isJML(((JmlClassDecl)clazz).mods)) { // FIXME - also must not be an inner class
//                env = specTopEnv;
//            }
            Type t = classEnter(clazz, env);
            if (t != null)
                ts.append(t);
        }
        return ts.toList();
    }

    @Override
    public void visitClassDef(JCClassDecl that) {
        // We need to match up classes before calling super.classDefs so that
        // the specs for nested classes can be computed. Nothing else should
        // be done with the specs, however, until the Java class is 'entered'
        // in the visitClassDef call.
        
        JmlClassDecl jmltree = (JmlClassDecl)that;
        
        // Propagate the reference to the CompilationUnit to nested classes
        for (JCTree t: that.defs) {
            if (t instanceof JmlClassDecl) ((JmlClassDecl)t).toplevel = jmltree.toplevel;
        }

        JmlClassDecl specstree = jmltree.specsDecls;
        if (specstree != null && specstree != jmltree) {
            JmlCompilationUnit top = specstree.toplevel;
            for (JCTree t: specstree.defs) {
                if (t instanceof JmlClassDecl) ((JmlClassDecl)t).toplevel = top;
            }
        }
        
        // Match up specs classes with java classes and adjust for unmatched classes or duplicates
        if (specstree != null) {
            // Attaches specs tree from second list at classdecl.specsDecls for each classdecl in the first list
            that.defs = matchClasses(that.defs, specstree.defs, jmltree.source().toString());
        }
        
        // FIXME - the rest of the method needs review
        
        // Do this check defensively - but eventually should never be null when nested classes are properly handled
        ClassSymbol cs = null;
        if (jmltree.toplevel != null) {
            Name flatname = jmltree.toplevel.pid == null ? that.name : names.fromString(jmltree.toplevel.pid.toString() + "." + that.name.toString());
            cs = reader.classExists(flatname);
            // cs is non-null if the class has already been loaded/entered
            // cs is null for a source file, with or without a specs file
        }
        {
            // Do not redo the visitClassDef for binary loading, when the class is read but the specs are not loaded
            if ((cs != null && cs.members_field == null) || jmltree.toplevel == null || JmlCompilationUnit.isForSource(jmltree.toplevel.mode)) {  // FIXME - ciould this be just if (cs == null) {
                super.visitClassDef(that);
                if (that.sym == null) {
                    log.error("jml.internal", "Unexpected null class symbol after processing class " + that.name);
                    return;
                }
                

// FIXME _ do need to check the explicit supertype and interfaces and throws type names
            } else {
                that.sym = cs;
                Env<AttrContext> localEnv = classEnv(that, env);
                typeEnvs.put(that.sym, localEnv);
                // We are entering a class within specification file for a binary load
                // So enter any nested classes within the class we have been entering
                // classEnter(that.defs, typeEnvs.get(cs)); // FIXME - no environment stored
            }
        }
        
        if (specstree != null) {
            checkAndEnterTypeParameters(that.sym, specstree, null);
        }

        
        // Set the sym and env fields of the classes
        Env<AttrContext> localEnv = getEnv(that.sym);
        jmltree.env = localEnv;
        
        if (specstree != null) {
            specstree.sym = that.sym;
            specstree.env = localEnv;
        }

        // FIXME - what is all this
        JmlClassDecl specsDecl = jmltree.specsDecls;
        JmlClassDecl principalDecl;
        if (localEnv != null) {
            // Typically a java class with or without specs
            principalDecl = (JmlClassDecl)localEnv.tree;
        } else if (specsDecl != null) {
            // A binary class with specs - JDK did not register an env because
            // there is no Java source.  We put in one for the spec file
            principalDecl = specsDecl;
        } else {
            principalDecl = null;
            // This happens for a binary class with no specs for the given type
        }

        if (that.sym != null) { // FIXME - local classes atleats hav ehave a null sym
            // FIXME - what is the purpose of the following?
            JmlSpecs.TypeSpecs combinedTypeSpecs = specs.getSpecs(that.sym);
            combinedTypeSpecs.refiningSpecDecls = specsDecl;
            if (principalDecl == null) {
                combinedTypeSpecs.modifiers = null;
                combinedTypeSpecs.decl = null;
                combinedTypeSpecs.file = that.sym.sourcefile;
            } else {
                principalDecl.typeSpecsCombined = specs.combineSpecs(that.sym,principalDecl,principalDecl.specsDecls);  // This line is absolutely needed - stores specs into the specs database
            }
        }

    }
    


    // FIXME - unify the recording of empty specs with default specs??
    public void recordEmptySpecs(ClassSymbol csymbol) {
        //log.noticeWriter.println("RECORDING EMPTY SPECS FOR " + csymbol.flatName());
        // TODO - change this if we store JML specs in boinary files - then could get annotation information from the symbol
        specs.putSpecs(csymbol,new JmlSpecs.TypeSpecs(null,JmlTree.Maker.instance(context).Modifiers(csymbol.flags(),List.<JCTree.JCAnnotation>nil()),null));
        if (csymbol.members_field != null) for (Symbol s: csymbol.getEnclosedElements()) {
            if (s instanceof ClassSymbol) recordEmptySpecs((ClassSymbol)s);
        }
    }


    // FIXME - do we need this?
//    /** Is called after parsing the specs for a binary type, to do what we do for
//     * source type via enter.main().  However, for binary types we do not need to
//     * enter all the classes in the database; we simply need to match up the
//     * declarations in the spec file with those in the binary, but do need to
//     * enter any specification (model) classes.
//     * 
//     * @param csymbol the ClassSymbol of the binary type
//     * @param speccu The parse tree of the specifications for the binary type
//     * (including the specifications for any secondary types that would have been in the same source
//     * compilation unit)
//     */
//    public void enterSpecsForBinaryClasses(ClassSymbol csymbol, JmlCompilationUnit speccu) {
//    	if (utils.jmlverbose >= Utils.JMLDEBUG)  log.getWriter(WriterKind.NOTICE).println("ENTER TOPLEVEL (BINARY) " + csymbol);
//
//    	csymbol.complete();
//    	
//        // First do all the linking of java types to specifications
//        // Since we do not have a Java compilation Unit to walk down, we will
//        // enter the model classes as well
//        if (speccu == null) {
//            // If there are no specs, we still make an (empty) record of that
//            // fact in the specs database, so that we don't go looking again.
//            recordEmptySpecs(csymbol);
//            return;
//        }
//
//        List<JCTree> specsDecls = speccu.defs;
//
//        // Search for secondary types
//        HashMap<Name,JmlClassDecl> names = new HashMap<Name,JmlClassDecl>();
//        for (JCTree t: specsDecls) {
//            if (t instanceof JmlClassDecl) {
//                Name n = ((JmlClassDecl)t).name;
//                if (names.get(n) == null) names.put(n,(JmlClassDecl)t);
//            }
//        }
//
//        // Do the primary type
//        enterSpecsForBinaryClasses(csymbol,specsDecls);
//        names.remove(csymbol.name);
//
//        // Do any secondary types
//        for (Name n: names.keySet()) {
//            // Need to look up symbol for name n in the package of csymbol
//            Scope.Entry e = csymbol.owner.members().lookup(n);
//            while (e.sym != null && !(e.sym instanceof ClassSymbol)) { e = e.next(); }
//            Symbol nsymbol = e.sym;
//            if (nsymbol instanceof ClassSymbol) enterSpecsForBinaryClasses((ClassSymbol)nsymbol,specsDecls);
//            else {
//                JavaFileObject prev = log.useSource(names.get(n).source());
//                log.error(names.get(n).pos,"jml.unmatched.secondary.type",n);
//                log.useSource(prev);
//            }
//        }
//        
//        // Do any top-level model types
//        {
//            for (JmlClassDecl modelType: speccu.parsedTopLevelModelTypes) {
//                classEnter(modelType,topLevelEnv(speccu));
//            }
//        }
//
//        Env<AttrContext> tlenv = topLevelEnv(speccu);
//        setSymbolAndEnv(speccu.defs,tlenv,csymbol); // FIXME: This only takes care of the primary class and its nested classes
//
//        //jcu.accept(this); // add in imports
//        for (JCTree t: speccu.defs) {
//            if (t instanceof JmlClassDecl) {
//                JmlClassDecl jtree = (JmlClassDecl)t;
//                if (jtree.name.equals(csymbol.name)) {
//                    jtree.sym = csymbol; // FIXME - what about secondary types
//                    jtree.env = classEnv(jtree,tlenv);
//                }
//            }
//        }
//
//
//        // Create a todo item for each toplevel class that needs processing
//        
//        // FIXME _ we should perhaps use the consolidated specifications 
//        // Here we need to avoid using unmatched specs
////        if (speccu != null) {
//            for (JCTree t: speccu.defs) {
//                if (t instanceof JmlClassDecl && ((JmlClassDecl)t).sym != null && ((JmlClassDecl)t).env != null) {
//                    binaryMemberTodo.add(((JmlClassDecl)t).env);
//                    //log.noticeWriter.println("APPENDING TO BINARYENVS " + specsSequence.get(0).sourcefile);
//                    binaryEnvs.append(speccu);
//                }
//            }
////        }
//
//    }
  
    // FIXME - do we need this
//    /** Finds any JmlClassDecl objects in the defs list that have a name matching csymbol and
//     * (a) sets the .sym field to csymbol and creates a class env object based on the given env.
//     * @param defs
//     * @param env
//     * @param csymbol
//     */
//    public void setSymbolAndEnv(List<JCTree> defs, Env<AttrContext> env, ClassSymbol csymbol) {
//        for (JCTree t: defs) {
//            if (t instanceof JmlClassDecl) {
//                JmlClassDecl jmltree = (JmlClassDecl)t;
//                if (jmltree.name.equals(csymbol.name)) {
//                    jmltree.sym = csymbol;
//                    jmltree.env = classEnv(jmltree,env);
//                    for (Symbol nested: csymbol.getEnclosedElements()) {
//                        if (nested instanceof ClassSymbol) setSymbolAndEnv(jmltree.defs,jmltree.env,(ClassSymbol)nested);
//                    }
//                }
//            }
//        }
//    }


    // FIXME - needs review
    /** Compares the type parameters for the Java class denoted by csym and the 
     * type parameters in the given type declaration (typically from a 
     * specification file), in the context of the given name environment.
     * Issues error messages if types or names do not match; attributes
     * the types; returns false if there were errors.
     * @param csym the class whose local env we are manipulating
     * @param specTypeDeclaration the declaration of the class in a specification file
     * @param classEnv the environment which is modified by the addition of any type parameter information
     */
    public boolean checkAndEnterTypeParameters(ClassSymbol csym, JmlClassDecl specTypeDeclaration, Env<AttrContext> classEnv) {
        Env<AttrContext> localEnv = classEnv;
        //Scope enterScope = enterScope(classEnv);
        boolean result = true;
        int numSpecTypeParams = specTypeDeclaration.typarams.size();
        int numJavaTypeParams = csym.type.getTypeArguments().size();
        if (numSpecTypeParams != numJavaTypeParams) {
            JavaFileObject prev = log.useSource(specTypeDeclaration.source());
            log.error(specTypeDeclaration.pos(),"jml.mismatched.type.arguments",specTypeDeclaration.name,csym.type.toString());
            //log.error(specTypeDeclaration.pos(),"jml.mismatched.type.parameters", specTypeDeclaration.name, csym.fullname, n, javaN);
            result = false;
            log.useSource(prev);
        }
        int nn = numSpecTypeParams; if (numJavaTypeParams < nn) nn = numJavaTypeParams;
        for (int i = 0; i<nn; i++) {
            JCTree.JCTypeParameter specTV = specTypeDeclaration.typarams.get(i);
            TypeVar javaTV = (TypeVar)((ClassType)csym.type).getTypeArguments().get(i);
            if (specTV.name != javaTV.tsym.name) {
                log.error(specTV.pos(),"jml.mismatched.type.parameter.name", specTypeDeclaration.name, csym.fullname, specTV.name, javaTV.tsym.name);
                result = false;
            } 
            // classEnter will set the type of the Type Variable, but it sets it to 
            // something new for each instance, which causes trouble in type mathcing
            // that I have not figured out. Here we preemptively set the type to be the
            // same as the Java type that it matches in the specification.
            specTV.type = javaTV;
            if (localEnv != null) classEnter(specTV,localEnv);
            //enterScope.enter(javaTV.tsym);
        }
        for (int i = nn; i<numSpecTypeParams; i++) {
            JCTree.JCTypeParameter specTV = specTypeDeclaration.typarams.get(i);
            if (localEnv != null) classEnter(specTV,localEnv);
//            JmlAttr.instance(context).attribType(specTV,localEnv);
        }
        // FIXME need to check that the types have the same bounds
        return result;
        //log.noticeWriter.println(" LOCAL ENV NOW " + localEnv);
    }

 
    /** This overrides the parent class method so that we allow file names
     * with spec extensions, not just .java 
     * 
     * @param c the class the file is associated with
     * @param env the Env object representing the filename 
     */
    @Override
    public boolean classNameMatchesFileName(ClassSymbol c, // DRC - changed from private to public
            Env<AttrContext> env) {
        JavaFileObject jfo = env.toplevel.sourcefile;
        if (jfo.getKind() == JavaFileObject.Kind.SOURCE) return super.classNameMatchesFileName(c, env);
        String classname = c.name.toString();
        // FIXME: Actually we are loose in our comparison
        String filename = jfo.getName();
        return filename.endsWith(classname + Strings.specsSuffix); // FIXME - what if classname is just the tail of the filename
    }

    /** Overrides Enter.main simply to add to the list of compilation units 
     * being processed the compilation units representing the specs of binary
     * classes.  This is so that they will get type checked.
     * 
     * @param trees the parse trees coming from the user-specified list of
     * files to process
     */
    @Override
    public void main(List<JCCompilationUnit> trees) {
        super.main(trees);
        // FIXME - these are not currently used - but perhaps should be to get the binary envs type checked
        for (JmlCompilationUnit jcu: binaryEnvs) {
            trees.append(jcu);
        }
        binaryEnvs.clear();
    }

}
