/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.comp;


import java.util.Collection;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.code.Type.TypeVar;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.ParserFactory;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

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
    
    /** This method is called when a JmlCompilationUnit is in the list of things to 'enter'.
     * It visits the designated compilation unit; first it matches
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
        // Already set: toplevel, sourcefile, specsCompilationUnit, 
        // Need to set: topLevelEnv
        if (!(tree instanceof JmlCompilationUnit)) {
            log.warning("jml.internal.notsobad","Encountered an unexpected JCCompilationUnit instead of a JmlCompilationUnit in JmlEnter.visitTopeLevel");
            super.visitTopLevel(tree);
            return;
        }
        JmlCompilationUnit jmltree = (JmlCompilationUnit)tree;

        if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(0,2,"entering " + jmltree.sourcefile.getName());
        
        // FIXME - a problem here is that the specs and the model fields/classes/methods will be attributed using the set of imports from the Java source file

        if (jmltree.specsCompilationUnit == null) {
            // If this is the case we have called visitTopLevel on a specs file
            specTopEnv = null;
        } else {
            JmlCompilationUnit specscu = jmltree.specsCompilationUnit;

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

        // Match specifications to the corresponding Java class, for each (toplevel) class; 
        if (jmltree.specsCompilationUnit != null && jmltree.mode != JmlCompilationUnit.SPEC_FOR_BINARY) {
            tree.defs = matchClasses(tree.defs, jmltree.specsCompilationUnit.defs, tree.sourcefile.toString());
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
//        for (JCTree t: specscu.defs) {
//            if (t instanceof JmlClassDecl) ((JmlClassDecl)t).toplevel = specscu;  // FIXME - this is already done, at lesat for parsed files?
//        }
        
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

        // FIXME - check this somewhere
//        // Checking that the specs and the class symbol use the same package
//        for (JCTree t: specscu.defs) {
//            if (t instanceof JmlClassDecl) {
//                JmlClassDecl jdecl = (JmlClassDecl)t;
//                if (jdecl.sym.owner != specscu.packge) {
//                    utils.error(specscu.sourcefile,specscu.getPackageName().pos,"jml.internal","The package in " + specscu.sourcefile.getName() + " is " + (specscu.pid == null ? "<default>" : specscu.pid.toString() + ", which does not match the binary file: " + jdecl.superSymbol.owner.toString()));
//                }
//            }
//        }

        // Match specifications to the corresponding Java class
        {
            String owner = (specscu.packge == syms.unnamedPackage?"":(specscu.packge.flatName()+"."));
            matchClassesForBinary(specTopEnv, owner, specscu.defs, null, null);
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
        if (defs !=  specsDefs) {
            for (JCTree tt: defs) { // Iterate over the Java classes 
                if (tt instanceof JmlTree.IInJML) {
                    if (((JmlTree.IInJML)tt).isJML()) continue;
                }
                newdefs.add(tt);
            }
        } else {
            newdefs.addAll(defs);
        }
        for (JCTree specDecl: specsDefs) {  // Iterate over the classes in the specification, to find the matching java declaration
            if (!(specDecl instanceof JmlClassDecl)) continue;
            JmlClassDecl specClassDecl = (JmlClassDecl)specDecl;
            boolean isSpecsJML = utils.isJML(specClassDecl.mods);
            // The declaration 'specClassDecl' is in a specification file.
            // We need to find the Java declaration that it matches
            // There is supposed to be one, and there should only be one declaration in the specsDefs list
            // that matches a particular java declaration.
            // A Java declaration need not have a match
            Name name = specClassDecl.name;
            JmlClassDecl matched = null;
            for (JCTree tt: newdefs) { // Iterate over the list of Java declarations 
                if (!(tt instanceof JmlClassDecl)) continue;
                JmlClassDecl javaDecl = (JmlClassDecl)tt;
                boolean isJML = utils.isJML(javaDecl.mods);
                if (name.equals(javaDecl.name)) {
                    matched = javaDecl;
                    if (javaDecl.specsDecl == null) {
                        // No previous match, so far
                        if (!isJML && isSpecsJML) {
                            // A specification declaration matches a java declaration,
                            // but the specification declaration is in a JML annotation - error - but use it as a match anyway
                            utils.error(specClassDecl.source(), specClassDecl.pos,
                                    "jml.duplicate.model",
                                    specClassDecl.name,javasource);
                            String s = utils.locationString(specClassDecl.pos, specClassDecl.source());
                            utils.error(javaDecl.source(), javaDecl.pos,"jml.associated.decl.cf",s);
                            javaDecl.specsDecl = specClassDecl; // Attach the specification to the matching Java AST
                        } else if (isJML && !isSpecsJML) {
                            // A specification declaration matches a java declaration,
                            // but the declaration in the Java file is in a JML annotation, and the specification declaration is not
                            // Since if the specs declaration list is different than the Java declaration list, 
                            // any such JML annotated declarations are removed from the Java declaration list,
                            // this must be a case of a file containing two declarations with the same name, 
                            // one in a JML annotation and one not
                            // Issue and error and omit the JML declaration
                            newdefs = Utils.remove(newdefs, javaDecl);
                            if (defs !=  specsDefs) {
                                utils.error(javaDecl.source(), javaDecl.pos, "jml.internal", "Unexpected JML declaration in the Java file");
                            } else {
                                utils.error(javaDecl.source(), javaDecl.pos,"jml.duplicate.jml.class.decl", javaDecl.name);
                                utils.error(specClassDecl.source(), specClassDecl.pos,"jml.associated.decl.cf",
                                        utils.locationString(javaDecl.pos, javaDecl.source()));
                            }
                        } else if (isJML && isSpecsJML) {
                            if (javaDecl != specClassDecl) {
                                // There are two declarations, both in JML annotations, with the same name
                                utils.error(javaDecl.source(), javaDecl.pos,"jml.duplicate.jml.class.decl", javaDecl.name);
                                utils.error(specClassDecl.source(), specClassDecl.pos,"jml.associated.decl.cf",
                                        utils.locationString(javaDecl.pos, javaDecl.source()));
                                newdefs = Utils.remove(newdefs,specClassDecl);
                            } else {
                                // The two declarations are the same one - OK
                                javaDecl.specsDecl = specClassDecl;
                            }
                        } else {
                            // else OK match
                            javaDecl.specsDecl = specClassDecl; // Attach the specification to the matching Java AST
                        }
                    } else {  // Duplicate - warn and ignore
                        if (!isJML) {
                            // This less informational error message is here just to duplicate previous behavior (and the Java compiler) for Java duplicates
                            utils.error(specClassDecl.source(), specClassDecl.pos,"duplicate.class",specClassDecl.name);
                        } else {
                            utils.error(specClassDecl.source(), specClassDecl.pos,"jml.duplicate.jml.class.decl",specClassDecl.name);
                            utils.error(javaDecl.specsDecl.source(), javaDecl.specsDecl.pos,"jml.associated.decl.cf",
                                    utils.locationString(specClassDecl.pos, specClassDecl.source()));
                        }
                        if (!isJML && utils.isJML(javaDecl.specsDecl.mods) && !isSpecsJML) javaDecl.specsDecl = specClassDecl;
                        newdefs = Utils.remove(newdefs, specClassDecl);
                    }
                    break;
                }
            }
            if (matched == null) {
                // This specification file is not matched, so it is like a
                // model class declaration. Pretend it is one.
                // If necessary, add information so that it appears to be declared in a JML annotation and as a model class
                // In any case, add it to the list of declarations to export
                
                if (!utils.isJML(specClassDecl.mods)) {
                    utils.error(specClassDecl.source(), specClassDecl.pos,
                            "jml.orphan.jml.class.decl",
                            specClassDecl.name,javasource);
                    utils.setJML(specClassDecl.mods);
                    JCAnnotation x = utils.tokenToAnnotationAST(JmlTokenKind.MODEL, specClassDecl.pos, specClassDecl.pos);
                    boolean has = false;
                    for (JCAnnotation a: specClassDecl.getModifiers().getAnnotations()) {
                        // FIXME - this is an inadequate comparison
                        if (((JCTree.JCFieldAccess)a.annotationType).name == ((JCTree.JCFieldAccess)x.annotationType).name) { has = true; break; }
                    }
                    if (!has) {
                        specClassDecl.mods.annotations = specClassDecl.mods.getAnnotations().append(x);
                    } else {
                        utils.error(specClassDecl.source(), specClassDecl.pos, "jml.ghost.model.on.java");
                    }
                }
                
                specClassDecl.specsDecl = specClassDecl; specClassDecl.env = null;
                newdefs.add(specClassDecl);
            }
        }
        return newdefs.toList();
    }
    
    /**
     * 
     * @param ownerenv
     * @param owner The flat String name of the package or enclosing class (with trailing period) that holds the declarations in specsDefs
     * @param specsDefs The specification declarations to be associated with classes
     * @param unmatchedTypesList
     * @param javasource
     */
    public void matchClassesForBinary(Env<AttrContext> ownerenv, String owner, List<JCTree> specsDefs, Collection<JmlClassDecl> unmatchedTypesList, String javasource) {
        for (JCTree specDecl: specsDefs) {  // Iterate over the classes in the specification
            if (!(specDecl instanceof JmlClassDecl)) continue;
            JmlClassDecl specsClass = (JmlClassDecl)specDecl;
            // The declaration 'specsClass' is in a specification file.
            // This is matching for a binary class, so there is no source code Java declarations
            // We need to find the Java declaration that it matches
            // There must be one, and there should only be one declaration in the specsDefs list
            // that matches a particular java declaration.
            // A Java declaration need not have a match

            ClassSymbol c = reader.enterClass( names.fromString( owner + specsClass.name.toString()));

            if (c != null) {
                if (utils.isJML(specsClass.mods)) {
                    // The specs class is in a JML annotation but still matches a java class - error
                    // FIXME _ fix this error message
                    utils.error(specsClass.source(), specsClass.pos,
                            "jml.duplicate.model",
                            specsClass.name,javasource);
                    String s = utils.locationString(specsClass.pos, specsClass.source());
                    utils.error(specsClass.source(), specsClass.pos,"jml.associated.decl.cf",s);
                } else {
                    specsClass.sym = c;
                    Env<AttrContext> localenv = classEnv(specsClass, ownerenv);
                    typeEnvs.put(c,localenv);
                    specsClass.env = localenv;
                    specs.combineSpecs(c,null,specsClass);
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
                } else {
                    Type t = classEnter(specsClass,ownerenv);
                    specsClass.sym = (ClassSymbol)t.tsym;
                    Env<AttrContext> localenv = classEnv(specsClass, ownerenv);
                    typeEnvs.put(c, localenv);
                    specsClass.env = localenv;
                    specs.combineSpecs(c,null,specsClass);
                }
                
                // This specification file is not matched, so it is like a
                // model class declaration. Pretend it is one.
                
                // FIXME - enter the class
            }
        }
    }

//    /** The arguments to this method are a class symbol and then a list of lists of class body definitions
//     * for that class; alternatively, the symbol can be null and the list is a list
//     * of the top level defs corresponding to a compilation unit.  The class body
//     * definitions come from specification files.  Each specification file that
//     * contains a specification for the given class will have a set of definitions
//     * for that class; each such set constitutes one element of the list that is
//     * the second argument to the method.  [ The argument is a list of list of
//     * definitions instead of a list of the parent class declarations so that
//     * nested classes and the top-level compilation unit can be treated in the
//     * same way.
//
//     * @param classToMatch a class symbol to be matched
//     * @param listOfSpecsDefs the class-body definitions from the specifications
//     * for the given class or top-level compilation unit
//     */
//    //@ requires (* this.env must be the local env of the 'classToMatch' *);
//    protected JmlClassDecl matchSpecsToClasses(ClassSymbol classToMatch, List<JCTree> specsDecls ) {
////        if (classToMatch.name.toString().equals("Content")) {
////            log.noticeWriter.println(classToMatch);
////        }
//        // We find the list of matching spec declarations.  We also fix their
//        // env fields, but only the ones that match - the others will be matched
//        // in a separate call, or ignored.
//        Name n = classToMatch.name;
//        if (specsDecls == null) {
//            // For these - model and local classes - attach self as specs
//            Env<AttrContext> classesenv = typeEnvs.get(classToMatch);
//            if (classesenv != null && classesenv.tree != null) {
//                specsDecls = List.<JCTree>of(classesenv.tree);
//                ((JmlClassDecl)classesenv.tree).env = classesenv;
//            }
//        }
//        JmlClassDecl matchedSpecClass = null;
//        if (specsDecls != null) {   
//            List<JCTree> list = specsDecls;
//            for (JCTree t: list) {
//                if (t instanceof JmlClassDecl) {
//                    JmlClassDecl specClass = (JmlClassDecl)t;
//                    if (specClass.name.equals(n)) {
//                        JavaFileObject prev = log.useSource(specClass.source());
//                        if (matchedSpecClass == null) {
//                            boolean ok = checkAndEnterTypeParameters(classToMatch,specClass,specClass.env);
//                            if (ok) {
//                                specClass.sym = classToMatch;
//                                matchedSpecClass = specClass;
//                                //specClass.env = classEnv(specClass, specClass.env); // FIXME - is this needed?
//           //                     for (JCTree tt: specClass.defs) {
//           //                         if (tt instanceof JmlClassDecl) ((JmlClassDecl)tt).env = classEnv((JmlClassDecl)tt,specClass.env);
//           //                     }
//                            }
//                        } else {
//                            log.error(specClass.pos,"jml.duplicate.jml.class.decl",specClass.name);
//                            log.error(matchedSpecClass.pos,"jml.associated.decl.cf",
//                                    utils.locationString(specClass.pos));
//                        }
//                        log.useSource(prev);
//                    }
//                }
//            }
//        }
//
//        // selflist is the list of specification type declarations that are
//        // a match to 'classToMatch'
//
//        Env<AttrContext> localenv = typeEnvs.get(classToMatch);
//        boolean wasNull = localenv == null;
//        if (localenv != null) {
//            // Typically a java class with or without specs
//            matchedSpecClass = (JmlClassDecl)localenv.tree;
//        } else if (matchedSpecClass != null) {
//            // A binary class with specs - JDK did not register an env because
//            // there is no Java source.  We put in one for the most refined
//            // spec file
//            localenv = matchedSpecClass.env;
//        } else {
//            // This happens for a binary class with no specs for the given type
//        }
//            // The above is either the java declaration, or (if the class is
//            // binary) the most refined specs declaration
//
//        JmlSpecs.TypeSpecs combinedTypeSpecs = specs.getSpecs(classToMatch);
//        if (matchedSpecClass == null) {
//            combinedTypeSpecs.modifiers = null;
//            combinedTypeSpecs.decl = null;
//            combinedTypeSpecs.file = classToMatch.sourcefile;
//        } else {
//            matchedSpecClass.typeSpecsCombined = specs.combineSpecs(classToMatch,null,matchedSpecClass);
//        }
//        combinedTypeSpecs.refiningSpecDecls = matchedSpecClass;
//
//        // Determine an env for this class if it does not have one
//        // We need to have some sort of declaration to do so - we use the
//        // most refined specs declaration
//        if (wasNull && matchedSpecClass != null) {
//            // This branch will not be taken for normal Java classes, since they have been
//            // entered; similarly for model classes
//            //log.noticeWriter.println("PUTTING TYPEENV " + classToMatch + " " + typeEnvs.get(classToMatch) + " " + env);
//            typeEnvs.put(classToMatch,matchedSpecClass.env);  // Binary classes with specs will have the environment be null;
//                                        // we add an environment that holds the specs class declaration so if gets attributed
//                                        // FIXME - we should handle this differently when we put in place envs for specs that 
//                                        // are different than the envs for the corresponding java class - to handle, for example,
//                                        // different lists of import statements
//        }
//
//        return matchedSpecClass;
//    }

    // FIXME - if we do not need spescTopEnv, then delete this override
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
            if (t != null) {
                ts.append(t);
            }
        }
        return ts.toList();
    }
    
    public void binaryEnter(JmlCompilationUnit specs) {
        Env<AttrContext> prevEnv = env;
        ((JmlMemberEnter)JmlMemberEnter.instance(context)).modeOfFileBeingChecked = specs.mode;
        env = specs.topLevelEnv;  // FIXME - is this ever nonnull?
        if (env == null) {
            
            env = specs.topLevelEnv = topLevelEnv(specs);
            visitTopLevel(specs);
            Env<AttrContext> prevEnvME = JmlMemberEnter.instance(context).env;
            JmlMemberEnter.instance(context).env = env;
            JmlMemberEnter.instance(context).importHelper(specs);
//            super.memberEnter(specs, env);  // Does not do members for binary classes
//            env = specs.topLevelEnv;
            for (JCTree d: specs.defs) {
                if (!(d instanceof JmlClassDecl)) continue;
                JmlClassDecl cd = (JmlClassDecl)d;
                cd.specsDecl = cd;
                Env<AttrContext> clenv = typeEnvs.get(cd.sym);
                if (clenv == null) {
                    clenv = classEnv(cd, env);
                    typeEnvs.put(cd.sym, clenv);
                }
                cd.env = clenv;
                JmlMemberEnter.instance(context).memberEnter(cd,clenv);  // FIXME - does nothing
            }
            JmlMemberEnter.instance(context).env = prevEnvME;
        }
        for (JCTree cd: specs.defs) {
            if (!(cd instanceof JmlClassDecl)) continue;
            JmlClassDecl jcd = (JmlClassDecl)cd;
            //JmlSpecs.instance(context).putSpecs(jcd.sym, new JmlSpecs.TypeSpecs(jcd));
            if (utils.isJML(jcd.mods)) {
                // A class declared within JML - so it is supposed to be a model class with a unique name
                // FIXME - check that name is not already used by a real Java class
                // FIXME - each model method will be entered for each declaration in the specification file
                // We have the source code for this so we want to enter this as a source-based class
                classEnter(cd,env);
            }
 //           Env<AttrContext> specClassenv = jcd.env;
 //           binaryMemberEnter(jcd.sym, jcd, specClassenv);
            // FIXME - need to handle any secondary classes and nested classes as well
        }
        env = prevEnv;
    }
    
//    public void binaryMemberEnter(ClassSymbol c, JmlClassDecl specs, Env<AttrContext> env) {
//        Env<AttrContext> prevenv = this.env;
//        JavaFileObject prev = log.useSource(specs.source());
//        try {
//        JmlAttr attr = JmlAttr.instance(context);
//        c.flags_field |= UNATTRIBUTED;
//        attr.addTodo(c);
//        Env<AttrContext> classenv = enter.getEnv(specs.sym);
//        
//        {
//            ClassSymbol cs = c;
//            ClassType ct = (ClassType)c.type;
//            // enter symbols for 'this' into current scope.
//            VarSymbol thisSym =
//                    new VarSymbol(FINAL | HASINIT, names._this, cs.type, cs);
//            thisSym.pos = Position.FIRSTPOS;
//            env.info.scope.enter(thisSym);
//            // if this is a class, enter symbol for 'super' into current scope.
//            if ((cs.flags_field & INTERFACE) == 0 &&
//                    ct.supertype_field != null &&
//                    ct.supertype_field.hasTag(CLASS)) {
//                VarSymbol superSym =
//                        new VarSymbol(FINAL | HASINIT, names._super,
//                                ct.supertype_field, cs);
//                superSym.pos = Position.FIRSTPOS;
//                env.info.scope.enter(superSym);
//            }
//        }
//        
//        if (!specs.typarams.isEmpty() ||  !((ClassType)c.type).typarams_field.isEmpty() ) {
//            // FIXME - not doing classes or methods with type argument for now
//                enter.recordEmptySpecs(c);
//        } else 
//
//        for (JCTree t: specs.defs) {
//            //env = prevenv;
//            if (t instanceof JmlMethodDecl) {
//                JmlMethodDecl md = (JmlMethodDecl)t;
////                if (!md.typarams.isEmpty() && !md.name.toString().equals("defaultEmpty")) {
////                    enter.recordEmptySpecs(c);  // FIXME _ not handling methods with type parameters
////                    break;
////                }
////                Env<AttrContext> localEnv = methodEnv(md, classenv);
////                env = classenv;
//                boolean isJML = utils.isJML(md.mods);
//                boolean isModel = isJML && utils.findMod(md.mods, JmlTokenKind.MODEL) != null;
//                if (md.sym == null) {
//                    this.env = classenv;
//                    visitMethodDef((JmlMethodDecl)md,c);
////                    boolean hasTypeArgs = !md.typarams.isEmpty();
////                    
////                    ClassType ctype = (ClassType)c.type;
////                    hasTypeArgs = hasTypeArgs || !ctype.typarams_field.isEmpty();
////                    //Type mtype = signature(null,md.typarams,md.params,md.getReturnType(),null,md.thrown,env);
////                    ListBuffer<Type> tyargtypes = new ListBuffer<Type>();
////                    for (JCTypeParameter param : md.typarams) {
////                        Type tt = attr.attribType(param, env);
////                        tyargtypes.add(tt);
////                    }
////                    ListBuffer<Type> argtypes = new ListBuffer<Type>();
////                    for (JCVariableDecl param : md.params) {
////                        Type tt = attr.attribType(param.vartype, env); // FIXME _ this does not work for type parameters, such as in Comparable
////                        param.type = tt;
////                        argtypes.add(tt);
////                    }
////                    if (md.restype != null) {
////                        attr.attribType(md.restype, env);
////                    }
////                    if (md.thrown != null) {
////                        for (JCExpression th: md.thrown) attr.attribType(th, env);
////                    }
////                    // FIXME - don't want an error message - just an indication of whether such a method exists
////                    Scope.Entry e = c.members().lookup(md.name);
////                    int count = 0;
////                    Types types = Types.instance(context);
////                    while (e.sym != null && e.scope != null && e.sym.name == md.name) {
////                        if (e.sym instanceof Symbol.MethodSymbol) {
////                            Symbol.MethodSymbol msym = (Symbol.MethodSymbol)e.sym;
////                            x: if (msym.getParameters().length() == md.params.length()) {
////                                if (!hasTypeArgs) {
////                                    int k = md.params.length();
////                                    for (int i=0; i<k; i++) {
////                                        if (!types.isSameType(msym.getParameters().get(i).type,md.params.get(i).type)) {
////                                            break x;
////                                        }
////                                    }
////                                }
////                                md.sym = msym;
////                                count++;
////                            }
////                        }
////                        e = e.next();
////                        while (e.sym != null && e.scope != null && e.sym.name != md.name) e = e.next();
////                    }
//                    
////                    if (count > 1) log.error(md.pos(),"jml.internal","Type comparison not implemented " + c.flatname + "." + md.name);
//
//                    //md.sym = (MethodSymbol)JmlResolve.instance(context).findFun(env,md.name,argtypes.toList(),tyargtypes.toList(),false,false);
//                    //md.sym = (MethodSymbol)JmlResolve.instance(context).resolveMethod(t.pos(),env,md.name,argtypes.toList(),tyargtypes.toList());
//                }
//                //if (md.name.toString().equals("defaultEmpty")) Utils.stop();
//                if (md.sym != null) {
//                    {
//                        Env<AttrContext> localEnv = methodEnv(md, env);
//                        annotateLater(md.mods.annotations, localEnv, md.sym, md.pos());
//                    }
//
//                    md.specsDecl = md;
//                    md.methodSpecsCombined = new JmlSpecs.MethodSpecs(md);
//                    JmlSpecs.instance(context).putSpecs(md.sym, md.methodSpecsCombined);
//                    checkMethodMatch(null, md.sym, md, c);
//                }
//                if (isJML && !isModel) {
//                    // Error: Non-model method declared within JML
//                } else if (md.sym != null && !isJML) {
//                    // Java method in spec matches the java declaration. Just add the specs.
//                    JmlSpecs.instance(context).putSpecs(md.sym, md.methodSpecsCombined); // FIXME - duplicate line above
//                } else if (md.sym == null && isJML) {
//                    // Add the model method to the binary class
//        // FIXME - need to sort out the env
//                    this.env = env;
//                    visitMethodDef(md);
////                    JmlSpecs.instance(context).putSpecs(md.sym, md.methodSpecsCombined);
//                } else if (md.sym != null && isJML) {
//                    // Error: model method matching a Java method 
//                } else { // if (md.sym == null && !isModel) {
//                    // Error: No method in class to match non-model specification method
//                }
//                
//            } else if (t instanceof JmlClassDecl) {
//                // FIXME - need symbol for nested class
//                //binaryMemberEnter(c,(JmlClassDecl)t);
//                JmlClassDecl tcd = (JmlClassDecl)t;
//                ClassSymbol sym = tcd.sym;
//                if (sym == null) {
//                    sym = tcd.sym = reader.classExists(names.fromString(c.toString() + "$" + tcd.name.toString()));
//                }
//                if (sym != null) enterSpecsForBinaryClasses(sym, List.<JCTree>of(t));
//                else {
//                    // FIXME - no such class - is it a JML class? if so enter it
//                }
//
//            } else if (t instanceof JmlVariableDecl) {
//                
//                enterSpecsForBinaryFields(c,(JmlVariableDecl)t);
//
//            }
//        }
//    } finally {
//        env = prevenv;
//        log.useSource(prev);
//    }
//        
//    }

//    /** This creates the specifications structures for a binary class.  We have
//     * the list of lists of specification declarations owned by the parent of
//     * 'csymbol' from which we extract our own declarations.
//     * @param csymbol the class whose specs we need
//     * @param specsdefs the list of specs declarations from the parent class or compilation unit
//     */
//    // FIXME - rename so as not to be confused with the 'enter' processing of OpenJDK
//    public void enterSpecsForBinaryClasses(ClassSymbol csymbol, List<JCTree> specsdefs) {
//        if (specs.get(csymbol) != null) return; // Already completed
//        
//        if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(0,2,"entering (binary) " + csymbol);
//
//        // FIXME _ fix the following comment
//        // In the following call we (a) find any declarations in the specsdefs 
//        // that match cysmbol by name (b) attach those to csymbol in the 
//        // specs database (c) determine the model types directly nested in
//        // csymbols's specs (d) combine csymbol's various specs into one
//        // combinedTypeSpec (e) get the list of specs defs to use for nested 
//        // classes.  The call also fixes the value of JmlClassDecl.env for 
//        // each JmlClassDecl in newlist
//        
//        // NOTE: specsdefs is not null, but it may be empty for any particular class
//
//        JmlClassDecl matched = matchSpecsToClasses(csymbol,specsdefs);
//
//        // newlist is the list of definition lists that we pass on to 
//        // nested classes
//
//        // Here we recurse over nested classes -- they will already exist as
//        // binary classes, so we just find them and match them to specs.
//        // FIXME - are the nested classes necessarily loaded?
//        for (Symbol nested: csymbol.getEnclosedElements()) {
//            if (nested instanceof ClassSymbol) {
//                enterSpecsForBinaryClasses((ClassSymbol)nested,matched.defs);
//            }
//        }
//
////        // Then enter this class's model types     // FIXME - should we use the combined list?
////        JmlSpecs.TypeSpecs combinedTypeSpecs = specs.getSpecs(csymbol);
////        JmlClassDecl cd = combinedTypeSpecs.refiningSpecDecls;
////        if (cd != null) {
////            enter.enterModelTypes(cd.typeSpecs.modelTypes,cd.env);
////        }
//
//    }

    /** Complain about a duplicate class. */
    @Override
    protected void duplicateClass(DiagnosticPosition pos, ClassSymbol c) {
        if (((JmlCheck)chk).noDuplicateWarn) return;
        log.error(pos, "duplicate.class", c.fullname);
    }


    @Override
    public void visitClassDef(JCClassDecl that) {
        // We need to match up classes before calling super.classDefs so that
        // the specs for nested classes can be computed. Nothing else should
        // be done with the specs, however, until the Java class is 'entered'
        // in the visitClassDef call.
        
        JmlClassDecl thattree = (JmlClassDecl)that;
        boolean isSpecForBinary = thattree.toplevel.mode == JmlCompilationUnit.SPEC_FOR_BINARY;
        
        JmlClassDecl specstree;
        JmlClassDecl jmltree;
        ClassSymbol csym = null;
        if (isSpecForBinary) {
            if (env.tree instanceof JmlCompilationUnit) {
                String s = ((JmlCompilationUnit)env.tree).packge.toString();
                if (!s.isEmpty()) s = s + ".";
                s = s + that.name.toString();
                csym = ClassReader.instance(context).classExists(names.fromString(s));
            } else if (env.tree instanceof JmlClassDecl) {
                String s = ((JmlClassDecl)env.tree).sym.flatname + "$";
                s = s + that.name.toString();
                csym = ClassReader.instance(context).classExists(names.fromString(s));
            }
            specstree = thattree;
            specstree.sym = csym;
            jmltree = null;
        } else {
            jmltree = thattree;
            specstree = thattree.specsDecl;
        }

//        if (specstree != null && specstree != jmltree) {
//            JmlCompilationUnit top = specstree.toplevel;
//            for (JCTree t: specstree.defs) {
//                if (t instanceof JmlClassDecl) ((JmlClassDecl)t).toplevel = top;
//            }
//        }
//        
        
        // FIXME - the rest of the method needs review
        
        ClassSymbol cs = csym;
//        {
//            Name flatname = specstree.toplevel.pid == null ? that.name : names.fromString(specstree.toplevel.pid.toString() + "." + that.name.toString());
//            cs = reader.classExists(flatname);
//            // cs is non-null if the class has already been loaded/entered
//            // cs is null for a source file, with or without a specs file
//        }
        {
            // Do not redo the visitClassDef for binary loading, when the class is read but the specs are not loaded
            
            // Match up specs classes with java classes and adjust for unmatched classes or duplicates
            Env<AttrContext> prevenv = this.env;
            if (specstree != null) {
                // Attaches specs tree from second list at classdecl.specsDecls for each classdecl in the first list
                // Matching classes has to come before visitClassDef because we need to filter out any non-Java class declarations
                // but we cannot add JML classes here because we don't have a class symbol yet
                that.defs = matchClasses(that.defs, specstree.defs, thattree.source().toString());
            }
            if (cs == null) { 
                if (isSpecForBinary) ((JmlCheck)chk).noDuplicateWarn = true;
                super.visitClassDef(that); // Uses this.env
                if (isSpecForBinary) ((JmlCheck)chk).noDuplicateWarn = false;
                if (that.sym == null) {
                    log.error("jml.internal", "Unexpected null class symbol after processing class " + that.name);
                    return;
                }
            } else {
                that.sym = cs;
                cs.completer = memberEnter;
                chk.checkFlags(thattree.pos(), thattree.mods.flags, cs, thattree); // Do not overwrite flags in the binary
                cs.sourcefile = thattree.sourcefile;
                //cs.members_field = new Scope(cs); // DO not overwrite the fields that are in the binary

                Scope enclScope = enterScope(env);
                enclScope.enter(cs);

             }

            Env<AttrContext> localEnv = classEnv(that, env); // FIXME - we might well need this, but classEnv(that,env) fails for loading secs of binary classes
            typeEnvs.put(that.sym, localEnv);
            thattree.env = localEnv;
                // We are entering a class within specification file for a binary load
                // So enter any nested classes within the class we have been entering
                // classEnter(that.defs, typeEnvs.get(cs)); // FIXME - no environment stored
//            }
        }
        
        if (specstree != null) {
            checkAndEnterTypeParameters(that.sym, specstree, null);
        }

        
        // Set the sym and env fields of the classes
        
        {
            Env<AttrContext> localEnv = getEnv(that.sym);
            thattree.env = localEnv;
            if (jmltree != null) {
                jmltree.env = localEnv;
            }
            if (specstree != null) {
                specstree.sym = that.sym;
                specstree.env = localEnv;
            }
        }

       
        {
            JmlSpecs.TypeSpecs tsp = specs.combineSpecs(that.sym,jmltree,specstree);
            if (jmltree != null) jmltree.typeSpecs = tsp;
            if (specstree != null) specstree.typeSpecs = tsp;
        }

    }
    


    // FIXME - unify the recording of empty specs with default specs??
    public void recordEmptySpecs(ClassSymbol csymbol) {
        // TODO - change this if we store JML specs in binary files - then could get annotation information from the symbol
        JmlSpecs.TypeSpecs typespecs = new JmlSpecs.TypeSpecs(csymbol, csymbol.sourcefile, JmlTree.Maker.instance(context).Modifiers(csymbol.flags(),List.<JCTree.JCAnnotation>nil()), null);
        specs.putSpecs(csymbol,typespecs);
        // FIXME - should we be checking for members_field being null? or should we allow completing to proceed?
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

    /** The net result of this call is that all classes, including secondary and nested classes (but not local classes)
     * defined in the given list of source code compilation units are created:
     *    a symbol is defined, 
     *    a typespecs structure is created and initialized with class-level annotations,
     *    for each class the JmlClassDecl.specsDecls field is filled in with the JmlClassDecl for the specifications (if any) 
     * But no members other than call members are processed.
     * Note that the compilation units in the argument list are all JmlCOmpilationUnits; the
     * tree.specsCompilationUnit field is filled in either with a reference to the same java source compilation unit or to the
     * specs compilation unit obtained by parsing the corresponding .jml file.
     * are created: a symbol is defined
     * 
     * @param trees the parse trees coming from the user-specified list of
     * files to process
     */
    @Override
    public void main(List<JCCompilationUnit> trees) {
        super.main(trees);
    }
    

}
