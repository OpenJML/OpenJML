/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.comp;


import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.JmlInternalError;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.code.Type.TypeVar;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;

/**  FIXME - revise this
 * This class extends Enter, which has the job of creating symbols for all the
 * types mentioned in a set of parse trees. JmlEnter adds to that functionality
 * to create symbols for all JML types (i.e., model classes) that are present in
 * the parse trees.  In addition it links each class declaration to declarations
 * containing that class's specifications.
 * <P>
 * JmlEnter expects that a compilation unit knows its specification files. It
 * walks those specification files, matching classes in the specification file
 * to the corresponding classes in the Java file, making links from the Java
 * classes to their specifications.  JmlEnter also expects that the parse 
 * tree contains JmlClassDecl nodes instead of JCClassDecl nodes, even where
 * no additional specs are present.
 * <P>
 * Note that the java file may contain JML declarations.  However, this may well
 * be an incomplete set of declarations.  So we ignore JML declarations in the
 * Java file and only deal with those in the specification sequence; the specs
 * sequence may contain the Java file as one (or the only one) of its 
 * members, in which case the specifications are dealt with in that context.
 * <P>
 * The process of entering a CU does these things:
 * <UL>
 * <LI> packages are completed by entering all the classes in the package
 * (TODO - are these then parsed? just entered into a symbol table?)
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
/*
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

    /** This is just used to communicate between levels of visit calls */
    protected ListBuffer<List<JCTree>> currentParentSpecList;
    
    public java.util.List<Env<AttrContext>> binaryMemberTodo = new LinkedList<Env<AttrContext>>();

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
        
        // Attach specification classes to the Java declarations
        if (jmltree.specsCompilationUnit != null) {
            for (JCTree t: tree.defs) {
                if (t instanceof JmlClassDecl) ((JmlClassDecl)t).toplevel = jmltree;
            }
            for (JCTree t: jmltree.specsCompilationUnit.defs) {
                if (t instanceof JmlClassDecl) ((JmlClassDecl)t).toplevel = jmltree.specsCompilationUnit;
            }
            matchClasses(tree.defs, jmltree.specsCompilationUnit.defs, jmltree.parsedTopLevelModelTypes);
        }
        
        // Then do all the regular Java registering of packages and types
        super.visitTopLevel(jmltree);

        if (jmltree.specsCompilationUnit == null) {
            // If there are no specs files we enter this branch
            // This might be because we are just processing an individual spec
            // file for a binary class
            currentParentSpecList = null;


        } else {

            // FIXME - explain what we are doing here
            
            ListBuffer<List<JCTree>> prev = currentParentSpecList;
            currentParentSpecList = new ListBuffer<List<JCTree>>();
            {
                JmlCompilationUnit jcu = jmltree.specsCompilationUnit; 
                jcu.packge = jmltree.packge; // FIXME - should we check that the packages are the same? why is this not set when it is parsed?
                currentParentSpecList.append(jcu.defs);
                Env<AttrContext> tlenv = topLevelEnv(jcu);
                for (JCTree t: jcu.defs) {
                    if (t instanceof JmlClassDecl) ((JmlClassDecl)t).env = tlenv; // FIXME - is this the best place for this?
                }
            }
            
            currentParentSpecList = prev;

            // It appears these are already checked and flagged
//            // Check for unmatched top-level JML types
//            for (List<? extends JCTree> list : newlist) {
//                for (JCTree t: list) {
//                    // The sym field being tested here was set in visitClassDef
//                    // when a specification declaration was attached to its
//                    // Java counterpart
//                    if (t instanceof JmlClassDecl && ((JmlClassDecl)t).sym == null) {
//                        JmlClassDecl cd = (JmlClassDecl)t;
//                        JavaFileObject prevv = log.useSource(cd.source());
//                        log.error(t.pos,"jml.orphan.jml.toplevel.class.decl",cd.name,jmltree.sourcefile);
//                        log.useSource(prevv);
//                    }
//                }
//            }

            
            // Then add in any top-level model types
            // FIXME - do we really need specsTopLevelModelTypes - same as typeSpecs.modelTypes, no?
            jmltree.specsTopLevelModelTypes = addTopLevelModelTypes(jmltree.packge,jmltree.specsCompilationUnit);
            
            currentParentSpecList = prev;

        }
        if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(0,2,"  completed entering " + jmltree.sourcefile.getName());
    }
    
    public void matchClasses(List<JCTree> defs, List<JCTree> specsDefs, Collection<JmlClassDecl> modelTypesList) {
        for (JCTree t: specsDefs) {
            if (!(t instanceof JmlClassDecl)) continue;
            JmlClassDecl specsClass = (JmlClassDecl)t;
            // The declaration 'specsClass' is in a specification file.
            // We need to find the Java declaration that it matches
            // There must be one, and there should only be one declaration in the specsDefs list
            // that matches a particular java declaration.
            // A Java declaration need not have a match
            Name name = specsClass.getSimpleName();
            JmlClassDecl matched = null;
            JavaFileObject javaSource = null;
            for (JCTree tt: defs) {
                if (!(tt instanceof JmlClassDecl)) continue;
                JmlClassDecl def = (JmlClassDecl)tt;
                javaSource = def.source();
                if (name.equals(def.getSimpleName())) {
                    matched = specsClass;
                    if (def.specsDecls == null) {
                        def.specsDecls = specsClass;
                    } else {
                        JavaFileObject prev = log.useSource(specsClass.source());
                        log.error(matched.pos,"jml.duplicate.jml.class.decl",matched.name);
                        log.error(def.specsDecls.pos,"jml.associated.decl.cf",
                        		utils.locationString(matched.pos));
                        log.useSource(prev);
                    }
                }
            }
            if (matched == null) {
                // Don't report the error if the class is model
                
                JavaFileObject prevv = log.useSource(specsClass.source());
                if (true) {
                    log.error(specsClass.pos,
                            "jml.orphan.jml.toplevel.class.decl",
                            specsClass.name,javaSource);
                } else {
                    log.error(specsClass.pos,
                            "jml.orphan.jml.class.decl",
                            specsClass.name,javaSource);

                }
                log.useSource(prevv);
                
                // This specification file is not matched, so it is like a
                // model class declaration. Pretend it is one.
                
                modelTypesList.add(specsClass);
            }
        }
    }
    
    @Override
    public void visitClassDef(JCClassDecl that) {
        // We need to match up classes before calling super.classDefs so that
        // the specs for nested classes can be computed. Nothing else should
        // be done with the specs, however, until the Java class is 'entered'
        // in the visitClassDef call.
        
        JmlClassDecl jmltree = (JmlClassDecl)that;
        
        for (JCTree t: that.defs) {
            if (t instanceof JmlClassDecl) ((JmlClassDecl)t).toplevel = jmltree.toplevel;
        }
        
        if (jmltree.specsDecls != null) {
            JmlClassDecl parent = jmltree.specsDecls;
            for (JCTree t: parent.defs) {
                if (t instanceof JmlClassDecl) ((JmlClassDecl)t).toplevel = parent.toplevel;
            }
            matchClasses(that.defs, jmltree.specsDecls.defs, jmltree.typeSpecs.modelTypes);
        }
        
        super.visitClassDef(that);
        if (that.sym == null) return; // Bad error in defining the class
        
        Env<AttrContext> localEnv = typeEnvs.get(that.sym);
        jmltree.env = localEnv;
        
        if (jmltree.specsDecls != null) {
            JmlClassDecl specDecl = jmltree.specsDecls;
            if (specDecl != jmltree) {
                specDecl.sym = that.sym;
                specDecl.env = classEnv(specDecl,localEnv); // Requires specDecl.sym to be set
                // FIXME - not sure about the following
                enterTypeParametersForBinary(that.sym,specDecl,localEnv);
            }
        }
        
        List<JmlClassDecl> nestedModelTypes = collectNestedModelTypes(jmltree.specsDecls).toList();
        for (JmlClassDecl modelType: nestedModelTypes) {
            modelType.specsDecls = modelType;
            modelType.toplevel = jmltree.toplevel;
            Utils.instance(context).setJML(modelType.mods); // FIXME - is this already set?
            classEnter(modelType,localEnv);
        }

        JmlClassDecl specsDecl = jmltree.specsDecls;
        Env<AttrContext> localenv = typeEnvs.get(that.sym);
        boolean wasNull = localenv == null;
        JmlClassDecl principalDecl;
        if (localenv != null) {
            // Typically a java class with or without specs
            principalDecl = (JmlClassDecl)localenv.tree;
        } else if (specsDecl != null) {
            // A binary class with specs - JDK did not register an env because
            // there is no Java source.  We put in one for the most refined
            // spec file
            principalDecl = specsDecl;
            localenv = specsDecl.env;
        } else {
            principalDecl = null;
            // This happens for a binary class with no specs for the given type
        }
            // The above is either the java declaration, or (if the class is
            // binary) the most refined specs declaration

        JmlSpecs.TypeSpecs combinedTypeSpecs = specs.getSpecs(that.sym);
        combinedTypeSpecs.refiningSpecDecls = specsDecl;
        if (principalDecl == null) {
            combinedTypeSpecs.modifiers = null;
            combinedTypeSpecs.decl = null;
            combinedTypeSpecs.file = that.sym.sourcefile;
        } else {
            combineSpecs(that.sym,principalDecl);
            principalDecl.typeSpecsCombined = combinedTypeSpecs; // FIXME - is this already the case
        }

    }
    
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        // Visit the rgular tree? FIXME
        that.racexpr.accept(this);
        
    }

//    // This presumes that the overridden method just calls classEnter on each element of defs, with the given context.
//    /** Overrides the parent class to handle the matching of specs to classes and
//     * then to go on to enter all nested Java and model classes.
//     * @param classToMatch the symbol of a class that is a member of a parent class or compilation unit
//     * @param parentDefs the list definitions from a parent class - any class definitions in this list are 
//     * @param classenv the local environment of 'classToMatch'
//     */
//    @Override
//    protected void enterNestedClasses(TypeSymbol classToMatch, List<? extends JCTree> parentDefs, Env<AttrContext> classenv) {
//
//        JmlTree jmltree;
//        
//        ListBuffer<List<JCTree>> specslist = currentParentSpecList;
//        
//        // First associate any specs with the nested classes
//
//        // Call the following even if specslist is null because it also
//        // initialized the type specs relationships
//        ListBuffer<List<JCTree>> newlist = matchSpecsToClasses((ClassSymbol)classToMatch,specslist);
//
//        // newlist is the list of definition lists that we pass on to 
//        // nested classes
//
//        // classEnter can go off to enter other classes as needed; since I don't
//        // know what all can happen in them, we reset currentParentSpecList on
//        // each iteration
//        for (JCTree t: parentDefs) {
//            currentParentSpecList = newlist;
//            classEnter(t,classenv); // actually calls accept on whatever type it receives
//        }
//
//        // Check for extra specs
//
//        if (newlist != null) for (List<? extends JCTree> list : newlist) {
//            for (JCTree t: list) {
//                if (t instanceof JmlClassDecl && ((JmlClassDecl)t).sym == null) {
//                    JmlClassDecl cd = (JmlClassDecl)t;
//                    JavaFileObject prev = log.useSource(cd.source());
//                    log.error(t.pos,"jml.orphan.jml.class.decl",cd.name,classToMatch.flatName());
//                    log.useSource(prev);
//                }
//            }
//        }
//
//
//        JmlSpecs.TypeSpecs combinedTypeSpecs = specs.getSpecs((ClassSymbol)classToMatch);
//
//        JmlClassDecl javaDecl = ((JmlClassDecl)typeEnvs.get(classToMatch).tree);
//        if (javaDecl != null) {
//            combinedTypeSpecs.decl = javaDecl;
//            // FIXME - not sure of the need for the following
//            if (javaDecl.sym.owner instanceof Symbol.MethodSymbol || utils.isJML(javaDecl.mods)) {
//                combinedTypeSpecs.refiningSpecDecls = javaDecl.specsDecls;
//            } else {
//                javaDecl.specsDecls = combinedTypeSpecs.refiningSpecDecls;
//            }
//        }
//
//        // Enter model types
//        enterModelTypes(combinedTypeSpecs.modelTypes,classenv);
//
//        currentParentSpecList = specslist; // Need to replace this for the next nested class
//    }

    /** The arguments to this method are a class symbol and then a list of lists of class body definitions
     * for that class; alternatively, the symbol can be null and the list is a list
     * of the top level defs corresponding to a compilation unit.  The class body
     * definitions come from specification files.  Each specification file that
     * contains a specification for the given class will have a set of definitions
     * for that class; each such set constitutes one element of the list that is
     * the second argument to the method.  [ The argument is a list of list of
     * definitions instead of a list of the parent class declarations so that
     * nested classes and the top-level compilation unit can be treated in the
     * same way.

     * @param classToMatch a class symbol to be matched
     * @param listOfSpecsDefs the class-body definitions from the specifications
     * for the given class or top-level compilation unit
     */
    //@ requires (* this.env must be the local env of the 'classToMatch' *);
    protected ListBuffer<List<JCTree>> matchSpecsToClasses(ClassSymbol classToMatch, ListBuffer<List<JCTree>> listOfSpecsDefs ) {
//        if (classToMatch.name.toString().equals("Content")) {
//            log.noticeWriter.println(classToMatch);
//        }
        // We find the list of matching spec declarations.  We also fix their
        // env fields, but only the ones that match - the others will be matched
        // in a separate call, or ignored.
        ListBuffer<List<JCTree>> newlist = new ListBuffer<List<JCTree>>();
        java.util.List<JmlClassDecl> selflist = new java.util.LinkedList<JmlClassDecl>();
        Name n = classToMatch.name;
        if (listOfSpecsDefs == null) {
            // For these - model and local classes - attach self as specs
            Env<AttrContext> classesenv = typeEnvs.get(classToMatch);
            if (classesenv != null && classesenv.tree != null) {
                listOfSpecsDefs = new ListBuffer<List<JCTree>>();
                listOfSpecsDefs.append(List.<JCTree>of(classesenv.tree));
                ((JmlClassDecl)classesenv.tree).env = classesenv;
            }
        }
        for (List<JCTree> list : listOfSpecsDefs) {
            JmlClassDecl matched = null;
            for (JCTree t: list) {
                if (t instanceof JmlClassDecl) {
                    JmlClassDecl specClass = (JmlClassDecl)t;
                    if (specClass.name.equals(n)) {
                        JavaFileObject prev = log.useSource(specClass.source());
                        if (matched == null) {
                            boolean ok = enterTypeParametersForBinary(classToMatch,specClass,specClass.env);
                            if (ok) {
                                specClass.sym = classToMatch;
                                selflist.add(specClass);
                                newlist.append(specClass.defs);
                                matched = specClass;
                                //specClass.env = classEnv(specClass, specClass.env); // FIXME - is this needed?
           //                     for (JCTree tt: specClass.defs) {
           //                         if (tt instanceof JmlClassDecl) ((JmlClassDecl)tt).env = classEnv((JmlClassDecl)tt,specClass.env);
           //                     }
                            }
                        } else {
                            log.error(specClass.pos,"jml.duplicate.jml.class.decl",specClass.name);
                            log.error(matched.pos,"jml.associated.decl.cf",
                            		utils.locationString(specClass.pos));
                        }
                        log.useSource(prev);
                    }
                }
            }
        }

        // selflist is the list of specification type declarations that are
        // a match to 'classToMatch'

        Env<AttrContext> localenv = typeEnvs.get(classToMatch);
        boolean wasNull = localenv == null;
        JmlClassDecl principalDecl;
        if (localenv != null) {
            // Typically a java class with or without specs
            principalDecl = (JmlClassDecl)localenv.tree;
        } else if (!selflist.isEmpty()) {
            // A binary class with specs - JDK did not register an env because
            // there is no Java source.  We put in one for the most refined
            // spec file
            principalDecl = selflist.get(0);
            localenv = selflist.get(0).env;
        } else {
            principalDecl = null;
            // This happens for a binary class with no specs for the given type
        }
            // The above is either the java declaration, or (if the class is
            // binary) the most refined specs declaration

        JmlSpecs.TypeSpecs combinedTypeSpecs = specs.getSpecs(classToMatch);
        if (principalDecl == null) {
            combinedTypeSpecs.modifiers = null;
            combinedTypeSpecs.decl = null;
            combinedTypeSpecs.file = classToMatch.sourcefile;
        } else {
            combineSpecs(classToMatch,principalDecl);
            principalDecl.typeSpecsCombined = combinedTypeSpecs; // FIXME - is this already the case
        }
        combinedTypeSpecs.refiningSpecDecls = principalDecl;

        // Determine an env for this class if it does not have one
        // We need to have some sort of declaration to do so - we use the
        // most refined specs declaration
        if (wasNull && !selflist.isEmpty()) {
            // This branch will not be taken for normal Java classes, since they have been
            // entered; similarly for model classes
            //log.noticeWriter.println("PUTTING TYPEENV " + classToMatch + " " + typeEnvs.get(classToMatch) + " " + env);
            typeEnvs.put(classToMatch,principalDecl.env);  // Binary classes with specs will have the environment be null;
                                        // we add an environment that holds the specs class declaration so if gets attributed
                                        // FIXME - we should handle this differently when we put in place envs for specs that 
                                        // are different than the envs for the corresponding java class - to handle, for example,
                                        // different lists of import statements
        }

        // newlist is the list of definition lists that we pass on to 
        // nested classes

        return newlist;
    }

    /** This finds all JML types dirdectly nested in the class declarations in
     * the argument.  Any names duplicating class names already found are
     * errored and ignored. 
     * @param selflist An array of class declarations - these are the specification
     * declarations for a common Java class
     * @return A list of JML types (they should be model) directly nested in
     * the elements of the argument
     */
    protected ListBuffer<JmlClassDecl> collectNestedModelTypes(@Nullable JmlClassDecl specs) {
        ListBuffer<JmlClassDecl> collected = new ListBuffer<JmlClassDecl>();
        if (specs == null) return collected;
        HashSet<Name> names = new HashSet<Name>();
        JmlClassDecl jcd = specs; 
        {  // this order or reverse order? FIXME
            for (JmlClassDecl mdecl: jcd.typeSpecs.modelTypes) {
                if (!names.add(mdecl.name)) {
                    // already contains this name
                    JavaFileObject prev = log.useSource(mdecl.source());
                    try { log.error(mdecl.pos,"jml.duplicate.jml.class.decl",mdecl.name); }
                    finally { log.useSource(prev); }
                } else {
                    collected.append(mdecl);
                }
            }
        }
        return collected;
    }

    /** Enters a list of model types
     * @param list a list of model types (all nested in a common class)
     * @param env the enclosing Env to use to enter these model classes
     */
    protected void enterModelTypes(ListBuffer<JmlClassDecl> list, Env<AttrContext> env) {
        for (JmlClassDecl classDecl: list) {
            currentParentSpecList = null;
            classEnter(classDecl,env);
        }
    }

//    /** This method is overridden in order to, along with doing the super
//     * class functionality, register any model classes declared as nested within
//     * the specifications for the argument.
//     */
//    @Override
//    public void visitClassDef(JCClassDecl javaClassDeclaration) {
//        //log.noticeWriter.println("VISITING " + javaClassDeclaration.name);
//        super.visitClassDef(javaClassDeclaration);
//        // Calls enterNestedClasses after determining its own symbol,
//        // before doing its subclasses
//    }

//    Type classEnter(JCTree tree, Env<AttrContext> env) {
//        // classEnter can be called with a compilation unit or a class declaration
//        // it should always be a Jml tree node, however
//        if (tree instanceof JmlClassDecl) {
//            JmlClassDecl jmltree = (JmlClassDecl)tree;
//            for (JCTree nested: jmltree.defs) {
//                if (!(nested instanceof JmlClassDecl)) continue;
//                JmlClassDecl nestedClass = (JmlClassDecl)nested;
//                java.util.List<JmlClassDecl> nestedSpecsList = new LinkedList<JmlClassDecl>();
//                for (JmlClassDecl parentSpecsList: jmltree.specsDecls) {
//                    boolean found = false;
//                    for (JCTree nestedSpecs: parentSpecsList.defs) {
//                        if (!(nestedSpecs instanceof JmlClassDecl)) continue;
//                        JmlClassDecl nestedSpecsClass = (JmlClassDecl)nestedSpecs;
//                        if (nestedSpecsClass.name.equals(nestedClass.name)) {
//                            // a match
//                            if (!found) {
//                                nestedSpecsList.add(nestedSpecsClass);
//                                found = true;
//                            } else {
//                                // duplicate nested class in the same compilation unit
//                            }
//                        }
//                    }
//                }
//                nestedClass.specsDecls = nestedSpecsList;
//            }
//        } else if (tree instanceof JmlCompilationUnit) {
//            JmlCompilationUnit jmltree = (JmlCompilationUnit)tree;
//            for (JCTree nested: jmltree.defs) {
//                if (!(nested instanceof JmlClassDecl)) continue;
//                JmlClassDecl nestedClass = (JmlClassDecl)nested;
//                java.util.List<JmlClassDecl> nestedSpecsList = new LinkedList<JmlClassDecl>();
//                // There is just one item in the jmltree.specsCompilationUnit, so we do not need a loop here
//                if (jmltree.specsCompilationUnit != null) {
//                    boolean found = false;
//                    for (JCTree nestedSpecs: jmltree.specsCompilationUnit.defs) {
//                        if (!(nestedSpecs instanceof JmlClassDecl)) continue;
//                        JmlClassDecl nestedSpecsClass = (JmlClassDecl)nestedSpecs;
//                        if (nestedSpecsClass.name.equals(nestedClass.name)) {
//                            // a match
//                            if (!found) {
//                                nestedSpecsList.add(nestedSpecsClass);
//                                found = true;
//                            } else {
//                                // duplicate nested class in the same compilation unit
//                            }
//                        }
//                    }
//                }
//                nestedClass.specsDecls = nestedSpecsList;
//            }
//        }
//        return super.classEnter(tree,env);
//    }

    /** Enters top-level model types in the specs sequence of the argument
     * 
     * @param packageSymbol The symbol of the package that owns this top-level declaration
     * @param specCompilationUnit The compilation unit holding specs to be searched for model types
     */
    public List<JmlClassDecl> addTopLevelModelTypes(PackageSymbol packageSymbol, JmlCompilationUnit specCompilationUnit) {


        ListBuffer<JmlClassDecl> specsTopLevelModelTypes = new ListBuffer<JmlClassDecl>();

        // We process all the top level model types here.  If there are duplicate
        // names, errors will be issued when the system tries to add the second
        // duplicate to the symbol table.  Model classes are expected to be
        // self-contained - there is no refinement across a specs sequence,
        // and this code does not attempt to combine material from different
        // declarations with the same name (instead, an error about duplicate
        // names is produced).
        // TODO - this does not reflect name lookup issues when there are multiple specification files
        {
            currentParentSpecList = new ListBuffer<List<JCTree>>();
            currentParentSpecList.append(specCompilationUnit.defs);  // Model types are their own specification
            specCompilationUnit.packge = packageSymbol;
            Env<AttrContext> tlenv = topLevelEnv(specCompilationUnit);
            env = tlenv;
            JavaFileObject prevSource = log.useSource(specCompilationUnit.sourcefile);
            for (JmlClassDecl specTypeDeclaration: specCompilationUnit.parsedTopLevelModelTypes) {
                if (utils.isJML(specTypeDeclaration.mods)) {
                    // This is a declaration made in a JML comment
                    // If it isn't actually annotated as 'model, 
                    // an error will be issued during modifier checking that is part of type checking

                    // Model class declarations are their own specification
                    specTypeDeclaration.specsDecls =specTypeDeclaration;
                    currentParentSpecList = new ListBuffer<List<JCTree>>();
                    currentParentSpecList.append(List.<JCTree>of(specTypeDeclaration));
                    
                    classEnter(specTypeDeclaration,tlenv);  // Does nested classes as well
                    // The above associated a new symbol with specTypeDeclaration; sourcefile, toplevel were already done
                    // Through enterNestedClasses all of the specs infrastructure is set up
                    specTypeDeclaration.env = classEnv(specTypeDeclaration,tlenv);

                    specsTopLevelModelTypes.append(specTypeDeclaration);
                } else {
                    log.warning("jml.internal.notsobad","Unexpected non-JML type declaration is in the list of parsed model types (ignored)");
                }
            }
            log.useSource(prevSource);
        }
//        if (packageSymbol instanceof ClassSymbol) {
//            specs.getSpecs((ClassSymbol)packageSymbol).modelTypes = specsTopLevelModelTypes;
//        }
        return specsTopLevelModelTypes.toList();
    }


    /** This method creates a combined type specs structure for the given class symbol.
     * It uses the list in getSpecs(sym).refiningSpecDecls as the list of
     * specs to combine.  If that list is empty or null, it will use the second argument
     * as the single source of specs.  It also presumes that the second argument,
     * if not null, is the java or primary specs declaration file and sets the
     * specTypeDecl.typeSpecsCombined field to the combined result, as well as
     * storing the combined type specs so that it is retrieved by specs.getSpecs()
     * @param sym
     * @param specTypeDecl
     */
    protected void combineSpecs(ClassSymbol sym, JmlClassDecl specTypeDecl) {
        JmlSpecs.TypeSpecs tspecs = specs.getSpecs(sym);

        // tspecs is to be the combinedSpecs
        // It already has: 
        //      csymbol, 
        //      refiningSpecDecls
        //      file
        // Also, if tspecs.decl is non-null, it already has tspecs.decl.typeSpecs == tspecs;
        // Not set here:
        //      modelFieldMethods
        //      checkInvariantDecl, checkStaticInvariantDecl (RAC related)

        if (tspecs.decl != null && specTypeDecl != tspecs.decl ) {
            log.noticeWriter.println("PRECONDITION FALSE IN COMBINESPECS " + sym + " " + (specTypeDecl != null) + " " + (tspecs.decl != null));
        }

        JmlSpecs.TypeSpecs nspecs = null;
        if (tspecs.refiningSpecDecls != null) {
            nspecs = tspecs.refiningSpecDecls.typeSpecs;  // first or last - current usage there is only ever one
        } else if (specTypeDecl != null) {
            // This can happen when we are using source files for runtime Utils classes, which probably happens
            // only in test scenarios
            nspecs = specTypeDecl.typeSpecs;
        } else {
            String msg = "Unexpected control branch taken in JmlEnter.combineSpecs";
            log.error("jml.internal",msg);
            throw new JmlInternalError(msg);
        }

        // FIXME - do not bother copying if there is only one file
        // TODO - do a proper combination of these over the stuff in refiningSpecDecls
        // tspecs.csymbol is already set, should be same as nspecs.csymbol
        // modelFieldMethods, checkInvariantDecl, checkStaticInvariantDecl not relevant yet
        //tspecs.file = nspecs.file;
        tspecs.blocks = nspecs.blocks;
        tspecs.clauses = nspecs.clauses;
        tspecs.fields = nspecs.fields;
        tspecs.methods = nspecs.methods;
        tspecs.modifiers = nspecs.modifiers;
        tspecs.modelTypes = collectNestedModelTypes(tspecs.refiningSpecDecls);

        tspecs.initializerSpec = nspecs.initializerSpec;
        tspecs.staticInitializerSpec = nspecs.staticInitializerSpec;
        tspecs.decl = specTypeDecl;
        if (specTypeDecl != null) {
            specTypeDecl.specsDecls = tspecs.refiningSpecDecls;
            specTypeDecl.typeSpecsCombined = tspecs;
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

    /** Is called after parsing the specs for a binary type, to do what we do for
     * source type via enter.main().  However, for binary types we do not need to
     * enter all the classes in the database; we simply need to match up the
     * declarations in the spec file with those in the binary, but do need to
     * enter any specification (model) classes.
     * 
     * @param csymbol the ClassSymbol of the binary type
     * @param speccu The parse tree of the specifications for the binary type
     * (including the specifications for any secondary types that would have been in the same source
     * compilation unit)
     */
    public void enterSpecsForBinaryClasses(ClassSymbol csymbol, JmlCompilationUnit speccu) {
    	if (utils.jmlverbose >= Utils.JMLDEBUG)  log.noticeWriter.println("ENTER TOPLEVEL (BINARY) " + csymbol);

        // First do all the linking of java types to specifications
        // Since we do not have a Java compilation Unit to walk down, we will
        // enter the model classes as well
        if (speccu == null) {
            // If there are no specs, we still make an (empty) record of that
            // fact in the specs database, so that we don't go looking again.
            recordEmptySpecs(csymbol);
            return;
        }

        Env<AttrContext> tlenv = topLevelEnv(speccu);
        setSymbolAndEnv(speccu.defs,tlenv,csymbol); // FIXME: This only takes care of the primary class and its nested classes

        ListBuffer<List<JCTree>> specslist = new ListBuffer<List<JCTree>>();
        if (speccu != null) {
            specslist.append(speccu.defs);
            //jcu.accept(this); // add in imports
            for (JCTree t: speccu.defs) {
                if (t instanceof JmlClassDecl) {
                    JmlClassDecl jtree = (JmlClassDecl)t;
                    if (jtree.name.equals(csymbol.name)) {
                        jtree.sym = csymbol; // FIXME - what about secondary types
                        jtree.env = classEnv(jtree,tlenv);
                    }
                }
            }
        }

        // Search for secondary types
        HashMap<Name,JmlClassDecl> names = new HashMap<Name,JmlClassDecl>();
        for (List<JCTree> tree : specslist) {
            for (JCTree t: tree) {
                if (t instanceof JmlClassDecl) {
                    Name n = ((JmlClassDecl)t).name;
                    if (names.get(n) == null) names.put(n,(JmlClassDecl)t);
                }
            }
        }

        // Do the primary type
        enterSpecsForBinaryClasses(csymbol,specslist);
        names.remove(csymbol.name);

        // Do any secondary types
        for (Name n: names.keySet()) {
            // Need to look up symbol for name n in the package of csymbol
            Scope.Entry e = csymbol.owner.members().lookup(n);
            while (e.sym != null && !(e.sym instanceof ClassSymbol)) { e = e.next(); }
            Symbol nsymbol = e.sym;
            if (nsymbol instanceof ClassSymbol) enterSpecsForBinaryClasses((ClassSymbol)nsymbol,specslist);
            else {
                JavaFileObject prev = log.useSource(names.get(n).source());
                log.error(names.get(n).pos,"jml.unmatched.secondary.type",n);
                log.useSource(prev);
            }
        }
        
        // Do any top-level model types
        if (speccu != null) {
            for (JmlClassDecl modelType: speccu.parsedTopLevelModelTypes) {
                classEnter(modelType,topLevelEnv(speccu));
            }
        }

        // Create a todo item for each toplevel class that needs processing
        // but only for those in the first item of the specsSequence
        // If the specsSequence is empty, there is nothing to do anyway
        
        // FIXME _ we should perhaps use the consolidated specifications 
        // Here we need to avoid using unmatched specs
        if (speccu != null) {
            for (JCTree t: speccu.defs) {
                if (t instanceof JmlClassDecl && ((JmlClassDecl)t).sym != null && ((JmlClassDecl)t).env != null) {
                    binaryMemberTodo.add(((JmlClassDecl)t).env);
                    //log.noticeWriter.println("APPENDING TO BINARYENVS " + specsSequence.get(0).sourcefile);
                    binaryEnvs.append(speccu);
                }
            }
        }

    }
    
    /** Finds any JmlClassDecl objects in the defs list that have a name matching csymbol and
     * (a) sets the .sym field to csymbol and creates a class env object based on the given env.
     * @param defs
     * @param env
     * @param csymbol
     */
    public void setSymbolAndEnv(List<JCTree> defs, Env<AttrContext> env, ClassSymbol csymbol) {
        for (JCTree t: defs) {
            if (t instanceof JmlClassDecl) {
                JmlClassDecl jmltree = (JmlClassDecl)t;
                if (jmltree.name.equals(csymbol.name)) {
                    jmltree.sym = csymbol;
                    jmltree.env = classEnv(jmltree,env);
                    for (Symbol nested: csymbol.getEnclosedElements()) {
                        if (nested instanceof ClassSymbol) setSymbolAndEnv(jmltree.defs,jmltree.env,(ClassSymbol)nested);
                    }
                }
            }
        }
    }

    /** This creates the specifications structures for a binary class.  We have
     * the list of lists of specification declarations owned by the parent of
     * 'csymbol' from which we extract our own declarations.
     * @param csymbol the class whose specs we need
     * @param specsdefs the list of specs declarations from the parent class or compilation unit
     */
    protected void enterSpecsForBinaryClasses(ClassSymbol csymbol, ListBuffer<List<JCTree>> specsdefs) {
        if (specs.get(csymbol) != null) return; // Already completed
        
        if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(0,2,"entering (binary) " + csymbol);

        // In the following call we (a) find any declarations in the specsdefs 
        // that match cysmbol by name (b) attach those to csymbol in the 
        // specs database (c) determine the model types directly nested in
        // csymbols's specs (d) combine csymbol's various specs into one
        // combinedTypeSpec (e) get the list of specs defs to use for nested 
        // classes.  The call also fixes the value of JmlClassDecl.env for 
        // each JmlClassDecl in newlist
        
        // NOTE: specsdefs is not null, but it may be empty for any particular class
        // specsSequence is not null and not empty

        ListBuffer<List<JCTree>> newlist = matchSpecsToClasses(csymbol,specsdefs);

        // newlist is the list of definition lists that we pass on to 
        // nested classes

        // In enterNestedClasses() we need to enter all of the classes themselves
        // and then recurse to nested classes;  here however, the class is already
        // entered - entering it again is a no-op but won't recurse to the nested
        // classes either.  Hence we need to do that recursion ourselves here.

        // Recurse over nested classes (which do not inclulde model classes yet)
        for (Symbol nested: csymbol.getEnclosedElements()) {
            if (nested instanceof ClassSymbol) {
                enterSpecsForBinaryClasses((ClassSymbol)nested,newlist);
            }
        }

        // Then enter this class's model types     // FIXME - should we use the combined list?
        JmlSpecs.TypeSpecs combinedTypeSpecs = specs.getSpecs(csymbol);
        JmlClassDecl cd = combinedTypeSpecs.refiningSpecDecls;
        if (cd != null) {
            enterModelTypes(cd.typeSpecs.modelTypes,cd.env);
        }

}

//    /** Checks that the inheritance relationships in the specification
//     * declaration match those in the class.  Presumes all types have been
//     * entered and have symbols assigned.
//     * @param specTypeDeclaration the spec declaration to check
//     */
//    private void checkSpecInheritance(JmlClassDecl specTypeDeclaration) {
//
//        ClassSymbol matchingCSymbol = specTypeDeclaration.sym;
//        
//        // Check that the package is correct
//        if (specTypeDeclaration.toplevel.packge != matchingCSymbol.packge()) {
//            log.error(specTypeDeclaration.toplevel.pid.pos,"jml.mismatched.package",  // TODO _ test this
//                    specTypeDeclaration.toplevel.packge,matchingCSymbol.packge());
//        }
//        // FIXME - use type comparison here
//        
//        // Check that the specification has the correct super types
//        if (!matchingCSymbol.equals(syms.objectType.tsym) && !matchingCSymbol.isInterface()) {
//            JCTree sup = specTypeDeclaration.extending;
//            Type suptype = matchingCSymbol.getSuperclass();
//            Name s = suptype.tsym.getQualifiedName();
//            if (sup == null && !suptype.tsym.equals(syms.objectType.tsym)) {
//                log.error("jml.missing.spec.superclass",matchingCSymbol.getQualifiedName().toString(),s.toString());
//            } else if (sup instanceof JCTree.JCIdent) {
//                if ( s != null && !s.toString().endsWith(((JCTree.JCIdent)sup).name.toString()) ) {
//                    log.error("jml.incorrect.spec.superclass",matchingCSymbol.getQualifiedName().toString(),((JCTree.JCIdent)sup).name.toString(),s.toString());
//                }
//            } else if (sup instanceof JCTree.JCFieldAccess) {
//                if ( !s.toString().endsWith(((JCTree.JCFieldAccess)sup).name.toString()) ) {
//                    log.error("jml.incorrect.spec.superclass",matchingCSymbol.getQualifiedName().toString(),((JCTree.JCFieldAccess)sup).name.toString(),s.toString());
//                }
//            }
//        }
//
//        // Check the interfaces
//
//        List<Type> interfaces = matchingCSymbol.getInterfaces();
//        Collection<Type> copy = new LinkedList<Type>();
//        for (Type t: interfaces) copy.add(t);
//
//        for (JCTree.JCExpression e : specTypeDeclaration.implementing) {
//            // FIXME - should match types
//            Name nm = null;
//            if (e instanceof JCTree.JCIdent) {
//                nm = ((JCTree.JCIdent)e).name;
//            } else if (e instanceof JCTree.JCFieldAccess) {
//                nm = ((JCTree.JCFieldAccess)e).name;
//            } else if (e instanceof JCTree.JCTypeApply){
//                JCTree.JCExpression ee = e;
//                while (ee instanceof JCTree.JCTypeApply) ee = ((JCTree.JCTypeApply)ee).clazz;
//                if (ee instanceof JCTree.JCIdent) nm = ((JCTree.JCIdent)ee).name;
//                if (ee instanceof JCTree.JCFieldAccess) nm = ((JCTree.JCFieldAccess)ee).name;
//            } else {
//                log.noticeWriter.println("UNSUPPORTED IMPLEMENTS TYPE (" + matchingCSymbol + "): " + e.getClass() + " " + e);
//                // ERROR - FIXME
//            }
//            if (nm != null) {
//                boolean found = false;
//                java.util.Iterator<Type> iter = copy.iterator();
//                while (iter.hasNext()) {
//                    Name nmm = iter.next().tsym.getQualifiedName();
//                    if (nmm.toString().contains(nm.toString())) {
//                        iter.remove();
//                        found = true;
//                        break;
//                    }
//                }
//                if (!found) {
//                    log.error("jml.missing.spec.interface",matchingCSymbol.getQualifiedName().toString(),nm.toString());
//                }
//            }
//        }
//        for (Type t: copy) {
//            if (t.toString().equals("java.lang.annotation.Annotation") && matchingCSymbol.isInterface()) continue;
//            log.error("jml.unimplemented.spec.interface",matchingCSymbol.getQualifiedName().toString(),t.toString());
//        }
//
//        // FIXME - should do thte above from resolved symbols
//        // FIXME - need to check modifiers
//    }

    /** Compares the type parameters for the Java class denoted by csym and the 
     * type parameters in the given type declaration (typically from a 
     * specification file), in the context of the given name environment.
     * Issues error messages if types or names do not match; attributes
     * the types; returns false if there were errors.
     * @param csym the class whose local env we are manipulating
     * @param specTypeDeclaration the declaration of the class in a specification file
     * @param classEnv the environment which is modified by the addition of any type parameter information
     */
    public boolean enterTypeParametersForBinary(ClassSymbol csym, JmlClassDecl specTypeDeclaration, Env<AttrContext> classEnv) {
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
            classEnter(specTV,localEnv);
            //enterScope.enter(javaTV.tsym);
        }
        for (int i = nn; i<numSpecTypeParams; i++) {
            JCTree.JCTypeParameter specTV = specTypeDeclaration.typarams.get(i);
            classEnter(specTV,localEnv);
//            JmlAttr.instance(context).attribType(specTV,localEnv);
        }
        // FIXME need to check that the types have the same bounds
        return result;
        //log.noticeWriter.println(" LOCAL ENV NOW " + localEnv);
    }

 
    /** This overrides the parent class mathod so that we allow file names
     * with spec extensions, not just .java 
     * 
     * @param c the class the file is associated with
     * @param env the Env object representing the filename 
     */
    @Override
    public boolean classNameMatchesFileName(ClassSymbol c, // DRC - changed from private to public
            Env<AttrContext> env) {
        String classname = c.name.toString();
        JavaFileObject jfo = env.toplevel.sourcefile;
        if (jfo.getKind() == JavaFileObject.Kind.SOURCE) return super.classNameMatchesFileName(c, env);
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
        // FIXME - these do not get entered? What if there are model classes in the binary specs?
        for (JmlCompilationUnit jcu: binaryEnvs) {
            trees.append(jcu);
        }
        binaryEnvs.clear();
    }

}
