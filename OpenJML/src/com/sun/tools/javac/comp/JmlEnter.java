package com.sun.tools.javac.comp;

import java.util.LinkedList;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlInternalError;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;

import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.code.Type.TypeVar;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

/**
 * This class extends Enter, which has the job of creating symbols for all the
 * types mentioned in a set of parse trees. JmlEnter adds to that functionality
 * to create symbols for all JML types (e.g., model classes) that are present in
 * the parse trees.
 * <P>
 * JmlEnter expects that a compilation unit knows its specification files. It
 * walks those specification files, matching classes in the specification file
 * to the corresponding classes in the Java file, making links from the Java
 * classes to their specifications.
 * <P>
 * Note that the java file may contain JML declarations.  However, this may well
 * be an incomplete set of declarations.  So we ignore JML declarations in the
 * Java file and only deal with those in the specification sequence; the specs
 * sequence may well contain the Java file as one (or the only one) of its 
 * members, in which case it is dealt with in that context.
 * <P>
 * The process of entering a CU does these things:
 * <UL>
 * <LI> packages are completed by entering all the classes in the package
 * (FIXME - are these then parsed? just entered into a symbol table?)
 * <LI> classes: a class symbol is defined; a completer is attached to the symbol
 * <LI> type parameters: recorded in the Env associated with the class
 * <LI> initiates the MemberEnter processing, which adds the members of a class
 * to its Env (its scope); this can have the side-effect of uncovering more
 * classes that need to be parsed and entered
 * </UL>
 * Also typeEnvs is a map that gives an Env<AttrContext> object for each class,
 * to be used when attributing types and resolving references within the class.
 * The enter process creates and stores this Env.
 * 
 * @author David Cok
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
            public Enter make() {
                return instance != null ? instance : (instance = new JmlEnter(context));
            }
        });
    }

    /** The context in which this instance was created. */
    Context context;
    
    /** Creates an instance of the JmlEnter tool in the given context; note that
     * any options must be already set in Options prior to creating the tool.
     * @param context
     */
    public JmlEnter(Context context) {
        super(context);
        this.context = context;
    }
    
    // TODO - see if we really need this
    public void remove(Symbol sym) {
        typeEnvs.remove(sym);
    }
    
    /** This method visits the designated compilation unit; first it matches
     * class declarations in the specification files to class declarations in
     * Java; then it calls the super class visitTopLevel method, but during 
     * visiting overriding methods in JmlEnter will be called when visiting
     * class declarations, so that a class can register in the symbol table
     * any model classes that are declared within it.
     */
    public void visitTopLevel(JCCompilationUnit tree) {
        if (!(tree instanceof JmlCompilationUnit)) {
            log.warning("jml.internal.notsobad","Encountered an unexpected JCCompilationUnit instead of a JmlCompilationUnit in JmlEnter.visitTopeLevel");
            super.visitTopLevel(tree);
            return;
        }
        JmlCompilationUnit jmltree = (JmlCompilationUnit)tree;
        modeOfCurrentCU = jmltree.mode;
        if (modeOfCurrentCU == 0) {
            throw new JmlInternalError();
        }

        if (Utils.jmldebug) System.out.println("entering " + jmltree.sourcefile.getName());
        
        if (jmltree.specsSequence == null) {
            // FIXME - when does this happen?
            
            // Then do all the regular Java registering of packages and types
            super.visitTopLevel(jmltree);

        } else {


            // First do all the linking of java types to specifications
            // This can be done just based on name and nesting - no resolution of
            // types is needed
            matchAndLinkSpecClasses(jmltree);
            //if (Utils.jmldebug) System.out.println("ENTER TOPLEVEL - SUPER " + jmltree.sourcefile.getName());
            // Then do all the regular Java registering of packages and types
            // This will recursively call visitClassDef for each java class declaration;
            // visitClassDef will process any linked specs
            super.visitTopLevel(jmltree);
            //if (Utils.jmldebug) System.out.println("ENTER TOPLEVEL - JML " + jmltree.sourcefile.getName());
            // Then add in any top-level model types
            addTopLevelModelTypes(jmltree);
        }
        if (Utils.jmldebug) System.out.println("  completed entering " + jmltree.sourcefile.getName());
    }

    /** Finds top-level model types in the specs sequence of the argument
     * 
     * @param javaCompilationUnit
     */
    public void addTopLevelModelTypes(JmlCompilationUnit javaCompilationUnit) {

        Env<AttrContext> prevEnv = env;
        
        // The env created in super.visitTopLevel is not necessarily saved in typeEnvs,
        // so we create a new Env from scratch
        env = typeEnvs.get(javaCompilationUnit.packge);
        if (env == null) env = topLevelEnv(javaCompilationUnit);  // FIXME - env of the java or the spec CU?
        
        // TODO - we process all the top level model types here; however, there is no
        // check for duplicate names and there is no combining of information from
        // multiple places in the spec sequence
        for (JmlCompilationUnit specCompilationUnit : javaCompilationUnit.specsSequence) {
            JavaFileObject prevSource = log.useSource(specCompilationUnit.sourcefile);
            for (JmlClassDecl specTypeDeclaration: specCompilationUnit.parsedTopLevelModelTypes) {
                if (Utils.isJML(specTypeDeclaration.mods)) {
                    // This is a model declaration
                    // If it isn't, an error gets issued during modifier checking that is part of type checking
                    if (Utils.jmldebug) System.out.println("ADDING " + specTypeDeclaration.name + " AT TOP LEVEL "  + specCompilationUnit.sourcefile.getName());
                    super.visitClassDef(specTypeDeclaration);
                    javaCompilationUnit.specsTopLevelModelTypes.add(specTypeDeclaration);
                    // Model class declarations are their own specification
                    JmlSpecs.instance(context).putSpecs(specTypeDeclaration.sym, // This is being run after sym has been set
                            new JmlSpecs.TypeSpecs(specTypeDeclaration));
                } else {
                    log.warning("jml.internal.notsobad","Unexpected non-model type declaration is in the list of parsed model types (ignored)");
                }
            }
            log.useSource(prevSource);
            env = prevEnv;

        }
    }

    /** This walks over the types in a specification file for a compilation unit,
     * matching and connecting types in the Java compilation unit to the types
     * in the specification; it complains about type declarations in the 
     * specification file that are duplicates or do not have corresponding 
     * types in the Java file.
     * @param javaCompilationUnit the compilation unit to process
     */
    public void matchAndLinkSpecClasses(JmlCompilationUnit javaCompilationUnit) {

        /*@ nullable*/java.util.List<JmlCompilationUnit> specsSequence = javaCompilationUnit.specsSequence;

        // Make a map of class names to declarations for the top-level declarations
        // in the Java compilation unit
        java.util.Map<Name,JmlClassDecl> decls = new java.util.HashMap<Name,JmlClassDecl>();
        for (JCTree t: javaCompilationUnit.defs) {
            if (t instanceof JmlClassDecl) decls.put(((JmlClassDecl)t).name,(JmlClassDecl)t);
        }
        
        // Scan over the specification file and match up all the types
        for (JmlCompilationUnit specCompilationUnit: specsSequence) {

            JavaFileObject prevSource = log.useSource(specCompilationUnit.sourcefile);
            for (JCTree def: specCompilationUnit.defs) {
                // Typically there are imports and type declarations
                if (def instanceof JmlClassDecl) {
                    JmlClassDecl specTypeDeclaration = (JmlClassDecl)def;
                    if (Utils.isJML(specTypeDeclaration.mods)) {
                        // This is a top-level model declaration
                        // but we cannot add it until we have processed the compilation unit
                        // through the super class call.
                        // We should not get here because all of the model declarations
                        // are supposed to have been put into javaCompilationUnit.parsedTopLevelModelTypes
                        log.warning("jml.internal.notsobad","A top-level model type was left in the Java compilation unit AST (ignored)");
                    } else {
                        // This is a Java declaration
                        JmlClassDecl matchingJavaTypeDeclaration = decls.get(specTypeDeclaration.name);
                        if (matchingJavaTypeDeclaration == null) {
                            // There is no Java declaration to match this specification declaration
                            Log.instance(context).error(specTypeDeclaration.pos(),"jml.orphan.jml.toplevel.class.decl",specTypeDeclaration.name,javaCompilationUnit.sourcefile.getName());
                        } else {
                            if (matchingJavaTypeDeclaration.specsDecl != null) {
                                // There has already been a match made to the Java type of the same name
                                Log.instance(context).error(specTypeDeclaration.pos(),"jml.duplicate.jml.class.decl",specTypeDeclaration.name);
                            } else {
                                // Link the Java type to the specification for future easy reference
                                matchingJavaTypeDeclaration.specsDecl = specTypeDeclaration;
                                // The registration in the specs database happens when visiting the class.  
                                // At this point the class Symbol is not yet defined.
                                // Now recursively match up nested types
                                matchAndLinkSpecClasses(matchingJavaTypeDeclaration);
                            }
                        }
                    }
                }
            }
            log.useSource(prevSource);
            break; // Just do the first one  FIXME
        }
    }
    
    // TODO - refactor the above to avoid some duplication
    // TODO - verify that nested model class declarations are either warned about or handled
    
    /** This walks over the types nested in a type declaration,
     * matching and connecting types in the Java declaration to the types
     * in the specification; it complains about type declarations in the 
     * specification file that are duplicates or do not have corresponding 
     * types in the Java type. It expects that the argument will
     * already have its own specsDecl field set to its linked specification.
     * @param javaTypeDeclaration the class declaration to process
     */
    // (javaTypeDeclaration.specsDecl 'matches' javaTypeDeclaration)
    public void matchAndLinkSpecClasses(/*@ non_null */ JmlClassDecl javaTypeDeclaration) {
        JmlClassDecl specTypeDeclaration = javaTypeDeclaration.specsDecl;
        if (specTypeDeclaration == null) return;  // This happens if there are no specifications matching the java declaration
        
        // Make a map of the types nested within this java type.
        java.util.Map<Name,JmlClassDecl> decls = new java.util.HashMap<Name,JmlClassDecl>();
        for (JCTree t: javaTypeDeclaration.defs) {
            if (t instanceof JmlClassDecl) decls.put(((JmlClassDecl)t).name,(JmlClassDecl)t);
        }
        
        for (JCTree specNestedDeclaration: specTypeDeclaration.defs) {
            if (specNestedDeclaration instanceof JmlClassDecl) {
                JmlClassDecl specNestedTypeDeclaration = (JmlClassDecl)specNestedDeclaration;
                JmlClassDecl matchingJavaTypeDeclaration = decls.get(specNestedTypeDeclaration.name);
                if (matchingJavaTypeDeclaration == null) {
                    // There is no Java declaration to match this specification declaration
                    Log.instance(context).error(specNestedTypeDeclaration.pos(),"jml.orphan.jml.class.decl",specNestedTypeDeclaration.name,javaTypeDeclaration.name);
                } else {
                    if (matchingJavaTypeDeclaration.specsDecl != null) {
                        // There has already been a match made to the Java type of the same name
                        Log.instance(context).error(specNestedTypeDeclaration.pos(),"jml.duplicate.jml.class.decl",specNestedTypeDeclaration.name);
                    } else {
                        matchingJavaTypeDeclaration.specsDecl = specNestedTypeDeclaration;
                        // The registration in the specs database happens when visiting the class.  
                        // At this point the class Symbol is not yet defined.
                        matchAndLinkSpecClasses(matchingJavaTypeDeclaration);
                    }
                }
            }
        }
    }
    
    /** This method is overridden in order to, along with doing the super
     * class functionality, register any model classes declared as nested within
     * the specifications for the argument.
     */
    @Override
    public void visitClassDef(JCClassDecl javaClassDeclaration) {
        // Do everything normally done for Java.
        // This includes 'entering' the class (creating a symbol,
        //   setting javaClassDeclaration.sym
        //   setting javaClassDeclaration.sym.sourcefile
        //   creating an Env
        //   recursively entering all nested classes, which recursively calls
        //   this method
        
        // FIXME - this will process any nested model methods in the Java file
        // regardless of whether they are part of the specs sequence
        super.visitClassDef(javaClassDeclaration);
        
        
        JmlClassDecl specsClassDeclaration = ((JmlClassDecl)javaClassDeclaration).specsDecl;
        // TODO - explain the following line, also review 
        if (JmlCompilationUnit.isSpec(modeOfCurrentCU)) specsClassDeclaration = (JmlClassDecl)javaClassDeclaration;
        if (specsClassDeclaration == null) {
            // Record that we found no specs, but that the class has been processed
            JmlSpecs.instance(context).putSpecs(javaClassDeclaration.sym,new JmlSpecs.TypeSpecs((JmlClassDecl)javaClassDeclaration));
            return;
        }
        JmlSpecs.instance(context).putSpecs(javaClassDeclaration.sym,new JmlSpecs.TypeSpecs(specsClassDeclaration));
        
        // Here we handle any classes in the specs of the java class declaration
        // These would be model classes; any non-model classes would be matches to
        // Java classes already entered
        // TODO - I expect we are handling material more than once - any problems from that? can it be avoided?
        for (JCTree specsNestedDeclaration: specsClassDeclaration.defs) {
            if (specsNestedDeclaration instanceof JmlTypeClauseDecl) {
                JmlTypeClauseDecl specsNestedDecl = (JmlTypeClauseDecl)specsNestedDeclaration;
                JCTree specsNestedJmlDecl = specsNestedDecl.decl;
                if (specsNestedJmlDecl instanceof JmlClassDecl) {
                    if (Utils.jmldebug) System.out.println("ADDING(JmlEnter) DECL FOR NESTED CLASS " + ((JmlClassDecl)specsNestedJmlDecl).name + " TO "  + javaClassDeclaration.name);
                    classEnter(specsNestedJmlDecl,typeEnvs.get(javaClassDeclaration.sym));
                    // the call above sets the sourcefile of the sym to that of the enclosing class, but a model
                    // class can be declared in a specification file, so we fix that
                    ((JmlClassDecl)specsNestedJmlDecl).sym.sourcefile = ((JmlClassDecl)specsNestedJmlDecl).sourcefile;
                }
            }
        }
    }
    
    private int modeOfCurrentCU = 0;
    
    public java.util.List<Env<AttrContext>> binaryMemberTodo = new LinkedList<Env<AttrContext>>();

    public void recordEmptySpecs(JmlSpecs specs, ClassSymbol csymbol) {
        specs.putSpecs(csymbol,new JmlSpecs.TypeSpecs(null,JmlTree.Maker.instance(context).Modifiers(csymbol.flags(),List.<JCTree.JCAnnotation>nil()),null));
        for (Symbol s: csymbol.getEnclosedElements()) {
            if (s instanceof ClassSymbol) recordEmptySpecs(specs,(ClassSymbol)s);
        }
    }
    /** Is called after parsing the specs for a binary type, to do what we do for
     * source type via enter.main().  However, for binary types we do not need to
     * enter all the classes in the database; we simply need to match up the
     * declarations in the spec file with those in the binary, but do need to
     * enter any specification (model) classes.
     * 
     * @param csymbol the ClassSymbol of the binary type
     * @param specsSequence the parse trees of the specifications for the binary type
     * (including the specifications for any secondary types that would have been in the same source
     * compilation unit)
     */
    public void enterTopLevelSpecClassesForBinary(ClassSymbol csymbol, java.util.List<JmlCompilationUnit> specsSequence) {
        if (Utils.jmldebug) System.out.println("ENTER TOPLEVEL (BINARY) " + csymbol);
        JmlSpecs specs = JmlSpecs.instance(context);

        // First do all the linking of java types to specifications
        // Since we do not have a Java compilation Unit to walk down, we will
        // enter the model classes as well
        // FIXME - only handling the first item in the spec sequence
        if (specsSequence == null || specsSequence.size() == 0) {
            // If there are no specs, we still make an (empty) record of that
            // fact in the specs database, so that we don't go looking again
            // Caution though.  If this is actually used, there have been 
            // problems because of the null declaration.
                    // FIXME - what about annotations stored in the binary file?  What about the source file?
            recordEmptySpecs(specs,csymbol);
            
            // FIXME - do we need to read in all the classes in the package?
            //reader.enterPackage(TreeInfo.fullName(specCompilationUnit.pid));
            //specCompilationUnit.packge.complete(); // Find all classes in package.  // FIXME - it seems this is generally null; maybe ok since we really don't want to read in every class in the package
            
            //Env<AttrContext> localEnv = topLevelEnv(specCompilationUnit);
            //typeEnvs.put(specCompilationUnit.packge, localEnv);
            //this.env = localEnv;

            //binaryMemberTodo.addLast(localEnv);
            
            //typeEnvs.put(csymbol, localEnv);

            return;
        }
        
        // Make a map of class names to declarations for the top-level declarations
        // in the compilation unit
        java.util.Map<Name,ClassSymbol> decls = new java.util.HashMap<Name,ClassSymbol>();
        // FIXME - actually need to do this differently
        // for each top-level class in the spec file we need to see if there is a binary somewhere for it
        // so can't use a map since we don't know them all ahead of time.
        // FIXME - spec files for binaries do not work for secondary types
        decls.put(csymbol.getSimpleName(), csymbol); 

        // Scan over the specification file and match up all the types
        JmlCompilationUnit specCompilationUnit = specsSequence.get(0);
        
        JavaFileObject prevSource = log.useSource(specCompilationUnit.sourcefile);
        modeOfCurrentCU = specCompilationUnit.mode;
        if (modeOfCurrentCU == JmlCompilationUnit.UNKNOWN) throw new JmlInternalError();
        
        Env<AttrContext> prevEnv = this.env;
        // Be sure that the package is defined
         // Note: This follows the code in Enter.visitTopLevel, without actually entering the class
        {
            if (specCompilationUnit.pid != null) {
                // The following just returns if the package is already defined
                specCompilationUnit.packge = reader.enterPackage(TreeInfo.fullName(specCompilationUnit.pid));
                // FIXME - does something need to be done with package annotations?  see Enter
            } else {
                specCompilationUnit.packge = syms.unnamedPackage;
            }
            specCompilationUnit.packge.complete(); // Find all classes in package.  // FIXME - it seems this is generally null; maybe ok since we really don't want to read in every class in the package
            Env<AttrContext> localEnv = topLevelEnv(specCompilationUnit);
            //typeEnvs.put(specCompilationUnit.packge, localEnv);
            this.env = localEnv;
            if (Utils.jmldebug) System.out.println("ADDED BINARY TODO " + 
                    localEnv.toplevel.sourcefile);

            binaryMemberTodo.add(localEnv);
        }
        for (JCTree def: specCompilationUnit.defs) {
            if (def instanceof JmlClassDecl) {
                JmlClassDecl specTypeDeclaration = (JmlClassDecl)def;
//                if (csymbol != specTypeDeclaration.sym) System.out.println("OUCH: SYMBOL CHANGED " + csymbol);
//                Scope newScope = specTypeDeclaration.sym.members();
//                System.out.println("SPEC TYPE SCOPE " + newScope);
                if (Utils.isJML(specTypeDeclaration.mods)) {
                    // This is a model declaration - we enter it into the symbol table
                    // FIXME - actually these have been sorted out and are dealt with later
                } else {
                    // This is a Java declaration
                    ClassSymbol matchingCSymbol = decls.get(specTypeDeclaration.name);  // FIXME - lookup the class, so we get secondary classes also
                    if (matchingCSymbol == null) {
                        // There is no Java declaration to match this specification declaration
                        // FIXME - check this error message
                        Log.instance(context).error(specTypeDeclaration.pos(),"jml.orphan.jml.toplevel.class.decl",specTypeDeclaration.name,csymbol);
                    } else {
                        JmlSpecs.TypeSpecs tspecs = specs.get(matchingCSymbol);
                        if (tspecs != null) {
                            // There has already been a match made to the Java type of the same name
                            // FIXME - check this error message
                            Log.instance(context).error(specTypeDeclaration.pos(),"jml.duplicate.jml.class.decl",specTypeDeclaration.name);
                        } else {
                            // Link the Java type to the specification for future easy reference
                            Env<AttrContext> localEnv = classEnv(specTypeDeclaration, env);
                            boolean ok = enterTypeParametersForBinary(matchingCSymbol,specTypeDeclaration,localEnv);
                            if (ok) {
                                // Now recursively match up nested types
                                specTypeDeclaration.sym = matchingCSymbol;
                                typeEnvs.put(matchingCSymbol, classEnv(specTypeDeclaration,localEnv));
                                specs.putSpecs(matchingCSymbol,new JmlSpecs.TypeSpecs(specTypeDeclaration));
                                enterNestedSpecClassesForBinary(matchingCSymbol,specTypeDeclaration);
                            }
                        }
                    }
                }
            }
        }
        if (Utils.jmldebug) System.out.println("ENTER TOPLEVEL (BINARY) - JML " + csymbol);
        // Then add in any top-level model types
        for (JmlClassDecl modelTypeDeclaration: specCompilationUnit.parsedTopLevelModelTypes) {
            modelTypeDeclaration.accept(this);  // FIXME - should this be classEnter?
        }
        this.env = prevEnv;
        modeOfCurrentCU = JmlCompilationUnit.UNKNOWN;
        
        log.useSource(prevSource);
        if (Utils.jmldebug) System.out.println("ENTER TOPLEVEL (BINARY) - COMPLETE " + csymbol);
    }
        
    public boolean enterTypeParametersForBinary(ClassSymbol csym, JmlClassDecl specTypeDeclaration, Env<AttrContext> localEnv) {
        int n = specTypeDeclaration.typarams.size();
        int javaN = csym.type.getTypeArguments().size();
        if (n != javaN) {
            log.error(specTypeDeclaration.pos(),"jml.mismatched.type.parameters", specTypeDeclaration.name, csym.fullname, n, javaN);
            return false;
        }
        int nn = n; if (javaN < nn) nn = javaN;
        for (int i = 0; i<nn; i++) {
            JCTree.JCTypeParameter specTV = specTypeDeclaration.typarams.get(i);
            TypeVar javaTV = (TypeVar)((ClassType)csym.type).getTypeArguments().get(i);
            if (specTV.name != javaTV.tsym.name) {
                log.error(specTV.pos(),"jml.mismatched.type.parameter.name", specTypeDeclaration.name, csym.fullname, specTV.name, javaTV.tsym.name);
                return false;
            }
        }
        for (int i = 0; i<nn; i++) {
            JCTree.JCTypeParameter specTV = specTypeDeclaration.typarams.get(i);
            TypeVar javaTV = (TypeVar)((ClassType)csym.type).getTypeArguments().get(i);
            specTV.type = javaTV;
            classEnter(specTV,localEnv);
        }
        for (int i = nn; i<n; i++) {
            JCTree.JCTypeParameter specTV = specTypeDeclaration.typarams.get(i);
            JmlAttr.instance(context).attribType(specTV,localEnv);
        }
        return true;
        //System.out.println(" LOCAL ENV NOW " + localEnv);
    }
    
    public void enterNestedSpecClassesForBinary(ClassSymbol csymbol, JmlClassDecl specTypeDeclaration) {
        if (specTypeDeclaration == null) return;
        
        // Make a map of the types nested within this java type.
        java.util.Map<Name,ClassSymbol> decls = new java.util.HashMap<Name,ClassSymbol>();
        for (Symbol s: csymbol.getEnclosedElements()) {   // FIXME - it would be better to lookup the name and then check that it is in the same class
            if (s.kind == Kinds.TYP) decls.put(s.getSimpleName(), (ClassSymbol)s); 
        }
        
        JmlSpecs specs = JmlSpecs.instance(context);
        for (JCTree specDeclaration: specTypeDeclaration.defs) {
            if (specDeclaration instanceof JmlClassDecl) {
                JmlClassDecl specNestedTypeDeclaration = (JmlClassDecl)specDeclaration;
                ClassSymbol matchingCSymbol = decls.get(specNestedTypeDeclaration.name);
                if (matchingCSymbol == null) {
                    // There is no Java declaration to match this specification declaration
                    // FIXME check this error message
                    Log.instance(context).error(specNestedTypeDeclaration.pos(),"jml.orphan.jml.class.decl",specNestedTypeDeclaration.name,csymbol);
                } else {
                    JmlSpecs.TypeSpecs tspecs = specs.get(matchingCSymbol);
                    if (tspecs != null) {
                        // There has already been a match made to the Java type of the same name
                        // FIXME check this error message
                        Log.instance(context).error(specNestedTypeDeclaration.pos(),"jml.duplicate.jml.class.decl",specNestedTypeDeclaration.name);
                    } else {
                        // Link the Java type to the specification for future easy reference
                        specs.putSpecs(matchingCSymbol,new JmlSpecs.TypeSpecs(specNestedTypeDeclaration));
                        specNestedTypeDeclaration.sym = matchingCSymbol;
                        Env<AttrContext> localEnv = classEnv(specNestedTypeDeclaration, env);
                        typeEnvs.put(matchingCSymbol, localEnv);
                        enterTypeParametersForBinary(matchingCSymbol,specNestedTypeDeclaration,localEnv);
                        // Now recursively match up nested types
                        enterNestedSpecClassesForBinary(matchingCSymbol,specNestedTypeDeclaration);
                    }
                }
            } else if (specDeclaration instanceof JmlTypeClauseDecl) {
                JmlTypeClauseDecl nestedTypeSpecs = (JmlTypeClauseDecl)specDeclaration;
                JCTree specsNestedJmlDecl = nestedTypeSpecs.decl;
                if (specsNestedJmlDecl instanceof JmlClassDecl) {
                    specs.get(csymbol).clauses.append(nestedTypeSpecs);
                    if (Utils.jmldebug) System.out.println("ADDING " + ((JmlClassDecl)specsNestedJmlDecl).name + " TO "  + csymbol);
                    classEnter(specsNestedJmlDecl,typeEnvs.get(csymbol)); // FIXME - is the typeENv non-null?
                    // the call above sets the sourcefile of the sym to that of the enclosing class, but a model
                    // class can be declared in a specification file, so we fix that
                    ((JmlClassDecl)specsNestedJmlDecl).sym.sourcefile = ((JmlClassDecl)specsNestedJmlDecl).sourcefile;
                }
            }
        }
    }
    
    // FIXME - find a better way to avoid this error for spec files
    public boolean classNameMatchesFileName(ClassSymbol c, // DRC - changed from private to public
            Env<AttrContext> env) {
        return true;
    }

}
