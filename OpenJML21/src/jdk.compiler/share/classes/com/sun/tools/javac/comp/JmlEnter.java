/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.comp;

import static com.sun.tools.javac.code.Flags.ENUM;
import static com.sun.tools.javac.code.Flags.FINAL;
import static com.sun.tools.javac.code.Flags.HASINIT;
import static com.sun.tools.javac.code.Flags.INTERFACE;
import static com.sun.tools.javac.code.Flags.PUBLIC;

import java.util.*;
import java.util.stream.StreamSupport;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlAnnotation;
import org.jmlspecs.openjml.JmlTree.JmlBlock;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlSpecs.MethodSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.ext.Modifiers;
import org.jmlspecs.openjml.ext.TypeInitializerClauseExtension;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Scope.*;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.Completer;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.ModuleSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Kinds.KindName;
import com.sun.tools.javac.code.Scope.WriteableScope;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.comp.Enter.UnenterScanner;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.main.JmlCompiler;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.resources.CompilerProperties.Errors;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import static com.sun.tools.javac.code.TypeTag.*;

/**
 * This class extends Enter, which has the job of creating symbols for all the
 * types mentioned in a set of parse trees. JmlEnter adds to that functionality
 * to create symbols for all JML types (i.e., model classes) that are present in
 * the parse trees. In addition it adds to the source class file any model
 * classes that need to be compiled and it links each class declaration to its
 * specifications (another class declaration), or to itself.
 * <P>
 * JmlEnter expects that a compilation unit knows its specification files (via
 * its specsCompilationUnit field). It walks those specification files, matching
 * classes in the specification file to the corresponding classes in the Java
 * file, making links from the Java classes to their specifications. JmlEnter
 * also expects that the parse tree contains JmlClassDecl nodes instead of
 * JCClassDecl nodes, even where no additional specs are present.
 * <P>
 * Per the current version of JML, specifications for a .java file are taken
 * from just one file (previously, the specifications were a combination of
 * specifications from a sequence of specification files). The one file may be
 * the .java file containing the Java definition of the class or it may be a
 * different (e.g., .jml) file. The file used is the one attached to the
 * JmlCompilationUnit.specsCompilationUnit field (which may be but is not
 * necessarily the AST for the .java file itself).
 * <P>
 * Note that members of classes referenced in the set of compilation unit trees passed to
 * Enter.main are not processed until later (during MemberEnter or Attribution).
 * If those classes exist as .java files they will be parsed and their
 * specifications attached as usual. If the referenced classes are only binary,
 * the specifications still need to be obtained and attached to the class
 * symbol.
 * <P>
 * The process of entering a CU does these things:
 * <UL>
 * <LI>packages are completed by entering all the classes in the package
 * <LI>classes: a class symbol is defined; a completer is attached to the symbol
 * <LI>type parameters: recorded in the Env associated with the class
 * <LI>initiates the MemberEnter processing, which adds the members of a class
 * to its Env (its scope); this can have the side-effect of uncovering more
 * classes that need to be loaded (by either parsing or finding the binary
 * class) and entered.
 * </UL>
 * Also typeEnvs is a map that gives an Env<AttrContext> object for each class,
 * to be used when attributing types and resolving references within the class.
 * The enter process creates and stores this Env. JmlEnter does the same for
 * model classes and for the specifications corresponding to binary classes.
 * 
 * @author David Cok
 */
/*
 * FIXME - REVIEW THE FOLLOWING Relationships that need to be set up (for binary
 * classes as well) class symbol: ClassSymbol csym class environment :
 * Env<AttrContext> classenv class specs: TypeSpecs cspecs class declaration:
 * JmlClassDecl cdecl
 * 
 * classenv = getEnv(csym) ; classenv created by classEnv(cdecl, topLevelEnv)
 * csym = cdecl.sym cspecs = specs.get(csym)
 * 
 * cdecl.typeSpecsCombined = cspecs (only for Java declaration) cdecl.typeSpecs
 * = specifications from this cdecl only, not combined [Set by
 * filterTypeBodyDeclarations() ] cdecl.toplevel = not reliably set ??? FIXME
 * cdecl.sourcefile = toplevel.sourcefile [ Set by JmlParser ] cdecl.specsDecls
 * = list of JmlClassDecls, including cdecl if class is binary [ Set in
 * JmlEnter, during matching of specs to class symbols ] cdecl.sym = csym [For
 * Java files, assigned when class dfinition is entered; for binary files,
 * assigned in JmlEnter during matching of specs to class symbols ]
 * 
 * csym.sourcefile = file for Java declaration; if binary, file for most refined
 * specs file (or null?)
 */
public class JmlEnter extends Enter {
	
	final static boolean debugEnter = org.jmlspecs.openjml.Utils.debug("enter");

	/**
	 * This registers a factory so that we do not have to prematurely create an
	 * instance of Enter, but the factory only produces a singleton instance per
	 * context.
	 * 
	 * @param context the context in which to register
	 */
	public static void preRegister(final Context context) {
		context.put(enterKey, new Context.Factory<Enter>() {
			public Enter make(Context context) {
				return new JmlEnter(context);
			}
		});
	}

	/** The context in which this instance was created. */
	/* @non_null */
	final protected Context context;

	/** A cached value of the Utils tool */
	/* @non_null */
	final protected Utils utils;

	/**
	 * This is a toplevel environment used for resolving synthetic fully-qualified
	 * typenames
	 */
	public Env<AttrContext> tlenv;

	/**
	 * Don't call this: use instance() instead. Creates an instance of the JmlEnter
	 * tool in the given context; note that any options must be already set in
	 * Options prior to creating the tool.
	 * 
	 * @param context the compilation context to use for this tool
	 */
	// @ assignable this.*;
	protected JmlEnter(Context context) {
		super(context); // automatically registers the new object
		this.context = context;
		this.utils = Utils.instance(context);
		var m = JmlTree.Maker.instance(context);
		var q = (JCFieldAccess)m.QualIdent("org", "jmlspecs", "lang");
		var p = m.PackageDecl(List.<JCAnnotation>nil(), q);
		var i = m.Import(q, false);
		JmlCompilationUnit cu = m.TopLevel(List.<JCTree>of(p));
//        cu.specsCompilationUnit = cu;
//        cu.modle = Symtab.instance(context).unnamedModule;
//        cu.packge = p.packge = syms.enterPackage(cu.modle, TreeInfo.fullName(p.pid));
//        try { cu.sourcefile = new DelegatedFileObject(); } catch (java.net.URISyntaxException e) {}
////        visitTopLevel(cu);
//        this.tlenv = getTopLevelEnv(cu);

//       var mdl = Symtab.instance(context).getModule(Names.instance(context).fromString("java.base"));
//       ClassSymbol cs = Symtab.instance(context).getClass(mdl, Names.instance(context).fromString("org.jmlspecs.lang.JMLDataGroup"));
//       var clenv = classEnv(cs);
//       this.tlenv = topLevelEnv(clenv.toplevel);
	}

//	public static class DelegatedFileObject extends javax.tools.SimpleJavaFileObject {
//		public DelegatedFileObject() throws java.net.URISyntaxException {
//			super(new java.net.URI("file:///A.java"), JavaFileObject.Kind.SOURCE);
//		}
//	}

	/** Returns the unique instance of Enter for the given context. */
	public static JmlEnter instance(Context context) {
		return (JmlEnter) Enter.instance(context);
	}

	/**
	 * This method is called when a JmlCompilationUnit is in the list of things to
	 * 'enter'. It visits the designated compilation unit; first it matches class
	 * declarations in the specification files to class declarations in Java; then
	 * it calls the super class visitTopLevel method to initiate walking the tree;
	 * overriding methods in JmlEnter will be called when visiting class
	 * declarations, so that a class can register in the symbol table any model
	 * classes that are declared within it. As classes are visited, the specs for
	 * that class are extracted from the specification AST and attached to the
	 * class. We also take care of secondary top-level class declarations and
	 * top-level model declarations.
	 */
	public void visitTopLevel(JCCompilationUnit tree) {
		if (!(tree instanceof JmlCompilationUnit compUnit)) {
			utils.error("jml.internal",
					"Encountered an unexpected JCCompilationUnit instead of a JmlCompilationUnit in JmlEnter.visitTopeLevel");
			return;
		}
		if (compUnit.specsCompilationUnit == null) {
			utils.error(tree.sourcefile, tree, "jml.internal",
					"Every source compilation unit must have an associated specification compilation unit, perhaps itself");
			compUnit.specsCompilationUnit = compUnit; // Just to recover -- this should have already been assigned
		}
		if (compUnit.sourcefile == null) {
			utils.error("jml.internal", "A JmlCompilationUnit without a sourcefile: " + tree);
			return;
		}
		var prevSource = log.useSource(compUnit.sourcefile);
		try {
			compUnit.defs = matchClasses(compUnit.defs, compUnit.specsCompilationUnit.defs,
					compUnit.pid == null ? "" : compUnit.pid.pid.toString());
			super.visitTopLevel(compUnit);
            compUnit.defs.forEach(d->{ if (d instanceof JmlClassDecl cd) JmlAttr.instance(context).addTodo(cd.sym); } );
		} finally {
			if (prevSource != null) log.useSource(prevSource);
		}
	}

	// The arguments are two lists of trees, one from a .java file and the other
	// from its specification file (either a .jml file or the same .java file).
	// The lists are either top-level classes (owned by a CU) or nested declarations
	// (owned by a class).
	// The 'owner' argument is a String rep of the owning tree just for error messages.
	// This method matches up spec declarations with their java counterparts,
	// producing error messages for improper/missing matches.
	// The output is a revision for javaClasses, without duplicates and with any new JML classes
	// We call putSpecs here -- classes have symbols, although they have not yet
	// been entered and the scope (in the env) is not complete
	public List<JCTree> matchClasses(List<JCTree> javaClasses, List<JCTree> specClasses, String owner) {
		var additionalDecls = new ListBuffer<JmlClassDecl>(); // Model classes not in the javaClasses list
		var revisedDecls = new ListBuffer<JCTree>(); // The javaClasses list with errors removed
		if (javaClasses == specClasses) {
			// The lists are the same -- so we just match everything to itself
			// But we still need to check for duplicate names
			// Because all the classes on the javaClasses list will be entered later, we do
			// not need to create an additionalDecls list
			for (var sd : specClasses) {
				if (sd instanceof JmlClassDecl specDecl) {
					specDecl.specsDecl = specDecl;
					JmlClassDecl match = (JmlClassDecl) javaClasses.stream()
							.filter(t -> (t instanceof JmlClassDecl d && d.name == specDecl.name)).findFirst()
							.orElseThrow(); // Should always at least match itself
					if (match != specDecl) { // match had better be non-null or something went really wrong
						// If the first match found is not the same declaration, then there was an
						// earlier declaration with the same name
						utils.errorAndAssociatedDeclaration(specDecl.sourcefile, specDecl, match.sourcefile, match,
								"jml.message", "duplicate class: " + specDecl.name);
						continue; // skip the revisedDecls.add
					}
				}
				revisedDecls.add(sd);
			}
		} else {
			for (var sd : specClasses) {
				if (sd instanceof JmlClassDecl specDecl) {
			        var fqName = (owner.isEmpty() ? "" : (owner + ".")) + specDecl.name; // Actually only partially qualified
				    JmlClassDecl match = (JmlClassDecl) javaClasses.stream()
							.filter(t -> (t instanceof JmlClassDecl d && d.name == specDecl.name)).findFirst().orElse(null);
					// Check that the type parameters match because we do not want to 'enter' incorrect type parameters
					if (match != null && match.typarams.size() != specDecl.typarams.size()) {
						// Could include this check in the matching expression above, but here we can give
						// a pointed error message
						utils.errorAndAssociatedDeclaration(specDecl.sourcefile, specDecl, match.sourcefile, match,
								"jml.mismatched.type.arguments",
								Utils.nameTP(specDecl), Utils.nameTP(match));
						continue; // disallow the match
					}
					if (match == null) {
						// No match in the Java list with the same name
					    if (utils.isJML(specDecl.mods)) {
					        // OK -- it is a model (JML-only) class declaration
					        specDecl.specsDecl = specDecl;
					        JmlClassDecl found = null;
					        for (var ad: additionalDecls) if (ad.name == specDecl.name) found = ad;
					        if (found == null) {
					            additionalDecls.add(specDecl);
					        } else {
					            utils.errorAndAssociatedDeclaration(specDecl.sourcefile, sd, found.sourcefile, found, "jml.message",
					               "This model class declaration has the same name as a previous one: " + specDecl.name);
		                        continue;
					        }
					    } else {
					        // unmatched non-model class in the .jml file -- an error
					        utils.error(specDecl.sourcefile, specDecl, "jml.message",
					                "There is no class to match this Java declaration in the specification file: " + fqName);
	                        continue;
					    }
					} else {
						// A match in the Java list with the same name
						if (utils.isJML(specDecl)) {
							// A JML-only class matches a Java class -- an error
							utils.error(specDecl.sourcefile, specDecl, "jml.message",
									"This JML class declaration conflicts with an existing Java class with the same name: "
											+ specDecl.name);
							utils.error(match.specsDecl == null ? match.sourcefile : match.specsDecl.sourcefile,
									match.specsDecl == null ? match : match.specsDecl, "jml.associated.decl.cf",
									utils.locationString(specDecl, specDecl.sourcefile));
							if (match.specsDecl == null)
								match.specsDecl = specDecl;
						} else if (match.specsDecl == null) {
							// OK - no previous match to this declaration in the Java list
							// so make the match
							match.specsDecl = specDecl;
						} else {
							// error - already matched - both are Java declarations
							utils.errorAndAssociatedDeclaration(specDecl.sourcefile, specDecl,
									match.specsDecl.sourcefile, match.specsDecl, "jml.message",
									"duplicate class: " + fqName);
						}
					}
				}
			}
			for (var jd : javaClasses) {
				if (jd instanceof JmlClassDecl javaDecl) {
					if (javaDecl.specsDecl == null) {
						javaDecl.specsDecl = javaDecl; // Java declaration has no specs, so it is its own specs (OK
														// because it was parsed without JML)
					}
					JmlClassDecl match = (JmlClassDecl) javaClasses.stream()
							.filter(t -> (t instanceof JmlClassDecl d && d.name == javaDecl.name)).findFirst()
							.orElseThrow(); // should at least match itself
					if (match != javaDecl) { // match had better be non-null or something went really wrong
						// If the first match found is not the same declaration, then there was an
						// earlier declaration with the same name
						utils.errorAndAssociatedDeclaration(javaDecl.sourcefile, javaDecl, match.sourcefile, match,
								"jml.message", "duplicate class: " + javaDecl.name);
						continue; // skip the revisedDecls.add
					}
				}
				revisedDecls.add(jd);
			}
			revisedDecls.addAll(additionalDecls); // Put new model classes at the end
		}
		return revisedDecls.toList();
	}

	@Override
	public void visitClassDef(JCClassDecl tree) {
		// env is the Env of the enclosing environment
		// specEnv is the spec Env of the enclosing spec environment
		var sourceCD = (JmlClassDecl) tree;
		JavaFileObject prevSource = null;
		try {
			if (sourceCD.specsDecl == null) {
				boolean isEnum = (sourceCD.mods.flags & Flags.ENUM) != 0;
				if (!isEnum) utils.error(sourceCD.sourcefile, sourceCD, "jml.internal",
							"A source class declaration unexpectedly has no specification declaration: " + sourceCD.name + " " + sourceCD.sourcefile);
				sourceCD.specsDecl = sourceCD; // Purely for recovery -- should have been assigned before
			}
			prevSource = log.useSource(sourceCD.specsDecl.sourcefile);
			// Do the nested class matching for this class; 
			// any JML-only (model) classes are in the output list
			// All non-class member matching is done in JmlMemberEnter
			// Matching is done before the owner class is entered, so that we don't enter the matching classes twice
			sourceCD.defs = matchClasses(sourceCD.defs, sourceCD.specsDecl.defs, sourceCD.name.toString());
			log.useSource(sourceCD.sourcefile);
			super.visitClassDef(sourceCD);
			if (!(sourceCD.sym.type instanceof Type.ErrorType)) {
	            sourceCD.defs.forEach(d->{ if (d instanceof JmlClassDecl cd) JmlAttr.instance(context).addTodo(cd.sym); } );
			}
		} finally {
			if (prevSource != null) log.useSource(prevSource);
		}
	}


	/*
	 * enter.main() -- also JavaCompiler.readSourceFile
	 *     | / 
	 *     V / 
	 * complete
	 *     |
	 *     V
	 * classEnter:List of CUs -- env is null, specEnv is undefined
	 *     | V
	 * [push specEnv, env]
	 * classEnter(single tree, env) -- env is null, specEnv is undefined, tree is a CU
	 *     |
	 *     V
	 * [ match all specs to source for the CU's declarations ]
	 * visitTopLevel(CU) -- env is null, specEnv is undefined
	 * [ compute package info ]
	 *     |
	 *     V
	 * [ compute specEnv for enclosing env ]
	 * classEnter:List of CDs, env is enclosing env
	 *     |
	 *     V
	 * [pushes specEnv, env]
	 * classEnter(single tree, env) -- env is enclosing env, specEnv is enclosing spec env, tree is a CD
	 * [ if tree is a CD, compute specEnv for given cd ]
	 *     |
	 *     V
	 * [ match all nested classes ]
	 * visitClassDecl -- env is enclosing env, specEnv is enclosing spec env, tree is a CD
	 * [ compute class sym , add class to enclosing scope ]
	 * [ compute class's env, add to typeEnvs map, add type parameters to class's scope ]
	 *  ... 
	 * [ After processing nested classes, set cd.specsDecl.sym ]
	 *     |
	 *     V
	 * Recurse to classEnter:List of nested CDs, with env the enclosing env for the nested classes, 
	 *    specEnv is still the enclosing env of the enclosing env for the list of classes
	 * 
	 * 
	 * 
	 * 
	 */

	// T can be a JmlCompilationUnit or a JmlClassDecl 
	<T extends JCTree> List<Type> classEnter(List<T> trees, Env<AttrContext> env) {
		// This is after super.classEnter for an individual class or CU has done all the
		// processing (e.g. symbol creation, type parameter entering)
		// for that class or CU, and now is calling classEnter on its own nested
		// declarations. So it is a good spot to do any JML-related processing that
	    // needs to happen after a class is handled by OpenJDK itself.
		// The env being passed in is for the enclosing environment (the one that owns the 'trees';
		// we need to compute the specEnv for the enclosing specification file
		try {
			if (env != null) {
				if (env.tree instanceof JmlClassDecl sourceDecl) { // class declaration of the enclosing environment
					// This is a spot to insert processing after a class has been created (in visitClassDef)
					// and before any nested classes are processed

					// cd is the enclosing class for the 'trees' argument
					//System.out.println("TREES " + trees);
					//if (sourceDecl.defs != trees) throw new AssertionError("defs mismatch: " + sourceDecl.name + " " + sourceDecl.sym);
					//enterScope(specEnv).enter(sourceDecl.sym); // FIXME - review -= can occur for enums, anonymous classes
					sourceDecl.specsDecl.sym = sourceDecl.sym; // sym will have the source classfile
			        super.classEnter(sourceDecl.typarams, env); // Enter the already typed type-parameters from the source decl so we have the same symbols in source and specs // FIXME - was classTPEnter
					postClassCreation(sourceDecl, env, env);
				} else if (env.tree instanceof JmlCompilationUnit sourceCU) { // enclosing env is a comp unit
					sourceCU.specsCompilationUnit.packge = sourceCU.packge; // package symbol has a sourcefile, which is the
					                                                        // source's, not the spec's
					sourceCU.specsCompilationUnit.modle = sourceCU.modle;
					sourceCU.specsCompilationUnit.locn = sourceCU.locn;
					sourceCU.specsCompilationUnit.topLevelEnv = topLevelEnv(sourceCU.specsCompilationUnit); // needs packge, modle defined before this call
				}
			}
			if (!allowRecursion) return null; // FIXME - review why this is needed
			return super.classEnter(trees, env);
		} finally {
		}
	}
	
	// env is for sourceDecl 
    // specEnv is for sourceDecl.specDecl
	public void postClassCreation(JmlClassDecl sourceDecl, Env<AttrContext> env, Env<AttrContext> specEnv) {
		if (env.tree != sourceDecl) throw new AssertionError("mismatched Java decl: " + sourceDecl.name + " " + sourceDecl.sym);
		if (sourceDecl.specsDecl == null) throw new AssertionError("null specsdecl: " + sourceDecl.name + " " + sourceDecl.sym + " " + sourceDecl.hashCode());
		if (sourceDecl.sym == null) throw new AssertionError("null sourceDecl symbol " + sourceDecl.name );

		JmlClassDecl specDecl = sourceDecl.specsDecl; // the specification class declaration (which may be the same as sourceDecl)

		var localEnv = getEnv(sourceDecl.sym);
		if (localEnv == null) { // Defensive check
			utils.error(sourceDecl.sourcefile, sourceDecl, "jml.internal",
					"An 'entered' class that does not have a stored Env: " + sourceDecl.sym);
		}
		if (specDecl == null) { // Defensive check
			utils.error(sourceDecl.sourcefile, sourceDecl, "jml.internal", "A source class that does not have a specs class: " + sourceDecl.sym);
			sourceDecl.specsDecl = specDecl = sourceDecl; // Recovery from an error situation
		}

		JmlSpecs.instance(context).putSpecs(sourceDecl.sym, new JmlSpecs.TypeSpecs(specDecl, sourceDecl, env));

		// The superclass and interfaces of specDecl are attributed and checked in JmlAttr.checkClassMods
		
		int numSourceTypeParams = sourceDecl.typarams.size();
		int numSpecsTypeParams = specDecl.typarams.size();
		if (numSourceTypeParams != numSpecsTypeParams) {
			// This error should not happen because it should have already been caught in
			// matchClasses
			utils.errorAndAssociatedDeclaration(specDecl.sourcefile, specDecl, sourceDecl.sourcefile, sourceDecl,
					"jml.message",
					"Specification declaration has different number of type parameters than source declaration: "
							+ sourceDecl.sym.owner + " " + sourceDecl.name);
		} else {
			for (int i = 0; i < numSpecsTypeParams; ++i) {
				var sourceTP = sourceDecl.typarams.get(i);
				var specsTP = specDecl.typarams.get(i);
				if (sourceTP.name != specsTP.name) {
					utils.errorAndAssociatedDeclaration(specDecl.sourcefile, specsTP, sourceDecl.sourcefile,
							sourceTP, "jml.message",
							"Specification type parameter must have the same name as in the source: "
									+ specsTP.name + " vs. " + sourceTP.name + " in " + sourceDecl.sym);
				} else {
				    // The source code symbols for type parameters are already entered into specEnv
				    // (which is why the names need to be the same)
					if (specsTP != sourceTP) {
					    // If they are not from the same file we need to set various properties of the specsTP
						// FIXME - should check and disallow specsTP that have different bounds or
						// annotations
						// That check needs to do type attribution, so it cannot be done in matchClasses
						// To avoid crashes later on, here we just override the spec's values with a
						// copy of the source's
                        specsTP.type = sourceTP.type;
						specsTP.annotations = sourceTP.annotations;
						specsTP.bounds = sourceTP.bounds;
					}
				}
			}
		}
		// Go on to do nested classes
	}

	// Note that the tree may be either a JmlCompilationUnit or a JmlClassDecl;
	// env will be null if tree is a CU
	// If tree is a class, then env is the env of the containing CU or class
	// and specEnv is the Env for the specification CU or class of the container
	public Type classEnter(JCTree tree, Env<AttrContext> env) {
		if (debugEnter && tree instanceof JCCompilationUnit cu) System.out.println("enter: Entering CU " + cu.sourcefile);
        if (debugEnter && tree instanceof JCClassDecl d) System.out.println("enter: Entering class " + d.name);
		if (tree instanceof JmlClassDecl cd && cd.specsDecl.name != cd.name) throw new AssertionError("wrong specsDecl-A: " + cd.name + " " + cd.specsDecl.name);

		try {
			Type t = super.classEnter(tree, env); // eventually calls tree.accept, assigning env to this.env
			if (debugEnter && tree instanceof JCCompilationUnit cu) System.out.println("enter: Entered CU " + cu.sourcefile + " " + t);
			if (debugEnter && tree instanceof JCClassDecl d) System.out.println("enter: Entered class " + d.sym + " " + t + " " + env);
			return t;
		} catch (Exception e) {
            if (tree instanceof JCCompilationUnit cu) utils.error(cu.sourcefile, cu, "jml.internal", "Unexpected exception: " + e.getMessage());
            if (tree instanceof JmlClassDecl d) utils.error(d.sourcefile, d, "jml.internal", "Unexpected exception: " + e.getMessage());
	        e.printStackTrace(System.out);
	        throw e;
		} finally {
		}
	}
	
	// This is for entering matching specifications with a binary class (no source file)
	// Recurses through the compilation unit to match all non-local class declarations to binary classes
	// Declarations that do not match are entered as model classes
	public void specsEnter(JmlCompilationUnit speccu) {
	    if (debugEnter) System.out.println("enter: Entering declarations from specification file " + speccu.sourcefile);
	    if (debugEnter) System.out.println("enter:                           Linked to Java file " + (speccu.sourceCU == null ? "<null>" : speccu.sourceCU.sourcefile.toString()));
	    var prev = log.useSource(speccu.sourcefile);
	    var specs = JmlSpecs.instance(context);
	    try {

	        String flatPackageName = speccu.pid == null ? "" : speccu.pid.pid.toString();
	        Name packageName = names.fromString(flatPackageName);
	        // Most spec file for binary files will be for the system library packages in java.base, so try that first
	        PackageSymbol p = syms.getPackage(syms.java_base,packageName);
	        if (p == null) {
	            // Otherwise try the unnamed module
	            p = syms.getPackage(syms.unnamedModule,packageName);
	        }
	        if (p == null) {
	            Collection<ModuleSymbol> mods = syms.listPackageModules(packageName);
	            if (mods.size() == 1) {
	                p = syms.getPackage(mods.iterator().next(),packageName);
	                //System.out.println("PACKAGE " + packageName + " IS IN " + (p==null?"NULL":p.modle) + " " + mods.iterator().next());
	            } else if (mods.isEmpty()) {
	                // fall through
	            } else {
	                String xtr = "Package exists in multiple modules: " + flatPackageName + " in";
	                for (var m: mods) xtr += " " + m;
	                utils.warning(speccu.pid, "jml.message", xtr);
	            }
	        }
	        //System.out.println("PACKAGE " + packageName + " IS IN " + (p==null?"NULL":p.modle));
	        if (p == null) { // FIXME Document when this is needed
	            utils.warning(speccu.pid, "jml.message", "Creating new package in unnamed module: " + flatPackageName);
	            p = syms.enterPackage(syms.unnamedModule, packageName);
	        }

	        var owner = speccu.packge = p;
	        speccu.modle = p.modle;
	        Env<AttrContext> specEnv = topLevelEnv(speccu);
	        TypeEnter.instance(context).completeClass.resolveImports(speccu, specEnv);

	        speccu.defs = specsListEnter(owner, speccu.defs, specEnv);
	        speccu.defs = specsMembersEnter(owner, speccu.defs);
	    } finally {
	        log.useSource(prev);
	    }
	}
	
	// owner is the owner of all the defs (which are specification declarations)
	// specsEnv corresponds to the owner
	// Matches all the declarations in specsDefs to binary members of owner, if there is a match
	public List<JCTree> specsListEnter(Symbol owner, List<JCTree> specsDefs, Env<AttrContext> specsEnv) {
		if (specsEnv == null) throw new AssertionError("specsEnv is null " + owner);
		if (specsEnv.tree instanceof JCCompilationUnit cu && cu.defs != specsDefs) throw new AssertionError("mismatched cus");
		if (specsEnv.tree instanceof JCCompilationUnit cu && cu.packge != owner) throw new AssertionError("mismatched package sym");
		if (specsEnv.tree instanceof JCClassDecl cd && cd.defs != specsDefs) throw new AssertionError("mismatched cds");
		if (specsEnv.tree instanceof JCClassDecl cd && cd.sym != owner) throw new AssertionError("mismatched cd sym");
        ListBuffer<JCTree> newdefs = new ListBuffer<>();
		for (JCTree decl: specsDefs) {
			if (decl instanceof JmlClassDecl specsDecl) {
				// Check for duplicates
				JmlClassDecl match = (JmlClassDecl)newdefs.stream().filter(d->d instanceof JmlClassDecl cd && cd.name == specsDecl.name && cd != specsDecl).findFirst().orElse(null);
				if (match != null) {
					utils.errorAndAssociatedDeclaration(specsDecl.source(), specsDecl, match.source(), match,
							"jml.message", "This JML class declaration conflicts with another declaration: " + specsDecl.name);
				} else {
					var ok = specsClassEnter(owner, specsDecl, specsEnv);
					if (ok) {
						newdefs.add(specsDecl);
						Todo.instance(context).add(specsDecl.env);
					}
				}
			} else {
				newdefs.add(decl); 
			}
		}
		// Return a new list that omits duplicates
		return newdefs.toList();
	}
	
	public boolean allowRecursion = true;
	
	// owner is the owner of all the defs (which are specification declarations)
	// specsEnv corresponds to the owner
	// match specDecl to a member of owner, or create it afresh
	public boolean specsClassEnter(Symbol owner, JmlClassDecl specDecl, Env<AttrContext> specsEnv) {
		// specsDecl is the declaration to enter. It is expected to be a member of 'owner'
		// specsEnv is the specification env for owner
		if (specsEnv == null) throw new AssertionError("specsEnv is null " + owner + " " + specDecl.name);
		if (specsEnv.tree instanceof JCClassDecl cd && cd.sym != owner) throw new AssertionError("Mismatched tree " + owner + " " + specDecl.name + " " + cd.name + " " + cd.sym);
		if (specsEnv.tree instanceof JCCompilationUnit cu && cu.packge != owner) throw new AssertionError("mismatched package sym");
		if (specsEnv.tree instanceof JCClassDecl cd && cd.sym != owner) throw new AssertionError("mismatched cd sym");
		
		var iter = owner.members().getSymbolsByName(specDecl.name, s->s instanceof ClassSymbol).iterator();
		ClassSymbol csym = iter.hasNext() ? (ClassSymbol)iter.next() : null;
		
		if (debugEnter) System.out.println("enter: Spec class " + owner + "." + specDecl.name + " " + specsEnv.toplevel.sourcefile + " " + csym );

    	boolean isJML = utils.isJML(specDecl);
//		boolean isOwnerJML = utils.isJML(owner.flags());
//		boolean isLocal = !(owner instanceof ClassSymbol || owner instanceof PackageSymbol);

		//if (Utils.isJML()) utils.warning(specDecl, "jml.message", "SPECCLASSENTER " + className + " " + specsEnv);
		// FIXME - the following may not work correctly for top-level classes whose u=owner is a package, at least in the test environment
		boolean ok = false;
		Env<AttrContext> localEnv = null;
		try {
			if (csym == null) {
				// owner has no binary class corresponding to specDecl
				if (!isJML) {
					utils.error(specDecl, "jml.message", "There is no binary class to match this Java declaration in the specification file: " + owner + "." + specDecl.name);
					return false;
				}
				// The specDecl is a JML (model) class and not in the binary
				// So enter the class in the package or the parent class
				// FIXME - not positive this is entered in a way that RAC will work or is even correct for attribution
				if (owner instanceof PackageSymbol powner) {
					specDecl.specsDecl = specDecl;
//					if (this.env != null) System.out.println("ENV IS ALREADY SET");
//					else this.env = specsEnv;
					allowRecursion = false;
					classEnter(specDecl, specsEnv);
					allowRecursion = true;
					csym = specDecl.sym;
                    if (debugEnter) System.out.println("enter: Entering toplevel model class in binary: " + csym + " (owner: " + owner +")" + " super: " + csym.getSuperclass());
					//csym.complete();
					csym.flags_field = specDecl.mods.flags | Flags.UNATTRIBUTED;

					localEnv = classEnv(specDecl, specsEnv);
					// Put this, super and type parameters in the Spec environment
                    if (csym.type instanceof ClassType ct && ct.supertype_field != null) TypeEnter.instance(context).new MembersPhase().enterThisAndSuper(csym,  localEnv);
                    ((ClassType)csym.type).typarams_field = classEnter(specDecl.typarams, localEnv); // FIXME - was classTPEnter

	                //					csym = syms.enterClass(powner.modle, specDecl.name, powner);
//					csym.completer = Completer.NULL_COMPLETER;
//					csym.sourcefile = powner.sourcefile; // FIXME: Not positive this is needed
//					// The following cloned from Enter.java
//					if ((specDecl.mods.flags & PUBLIC) != 0 && !classNameMatchesFileName(csym, specsEnv)) {
//						KindName topElement = KindName.CLASS;
//						if ((specDecl.mods.flags & ENUM) != 0) {
//							topElement = KindName.ENUM;
//						} else if ((specDecl.mods.flags & INTERFACE) != 0) {
//							topElement = KindName.INTERFACE;
//						}
//						log.error(specDecl.pos(),
//								Errors.ClassPublicShouldBeInFile(topElement, specDecl.name));
//					}
				} else { // owner is a ClassSymbol
					ClassSymbol cowner = (ClassSymbol)owner;
					specDecl.specsDecl = specDecl;
//	                if (this.env != null) System.out.println("ENV IS ALREADY SET");
//	                else this.env = specsEnv;
					if (specDecl.specsDecl != specDecl) throw new AssertionError("wrong specsDecl: " + cowner + " " + specDecl.name);
                    allowRecursion = false; // FIXME - should allow recursion, and not do nested defs at end of this method
					classEnter(specDecl, specsEnv);
					allowRecursion = true;
					csym = specDecl.sym;
                    if (debugEnter) System.out.println("enter: Entering nested JML class: " + csym + " (owner: " + owner +")" + " super: " + csym.getSuperclass());
//					((ClassType)csym.type).typarams_field = classTPEnter(specDecl.typarams, specsEnv);
//					System.out.println("ENTERED-CLASS " + specDecl.name + " " + csym + " " + specsEnv + " " + cowner.members());
//					csym = syms.enterClass(specsEnv.toplevel.modle, specDecl.name, cowner);
//					csym.completer = Completer.NULL_COMPLETER;
//					csym.sourcefile = cowner.sourcefile;
//					((ClassType)csym.type).typarams_field = List.from(cowner.type.getTypeArguments()); // FIXME - what about additional type parameters?

					// FIXME - are the following needed
					var ct = (ClassType)csym.type;
					if (specDecl.extending != null) ct.supertype_field = specDecl.extending.type;
					else if ((specDecl.mods.flags & Flags.INTERFACE) == 0) ct.supertype_field = syms.objectType;
//					specDecl.typarams.forEach(t -> Attr.instance(context).attribType(t,env));
//					specDecl.implementing.forEach(t -> Attr.instance(context).attribType(t,env));
//					specDecl.permitting.forEach(t -> Attr.instance(context).attribType(t,env));
					csym.members_field = WriteableScope.create(csym); // FIXME - why is this needed
					owner.members().enter(csym);
					specDecl.type = ct;
					csym.flags_field = specDecl.mods.flags | Flags.UNATTRIBUTED;
	                if (localEnv == null) {
	                    localEnv = classEnv(specDecl, specsEnv);
	                    if (csym.type instanceof ClassType cty && cty.supertype_field != null) TypeEnter.instance(context).new MembersPhase().enterThisAndSuper(csym,  localEnv);
	                    ((ClassType)csym.type).typarams_field = classEnter(specDecl.typarams, localEnv); // FIXME - was classTPEnter
                    }
//	                if (typeEnvs.get(csym) == null) {
//	                    ((ClassType)csym.type).typarams_field = classEnter(specDecl.typarams, localSpecEnv); // FIXME - what does this do??? -- was classTPEnter
//	                }
				}
			} else {
				// owner has a binary class corresponding to specDecl, namely csym
				if (isJML) {
					utils.error(specDecl.sourcefile, specDecl,
							"jml.message", "This JML class declaration conflicts with an existing binary class with the same name: " + csym);
					return false; // disallow the match
				}
				if (csym.getTypeParameters().size() != specDecl.typarams.size()) {
					utils.error(specDecl.sourcefile, specDecl,
							"jml.mismatched.type.arguments", Utils.nameTP(specDecl), csym.type);
                    //recordEmptySpecs(csym); // so we don't keep trying to load it
                    //System.out.println("FAILED MATCH " + csym + " " + ((csym.flags_field & Flags.UNATTRIBUTED) != 0));
                    csym.flags_field &= ~Flags.UNATTRIBUTED;
					return false; // disallow the match
				}
				specDecl.sym = csym;
				specDecl.type = csym.type;
				specDecl.specsDecl = specDecl;
				localEnv = classEnv(specDecl, specsEnv);
                TypeEnter.instance(context).new MembersPhase().enterThisAndSuper(csym,  localEnv);
				if (!checkAndEnterTypeParameters(csym,specDecl,localEnv)) {
                    //recordEmptySpecs(csym); // so we don't keep trying to load it
                    //System.out.println("FAILED MATCH-B " + csym + " " + ((csym.flags_field & Flags.UNATTRIBUTED) != 0));
				    return false;
				}
				if (localEnv.tree instanceof JCClassDecl cd &&  csym != cd.sym) System.out.println("MISMATCHED-A " + csym);
                typeEnvs.put(csym, localEnv);
				// FIXME - be sure that annotations are checked as well
				if (utils.verbose()) utils.note("Matched to binary class: " + csym + " (owner: " + csym.owner +")" );

				((ClassType)csym.type).typarams_field = classEnter(specDecl.typarams, localEnv); // FIXME - what does this do??? -- was classTPEnter
	            csym.flags_field |= Flags.UNATTRIBUTED;
			}
//			if (specDecl.typarams.size() == ((ClassType)csym.type).typarams_field.size()) {
//				for (int i = 0; i < specDecl.typarams.length(); ++i) {
//					System.out.println("TYPEPARAM " + csym + " " + ((ClassType)csym.type).typarams_field.get(i) + " " + ((ClassType)csym.type).typarams_field.get(i).hashCode() + " " + ((ClassType)csym.type).typarams_field.get(i).tsym + " " + specDecl.typarams.get(i).type + " " + specDecl.typarams.get(i).type.hashCode());
//					specDecl.typarams.get(i).type = ((ClassType)csym.type).typarams_field.get(i);
//				}
//			}
			specDecl.sym = csym;
			specDecl.env = localEnv;
			var tspecs = new JmlSpecs.TypeSpecs(specDecl, null, localEnv);
			JmlSpecs.instance(context).putSpecs(csym, tspecs);
			// Do all nested classes, recursively
			specDecl.defs = specsListEnter(csym, specDecl.defs, localEnv);
		} catch (Exception e) {
			utils.unexpectedException("JmlEnterspecsClassEnter", e);
			return false;
		} finally {
		}
		return true;
    }

//	public <T> T find(List<T> list, java.util.function.Predicate<T> pred) {
//		if (list != null)
//			for (var item : list) {
//				if (pred.test(item))
//					return item;
//			}
//		return null;
//	}


	public List<JCTree> specsMembersEnter(Symbol owner, List<JCTree> defs) {
		for (JCTree decl: defs) {
			if (decl instanceof JmlClassDecl specDecl) {
			    ClassSymbol cs = specDecl.sym;
                if (cs.owner != owner) throw new AssertionError("Mismatched owner");
			    if (utils.isJML(specDecl)) {
			        cs.complete();
			    	//TypeEnter.instance(context).new MembersPhase().enterThisAndSuper(cs, JmlSpecs.instance(context).getLoadedSpecs(cs).specsEnv);
                    //specsMemberEnter(specDecl); // Enter class specDecl non-recursively
                    //specsMembersEnter(cs, specDecl.defs); // Enter any classes in specDecl
			    } else {
			        specsMemberEnter(specDecl); // Enter class specDecl non-recursively
			        specsMembersEnter(cs, specDecl.defs); // Enter any classes in specDecl
			    }
			}
		}
		return defs;
	}

	public void specsMemberEnter(JmlClassDecl specDecl) {
	    boolean print = false; // specDecl.name.toString().equals("Collection");
	    if (print) System.out.println("SME " + specDecl);
	    if (debugEnter || print) System.out.println("enter: Entering members for binary " + specDecl.sym + " : " + 
	                            Utils.join(" ",specDecl.defs,d->(d instanceof JmlVariableDecl vd ? vd.name : d instanceof JmlMethodDecl md ? md.name : "")));
		var saved = JmlResolve.instance(context).setAllowJML(utils.isJML(specDecl.mods));
		ClassSymbol csym = specDecl.sym;
		Symbol owner = csym.owner;
		JmlSpecs specs = JmlSpecs.instance(context);
		var tspecs = JmlSpecs.instance(context).get(csym);
		if (tspecs == null)
			System.out.println("No specs for " + csym + " " + specDecl.name );
		var specsEnv = tspecs.specsEnv;
		if (specsEnv == null)
			System.out.println("No specs ENV for " + csym + " " + specDecl.name);
		//if (specDecl.name.toString().contains("Function")|| specDecl.name.toString().contains("Identity")) System.out.println("SPECSENV " + tspecs + " : " + specsEnv);
		if (specDecl.extending != null) {
			Type t = specDecl.extending.type = JmlAttr.instance(context).attribType(specDecl.extending, specsEnv);
			if (!JmlTypes.instance(context).isSameType(t, csym.getSuperclass())) {
				utils.error(specDecl.extending, "jml.message",
						"Supertype in specification differs from supertype in source/binary: " + csym + " " + t + " "
								+ csym.getSuperclass() + " " + owner + " " + specDecl);
			}
		} else if (!csym.isInterface() && !csym.isEnum() && !csym.isRecord()) {
			// jdecl has no declared supertype so either
			// (a) it is Object and csym is also java.lang.Object
			// or (b) the superclass of csym is Object
			if (!JmlTypes.instance(context).isSameType(syms.objectType, csym.type)
					&& !JmlTypes.instance(context).isSameType(syms.objectType, csym.getSuperclass())) {
				utils.error(specDecl, "jml.message",
						"Supertype in specification differs from supertype in source/binary: " + "Object" + " "
								+ csym.getSuperclass());
			}
		}
		// FIXME - check type parameters, interfaces, permitted, flags, annotations,
		// enclosing class

		boolean hasStaticInit = false;
		boolean hasInstanceInit = false;
		boolean ok;
		var newdefs = new ListBuffer<JCTree>();
		for (JCTree t : specDecl.defs) {
			ok = true;
			if (t instanceof JmlMethodDecl md) {
				ok = specsMethodEnter(csym, md, specsEnv);
			} else if (t instanceof JmlVariableDecl vd) {
				ok = specsFieldEnter(csym, vd, specsEnv);
			} else if (t instanceof JmlBlock block) {
    			if (block.isInitializerBlock && block.sourcefile.getKind() != JavaFileObject.Kind.SOURCE && !utils.isJML(specsEnv.enclClass.mods)) {
    				utils.error(block.source(), block, "jml.initializer.block.allowed");
    				ok = false;
    			}
			} else if (t instanceof JmlTypeClauseInitializer init) {
				if (init.keyword == TypeInitializerClauseExtension.staticinitializerID) {
					if (hasStaticInit) {
						utils.error(t, "jml.one.initializer.spec.only");
						ok = false;
					} else {
						hasStaticInit = true;
					}
				}
				if (((JmlTypeClauseInitializer) t).keyword == TypeInitializerClauseExtension.initializerID) {
					if (hasInstanceInit) {
						utils.error(t, "jml.one.initializer.spec.only");
						ok = false;
					} else {
						hasInstanceInit = true;
					}
				}
			}
			if (ok) newdefs.add(t);
		}
		specDecl.defs = newdefs.toList();

		var classIsPure = utils.findMod(specDecl.mods, Modifiers.PURE);

		// Add specifications for Java declarations that do not have specification
		// declarations
		for (Symbol m : specDecl.sym.members().getSymbols(s -> s instanceof MethodSymbol)) {
			MethodSymbol ms = (MethodSymbol) m;
			if (print) System.out.println("SME METH " + ms + " " + specs.get(ms));
			if (specs.get(ms) == null) {
				// utils.note("Method " + specDecl.sym + "." + m + " has no specifications --
				// using defaults");
				specs.putAttrSpecs(ms, specs.defaultSpecs(null, ms, com.sun.tools.javac.util.Position.NOPOS));
			}
		}

		JmlResolve.instance(context).setAllowJML(saved);
        if (debugEnter) System.out.println("enter: Entered members for binary " + specDecl.sym + " : " + 
                Utils.join(" ",specDecl.defs,d->(d instanceof JmlVariableDecl vd ? vd.name : d instanceof JmlMethodDecl md ? md.name : "")));
	}
	

	public void addAttribute(List<JCAnnotation> alist, Type t, Env<AttrContext> env) {
		for (var a : alist) {
			a.attribute = annotate.attributeTypeAnnotation(a, t, env);
		}
	}

	public void addAttribute(JCExpression at, Type t, Env<AttrContext> env) {
		if (at instanceof JCAnnotatedType) {
			addAttribute(((JCAnnotatedType) at).annotations, t, env);
			addAttribute(((JCAnnotatedType) at).underlyingType, t, env);
		}
	}

	public MethodSymbol findMethod(ClassSymbol csym, JmlMethodDecl mdecl, Env<AttrContext> env) {
		boolean print =  false;//mdecl.name.toString().equals("charAt");
		boolean hasTypeParams = mdecl.typarams.length() != 0;
		boolean useStringComparison = false;
		if (print)
			System.out.println("SEEKING " + csym + " " + mdecl.name + " " + mdecl.sym + " " + mdecl.type + " "
					+ hasTypeParams + " " + csym.members());
		if (print && mdecl.sym != null)
			System.out.println("       SYMTYPE " + mdecl.sym.type);
		for (var p : mdecl.params) {
			addAttribute(p.vartype, syms.annotationType, env);
		}
		if (mdecl.restype != null) {
			addAttribute(mdecl.restype, syms.annotationType, env);
		}
//    	try {
//    		annotate.flush();
//    	} catch (Exception ee) {
//    		System.out.println("EXCEPTION-FLUSH " + ee);
//    		ee.printStackTrace(System.out);
//    	}
//    			if (mdecl.name.toString().equals("getAvailableLocales")) {
//    				var rt = mdecl.restype;
//    				System.out.println("RESTYPE " + rt.getClass() + rt.type);
//    				if (rt instanceof JCAnnotatedType) {
//    					var rat = (JCAnnotatedType)rt;
//    					System.out.println("RESTYPE ANN " + rat.annotations.hashCode() + " " + rat.annotations);
//    					System.out.println("RESTYPE ANN " + ((JCAnnotatedType)rt).underlyingType);
//    					System.out.println("RESTYPE ANN " + ((JCAnnotatedType)rt).annotations);
//    					for (var a: ((JCAnnotatedType)rt).annotations) {
//    						JmlAnnotation aa = (JmlAnnotation)a;
//        					System.out.println("RESTYPE AA " + aa + " " + aa.kind + " " + aa.hashCode() + " " + aa.attribute);
//        					attr.attribAnnotationTypes(rat.annotations, env);
//        					System.out.println("RESTYPE AA " + aa + " " + aa.kind + " " + aa.hashCode() + " " + aa.attribute);
//    					}
//    				}
//    			}
//    			if (mdecl.thrown != null) attr.attribTypes(mdecl.thrown, env);
//    		} catch (Exception e) {
//    			utils.warning(mdecl, "jml.message", "Failed to attribute types");
//    			e.printStackTrace(System.out);
//    			useStringComparison = true;
//    		} finally {
//    			try {
//    				annotate.flush();
//    			} catch (Exception ee) {
//    				System.out.println("UNEXPECTED EXCEPTION - annotate.flush");
//    				ee.printStackTrace(System.out);
//    			}
//    		}
//    	}
		Symbol.MethodSymbol msym = null;
		MethodSymbol first = null;
		int count = 0;
		var iter = csym.members().getSymbolsByName(mdecl.name, s -> (s instanceof Symbol.MethodSymbol)).iterator();
		x: while (iter.hasNext()) {
			var m = (MethodSymbol) iter.next();
			if (print) System.out.println(
						"CONSIDERING " + m + " " + m.type + " " + m.params.length() + " " + mdecl.params.length() + " "
								+ m.getTypeParameters().length() + " " + mdecl.getTypeParameters().length());
			if (m.params.length() != mdecl.params.length())
				continue;
			if (m.getTypeParameters().length() != mdecl.getTypeParameters().length())
				continue;
			if (print) System.out.println("CONSIDERING-A " + m);
			first = m;
			count++;
			if (hasTypeParams) {
				if (print) System.out.println("COMPARING-TP " + m.type + " " + mdecl.sym.type + " "
							+ types.isSameType(m.type, mdecl.sym.type));
//				var atypes = m.type.getTypeArguments();
//				var btypes = mdecl.sym.type.getTypeArguments();
//				var ntype = types.subst(m.type, atypes, btypes);
				if (!types.isSameType(m.type, mdecl.sym.type))
					continue x;
//				for (int i=0; i<m.params.length(); i++) {
//					// FIXME - When there are type parameters, the type resolution above is not working
//					// so we fall back to string comparison -- a hack that only partially works
//					// Probably has to do with getting the correct env
//					//if (Utils.debug()) System.out.println("TYPES " + m.params.get(i).type.toString() + " " + mdecl.params.get(i).vartype.toString());
//					if (!matchAsStrings(m.params.get(i).type, mdecl.params.get(i).vartype)) continue x;
//				}
			} else {
				if (print)
					System.out.println("COMPARING-T " + m.type + " " + mdecl.sym.type + " "
							+ types.isSameType(m.type, mdecl.sym.type));
				if (!types.isSameType(m.type, mdecl.sym.type))
					continue x;
			}
			if (msym != null) {
				// It turns out that there sometimes are two method symbols with the same
				// signature.
				// cf. AbstractStringBuilder, StringBuffer
				// So instead of doing this check, we just exit (via the return) on finding the
				// first one.
				utils.note(mdecl, "jml.message", "Unexpectedly found duplicate binary method symbols: " + msym + " "
						+ msym.isAbstract() + " " + m.isAbstract());
			} else {
				msym = m;
				break x;
			}
		}
		if (msym == null && count == 1 && !utils.isJML(mdecl)) {
			// utils.note(mdecl, "jml.message", "No match; could use the unique candidate "
			// + first + " " + (!hasTypeParams?"": " (hasTypeParameters)"));
			msym = first;
		}
		if (msym != null && useStringComparison && !utils.isJML(mdecl)) {
			var mt = msym.type.asMethodType();
			mdecl.restype.type = mt.restype;
			for (int i = 0; i < mdecl.getTypeParameters().length(); ++i) {
				var mi = mdecl.getTypeParameters().get(i);
				var mj = msym.getTypeParameters().get(i);
				mi.type = mj.type;
				for (int j = 0; j < mi.bounds.length(); ++j)
					mi.bounds.get(j).type = mj.getBounds().get(j);
			}
			for (int i = 0; i < mdecl.params.length(); ++i)
				mdecl.params.get(i).type = mt.argtypes.get(i);
		}
		return msym;
	}

	public MethodSymbol makeAndEnterMethodSym(JmlMethodDecl tree, Env<AttrContext> specsEnv) {
		JmlMemberEnter memberEnter = JmlMemberEnter.instance(context);
		var saved = memberEnter.env;
//    	var savedEJ = memberEnter.enterJML;
		try {
			memberEnter.env = specsEnv;
//        	memberEnter.enterJML = true;
			memberEnter.visitMethodDef(tree); // This also calls putSpecs
		} finally {
//    		memberEnter.enterJML = savedEJ;
			memberEnter.env = saved;
		}
		return tree.sym;
	}
	
	public Env<AttrContext> methodEnv;

	public boolean specsMethodEnter(ClassSymbol csym, JmlMethodDecl mdecl, Env<AttrContext> specsEnv) {
		boolean print = false;// mdecl.name.toString().equals("toString") && csym.toString().equals("java.lang.Object");
		if (print) System.out.println("SPECSMETHODENTER " + csym + " " + mdecl + " " + mdecl.sym + " " + specsEnv + " " + mdecl.specsDecl);
		boolean isJML = utils.isJML(mdecl);
		boolean isOwnerJML = utils.isJML(csym.flags());
		boolean isModel = utils.hasModifier(mdecl.mods, Modifiers.MODEL);
		var specs = JmlSpecs.instance(context);
		if (mdecl.sym != null) {
	        if (print) System.out.println("  SYM EXISTS " + mdecl.sym.owner);
			// Expect isOwnerJML==true?
			// What if mdecl.sym.owner != csym ?
			var ssp = new JmlSpecs.MethodSpecs(mdecl);
			ssp.javaDecl = null; // is null
			ssp.specDecl = mdecl;
			ssp.javaSym = mdecl.sym;
			ssp.specSym = mdecl.sym;
			var localEnv = MemberEnter.instance(context).methodEnv(mdecl,specsEnv); // FIXME _ do more than this?
			ssp.javaEnv = localEnv;
			ssp.specsEnv = localEnv;
			if (print) System.out.println("ASSIGNING SPECS ENV-A " + mdecl.sym.owner + " " + mdecl.sym + " " + specsEnv + " : " + localEnv );
			specs.putSpecs(mdecl.sym, ssp);
			return true;
		}
		
		// FIXME - move to JmlAttr
		if (isOwnerJML && isModel) {
			utils.error(mdecl, "jml.message",
					"A model type may not contain model declarations: " + mdecl.name + " in " + csym);
			// Attempt recovery by removing the offending annotation
			utils.removeAnnotation(mdecl.mods, Modifiers.MODEL);
		} else if (!isJML && isModel) {
			var pos = utils.locMod(mdecl.mods, Modifiers.MODEL);
			utils.error(pos, "jml.message",
					"A Java method declaration must not be marked model: " + mdecl.name + " (owner: " + csym + ")");
			// Attempt recovery by removing the offending annotation
			utils.removeAnnotation(mdecl.mods, Modifiers.MODEL);
		} else if (isJML && !isModel && !isOwnerJML) {
			utils.error(mdecl, "jml.message",
					"A JML method declaration must be marked model: " + mdecl.name + " (owner: " + csym + ")");
			// Attempt recovery by adding a model annotation
			JmlTreeUtils.instance(context).addAnnotation(mdecl.mods, mdecl.mods.pos, mdecl.mods.pos, Modifiers.MODEL,
					null);
		}

		Env<AttrContext> localEnv = null;
		WriteableScope enclScope = enterScope(specsEnv);
		Symbol.MethodSymbol msym = mdecl.sym; // Nonnull if specs and java decls are the same file
		if (mdecl.sym == null) {
			var saved = JmlMemberEnter.instance(context).enterJML;
			JmlMemberEnter.instance(context).enterJML = false;
			makeAndEnterMethodSym(mdecl, specsEnv);
			localEnv = methodEnv;
			JmlMemberEnter.instance(context).enterJML = saved;
			for (int i = 0; i < mdecl.params.length(); ++i) { // One would think that the attribution of mdecl would set
				// the parameter types, but it just sets the types in
				// the parameter sym
				mdecl.params.get(i).type = mdecl.sym.params.get(i).type;
			}
			msym = findMethod(csym, mdecl, specsEnv);
            if (print && msym != null) System.out.println("FOUND " + msym.owner + " " + msym + " " + csym);
            if (print && msym == null) System.out.println("NOT FOUND " + csym + " " + mdecl);
		}
		

		if (msym == null) {
			// No corresponding Java binary method (and not in a model class)
			if (!isJML && !isOwnerJML) {
				String msg = "There is no binary method to match this Java declaration in the specification file: "
						+ csym + "." + mdecl.name ;
				for (var s : csym.members().getSymbolsByName(mdecl.name, s -> (s instanceof MethodSymbol))) {
					msg = msg + "\n    " + csym + " has " + s;
				}
				utils.error(mdecl, "jml.message", msg);
				return false;
			}
			// Enter the method in the parent class
			msym = mdecl.sym; // makeAndEnterMethodSym(mdecl, specsEnv); // Also calls putSpecs
			enclScope.enter(msym);
			var sp = new JmlSpecs.MethodSpecs(mdecl);
			sp.javaDecl = null;
			sp.specDecl = mdecl;
			sp.javaSym = null;
			sp.specSym = mdecl.sym;
			sp.javaEnv = null;
			sp.specsEnv = localEnv;
            if (print) System.out.println("ASSIGNING SPECS ENV-B " + mdecl.sym.owner + " " + mdecl.sym + " " + specsEnv + " : " + localEnv );
			specs.putSpecs(msym, sp);
			if (!isModel && mdecl.body != null) {
				utils.error(mdecl.body, "jml.message",
						"The specification of the method " + csym + "." + msym + " must not have a body");
			}
			if (debugEnter) System.out.println("enter: Entered JML method: " + msym + " (owner: " + csym + ")");
		} else {
			// Found a matching Java binary method
			//if (print) System.out.println("MATCHED " + msym);
			boolean matchIsJML = utils.isJML(msym.flags());
			JmlSpecs.MethodSpecs mspecs = JmlSpecs.instance(context).get(msym); // Raw get to see if specs are present

			if (isJML && matchIsJML) {
				utils.error(mdecl.source(), mdecl, "jml.message",
						"This JML method declaration conflicts with a previous JML method: " + msym
						+ " (owner: " + csym + ")");
				utils.error(mspecs.cases.decl.source(), mspecs.cases.decl, "jml.associated.decl.cf",
						utils.locationString(mdecl, mdecl.source()));
				return false;
			} else if (isJML && !matchIsJML) {
				utils.error(mdecl.source(), mdecl, "jml.message",
						"This JML method declaration conflicts with an existing binary method with the same signature: "
								+ csym + "." + msym);
				return false;
			}

			if (!isJML && matchIsJML) {
				utils.error(mdecl.source(), mdecl, "jml.message", "This Java method declaration conflicts with a previous JML method: "
						+ mdecl.name + " (owner: " + csym + ")");
				utils.error(mspecs.cases.decl.source(), mspecs.cases.decl, "jml.associated.decl.cf",
						utils.locationString(mdecl, mdecl.source()));
				return false;
			}
			if (!isJML && !matchIsJML && mspecs != null) {
				utils.error(mdecl.source(), mdecl, 
						"jml.message", "This Java method declaration conflicts with an existing binary method with the same signature: "
						+ csym + "." + msym);
				utils.error(mspecs.cases.decl.source(), mspecs.cases.decl, "jml.associated.decl.cf",
						utils.locationString(mdecl, mdecl.source()));
				return false;
			}
			typeEnvs.put(csym, specsEnv);
			if (mdecl.restype != null) {
				Type t = Attr.instance(context).attribType(mdecl.restype, csym);
				// The difficulty here is that TypeVars show up as different types,
				// and that binary types are erased, so do not have type arguments.
				try {
					msym.getReturnType();
				} catch (Exception e) {
					System.out.println("RETTYPE " + msym + " " + t + " " + mdecl.sym + " " + (msym.type != null) + " "
							+ msym.type + " " + mdecl.sym.type);
				}
				if (!specsTypeSufficientlyMatches(t, msym.getReturnType())) {
					utils.error(mdecl.restype, "jml.mismatched.return.type",
							msym.enclClass().fullname + "." + msym.toString(), t, msym.getReturnType());
				}
			}
			
//			// FIXME - move to Attr
//			if (!isModel && mdecl.body != null && ((msym.flags() & Flags.GENERATEDCONSTR) == 0)) {
//				utils.error(mdecl.source(), mdecl.body, "jml.message",
//						"The specification of the method " + csym + "." + msym + " must not have a body");
//				;
//			}

			// Either
			// 0) There is no Java declaration, just a (model/ghost) spec declaration --
			// that is the case above with msym == null
			// 1) Just binary, no source Java declaration, and a jml declaration: javaMDecl
			// == null
			// 2) Java and JML are the same file: javaMDecl == mdecl
			// 3) Java and JML are different files: javaMDecl != null, javaMDecl != mdecl
			// Note that the javaSym may have already been used for attribution of other
			// code, so we have to use it
			// as the MethodSymbol to retrive information from the specs database.
			{
				if (utils.verbose())
					utils.note("Matched method: (binary) " + msym + " (owner: " + msym.owner + ")");
				// No specs entry for msym -- msym is just the symbol created on loading the
				// binary class file
				var ssp = new JmlSpecs.MethodSpecs(mdecl);
				//    			if (msym.toString().contains("arraycopy")) {
				//    				System.out.println("JMLENTER-J " + msym + " " + msym.params.head + " " + msym.params.head.hashCode());
				//    				System.out.println("JMLENTER-S " + mdecl.sym + " " + mdecl.sym.params.head + " " + mdecl.sym.params.head.hashCode());
				//    				System.out.println("JMLENTER-SS " + mdecl.params.head.sym + " " + mdecl.params.head.sym.hashCode());
				//    				System.out.println("SPECENV " + specs.getLoadedSpecs(mdecl.sym).specsEnv.info.scope().getSymbolsByName(mdecl.sym.params.head.name).iterator().next().hashCode());
				//    				//System.out.println("JAVAENV " + specs.getLoadedSpecs(msym).specsEnv.info.scope().getSymbolsByName(msym.params.head.name).iterator().next().hashCode());
				//    			}
				ssp.javaDecl = null; // is null
				ssp.specDecl = mdecl;
				ssp.javaSym = msym;
				ssp.specSym = mdecl.sym;
				ssp.javaEnv = null;
				ssp.specsEnv = localEnv;
	            if (print) System.out.println("ASSIGNING SPECS ENV-C " + msym.owner + " " + msym + " " + specsEnv + " : " + localEnv );
				specs.putSpecs(msym, ssp);
				ssp.specSym = mdecl.sym;
				specs.dupSpecs(mdecl.sym, msym); // FIXME - not sure this is needed
				//checkMethodMatch(null, msym, mdecl, csym);
			}
		}
//		var iter = msym.params.iterator();
//		VarSymbol vs = null;
//		for (var v : mdecl.params) {
//			if (iter.hasNext())
//				specs.putSpecs(vs = iter.next(), new JmlSpecs.FormalSpecs((JmlVariableDecl) v));
//			specs.putSpecs(v.sym, new JmlSpecs.FormalSpecs((JmlVariableDecl) v));
//
//		}
		return true;
	}

	public boolean specsFieldEnter(ClassSymbol csym, JmlVariableDecl vdecl, Env<AttrContext> specsEnv) {
	    // FIXME - error messages need a sourcefile
		boolean isJML = utils.isJML(vdecl);
		boolean isOwnerJML = utils.isJML(csym.flags());
		boolean isGhost = utils.hasMod(vdecl.mods, Modifiers.GHOST);
		boolean isGhostOrModel = isGhost || utils.hasMod(vdecl.mods, Modifiers.MODEL);
		boolean ok = false;

		Symbol.VarSymbol vsym = findVarInBinary(csym, vdecl);
		try {
			// FIXME - move to JmlAttr
			if (isOwnerJML && isGhostOrModel) {
				utils.error(vdecl.source(), vdecl, "jml.message", "A model type may not contain " + (isGhost ? "ghost" : "model")
						+ " declarations: " + vdecl.name + " in " + csym);
				// Attempt recovery by removing the offending annotation
				utils.removeAnnotation(vdecl.mods, Modifiers.MODEL);
			} else if (isJML && !isGhostOrModel && !isOwnerJML) {
				utils.error(vdecl.source(), vdecl, "jml.message", "A JML field declaration must be marked either ghost or model: "
						+ vdecl.name + " (owner: " + csym + ")");
				// Attempt recovery by adding a ghost annotation
				JmlTreeUtils.instance(context).addAnnotation(vdecl.mods, vdecl.mods.pos, vdecl.mods.pos,
						Modifiers.GHOST, null);
			} else if (!isJML && isGhostOrModel) {
				var pos = utils.locMod(vdecl.mods, Modifiers.GHOST, Modifiers.MODEL);
				utils.error(vdecl.source(), pos, "jml.message", "A Java field declaration must not be marked either ghost or model: "
						+ vdecl.name + " (owner: " + csym + ")");
				// Attempt recovery by removing the offending annotation
				utils.removeAnnotation(vdecl.mods, Modifiers.MODEL);
				utils.removeAnnotation(vdecl.mods, Modifiers.GHOST);
			}

			if (vsym == null) {
				// No corresponding binary field
				if (!isJML) {
					utils.error(vdecl.source(), vdecl, "jml.message",
							"There is no binary field to match this declaration in the specification file: " +
									csym + "." + vdecl.name );
					return false;
				}
				// Enter the class in the package or the parent class

				// boolean declaredFinal = (vdecl.mods.flags & Flags.FINAL) != 0;
				MemberEnter me = MemberEnter.instance(context);
				var savedEnv = me.env;
				me.env = specsEnv;
				me.visitVarDef(vdecl); // Does all necessary type attribution
				vdecl.vartype.type = vdecl.type = vdecl.sym.type;
				vsym = vdecl.sym;
				// if (isGhostOrModel && vsym.owner.isInterface()) {
				// // not final by default; no static if declared instance
				// System.out.println("UNDOING FINAL " + !declaredFinal + (vsym.flags()&63));
				// if (!declaredFinal && (vsym.flags() & Flags.FINAL)!= 0) vsym.flags_field &=
				// ~Flags.FINAL;
				// if (utils.hasMod(vdecl.mods, Modifiers.INSTANCE)) vsym.flags_field &=
				// ~Flags.STATIC;
				// }
				me.env = savedEnv;

				if (debugEnter) System.out.println("enter: Entered JML field: " + vsym.type + " " + vsym + " (owner: " + vsym.owner + ")");
				ok = true;
			} else if (vsym.name != names.error) {
				// Found a matching binary field
				boolean matchIsJML = utils.isJML(vsym.flags());
				JmlSpecs.FieldSpecs fspecs = JmlSpecs.instance(context).get(vsym); // Raw get to see if specs are present
				if ((isJML || matchIsJML) && fspecs == null) {
					utils.error(vdecl.source(), vdecl, "jml.internal", "No FieldSpecs for an already entered JML field " + csym + "." + vsym);
				}
				var prevDecl = fspecs == null ? null : fspecs.decl;
				if (isJML) {
					if (matchIsJML) {
						utils.error(vdecl.source(), vdecl, "jml.message",
								"This JML field declaration conflicts with a previous JML field: " + csym + "." + vsym);
						// FIXME - Conflicts with a JML declaration added above - but can we get a decl to point to?
					} else {
						utils.error(vdecl.source(), vdecl, "jml.message",
								"This JML field declaration conflicts with an existing field with the same name: "
										+ csym + "." + vsym);
						// FIXME - Conflicts with a JML declaration added above - but can we get a decl to point to?
						//							if (javaVDecl != null)
					}
					if (prevDecl != null) utils.error(prevDecl.source(), prevDecl, "jml.associated.decl.cf",
							utils.locationString(vdecl.pos, vdecl.source()));
					return false;
				}
				if (matchIsJML) {
					utils.error(vdecl, "jml.message",
							"This Java field declaration conflicts with a previous JML field: " + csym + "." + vsym);
					if (prevDecl != null) utils.error(prevDecl.source(), prevDecl, "jml.associated.decl.cf",
							utils.locationString(vdecl.pos, vdecl.source()));
					return false;
				}
				if (fspecs != null) {
					utils.errorAndAssociatedDeclaration(vdecl.source(), vdecl, fspecs.decl.source(), fspecs.decl,
							"jml.message",
							"This JML field declaration conflicts with an existing field with the same name: "
									+ csym + "." + vsym);
				}

				// Attribute the type and annotations of vdecl
				// FIXME - review this annotation and type attribution code. Did it come from somewhere
				if (vdecl.vartype instanceof JCAnnotatedType) {
				    for (var a : ((JCAnnotatedType) vdecl.vartype).annotations) {
				        a.attribute = annotate.attributeTypeAnnotation(a, syms.annotationType, specsEnv);
				    }
				}
				Type t = Attr.instance(context).attribType(vdecl.vartype, specsEnv);
				annotate.flush();

				if (t == null) t = vdecl.vartype.type; // FIXME - not sure where attribType puts its result
				if (!specsTypeSufficientlyMatches(t, vsym.type)) {
					String msg = "Type of field " + vdecl.name
							+ " in specification differs from type in binary: " + t + " vs. "
							+ vsym.type;
					return false;
				}
				ok = true;
				vdecl.type = vdecl.vartype.type = vsym.type;
				vdecl.sym = vsym;

				if (ok && debugEnter) System.out.println("enter: Matched field to binary: " + vsym + " (owner: " + csym + ")");
			} else {
				ok = false;
				vdecl.type = vdecl.vartype.type = vsym.type;
			}
		} catch (Throwable t) {
			utils.error(vdecl.sourcefile, vdecl, "jml.message", "Exception while entering field from jml for binary: " + csym + "." + vdecl.name);
			t.printStackTrace(System.out);
			ok = false;
		} finally {
			if (vsym != null) {
				JmlSpecs.instance(context).putSpecs(vsym, vdecl.fieldSpecs);
				if (!ok) JmlSpecs.instance(context).setStatus(vsym, JmlSpecs.SpecsStatus.ERROR);
			}
		}
		return ok;
	}


	/** Finds a member field of 'csym' that has the same name as 'vdecl'; 
     * if found, attributes the type and annotations of 'vdecl' in the given 'env';
     * returns null or the VarSymbol of the found field
     */
    public VarSymbol findVarInBinary(ClassSymbol csym, JmlVariableDecl vdecl) {
    	Name vname = vdecl.name;
    	var iter = csym.members().getSymbolsByName(vname, s -> (s instanceof VarSymbol && s.owner == csym)).iterator();
    	if (iter.hasNext()) {
    		Symbol vsym = iter.next();
    		if (iter.hasNext()) {
    			var v = iter.next();
    			// This should never happen - two binary fields with the same name
    			if (vsym.name != names.error)
    				utils.error(vdecl.sourcefile, vdecl, "jml.message", "Unexpectedly found duplicate binary field symbols named " + vname
    						+ " in " + csym + " (" + vsym + " vs. " + v + ")");
    		}
    		return (VarSymbol) vsym;
    	}
    	return null;
    }

    /** Returns true iff the two arguments are the same type, modulo remapping of the type parameters
     */
    public boolean specsTypeSufficientlyMatches(Type specsType, Type javaType) {
        // The difficulty here is that TypeVars show up as different types,
        // and that binary types are erased, so do not have type arguments.
        // if (sym.name.toString().equals("k")) System.out.println("COMPARING " + sym +
        // " " + isBinary + " " + specsType + " " + javaType + " " +
        // (specsType.getClass()));
        if (types.isSameType(specsType, javaType))
            return true;
//      if ((specsType instanceof Type.TypeVar) != (javaType instanceof Type.TypeVar)) return false;
//      if (specsType instanceof Type.TypeVar) return specsType.toString().equals(javaType.toString()); 
//      if (!isBinary) return false;

        if (specsType.toString().startsWith(javaType.toString()))
            return true;
        return false; // types.isSubtype(specsType, javaType);
    }


    //    // FIXME - needs review
//    /** Compares the type parameters for the Java class denoted by csym and the 
//     * type parameters in the given type declaration (typically from a 
//     * specification file), in the context of the given name environment.
//     * Issues error messages if types or names do not match; attributes
//     * the types; returns false if there were errors.
//     * @param csym the class whose local env we are manipulating
//     * @param specTypeDeclaration the declaration of the class in a specification file
//     * @param classEnv the environment which is modified by the addition of any type parameter information
//     */
	public boolean checkAndEnterTypeParameters(ClassSymbol csym, JmlClassDecl specTypeDeclaration,
			Env<AttrContext> classEnv) {
		// utils.warning(-1, "jml.message", "TYPEPARAMS " + csym + " " +
		// specTypeDeclaration.name + " " + specTypeDeclaration.sym + " " +
		// ((JmlClassDecl)classEnv.tree).name);
		Env<AttrContext> localEnv = classEnv;
		// Scope enterScope = enterScope(classEnv);
		boolean result = true;
		int numSpecTypeParams = specTypeDeclaration.typarams.size();
		int numJavaTypeParams = csym.type.getTypeArguments().size();
		if (numSpecTypeParams != numJavaTypeParams) {
			utils.error(specTypeDeclaration.source(), specTypeDeclaration.pos(), "jml.mismatched.type.arguments",
					specTypeDeclaration.name, csym.type.toString());
			return false;
		}
        for (int i = 0; i < numSpecTypeParams; i++) {
            JCTree.JCTypeParameter specTV = specTypeDeclaration.typarams.get(i);
            var javaTV = (Type.TypeVar) ((ClassType) csym.type).getTypeArguments().get(i);
            if (specTV.name != javaTV.tsym.name) {
                utils.error(specTV.pos(), "jml.mismatched.type.parameter.name", specTypeDeclaration.name, csym.fullname,
                        specTV.name, javaTV.tsym.name);
                result = false;
            }
        }
        if (!result) return result;

		
		int nerrors = log.nerrors;

		var env = classEnv;
		
        specTypeDeclaration.sym = csym;
        for (int i = 0; i < numSpecTypeParams; i++) {
            JCTree.JCTypeParameter specTV = specTypeDeclaration.typarams.get(i);
            var javaTV = (Type.TypeVar) ((ClassType) csym.type).getTypeArguments().get(i);
            // classEnter will set the type of the Type Variable, but it sets it to
            // something new for each instance, which causes trouble in type matching
            // that I have not figured out. Here we preemptively set the type to be the
            // same as the Java type that it matches in the specification.
            specTV.type = javaTV;
            classEnter(specTV,localEnv);
        }
        for (int i = 0; i < numSpecTypeParams; i++) {
            JCTree.JCTypeParameter specTV = specTypeDeclaration.typarams.get(i);
            var javaTV = (Type.TypeVar) ((ClassType) csym.type).getTypeArguments().get(i);
            
            result &= checkAndCopyBounds(csym, specTV, specTV.getBounds(), javaTV.getUpperBound(), localEnv);
        }
        if (!result) return result;


        Env<AttrContext> baseEnv = baseEnv(specTypeDeclaration, env);
        attribSuperTypes(env, baseEnv);

        if (!csym.isInterface()) check(specTypeDeclaration, specTypeDeclaration.extending, csym.getSuperclass());

        var iter = csym.getInterfaces().iterator();
        for (var iface : specTypeDeclaration.implementing) {
            if (!iter.hasNext()) {
                check(specTypeDeclaration, iface, null);
                break;
            }
            check(specTypeDeclaration, iface, iter.next());
        }
        if (iter.hasNext()) {
            check(specTypeDeclaration, null, iter.next());
        }

//        // FIXME need to check that the types have the same bounds
		if (nerrors != log.nerrors) return false;
		return result;
	}
	
	public boolean checkAndCopyBounds(ClassSymbol owner, JCTree.JCTypeParameter specTV, List<JCExpression> specBounds, Type javaType, Env<AttrContext> localenv) {
	    if (specBounds.isEmpty() ) {
	        if (javaType.tsym == syms.objectType.tsym) return true;
	        utils.error(specTV, "jml.message", "Type parameter " + specTV + " is missing an upper bound: " + javaType);
	        return false;
	    }
	    Attr attr = JmlAttr.instance(context);
	    specBounds.forEach(b->attr.attribType(b,localenv));
	    if (specBounds.size() == 1) {
	        //System.out.println("BOUND " + specTV + " ^ " + specBounds.head + " " + specBounds.head.type + " " + specBounds.head.getClass() + " " + javaType);
//	        specBounds.head.type = javaType;
	        return true;
	    }
	    // FIXME - need to check that number of bounds is the same
        System.out.println("BOUNDS " + specTV + " ^ " + specBounds.size() + " " + specBounds + " # " + javaType + " " + javaType.getClass() );
	    return true;
	}

	public boolean check(JmlClassDecl specTypeDeclaration, JCExpression e, Type t) {
		// System.out.println("CHECKING " + e + " " + e.type + " " + t);
		if (e == null) {
			if (t == Type.noType || t == syms.objectType || t == syms.annotationType
					|| t.toString().startsWith("java.lang.Enum"))
				return true;
			utils.error(specTypeDeclaration.pos, "jml.message", "Missing super type or interface: " + t);
			return false;
		} else if (e.type == null) {
			utils.warning(e, "jml.message", "No type for " + e);
		} else if (t == null || !types.isSameType(e.type, t)) {
			utils.error(e, "jml.message", "Mismatched types: " + e.type + " vs. " + t);
			return false;
		}
		int numSpecTypeParams = e instanceof JCTypeApply et ? et.arguments.size() : 0;
		int numJavaTypeParams = t.getTypeArguments().size();
		if (numSpecTypeParams != numJavaTypeParams) {
			utils.error(specTypeDeclaration.source(), specTypeDeclaration.pos(), "jml.mismatched.type.arguments", e, t);
			return false;
		}
		for (int i = 0; i < numSpecTypeParams; i++) {
			var specTV = ((JCTypeApply) e).arguments.get(i);
			Type javaTV = t.getTypeArguments().get(i);
			if (!types.isSameType(specTV.type, javaTV)) {
				utils.error(specTV.pos(), "jml.message",
						"Mismatched type parameters: " + specTV.type + " vs. " + javaTV);
				return false;
			}
		}
		return true;
	}

	protected void attribSuperTypes(Env<AttrContext> env, Env<AttrContext> baseEnv) {
		JmlAttr attr = JmlAttr.instance(context);
		JCClassDecl tree = env.enclClass;
		ClassSymbol sym = tree.sym;
		ClassType ct = (ClassType) sym.type;
		// Determine supertype.
		Type supertype;
		JCExpression extending;
		// if (org.jmlspecs.openjml.Utils.isJML())
		// ((JmlAttr)attr).utils.warning(tree.pos,"jml.message","ASUPERTYPES " +
		// tree.name + " " + sym + " " + ct + " " + tree.extending + " : " +
		// tree.implementing);

		if (tree.extending != null) {
			extending = clearTypeParams(tree.extending);
			supertype = attr.attribBase(extending, baseEnv, tree, true, false, true);
			if (supertype == syms.recordType) {
				log.error(tree, Errors.InvalidSupertypeRecord(supertype.tsym));
			}
			tree.extending.type = supertype;
		} else {
			extending = null;
			supertype = ((tree.mods.flags & Flags.ENUM) != 0)
					? attr.attribBase(enumBase(tree.pos, sym), baseEnv, tree, true, false, false)
					: (sym.fullname == names.java_lang_Object) ? Type.noType
							: sym.isRecord() ? syms.recordType : syms.objectType;
		}
		ct.supertype_field = supertype;

		// Determine interfaces.
		ListBuffer<Type> interfaces = new ListBuffer<>();
		ListBuffer<Type> all_interfaces = null; // lazy init
		List<JCExpression> interfaceTrees = tree.implementing;
		for (JCExpression iface : interfaceTrees) {
			// if (org.jmlspecs.openjml.Utils.isJML())
			// ((JmlAttr)attr).utils.warning(tree.pos,"jml.message","ASUPERTYPES-A " + iface
			// + " " + ct);
			iface = clearTypeParams(iface);
			// if (org.jmlspecs.openjml.Utils.isJML())
			// ((JmlAttr)attr).utils.warning(tree.pos,"jml.message","ASUPERTYPES-B " + iface
			// );
			Type it = attr.attribBase(iface, baseEnv, tree, false, true, true);
			// if (org.jmlspecs.openjml.Utils.isJML())
			// ((JmlAttr)attr).utils.warning(tree.pos,"jml.message","ASUPERTYPES-C " + iface
			// + " " + it);
			iface.type = it;
			if (it.hasTag(CLASS)) {
				interfaces.append(it);
				if (all_interfaces != null)
					all_interfaces.append(it);
			} else {
				if (all_interfaces == null)
					all_interfaces = new ListBuffer<Type>().appendList(interfaces);
				// all_interfaces.append(modelMissingTypes(baseEnv, it, iface, true));
			}
		}

//        // Determine permits.
//        ListBuffer<Symbol> permittedSubtypeSymbols = new ListBuffer<>();
//        List<JCExpression> permittedTrees = tree.permitting;
//        for (JCExpression permitted : permittedTrees) {
//            Type pt = attr.attribBase(permitted, baseEnv, tree, false, false, false);
//            permittedSubtypeSymbols.append(pt.tsym);
//        }
//
		if ((sym.flags_field & Flags.ANNOTATION) != 0) {
			ct.interfaces_field = List.of(syms.annotationType);
			ct.all_interfaces_field = ct.interfaces_field;
		} else {
			ct.interfaces_field = interfaces.toList();
			ct.all_interfaces_field = (all_interfaces == null) ? ct.interfaces_field : all_interfaces.toList();
		}
//
//        /* it could be that there are already some symbols in the permitted list, for the case
//         * where there are subtypes in the same compilation unit but the permits list is empty
//         * so don't overwrite the permitted list if it is not empty
//         */
//        if (!permittedSubtypeSymbols.isEmpty()) {
//            sym.permitted = permittedSubtypeSymbols.toList();
//        }
//        sym.isPermittedExplicit = !permittedSubtypeSymbols.isEmpty();
	}

	// where:
	protected Env<AttrContext> baseEnv(JCClassDecl tree, Env<AttrContext> env) {
		WriteableScope baseScope = WriteableScope.create(tree.sym);
		// import already entered local classes into base scope
		for (Symbol sym : env.outer.info.scope.getSymbols(Scope.LookupKind.NON_RECURSIVE)) {
			if (sym.isDirectlyOrIndirectlyLocal()) {
				baseScope.enter(sym);
			}
		}
		// import current type-parameters into base scope
		if (tree.typarams != null)
			for (List<JCTypeParameter> typarams = tree.typarams; typarams.nonEmpty(); typarams = typarams.tail)
				baseScope.enter(typarams.head.type.tsym);
		Env<AttrContext> outer = env.outer; // the base clause can't see members of this class
		Env<AttrContext> localEnv = outer.dup(tree, outer.info.dup(baseScope));
		localEnv.baseClause = true;
		localEnv.outer = outer;
		localEnv.info.isSelfCall = false;
		return localEnv;
	}

	protected JCExpression enumBase(int pos, ClassSymbol c) {
		JCExpression result = make.at(pos).TypeApply(make.QualIdent(syms.enumSym), List.of(make.Type(c.type)));
		return result;
	}

	// FIXME - what is this suppsed to be doing
	protected JCExpression clearTypeParams(JCExpression superType) {
		return superType;
	}

	protected boolean classNameMatchesFileName(ClassSymbol c, Env<AttrContext> env) {
		boolean b = env.toplevel.sourcefile.isNameCompatible(c.name.toString(), JavaFileObject.Kind.SOURCE);
		if (!b)
			b = env.toplevel.sourcefile.isNameCompatible(c.name.toString(), JavaFileObject.Kind.JML);
		return b;
	}

    public int nestingLevel = 0;

    public void hold() {
        nestingLevel++;
        if (debugSpecs) System.out.println("specs: hold level=" + nestingLevel);
    }

    public void release() {
        nestingLevel--;
        if (debugSpecs) System.out.println("specs: release level=" + nestingLevel);
    }

    public boolean flush() {
        if (nestingLevel == 0) {
            var any = !binaryEnterTodo.isEmpty();
            completeBinaryEnterTodo();
            return any;
        }
        return false;
    }

    final static boolean debugSpecs = org.jmlspecs.openjml.Utils.debug("specs");

	/**
	 * Queues a class for loading specs. Once loaded, JmlSpecs contains the specs
	 * for each class, method, and field, but they are not yet attributed. This is
	 * called to load specs for the binary as in the 
	 * current implementation, source class spec are parsed and loaded along with the
	 * source class itself).
	 * 
	 * Returns true if the class was actually loaded, false if it was just queued
	 * 
	 * @param csymbol the class whose specs are wanted
	 */
	public boolean requestSpecs(ClassSymbol csymbol) {
	    // Requests for nested classes are changed to a request for their outermost class
		while (csymbol.owner instanceof ClassSymbol)
			csymbol = (ClassSymbol) csymbol.owner;

		JmlSpecs.SpecsStatus tsp = JmlSpecs.instance(context).status(csymbol);
		if (debugSpecs) System.out.println("specs: requestSpecs for " + csymbol + " " + tsp + " level=" + nestingLevel
		    + " " + binaryEnterTodo.contains(csymbol) + " size=" + binaryEnterTodo.size());
		if (!tsp.less(JmlSpecs.SpecsStatus.QUEUED)) {
		    if (tsp == JmlSpecs.SpecsStatus.QUEUED) {
		        if (debugSpecs || utils.verbose()) System.out.println("specs: Requesting specs " + csymbol + ", but specs already in progress");
	            if (nestingLevel == 0) {
	                completeBinaryEnterTodo();
	                return JmlSpecs.SpecsStatus.QUEUED.less(JmlSpecs.instance(context).status(csymbol));
	            }
	            return false;
		    } else {
		        if (debugSpecs || utils.verbose()) System.out.println("specs: Requesting specs " + csymbol + ", but specs already loaded or attributed");
		        return true;
		    }
		} else {
			// The binary Java class itself is already loaded - it is needed to produce the classSymbol itself

			if (!binaryEnterTodo.contains(csymbol)) {
				nestingLevel++;
				try {
//					// It can happen that the specs are loaded during the loading of the super class
//					// since complete() may be called on the class in order to fetch its superclass,
//					// or during the loading of any other class that happens to mention the type.
//					// So we recheck here, before reentering the class in the todo list
//				    if (!JmlSpecs.instance(context).status(csymbol).less(JmlSpecs.SpecsStatus.SPECS_LOADED)) return true;
//				    if (JmlSpecs.instance(context).status(csymbol) != JmlSpecs.SpecsStatus.NOT_LOADED) return false;

					// Classes are prepended to the todo list in reverse order, so that parent
					// classes have specs read first.

					// Note that nested classes are specified in the same source file as their
					// enclosing classes
					// Everything within a specification text file is loaded together

					JmlSpecs.instance(context).setStatus(csymbol, JmlSpecs.SpecsStatus.QUEUED);
					if (debugSpecs) System.out.println("specs: Queueing specs request for " + csymbol + " [" + nestingLevel + "]" + " "
								+ binaryEnterTodo.contains(csymbol) + " " + csymbol.hashCode());
					binaryEnterTodo.prepend(csymbol);
					
					if (!utils.isExtensionValueType(csymbol.type)) {
					    for (Type t : csymbol.getInterfaces()) {
					        requestSpecs((ClassSymbol) t.tsym);
					    }
					    if (csymbol.getSuperclass() != Type.noType) { // Object has noType as a superclass
					        requestSpecs((ClassSymbol) csymbol.getSuperclass().tsym);
					    }
					}
					if (debugSpecs) System.out.println("specs: Finished queueing supers for " + csymbol);

				} finally {
					nestingLevel--;
				}
			}

			// This nesting level is used to be sure we do not start processing a class,
			// say a superclass, before we have finished loading specs for a given class
			if (nestingLevel == 0) {
			    completeBinaryEnterTodo();
	            return true;
			}
            return false;
		}
	}

	ListBuffer<ClassSymbol> binaryEnterTodo = new ListBuffer<ClassSymbol>();

	/** This processes the entires on the 'binaryEnterTodo' queue, for each entry it reads the specs (from a .jml file)
	 * and connects the specs with the binary via 'specsEnter'. This is only for specs connected with binary classes.
	 * Anything with a source file should go through Enter.main
	 */
	public void completeBinaryEnterTodo() {
        if (debugSpecs) System.out.println("specs: Starting completeBinaryEnterTodo " + binaryEnterTodo.size());
		JmlSpecs specs = JmlSpecs.instance(context);
		while (!binaryEnterTodo.isEmpty()) {
			ClassSymbol csymbol = binaryEnterTodo.remove();
			var sourceEnv = getEnv(csymbol);
			if (sourceEnv != null) {
			    // This is fairly drastic violation of understood invariants.
			    // We are reading specs for a binary class; there should be no source AST or Env
			    JmlCompilationUnit javaCU = (JmlCompilationUnit) sourceEnv.toplevel;
				utils.error(javaCU.sourcefile, javaCU, "jml.internal",
						"Unexpectedly have a source environment when expecting a binary: " + csymbol + " " + javaCU.sourcefile);
				continue;
			}

			if (debugSpecs) System.out.println("specs: Dequeued to enter specs: " + csymbol + " " + specs.status(csymbol) );

			// Last check to see if specs are already present
			if (JmlSpecs.SpecsStatus.QUEUED.less(specs.status(csymbol))) continue;

			nestingLevel++;
			JmlCompilationUnit speccu = null;
			try {
				speccu = JmlCompiler.instance(context).parseSpecs(csymbol);
				if (speccu != null) {
				    // There is a specs file for the binary
				    speccu.sourceCU = null; // null indicates a binary; non-null a source Java file
				    speccu.specsCompilationUnit = speccu;
				    specsEnter(speccu);
				    TypeSpecs tspecs = specs.get(csymbol);
				    if (tspecs == null) {
                        // Specs were found but they did not match and were discarded
				        // But need to record some empty specs
	                    recordEmptySpecs(csymbol); // so we don't keep trying to load it
				    } else if (tspecs.specDecl == null) {
				        // Specs were found but they did not match and were discarded
				        // Empty specs have already been recorded
				    } else {
//				        csymbol.flags_field |= Flags.UNATTRIBUTED; // FIXME - verify that this is needed
				    }
				} else {
				    // No specs -- binary with no .jml file
				    recordEmptySpecs(csymbol); // so we don't keep trying to load it
				    if (org.jmlspecs.openjml.JmlOptions.instance(context).warningKeys.getOrDefault("missing-specs", false)) {
				        utils.warning("jml.message", "[missing-specs] No specifications file found for binary " + csymbol);
				    }
				}

			} finally {
				if (debugSpecs) System.out.println("specs: Completed entering specs for binary " + csymbol + " specfile: " + 
				                        (speccu == null ? "(no spec file)" : speccu.sourcefile));
				nestingLevel--;
			}
		}
	}

	/** Records an empty type specs structure, with no spec file or Env, just any Java modifiers */
	public void recordEmptySpecs(ClassSymbol csymbol) {
    	JmlSpecs.TypeSpecs typespecs = new JmlSpecs.TypeSpecs(csymbol, null, 
    			(JmlTree.JmlModifiers)JmlTree.Maker.instance(context).Modifiers(csymbol.flags()), 
    			null);
    	JmlSpecs.instance(context).putSpecs(csymbol,typespecs);
    }

	/** Just initializes the import scopes -- does not load any imports into them. */
    @Override
    Env<AttrContext> topLevelEnv(JCCompilationUnit tree) {
        Env<AttrContext> localEnv = super.topLevelEnv(tree);
        var jtree = (JmlCompilationUnit)tree;
        jtree.topLevelEnv = localEnv;
        var speccu = jtree.specsCompilationUnit;
        if (speccu != null && speccu != tree) {
            speccu.toplevelScope = jtree.toplevelScope;
            Env<AttrContext> specLocalEnv = super.topLevelEnv(speccu);
            // The spec cu and the source cu share the top level scope. Anything in the source cu is automatically seen in the
            // spec cu. Anything extra in the spec cu must be model and is distinguished by JmlResolve.allowJML
            speccu.topLevelEnv = specLocalEnv;
        }
        return localEnv;
    }



	/** Overrides Enter.unenter solely to enable scanning over JML AST nodes */
	@Override
	public void unenter(JCCompilationUnit topLevel, JCTree tree) {
		new JmlUnenterScanner(topLevel.modle).scan(tree);
	}

	/** Extends Enter.UnenterScanner solely to enable scanning over JML AST nodes, via default methods in IJmlVisitor */ 
	class JmlUnenterScanner extends UnenterScanner implements org.jmlspecs.openjml.visitors.IJmlVisitor {

		public JmlUnenterScanner(ModuleSymbol msym) {
			super(msym);
		}

	}

}
