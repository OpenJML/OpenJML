/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.comp;


import java.util.Collection;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.ext.Modifiers;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.CompletionFailure;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.code.Type.TypeVar;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.main.JmlCompiler;
import com.sun.tools.javac.main.Option.PkgInfo;
import com.sun.tools.javac.resources.CompilerProperties.Errors;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.Pretty;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;

/** 
 * This class extends Enter, which has the job of creating symbols for all the
 * types mentioned in a set of parse trees. JmlEnter adds to that functionality
 * to create symbols for all JML types (i.e., model classes) that are present in
 * the parse trees.  In addition it adds to the source class file any model classes 
 * that need to be compiled and it links each class declaration to its 
 * specifications (another class declaration), or to itself.
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
            public Enter make(Context context) {
                return new JmlEnter(context);
            }
        });
    }

    /** The context in which this instance was created. */
    /*@non_null*/
    final protected Context context;

//    /** A cached value of the specs tool for this compilation context */
//    /*@non_null*/
//    final protected JmlSpecs specs;
    
    /** A cached value of the Utils tool */
    /*@non_null*/
    final protected Utils utils;

    /** Creates an instance of the JmlEnter tool in the given context; note that
     * any options must be already set in Options prior to creating the tool.
     * @param context the compilation context to use for this tool
     */
    //@ assignable this.*;
    public JmlEnter(Context context) {
        super(context); // automatically registers the new object
        this.context = context;
        this.utils = Utils.instance(context);
//        this.specs = JmlSpecs.instance(context);
    }
    
    /** The env (scope) to be used within specifications corresponding to the env for Java, as passed internally
     * from visitTopLevel to classEnter.
     */
    private Env<AttrContext> specTopEnv;
    
    public String getTopLevelName(JmlCompilationUnit cu) {
    	String nn = cu.sourcefile.getName();
    	nn = nn.substring(0,nn.lastIndexOf('.'));
    	int k = nn.lastIndexOf('/');
    	int kk = nn.lastIndexOf('\\');
    	k = k>kk?k:kk;
    	nn = nn.substring(k+1);
    	var pid = cu.pid;
    	if (pid != null) nn = pid.getPackageName() + "." + nn;
    	return nn;
    }
    
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
		if (!(tree instanceof JmlCompilationUnit)) {
			utils.error("jml.internal","Encountered an unexpected JCCompilationUnit instead of a JmlCompilationUnit in JmlEnter.visitTopeLevel");
			return;
		}
		var jtree = (JmlCompilationUnit)tree;
    	JavaFileObject prevSource = log.useSource(tree.sourcefile);
    	try {
    		String n = getTopLevelName(jtree);
    		JavaFileObject specJfo = JmlSpecs.instance(context).findAnySpecFile(n);
    		// FIXME _ warn about specs path if nothing found
    		if (specJfo == null) specJfo = tree.sourcefile;
    		var speccu = (JmlCompilationUnit)tree;
    		if (!specJfo.toUri().equals(tree.sourcefile.toUri())) {
    			speccu = JmlCompiler.instance(context).parseSingleFile(specJfo);
    			var p = findPackageDef(tree);
    			var pp = findPackageDef(speccu);
    			String pn = p == null ? "<default package>" : Pretty.toSimpleString(p);
    			String ppn = pp == null ? "<default package>" : Pretty.toSimpleString(pp);
    			if (!pn.equals(ppn)) {
    				utils.error(speccu.sourcefile, pp==null?p:pp,
    						"jml.mismatched.package",
    						"The package in " + speccu.sourcefile.getName() + " is " + ppn,
    						"package in .java file: " + pn);
    			}
    		}
    		var declsToAdd = matchMembers(null, tree.defs, speccu.defs, speccu.sourcefile);
        	if (declsToAdd.size() != 0) {
        		tree.defs = tree.defs.appendList(declsToAdd);
        	}
    		jtree.specsCompilationUnit = speccu;
    		
    		super.visitTopLevel(tree);
    		
//    		if (utils.jmlverbose >= Utils.JMLVERBOSE) context.get(Main.IProgressListener.class).report(2,"entering " + jmltree.sourcefile.getName());
//
//    		// FIXME - a problem here is that the specs and the model fields/classes/methods will be attributed using the set of imports from the Java source file
//
//    		JmlCompilationUnit specscu;
//    		if (jmltree.specsCompilationUnit == null) {
//    			// If this is the case we have called visitTopLevel on a specs file
//    			specTopEnv = null;
//    			specscu = jmltree;
//    		} else {
//    			specscu = jmltree.specsCompilationUnit;
//    		}
//
//
//    		String owner;
//
//    		{
//    			boolean addEnv = false;
//    			boolean isPkgInfo = tree.sourcefile.isNameCompatible("package-info",
//    					JavaFileObject.Kind.SOURCE);
//    			// This if-else statement copied from Enter
//    			JCPackageDecl pd = tree.getPackage();
//    			if (pd != null) {
//    				tree.packge = pd.packge = syms.enterPackage(tree.modle, TreeInfo.fullName(pd.pid));
//    				if (   pd.annotations.nonEmpty()
//    						|| pkginfoOpt == PkgInfo.ALWAYS
//    						|| tree.docComments != null) {
//    					if (isPkgInfo) {
//    						addEnv = true;
//    					} else if (pd.annotations.nonEmpty()) {
//    						log.error(pd.annotations.head.pos(),
//    								Errors.PkgAnnotationsSbInPackageInfoJava);
//    					}
//    				}
//    			} else {
//    				tree.packge = tree.modle.unnamedPackage;
//    			}
//    			specscu.packge.complete(); // Find all classes in package.
//    			specTopEnv = topLevelEnv(specscu);
//    			specscu.topLevelEnv = specTopEnv;
//    		}
//
//    		// Match specifications to the corresponding Java class, for each (toplevel) class; 
//    		if (jmltree.specsCompilationUnit != null && jmltree.mode != JmlCompilationUnit.SPEC_FOR_BINARY) {
//    			tree.defs = matchClasses(tree.defs, jmltree.specsCompilationUnit.defs, tree.sourcefile.toString());
//    		} else {
//    			//            specscu.defs = matchClassesForBinary(specTopEnv, owner, specscu.defs, null, tree.sourcefile.toString());
//    		}
//
//    		if (jmltree.mode == JmlCompilationUnit.SPEC_FOR_BINARY) {
//    			checkForUnmatched(specscu);
//    		}
//
//    		// Then do all the regular Java registering of packages and types
//    		super.visitTopLevel(jmltree);
//
//    		if (jmltree.mode == JmlCompilationUnit.SPEC_FOR_SOURCE) {
//    			checkForUnmatched(specscu);
//    		}
//
//
//    		// Checking that the specs and the java source declare the same package 
//    		//        if (jmltree.specsCompilationUnit != null && jmltree.specsCompilationUnit != jmltree) {
//    		//
//    		//            if (specscu.packge != jmltree.packge) {
//    		//                // FIXME - use jml.mismatched.package
//    		//                int pos = specscu.getPackageName()==null ? specscu.pos : specscu.getPackageName().pos;
//    		//                utils.error(specscu.sourcefile,pos,
//    		//                        "jml.mismatched.package",
//    		//                        "The package in " + specscu.sourcefile.getName() + " is " + (specscu.pid == null ? "<default>" : specscu.pid.toString()),"package in .java file: " + jmltree.packge.toString());
//    		//                String s = utils.locationString(pos, specscu.sourcefile);
//    		//                utils.error(jmltree.getSourceFile(), jmltree.getPackageName().pos,"jml.associated.decl.cf",s);
//    		//            }
//    		////            specscu.packge = jmltree.packge;
//    		//        }
//    		if (utils.jmlverbose >= Utils.JMLVERBOSE) context.get(Main.IProgressListener.class).report(2,"  completed entering " + jmltree.sourcefile.getName());

        } finally {
            log.useSource(prevSource);
        }
    }

//    <T extends JCTree> List<Type> classEnter(List<T> trees, Env<AttrContext> env) {
//    	var result = super.classEnter(trees, env);
//    	return result;
//    }

    public void checkForUnmatched(JmlCompilationUnit jmltree) {
        String pack = jmltree.pid == null ? "" : (jmltree.pid.toString() + ".");
        ListBuffer<JCTree> newlist = new ListBuffer<>();
        boolean removed = false;
        for (JCTree d : jmltree.defs) {
            if (d instanceof JmlClassDecl) {
                JmlClassDecl cd = (JmlClassDecl)d;
                if (!utils.isJML(cd.mods)) { 
                    String cdn = pack + cd.name.toString();
                    try {
                        if (ClassReader.instance(context).enterClass(names.fromString(cdn)) == null) {
                            utils.error(jmltree.sourcefile, cd.pos,
                                    "jml.unmatched.type",cdn);
                            removed = true;
                            continue;
                        }
                    } catch (CompletionFailure ex) {
                        utils.error(jmltree.sourcefile, cd.pos,
                                "jml.unmatched.type",cdn);
                        removed = true;
                        continue;
                    }
                }
            }
            newlist.add(d);
        }
        if (removed) jmltree.defs = newlist.toList();
    }
    
    public boolean matches(JCExpression jtype, JCExpression stype) {
    	return Pretty.toSimpleString(jtype).equals(Pretty.toSimpleString(stype));
    }
    
    public boolean matches(JmlMethodDecl specsDecl, JmlMethodDecl javaDecl) {
    	if (!specsDecl.name.equals(javaDecl.name)) return false;
    	if (specsDecl.params.size() != javaDecl.params.size()) return false;
    	var jiter = specsDecl.params.iterator();
    	var siter = specsDecl.params.iterator();
    	while (jiter.hasNext()) {
    		if (!matches(jiter.next().vartype, siter.next().vartype)) return false;
    	}
    	return true;
    }

    public List<JCTree> matchMembers(/*@nullable*/ JCClassDecl owner, List<JCTree> javaDefs, List<JCTree> specsDefs, JavaFileObject javasource) {
    	ListBuffer<JCTree> adds = new ListBuffer<>();
    	if (javaDefs == specsDefs) {
    		for (var decl: javaDefs) {
    			if (decl instanceof JmlClassDecl) {
    				((JmlClassDecl)decl).specsDecl = (JmlClassDecl)decl;
    			} else if (decl instanceof JmlMethodDecl) {
    				((JmlMethodDecl)decl).specsDecl = (JmlMethodDecl)decl;
    			} else if (decl instanceof JmlVariableDecl) {
    				((JmlVariableDecl)decl).specsDecl = (JmlVariableDecl)decl;
    			}
    		}
    	} else {
        	var matched = new java.util.HashSet<JCTree>();
    		for (var decl: javaDefs) {
    			if (decl instanceof JmlClassDecl) {
    				JmlClassDecl javaDecl = (JmlClassDecl)decl;
    				x: {
    					for (var sdecl: specsDefs) {
    						if (!(sdecl instanceof JmlClassDecl)) continue;
    						JmlClassDecl specsDecl = (JmlClassDecl)sdecl;
    		    			boolean isSpecsJML = utils.isJML(specsDecl);
    						if (specsDecl.name.equals(javaDecl.name)) {
    							matched.add(specsDecl);
    							if (isSpecsJML) {
        							// A specification declaration matches a java declaration,
        							// but the specification declaration is in a JML annotation - error - but use it as a match anyway
        							utils.error(specsDecl.source(), specsDecl.pos,
        									"jml.duplicate.model",
        									specsDecl.name,javasource);
        							String s = utils.locationString(specsDecl.pos, specsDecl.source());
        							utils.error(javaDecl.source(), javaDecl.pos, "jml.associated.decl.cf", s);
    							}
    							javaDecl.specsDecl = specsDecl;
    							break x;
    						}
    					}
    					javaDecl.specsDecl = javaDecl; // FIXME - should be default specs
    				}
    			} else if (decl instanceof JmlMethodDecl) {
    				JmlMethodDecl javaDecl = (JmlMethodDecl)decl;
    				x: {
    					for (var sdecl: specsDefs) {
    						if (!(sdecl instanceof JmlMethodDecl)) continue;
    						JmlMethodDecl specsDecl = (JmlMethodDecl)sdecl;
    		    			boolean isSpecsJML = utils.isJML(specsDecl);
    						if (matches(specsDecl,javaDecl)) {
    							matched.add(specsDecl);
    							if (isSpecsJML) {
        							// A specification declaration matches a java declaration,
        							// but the specification declaration is in a JML annotation - error - but use it as a match anyway
        							utils.error(specsDecl.source(), specsDecl.pos,
        									"jml.duplicate.model",
        									specsDecl.name,javasource);
        							String s = utils.locationString(specsDecl.pos, specsDecl.source());
        							utils.error(javaDecl.source(), javaDecl.pos, "jml.associated.decl.cf", s);
    							}
    							javaDecl.specsDecl = specsDecl;
    							break x;
    						}
    					}
    					javaDecl.specsDecl = javaDecl; // FIXME - should be default specs
    				}

    			} else if (decl instanceof JmlVariableDecl) {
    				JmlVariableDecl javaDecl = (JmlVariableDecl)decl;
    				x: {
    					for (var sdecl: specsDefs) {
    						if (!(sdecl instanceof JmlVariableDecl)) continue;
    						JmlVariableDecl specsDecl = (JmlVariableDecl)sdecl;
    		    			boolean isSpecsJML = utils.isJML(specsDecl);
    						if (specsDecl.name.equals(javaDecl.name)) {
    							matched.add(specsDecl);
    							if (isSpecsJML) {
        							// A specification declaration matches a java declaration,
        							// but the specification declaration is in a JML annotation - error - but use it as a match anyway
        							utils.error(specsDecl.source(), specsDecl.pos,
        									"jml.duplicate.model",
        									specsDecl.name,javasource);
        							String s = utils.locationString(specsDecl.pos, specsDecl.source());
        							utils.error(javaDecl.source(), javaDecl.pos, "jml.associated.decl.cf", s);
    							}
    							javaDecl.specsDecl = specsDecl;
    							break x;
    						}
    					}
    					javaDecl.specsDecl = javaDecl; // FIXME - should be default specs
    				}
    			}
    		}
    		for (var sdecl: specsDefs) {
    			if (matched.contains(sdecl)) continue;
    			if (sdecl instanceof JmlClassDecl) {
    				var specDecl = (JmlClassDecl)sdecl;
    				if (utils.isJML(specDecl.mods)) {
    					adds.add(sdecl);
    					specDecl.specsDecl = specDecl;
    				} else {
    					utils.error(specDecl.source(), specDecl.pos,
    							"jml.orphan.jml.class.decl",
    							specDecl.name,javasource);
    				}
    			} else if (sdecl instanceof JmlMethodDecl) {
    				var specDecl = (JmlMethodDecl)sdecl;
    				if (utils.isJML(specDecl.mods)) {
    					adds.add(sdecl);
    					specDecl.specsDecl = specDecl;
    				} else if ((owner.mods.flags & Flags.RECORD) == 0) { // FIXME - handle records
    					utils.error(specDecl.source(), specDecl.pos,
    							"jml.no.method.match",
    							specDecl.name,javasource);
    				}
    			} else if (sdecl instanceof JmlVariableDecl) {
    				var specDecl = (JmlVariableDecl)sdecl;
    				if (utils.isJML(specDecl.mods)) {
    					adds.add(sdecl);
    					specDecl.specsDecl = specDecl;
    				} else if ((owner.mods.flags & Flags.RECORD) == 0) { // FIXME - handle records
    					utils.error(specDecl.source(), specDecl.pos,
    							"jml.no.var.match",
    							specDecl.name,javasource);
    				}
    			}
    		}
    	}
    	return adds.toList();
    }


    /** This routine matches class declarations in the specifications ('specsDefs' list) with Java declarations ('defs' list).
     * Note that these may be top-level declarations in corresponding files; they may also be lists of nested declaration
     * from corresponding nested locations. The composite list of declarations (to replace 'defs') is returned. Any duplicate
     * orphan declarations are warned about. The returned 'defs' will omit duplicates and include any classes in JML specifications;
     * thus this revised 'defs' list is the one to be submitted to 'classEnter'
     */
    public List<JCTree> matchClasses(List<JCTree> javaDefs, List<JCTree> specsDefs, JavaFileObject javasource) {
        ListBuffer<JCTree> newdefs = new ListBuffer<JCTree>();
//        if (defs !=  specsDefs) {
//            for (JCTree tt: defs) { // Iterate over the Java classes 
//                if (tt instanceof JmlTree.IInJML) {
//                    if (((JmlTree.IInJML)tt).isJML()) continue;
//                }
//                newdefs.add(tt);
//            }
//        } else {
//            newdefs.addAll(defs);
//        }
    	if (javaDefs == specsDefs) {
    		for (JCTree javadef: javaDefs) {
    			if (!(javadef instanceof JmlClassDecl)) continue;
    			JmlClassDecl jjavadef = (JmlClassDecl)javadef;
    			jjavadef.specsDecl = jjavadef;
    		}
    	} else {
    		for (JCTree specDecl: specsDefs) {  // Iterate over the classes in the specification, to find the matching java declaration
    			if (!(specDecl instanceof JmlClassDecl)) continue;
    			JmlClassDecl specClassDecl = (JmlClassDecl)specDecl;
    			boolean isSpecsJML = utils.isJML(specClassDecl.mods);
    			if (isSpecsJML) continue; // FIXME - ignore model classes for now
    			
    			// The declaration 'specClassDecl' is in a specification file.
    			// We need to find the Java declaration that it matches
    			// There is supposed to be one, and there should only be one declaration in the specsDefs list
    			// that matches a particular java declaration.
    			// A Java declaration need not have a match
    			Name name = specClassDecl.name;
    			JmlClassDecl matched = null;
    			for (JCTree javaDecl: javaDefs) { // Iterate over the list of Java declarations 
    				if (!(javaDecl instanceof JmlClassDecl)) continue;
    				JmlClassDecl jmlDecl = (JmlClassDecl)javaDecl;
    				if (name.equals(jmlDecl.name)) {
    					matched = jmlDecl;
    					if (jmlDecl.specsDecl == null) {
    						// No previous match, so far
    						if (isSpecsJML) {
    							// A specification declaration matches a java declaration,
    							// but the specification declaration is in a JML annotation - error - but use it as a match anyway
    							utils.error(specClassDecl.source(), specClassDecl.pos,
    									"jml.duplicate.model",
    									specClassDecl.name,javasource);
    							String s = utils.locationString(specClassDecl.pos, specClassDecl.source());
    							utils.error(jmlDecl.source(), jmlDecl.pos,"jml.associated.decl.cf",s);
    							jmlDecl.specsDecl = specClassDecl; // Attach the specification to the matching Java AST
//    						} else {
//    							// A specification declaration matches a java declaration,
//    							// but the declaration in the Java file is in a JML annotation, and the specification declaration is not
//    							// Since if the specs declaration list is different than the Java declaration list, 
//    							// any such JML annotated declarations are removed from the Java declaration list,
//    							// this must be a case of a file containing two declarations with the same name, 
//    							// one in a JML annotation and one not
//    							// Issue and error and omit the JML declaration
//    							newdefs = Utils.remove(newdefs, javaDecl);
//    							if (defs !=  specsDefs) {
//    								utils.error(javaDecl.source(), javaDecl.pos, "jml.internal", "Unexpected JML declaration in the Java file");
//    							} else {
//    								utils.error(javaDecl.source(), javaDecl.pos,"jml.duplicate.jml.class.decl", javaDecl.name);
//    								utils.error(specClassDecl.source(), specClassDecl.pos,"jml.associated.decl.cf",
//    										utils.locationString(javaDecl.pos, javaDecl.source()));
//    							}
//    						} else if (isJML && isSpecsJML) {
//    							if (javaDecl != specClassDecl) {
//    								// There are two declarations, both in JML annotations, with the same name
//    								utils.error(javaDecl.source(), javaDecl.pos,"jml.duplicate.jml.class.decl", javaDecl.name);
//    								utils.error(specClassDecl.source(), specClassDecl.pos,"jml.associated.decl.cf",
//    										utils.locationString(javaDecl.pos, javaDecl.source()));
//    								newdefs = Utils.remove(newdefs,specClassDecl);
//    							} else {
//    								// The two declarations are the same one - OK
//    								javaDecl.specsDecl = specClassDecl;
//    							}
    						} else {
    							// else OK match
    							jmlDecl.specsDecl = specClassDecl; // Attach the specification to the matching Java AST
    						}
    					} else {  // Duplicate - warn and ignore
//    						if (!isJML) {
//    							// This less informational error message is here just to duplicate previous behavior (and the Java compiler) for Java duplicates
//    							utils.error(specClassDecl.source(), specClassDecl.pos,"duplicate.class",specClassDecl.name);
//    						} else {
    							utils.error(specClassDecl.source(), specClassDecl.pos, "jml.duplicate.jml.class.decl", specClassDecl.name);
    							utils.error(specClassDecl.source(), jmlDecl.specsDecl.pos, "jml.associated.decl.cf",
    									utils.locationString(specClassDecl.pos, specClassDecl.source()));
//    						}
//    						if (!isJML && utils.isJML(javaDecl.specsDecl.mods) && !isSpecsJML) javaDecl.specsDecl = specClassDecl;
//    						newdefs = Utils.remove(newdefs, specClassDecl);
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
    					JCAnnotation x = utils.modToAnnotationAST(Modifiers.MODEL, specClassDecl.pos, specClassDecl.pos);
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
    		for (JCTree javadef: javaDefs) {
    			if (!(javadef instanceof JmlClassDecl)) continue;
    			JmlClassDecl jjavadef = (JmlClassDecl)javadef;
    			if (jjavadef.specsDecl == null) jjavadef.specsDecl = jjavadef;
    		}

        }
        return javaDefs;
    }
 
    public List<JCTree> matchFields(List<JCTree> javaDefs, List<JCTree> specsDefs, JavaFileObject javasource) {
        ListBuffer<JCTree> newdefs = new ListBuffer<JCTree>();
//        if (defs !=  specsDefs) {
//            for (JCTree tt: defs) { // Iterate over the Java classes 
//                if (tt instanceof JmlTree.IInJML) {
//                    if (((JmlTree.IInJML)tt).isJML()) continue;
//                }
//                newdefs.add(tt);
//            }
//        } else {
//            newdefs.addAll(defs);
//        }
    	if (javaDefs == specsDefs) {
    		for (JCTree javadef: javaDefs) {
    			if (!(javadef instanceof JmlVariableDecl)) continue;
    			JmlVariableDecl jjavadef = (JmlVariableDecl)javadef;
    			jjavadef.specsDecl = jjavadef;
    		}
    	} else {
    		for (JCTree specDecl: specsDefs) {  // Iterate over the classes in the specification, to find the matching java declaration
    			if (!(specDecl instanceof JmlVariableDecl)) continue;
    			JmlVariableDecl specVarDecl = (JmlVariableDecl)specDecl;
    			boolean isSpecsJML = utils.isJML(specVarDecl.mods);
    			if (isSpecsJML) continue; // FIXME - ignore model/ghost fields for now
    			
    			// The declaration 'specClassDecl' is in a specification file.
    			// We need to find the Java declaration that it matches
    			// There is supposed to be one, and there should only be one declaration in the specsDefs list
    			// that matches a particular java declaration.
    			// A Java declaration need not have a match
    			Name name = specVarDecl.name;
    			JmlVariableDecl matched = null;
    			for (JCTree javaDecl: javaDefs) { // Iterate over the list of Java declarations 
    				if (!(javaDecl instanceof JmlVariableDecl)) continue;
    				JmlVariableDecl jmlDecl = (JmlVariableDecl)javaDecl;
    				if (name.equals(jmlDecl.name)) {
    					matched = jmlDecl;
    					if (jmlDecl.specsDecl == null) {
    						// No previous match, so far
    						if (isSpecsJML) {
    							// A specification declaration matches a java declaration,
    							// but the specification declaration is in a JML annotation - error - but use it as a match anyway
    							utils.error(specVarDecl.source(), specVarDecl.pos,
    									"jml.duplicate.model", // FIXME - duplicate field
    									specVarDecl.name,javasource);
    							String s = utils.locationString(specVarDecl.pos, specVarDecl.source());
    							utils.error(jmlDecl.source(), jmlDecl.pos,"jml.associated.decl.cf",s);
    							jmlDecl.specsDecl = specVarDecl; // Attach the specification to the matching Java AST
//    						} else {
//    							// A specification declaration matches a java declaration,
//    							// but the declaration in the Java file is in a JML annotation, and the specification declaration is not
//    							// Since if the specs declaration list is different than the Java declaration list, 
//    							// any such JML annotated declarations are removed from the Java declaration list,
//    							// this must be a case of a file containing two declarations with the same name, 
//    							// one in a JML annotation and one not
//    							// Issue and error and omit the JML declaration
//    							newdefs = Utils.remove(newdefs, javaDecl);
//    							if (defs !=  specsDefs) {
//    								utils.error(javaDecl.source(), javaDecl.pos, "jml.internal", "Unexpected JML declaration in the Java file");
//    							} else {
//    								utils.error(javaDecl.source(), javaDecl.pos,"jml.duplicate.jml.class.decl", javaDecl.name);
//    								utils.error(specClassDecl.source(), specClassDecl.pos,"jml.associated.decl.cf",
//    										utils.locationString(javaDecl.pos, javaDecl.source()));
//    							}
//    						} else if (isJML && isSpecsJML) {
//    							if (javaDecl != specClassDecl) {
//    								// There are two declarations, both in JML annotations, with the same name
//    								utils.error(javaDecl.source(), javaDecl.pos,"jml.duplicate.jml.class.decl", javaDecl.name);
//    								utils.error(specClassDecl.source(), specClassDecl.pos,"jml.associated.decl.cf",
//    										utils.locationString(javaDecl.pos, javaDecl.source()));
//    								newdefs = Utils.remove(newdefs,specClassDecl);
//    							} else {
//    								// The two declarations are the same one - OK
//    								javaDecl.specsDecl = specClassDecl;
//    							}
    						} else {
    							// else OK match
    							jmlDecl.specsDecl = specVarDecl; // Attach the specification to the matching Java AST
    						}
    					} else {  // Duplicate - warn and ignore
//    						if (!isJML) {
//    							// This less informational error message is here just to duplicate previous behavior (and the Java compiler) for Java duplicates
//    							utils.error(specClassDecl.source(), specClassDecl.pos,"duplicate.class",specClassDecl.name);
//    						} else {
    							utils.error(specVarDecl.source(), specVarDecl.pos, "jml.duplicate.jml.class.decl", specVarDecl.name);
    							utils.error(specVarDecl.source(), jmlDecl.specsDecl.pos, "jml.associated.decl.cf",
    									utils.locationString(specVarDecl.pos, specVarDecl.source()));
//    						}
//    						if (!isJML && utils.isJML(javaDecl.specsDecl.mods) && !isSpecsJML) javaDecl.specsDecl = specClassDecl;
//    						newdefs = Utils.remove(newdefs, specClassDecl);
    					}
    					break;
    				}
    			}
    			if (matched == null) {
    				// This specification declaration is not matched, so it is like a
    				// model/ghost class declaration. Pretend it is one.
    				// If necessary, add information so that it appears to be declared in a JML annotation and as a model class
    				// In any case, add it to the list of declarations to export

    				if (!utils.isJML(specVarDecl.mods)) {
    					utils.error(specVarDecl.source(), specVarDecl.pos,
    							"jml.orphan.jml.class.decl",
    							specVarDecl.name,javasource);
    					utils.setJML(specVarDecl.mods);
    					JCAnnotation x = utils.modToAnnotationAST(Modifiers.GHOST, specVarDecl.pos, specVarDecl.pos);
    					boolean has = false;
    					for (JCAnnotation a: specVarDecl.getModifiers().getAnnotations()) {
    						// FIXME - this is an inadequate comparison
    						if (((JCTree.JCFieldAccess)a.annotationType).name == ((JCTree.JCFieldAccess)x.annotationType).name) { has = true; break; }
    					}
    					if (!has) {
    						specVarDecl.mods.annotations = specVarDecl.mods.getAnnotations().append(x);
    					} else {
    						utils.error(specVarDecl.source(), specVarDecl.pos, "jml.ghost.model.on.java");
    					}
    				}

    				specVarDecl.specsDecl = specVarDecl; // FIXME specVarDecl.env = null;
    				newdefs.add(specVarDecl);
    			}
    		}
        }
        return javaDefs;
    }
    

//    /**
//     * 
//     * @param ownerenv
//     * @param owner The flat String name of the package or enclosing class (with trailing period) that holds the declarations in specsDefs
//     * @param specsDefs The specification declarations to be associated with classes
//     * @param unmatchedTypesList
//     * @param javasource
//     */
//    public List<JCTree> matchClassesForBinary(Env<AttrContext> ownerenv, String owner, List<JCTree> specsDefs, Collection<JmlClassDecl> unmatchedTypesList, String javasource) {
//        // The owner env is either the top-level env, if specsDefs is the list of top-level declarations, 
//        // or the class env if specsDefs is a nested list of class body declarations. The important aspect for this
//        // procedure are any classes declared
//        
//        ListBuffer<JCTree>  newlist = null;
//        for (JCTree specDecl: specsDefs) {  // Iterate over the classes in the list
//            if (!(specDecl instanceof JmlClassDecl)) continue;
//            JmlClassDecl specsClass = (JmlClassDecl)specDecl;
//            // The declaration 'specsClass' is in a specification file.
//            // This is matching for a binary class, so there is no source code Java declarations
//            // We need to find the Java declaration that it matches
//            // There must be one, and there should only be one declaration in the specsDefs list
//            // that matches a particular java declaration.
//            // A Java declaration need not have a match
//
//            // Load the binary if it exists  // FIXME - might this load from source?
//            Name flatname = names.fromString( owner + specsClass.name.toString());
//            ClassSymbol c;
//            try {
//                // The following just returns the symbol if the class is already loaded or known
//                c = syms.enterClass(env.toplevel.modle, flatname, syms.getPackage(null,names.fromString(owner)));
//                //c = syms.enterClass(flatname);
//            } catch (CompletionFailure eee) {
//                c = null;
//            }
//            
//            // FIXME - we are not checking for duplicate declarations in the JML file.
//
//            if (c != null) {
//                // The binary exists for the given name
//                if (utils.isJML(specsClass.mods)) {
//                    // The specs class is in a JML annotation but still matches a java class - error
//                    // FIXME _ fix this error message
//                    utils.error(specsClass.source(), specsClass.pos,
//                            "jml.duplicate.model",
//                            specsClass.name,javasource);
//                    String s = utils.locationString(specsClass.pos, specsClass.source());
//                    utils.error(specsClass.source(), specsClass.pos,"jml.associated.decl.cf",s);
//                    if (newlist == null) {
//                        newlist = new ListBuffer<JCTree>();
//                        newlist.addAll(specsClass.defs);
//                    }
//                    newlist = Utils.remove(newlist,  specDecl);
//                } else {
//                    // OK - there is a specification matching the binary class
//                    specsClass.sym = c;
//                    Env<AttrContext> localenv = classEnv(specsClass, ownerenv);
//                    typeEnvs.put(c,localenv);
//                    specsClass.env = localenv;
//                    specs.combineSpecs(c,null,specsClass);
//                    specsClass.defs = matchClassesForBinary(localenv, flatname.toString()+"$", specsClass.defs, unmatchedTypesList, javasource);
//                }
//            }
//            if (c == null) {
//                if (!utils.isJML(specsClass.mods)) {
//                //if (!utils.isJML(specsClass.mods) && !specsClass.getSimpleName().toString().equals("Array")) {
//                    // We have a Java declaration in the specs file that does not match an actual Java class.
//                    // This is an error. We will ignore the declaration.
//                    utils.error(specsClass.source(), specsClass.pos,
//                            "jml.unmatched.type",
//                            owner + specsClass.name.toString(),javasource);
//                    if (newlist == null) {
//                        newlist = new ListBuffer<JCTree>();
//                        newlist.addAll(specsDefs);
//                    }
//                    newlist = Utils.remove(newlist,  specDecl);
//                } else {
//                    // There is no Java declaration, but we have a JML declaration (presumably a model declaration)
//                    // We leave it to be added as a new declaration
//                    // FIXME - we need to catch duplicate declarations
//                    if (unmatchedTypesList != null) unmatchedTypesList.add(specsClass);
//                }
//            }
//        }
//        return newlist == null ? specsDefs : newlist.toList();
//    }



//    // FIXME - if we do not need spescTopEnv, then delete this override
//    // Overridden to use the specTopEnv when appropriate
//    @Override
//    public <T extends JCTree> List<Type> classEnter(List<T> trees, Env<AttrContext> env) { 
//        ListBuffer<Type> ts = new ListBuffer<Type>();
//        for (List<T> l = trees; l.nonEmpty(); l = l.tail) {
//            T clazz = l.head; 
//            Type t = null;
//            try {
//                t = classEnter(clazz, env);
//                if (t != null) {
//                    ts.append(t);
//                }
//            } catch (Exception e) {
//                utils.error(clazz,"jml.message", "Catastrophic failure during processing of input file");
//            }
//        }
//        return ts.toList();
//    }
    
    // FIXME - document
    public boolean binaryEnter(JmlCompilationUnit specs) {
    	for (JCTree decl: specs.defs) {
    		if (decl instanceof JmlMethodDecl) ((JmlMethodDecl)decl).specsDecl = (JmlMethodDecl)decl;
    		if (decl instanceof JmlVariableDecl) ((JmlVariableDecl)decl).specsDecl = (JmlVariableDecl)decl;
    	}
    	classEnter(specs, null);

//        Env<AttrContext> prevEnv = env;
//        JmlMemberEnter.instance(context).modeOfFileBeingChecked = specs.mode;
////        env = specs.topLevelEnv;  // FIXME - is this ever nonnull?
////        if (env == null) {
//            
//            env = specs.topLevelEnv = topLevelEnv(specs);
//            visitTopLevel(specs);
//            Env<AttrContext> prevEnvME = JmlMemberEnter.instance(context).env;
//            JmlMemberEnter.instance(context).env = env;
//            JmlMemberEnter.instance(context).importHelper(specs);
//
//            ListBuffer<JCTree> newlist = null;
//            for (JCTree d: specs.defs) {
//                if (!(d instanceof JmlClassDecl)) continue;
//                JmlClassDecl cd = (JmlClassDecl)d;
//                if (cd.sym == null) {
//                    // This class had errors such that we should remove it
//                    if (newlist == null) {
//                        newlist = new ListBuffer<>();
//                        newlist.appendList(specs.defs);
//                    }
//                    newlist = Utils.remove(newlist, cd);
//                    continue;
//                }
//                cd.specsDecl = cd;
//                Env<AttrContext> clenv = typeEnvs.get(cd.sym);
//                if (clenv == null) {
//                    clenv = classEnv(cd, env);
//                    typeEnvs.put(cd.sym, clenv);
//                }
//                cd.env = clenv;
//                JmlMemberEnter.instance(context).memberEnter(cd,clenv);  // FIXME - does nothing
//            }
//            if (newlist != null) specs.defs = newlist.toList();
//            JmlMemberEnter.instance(context).env = prevEnvME;
//        }
//        
//        // Add in any top-level classes that are in JML specs
//        for (JCTree cd: specs.defs) {
//            if (!(cd instanceof JmlClassDecl)) continue;
//            JmlClassDecl jcd = (JmlClassDecl)cd;
//            if (utils.isJML(jcd.mods)) {
//                // A class declared within JML - so it is supposed to be a model class with a unique name
//                // FIXME - check that name is not already used by a real Java class
//                // FIXME - each model method will be entered for each declaration in the specification file
//                // We have the source code for this so we want to enter this as a source-based class
//                classEnter(cd,env);
//            }
//        }
//        env = prevEnv;
        return true;
    }
    


//    /** Complain about a duplicate class. Override so we can shut off the error 
//     * when we are just checking to see if the class is already declared. */
//    @Override
//    protected void duplicateClass(DiagnosticPosition pos, ClassSymbol c) {
//        if (((JmlCheck)chk).noDuplicateWarn) return;
//        utils.error(pos, "duplicate.class", c.fullname);
//    }
    
    JCExpression findPackageDef(JCCompilationUnit that) {
    	for (var tree: that.defs) {
    		if (tree instanceof JCPackageDecl) return ((JCPackageDecl)tree).pid;
    	}
    	return null;
    }


    @Override
    public void visitClassDef(JCClassDecl that) {
        // We need to match up classes before calling super.classDefs so that
        // the specs for nested classes can be computed. Nothing else should
        // be done with the specs, however, until the Java class is 'entered'
        // in the visitClassDef call.
    	
    	JmlClassDecl jthat = (JmlClassDecl)that;
    	JmlClassDecl jspec = jthat.specsDecl;
    	if (jspec == null) System.out.println("NULL SPEC FOR " + that.name);
    	
    	var declsToAdd = matchMembers(that, jthat.defs, jspec.defs, jspec.sourcefile);
    	if (declsToAdd.size() != 0) {
    		that.defs = that.defs.appendList(declsToAdd);
    	}
    	
//    	List<JCTree> defs;
//    	if (spectree instanceof JCCompilationUnit) {
//    		defs = ((JCCompilationUnit)spectree).defs;
//    	} else {
//    		defs = ((JCClassDecl)spectree).defs;
//    	}
        
//        JmlClassDecl thattree = (JmlClassDecl)that;
//        boolean isSpecForBinary = thattree.toplevel != null && thattree.toplevel.mode == JmlCompilationUnit.SPEC_FOR_BINARY;
//        
//        JmlClassDecl specstree;
//        JmlClassDecl jmltree;
//        ClassSymbol csym = null;
//        String flatname = null;
//        if (isSpecForBinary) {
//            JCExpression pid = findPackageDef(that);
//            String packagePrefix = pid == null ? "" : (pid.toString() + ".");
//            if (env.tree instanceof JmlCompilationUnit) {
//                flatname = packagePrefix + that.name.toString();
//                csym = syms.enterClass(null,names.fromString(flatname));  // FIXME - here and below - modules
//                flatname = flatname + "$";
//            } else if (env.tree instanceof JmlClassDecl) {
//                JmlClassDecl cd = (JmlClassDecl)env.tree;
//                if (that.name == cd.name) { 
//                    flatname = packagePrefix + cd.name.toString();
//                    csym = syms.enterClass(null,names.fromString(flatname));
//                    flatname = flatname + "$";
//                } else {
//                    flatname = cd.sym.flatname.toString() + "$" + that.name.toString();
//                    csym = syms.enterClass(null,names.fromString(flatname));
//                    flatname = flatname + "$";
//                }
//            }
//            specstree = thattree;
//            specstree.sym = csym;
//            jmltree = null;
//        } else {
//            jmltree = thattree;
//            specstree = thattree.specsDecl;
//            if (specstree == null) specstree = thattree.specsDecl= thattree;
//        }
//
//        
//        java.util.List<JmlClassDecl> unmatched = new java.util.LinkedList<>();
//            
//        // Match up specs classes with java classes and adjust for unmatched classes or duplicates
//        if (specstree != null) {
//            // Attaches specs tree from second list at classdecl.specsDecls for each classdecl in the first list
//            // Matching classes has to come before visitClassDef because we need to filter out any non-Java class declarations
//            // but we cannot add JML classes here because we don't have a class symbol yet
//            if (!isSpecForBinary) {
//                JavaFileObject source = thattree.source();
//                that.defs = matchClasses(that.defs, specstree.defs, source == null ? null : source.toString());
//            } else {
//                specstree.defs = matchClassesForBinary(env, flatname, specstree.defs, unmatched, thattree.source().toString());
//            }
//        }
//        if (csym == null) { 
//            boolean pre = ((JmlCheck)chk).noDuplicateWarn;
//            if (isSpecForBinary) ((JmlCheck)chk).noDuplicateWarn = true;  // FIXME - should this be !jml - as for COllection.Content
            super.visitClassDef(that); // Uses this.env
            
            var typeSpecs = new JmlSpecs.TypeSpecs(jspec);
            jthat.specsDecl.sym = that.sym;
            JmlSpecs.instance(context).putSpecs(that.sym, typeSpecs);
            
            
//            if (isSpecForBinary) ((JmlCheck)chk).noDuplicateWarn = pre;
//            if (that.sym == null) {
//                log.error("jml.internal", "Unexpected null class symbol after processing class " + that.name);
//                result = null;
//                return;
//            }
//            csym = that.sym;
//        } else {
//            
//            // Binary classes can come here if, for example, the class symbol was created by completing a package.
//            // It 
//   // FIXME         
////            that.sym = csym;
////            csym.completer = memberEnter;
////            chk.checkFlags(thattree.pos(), thattree.mods.flags, csym, thattree); // Do not overwrite flags in the binary
////            csym.sourcefile = thattree.sourcefile;
////            //cs.members_field = new Scope(cs); // DO not overwrite the fields that are in the binary
////
////            Scope enclScope = enterScope(env);
////            enclScope.enter(csym);
//
//        }
//
//        Env<AttrContext> localEnv  = null;
//        if (isSpecForBinary) {
//            // FIXME - this is already done for source classes. Is it needed for binary classes?
//            localEnv = classEnv(that, env); // FIXME - we might well need this, but classEnv(that,env) fails for loading secs of binary classes
//            typeEnvs.put(csym, localEnv);
//            thattree.env = localEnv;
//        }
//        
//        boolean ok = true;
//        if (specstree != null) {
//            // Check the names of type parameters in the specifications against those defined
//            // in the class symbol (so should work for both source and binary).
//            // Sets the type of type parameters in the specs declaration accordingly.
//            // With the third argument null, no class entering is performed; all the type
//            // parameters from the source/binary Java file should be entered and in scope.
//
//            ok = checkAndEnterTypeParameters(csym, specstree, typeEnvs.get(csym));
//        }
//
//        
//        // Set the sym and env fields of the classes
//        
//        if (ok) {
//            Env<AttrContext> localenv = getEnv(csym);
//            thattree.env = localenv;
//            if (jmltree != null) {
//                jmltree.env = localenv;
//            }
//            if (specstree != null) {
//                specstree.sym = that.sym;
//                // FIXME - the specstree might actually want a different local environment because it may have different imports
//                specstree.env = localenv;
//            }
//        } else {
//            if (specstree != null) {
//                specstree.sym = null;
//                specstree.env = null;
//            }
//        }
//
//       
//        if (ok) {
//            JmlSpecs.TypeSpecs tsp = specs.combineSpecs(that.sym,jmltree,specstree);
//            if (jmltree != null) jmltree.typeSpecs = tsp;
//            if (specstree != null) specstree.typeSpecs = tsp;
//        } else {
//            csym.completer = null;
//            recordEmptySpecs(csym);
//            result = null;
//        }
//        
//        if (isSpecForBinary && !unmatched.isEmpty()) {
//            for (JmlClassDecl c: unmatched) {
//                classEnter(c, localEnv);
//            }
//        }
//        if (isSpecForBinary) {
//            Env<AttrContext> saved = env;
//            env = specstree.env;
//            for (JCTree t: specstree.defs) {
//                if (!(t instanceof JmlClassDecl)) continue;
//                visitClassDef((JmlClassDecl)t);
//            }
//            env = saved;
//        }

    }
    
     // FIXME - unify the recording of empty specs with default specs??
    public void recordEmptySpecs(ClassSymbol csymbol) {
        JmlSpecs.TypeSpecs typespecs = new JmlSpecs.TypeSpecs(csymbol, csymbol.sourcefile, JmlTree.Maker.instance(context).Modifiers(csymbol.flags(),List.<JCTree.JCAnnotation>nil()), null);
        JmlSpecs.instance(context).putSpecs(csymbol,typespecs);
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
//    public boolean checkAndEnterTypeParameters(ClassSymbol csym, JmlClassDecl specTypeDeclaration, Env<AttrContext> classEnv) {
//        Env<AttrContext> localEnv = classEnv;
//        //Scope enterScope = enterScope(classEnv);
//        boolean result = true;
//        int numSpecTypeParams = specTypeDeclaration.typarams.size();
//        int numJavaTypeParams = csym.type.getTypeArguments().size();
//        if (numSpecTypeParams != numJavaTypeParams) {
//            utils.error(specTypeDeclaration.source(),specTypeDeclaration.pos(),"jml.mismatched.type.arguments",specTypeDeclaration.name,csym.type.toString());
//            //log.error(specTypeDeclaration.pos(),"jml.mismatched.type.parameters", specTypeDeclaration.name, csym.fullname, n, javaN);
//            result = false;
//        }
//        int nn = numSpecTypeParams; if (numJavaTypeParams < nn) nn = numJavaTypeParams;
//        for (int i = 0; i<nn; i++) {
//            JCTree.JCTypeParameter specTV = specTypeDeclaration.typarams.get(i);
//            TypeVar javaTV = (TypeVar)((ClassType)csym.type).getTypeArguments().get(i);
//            if (specTV.name != javaTV.tsym.name) {
//                utils.error(specTV.pos(),"jml.mismatched.type.parameter.name", specTypeDeclaration.name, csym.fullname, specTV.name, javaTV.tsym.name);
//                result = false;
//            } 
//            // classEnter will set the type of the Type Variable, but it sets it to 
//            // something new for each instance, which causes trouble in type mathcing
//            // that I have not figured out. Here we preemptively set the type to be the
//            // same as the Java type that it matches in the specification.
//            specTV.type = javaTV;
//            if (localEnv != null) classEnter(specTV,localEnv); // FIXME - wouldn't this be a duplicate - or is localEnv always null
//            //enterScope.enter(javaTV.tsym);
//        }
//        for (int i = nn; i<numSpecTypeParams; i++) {
//            JCTree.JCTypeParameter specTV = specTypeDeclaration.typarams.get(i);
//            if (localEnv != null) classEnter(specTV,localEnv);
//        }
//        // FIXME need to check that the types have the same bounds
//        return result;
//        //log.noticeWriter.println(" LOCAL ENV NOW " + localEnv);
//    }

 // FIXME ?
//    /** This overrides the parent class method so that we allow file names
//     * with spec extensions, not just .java 
//     * 
//     * @param c the class the file is associated with
//     * @param env the Env object representing the filename 
//     */
//    @Override
//    public boolean classNameMatchesFileName(ClassSymbol c, // OPENJML - changed from private to public
//            Env<AttrContext> env) {
//        JavaFileObject jfo = env.toplevel.sourcefile;
//        if (jfo.getKind() == JavaFileObject.Kind.SOURCE) return super.classNameMatchesFileName(c, env);
//        String classname = c.name.toString();
//        // FIXME: Actually we are loose in our comparison
//        String filename = jfo.getName();
//        return filename.endsWith(classname + Strings.specsSuffix); // FIXME - what if classname is just the tail of the filename
//    }

    protected boolean classNameMatchesFileName(ClassSymbol c, 
            Env<AttrContext> env) {
    	boolean b =  env.toplevel.sourcefile.isNameCompatible(c.name.toString(),
                JavaFileObject.Kind.SOURCE);
    	if (!b) b = env.toplevel.sourcefile.isNameCompatible(c.name.toString(),
                JavaFileObject.Kind.JML);
    	return b;
}

    
}
