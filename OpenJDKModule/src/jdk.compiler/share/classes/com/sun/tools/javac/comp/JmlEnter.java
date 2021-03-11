/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.comp;


import static com.sun.tools.javac.code.Flags.DEFAULT;
import static com.sun.tools.javac.code.Flags.SIGNATURE_POLYMORPHIC;
import static com.sun.tools.javac.code.Flags.UNATTRIBUTED;

import java.util.Collection;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlPretty;
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
import com.sun.tools.javac.code.Symbol.Completer;
import com.sun.tools.javac.code.Symbol.CompletionFailure;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Scope.WriteableScope;
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
import com.sun.tools.javac.util.Assert;
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
    
    public static JmlEnter instance(Context context) {
    	return (JmlEnter)Enter.instance(context);
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
    			speccu = (JmlCompilationUnit)JmlCompiler.instance(context).parse(specJfo);
    			speccu.sourceCU = jtree;
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
    		jtree.specsCompilationUnit = speccu;
    		var declsToAdd = matchMembers(null, tree.defs, speccu.defs, speccu.sourcefile);
        	if (declsToAdd.size() != 0) {
        		tree.defs = tree.defs.appendList(declsToAdd);
        	}
    		
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
    
    boolean compare = false;
    
    public boolean matches(JCExpression jtype, JCExpression stype) {
    	String a = JmlPretty.write(jtype);
    	String b = JmlPretty.write(stype);
    	return a.equals(b) || a.endsWith("." + b) || b.endsWith("." + a);
    }
    
    public boolean matches(JmlMethodDecl specsDecl, JmlMethodDecl javaDecl) {
    	if (!specsDecl.name.equals(javaDecl.name)) return false;
    	if (specsDecl.params.size() != javaDecl.params.size()) return false;
    	var jiter = javaDecl.params.iterator();
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
			boolean compare = (org.jmlspecs.openjml.Main.useJML && owner != null && owner.toString().endsWith("Throwable"));
        	var matched = new java.util.HashSet<JCTree>();
    		for (var decl: javaDefs) {
    			if (decl instanceof JmlClassDecl) {
    				JmlClassDecl javaDecl = (JmlClassDecl)decl;
    				x: {
    					for (var sdecl: specsDefs) {
    						if (!(sdecl instanceof JmlClassDecl)) continue;
    						JmlClassDecl specsDecl = (JmlClassDecl)sdecl;
    		    			boolean isSpecsJML = utils.isJML(specsDecl.mods);
    						if (specsDecl.name.equals(javaDecl.name)) {
    							matched.add(specsDecl);
    							if (isSpecsJML) {
        							// A specification declaration matches a java declaration,
        							// but the specification declaration is in a JML annotation - error - but use it as a match anyway
        							utils.error(specsDecl.source(), specsDecl.pos,
        									"jml.duplicate.model",
        									"type", specsDecl.name, javasource);
        							String s = utils.locationString(specsDecl.pos, specsDecl.source());
        							utils.error(javaDecl.source(), javaDecl.pos, "jml.associated.decl.cf", s);
    							}
    							javaDecl.specsDecl = specsDecl;
    							break x;
    						}
    						// No specs found
    					}
    					javaDecl.specsDecl = javaDecl; // FIXME - should be default specs
    				}
    			} else if (decl instanceof JmlMethodDecl) {
    				JmlMethodDecl javaDecl = (JmlMethodDecl)decl;
	    			//if (compare) System.out.println("MATCHING " + javaDecl + " " + javaDecl.sourcefile);
   				    x: {
    					for (var sdecl: specsDefs) {
    						if (!(sdecl instanceof JmlMethodDecl)) continue;
    						JmlMethodDecl specsDecl = (JmlMethodDecl)sdecl;
    		    			//if (compare) System.out.println("TRYING " + specsDecl.name);
    						boolean isSpecsJML = utils.isJML(specsDecl.mods);
    						if (matches(specsDecl,javaDecl)) {
        		    			if (compare) System.out.println("MATCHED " + specsDecl.hashCode() + " " + specsDecl);
    							matched.add(specsDecl);
    							if (isSpecsJML) {
        							// A specification declaration matches a java declaration,
        							// but the specification declaration is in a JML annotation - error - but use it as a match anyway
        							utils.error(specsDecl.source(), specsDecl.pos,
        									"jml.duplicate.model",
        									"method",specsDecl.name,javasource);
        							String s = utils.locationString(specsDecl.pos, specsDecl.source());
        							utils.error(javaDecl.source(), javaDecl.pos, "jml.associated.decl.cf", s);
    							}
    							javaDecl.specsDecl = specsDecl;
    							break x;
    						}
    						// No specs found
    					}
    					javaDecl.specsDecl = javaDecl; // FIXME - should be default specs
    				}

    			} else if (decl instanceof JmlVariableDecl) {
    				JmlVariableDecl javaDecl = (JmlVariableDecl)decl;
    				// The parser inserts some implicit JML declarations, so a Java compilation unit
    				// may already have some JML declarations.
    				boolean isJavaJML = utils.isJML(javaDecl.mods);
    				x: {
    					for (var sdecl: specsDefs) {
    						if (!(sdecl instanceof JmlVariableDecl)) continue;
    						JmlVariableDecl specsDecl = (JmlVariableDecl)sdecl;
    		    			boolean isSpecsJML = utils.isJML(specsDecl.mods);
    						if (specsDecl.name.equals(javaDecl.name)) {
    							matched.add(specsDecl);
    							if (isSpecsJML && !isJavaJML) {
        							// A specification declaration matches a java declaration,
        							// but the specification declaration is in a JML annotation - error - but use it as a match anyway
        							utils.error(specsDecl.source(), specsDecl.pos,
        									"jml.duplicate.model",
        									"field",specsDecl.name,javasource);
        							String s = utils.locationString(specsDecl.pos, specsDecl.source());
        							utils.error(javaDecl.source(), javaDecl.pos, "jml.associated.decl.cf", s);
    							} else if (!isSpecsJML && isJavaJML) {
    								utils.warning(specsDecl.source(), specsDecl.pos,
    										"jml.message",
    										"This specification declaration should be in a JML comment to match the declaration in the Java file");
        							String s = utils.locationString(specsDecl.pos, specsDecl.source());
        							utils.error(javaDecl.source(), javaDecl.pos, "jml.associated.decl.cf", s);
    							}
    							javaDecl.specsDecl = specsDecl;
    							break x;
    						}
    						// No specs found
    					}
    					javaDecl.specsDecl = javaDecl; // FIXME - should be default specs
    				}
    			}
    		}
    		x: for (var sdecl: specsDefs) {
    			if (matched.contains(sdecl)) continue;
    			if (compare) System.out.println("UNMATCHED " + sdecl);
    			if (sdecl instanceof JmlClassDecl) {
    				var specDecl = (JmlClassDecl)sdecl;
    				if (utils.isJML(specDecl.mods)) {
    					adds.add(sdecl);
    					specDecl.specsDecl = specDecl;
    				} else {
    		    		for (var sdecl2: specsDefs) {
    		    			if (sdecl != sdecl2 && sdecl2 instanceof JmlVariableDecl && specDecl.name == ((JmlMethodDecl)sdecl2).name) {
    	    					utils.error(specDecl.source(), sdecl.pos,
    	    							"jml.duplicate.jml.class.decl",
    	    							specDecl.name);
    							String s = utils.locationString(sdecl2.pos, specDecl.source());
    							utils.error(specDecl.source(), sdecl2.pos, "jml.associated.decl.cf", s);
    		    				continue x;
    		    			}
    		    		}
    					utils.error(specDecl.source(), specDecl.pos,
    							"jml.orphan.jml.class.decl",
    							specDecl.name,javasource);
    				}
    			} else if (sdecl instanceof JmlMethodDecl) {
    				var specDecl = (JmlMethodDecl)sdecl;
    				if (utils.isJML(specDecl.mods)) {
//    					if (org.jmlspecs.openjml.Main.useJML && specDecl.name.toString().equals("standardThrowable"))
//    						System.out.println("UNMATCHED ADDING " + specDecl);
    					adds.add(sdecl);
    					specDecl.specsDecl = specDecl;
    				} else if ((owner.mods.flags & Flags.RECORD) == 0) { // FIXME - handle records
    		    		for (var sdecl2: specsDefs) {
    		    			if (sdecl != sdecl2 && sdecl2 instanceof JmlMethodDecl && matches(specDecl,(JmlMethodDecl)sdecl2)) {
    	    					utils.error(specDecl.source(), sdecl.pos,
    	    							"jml.duplicate.jml.method.decl",
    	    							specDecl.name);
    							String s = utils.locationString(sdecl2.pos, specDecl.source());
    							utils.error(specDecl.source(), sdecl2.pos, "jml.associated.decl.cf", s);
    		    				continue x;
    		    			}
    		    		}
    					utils.warning(specDecl.source(), specDecl.pos,
    							"jml.no.method.match",
    							specDecl.name);
						String s = utils.locationString(specDecl.pos, specDecl.source());
						utils.warning(((JmlClassDecl)owner).sourcefile, owner.pos, "jml.associated.decl.cf", s);
    				}
    			} else if (sdecl instanceof JmlVariableDecl) {
    				var specDecl = (JmlVariableDecl)sdecl;
    				if (utils.isJML(specDecl.mods)) {
    					adds.add(sdecl);
    					specDecl.specsDecl = specDecl;
    				} else if ((owner.mods.flags & Flags.RECORD) == 0) { // FIXME - handle records
    		    		for (var sdecl2: specsDefs) {
    		    			if (sdecl != sdecl2 && sdecl2 instanceof JmlVariableDecl && specDecl.name == ((JmlMethodDecl)sdecl2).name) {
    	    					utils.error(specDecl.source(), sdecl.pos,
    	    							"jml.duplicate.jml.var.decl",
    	    							specDecl.name);
    							String s = utils.locationString(sdecl2.pos, specDecl.source());
    							utils.error(specDecl.source(), sdecl2.pos, "jml.associated.decl.cf", s);
    		    				continue x;
    		    			}
    		    		}
    					utils.error(specDecl.source(), specDecl.pos,
    							"jml.no.var.match",
    							specDecl.name,javasource);
    				}
    			}
    		}
    	}
    	return adds.toList();
    }



    
    // FIXME - document
    public void binaryEnter(JmlCompilationUnit speccu) {
    	utils.note(true, "Entering declarations from specification file " + speccu.sourcefile);
		var prev = log.useSource(speccu.sourcefile);
		try {

			String flatPackageName = speccu.pid.pid.toString();
			Name packageName = names.fromString(flatPackageName);
			PackageSymbol p = syms.getPackage(syms.unnamedModule,packageName);
			if (p == null) p = syms.getPackage(syms.java_base,packageName);
			// FIXME - what about other modules, or user modules
			if (p == null) {
				utils.warning(speccu.pid, "jml.message", "Creating new package in unnamed module: " + flatPackageName); // FIXME - figure out haw to create it
				p = syms.enterPackage(syms.unnamedModule, packageName);
			}

			speccu.packge = p;
			Env<AttrContext> env = topLevelEnv(speccu);
            TypeEnter.instance(context).completeClass.resolveImports(speccu, env);

			for (JCTree decl: speccu.defs) {
				if (!(decl instanceof JmlClassDecl)) continue;
				var jdecl = (JmlClassDecl)decl;
				binaryEnter(p, jdecl, env);
			}
		} finally {
			log.useSource(prev);
		}
    }
    
    public void binaryEnter(Symbol owner, JmlClassDecl jdecl, Env<AttrContext> env) {
		Name className = jdecl.name;
		boolean isJML = utils.isJML(jdecl);
		boolean isGhostOrModel = utils.hasMod(jdecl.mods, Modifiers.GHOST) || utils.hasMod(jdecl.mods, Modifiers.MODEL);
		
		ClassSymbol csym = (ClassSymbol)owner.members().findFirst(className);
		if (csym == null) {
			// No corresponding binary class
			if (!isJML) {
				utils.error(jdecl, "jml.message", "There is no binary class to match this Java declaration in the specification file: " + className + " (owner: " + owner +")");
				return;
			}
			if (!isGhostOrModel) {
				utils.error(jdecl, "jml.message", "A JML class declaration must be marked either ghost or model: " + className + " (owner: " + owner +")");
				return;
			}
			// Enter the class in the package or the parent class
            if (owner instanceof PackageSymbol) {
            	csym = syms.enterClass(env.toplevel.modle, jdecl.name, (PackageSymbol)owner);
            } else { // owner is a ClassSymbol
            	ClassSymbol cowner = (ClassSymbol)owner;
            	csym = syms.enterClass(env.toplevel.modle, jdecl.name, (Symbol.TypeSymbol)owner);
            	csym.completer = Completer.NULL_COMPLETER;
            	csym.flags_field = jdecl.mods.flags;
            	var ct = (ClassType)csym.type;
            	if (jdecl.extending != null) ct.supertype_field = jdecl.extending.type = Attr.instance(context).attribType(jdecl.extending,env);
            	csym.sourcefile = cowner.sourcefile;
            	csym.members_field = WriteableScope.create(csym);
            	ct.typarams_field = List.from(cowner.type.getTypeArguments());
            }
			utils.note(true,  "Entering JML class: " + csym + " (owner: " + owner +")" );
		} else {
			// Found a matching binary class
    		boolean matchIsJML = utils.isJML(csym.flags());
			if (isJML) {
				if (matchIsJML) {
		    		JmlSpecs.TypeSpecs jspecs = JmlSpecs.instance(context).getxx(csym);
					utils.error(jdecl, "jml.message", "This JML class declaration conflicts with a previous JML class: " + jdecl.name + " (owner: " + csym +")");
					utils.error(jspecs.decl, "jml.associated.decl.cf", utils.locationString(jdecl.pos, log.currentSourceFile()));
				} else {
					utils.error(jdecl, "jml.message", "This JML class declaration conflicts with an existing binary class with the same name: " + className + " (owner: " + owner +")");
				}
				return;
			}
			if (matchIsJML) {
	    		JmlSpecs.TypeSpecs jspecs = JmlSpecs.instance(context).getxx(csym);
				utils.error(jdecl, "jml.message", "This method declaration conflicts with a previous JML method: " + jdecl.name + " (owner: " + csym +")");
				utils.error(jspecs.decl, "jml.associated.decl.cf", utils.locationString(jdecl.pos, log.currentSourceFile()));
				return;
			}
			if (isGhostOrModel) {
				var pos = utils.locMod(jdecl.mods, Modifiers.GHOST, Modifiers.MODEL);
				utils.error(pos, "jml.message", "A Java class declaration must not be marked either ghost or model: " + className + " (owner: " + owner +")");
				return;
			}
			utils.note(true,  "Matched class: " + csym + " (owner: " + csym.owner +")" );
		}
		jdecl.sym = csym;
		for (int i = 0; i < jdecl.typarams.length(); ++i) jdecl.typarams.get(i).type = csym.type.getTypeArguments().get(i).tsym.type;
		Env<AttrContext> localEnv = classEnv(jdecl, env);
		TypeEnter.instance(context).new MembersPhase().enterThisAndSuper(csym,  localEnv);
		((ClassType)csym.type).typarams_field = classEnter(jdecl.typarams, localEnv);
        typeEnvs.put(csym, localEnv);
		var tspecs = new JmlSpecs.TypeSpecs(jdecl, localEnv);
		if (csym != null) JmlSpecs.instance(context).putSpecs(csym, tspecs);

        // Do all nested classes first, so their names are known
		for (JCTree t: jdecl.defs) {
			if (t instanceof JmlClassDecl) {
				binaryEnter(csym, (JmlClassDecl)t, localEnv);
			}
		}
		
		if (false && Utils.debug() && csym.flatName().toString().contains("Comparable")) {
			var iter = csym.members().getSymbols().iterator();
			while (iter.hasNext()) {
				var s = iter.next();
				System.out.println("BINARY ENTER: " + csym.flatName() + " has " + s + " " + s.owner + " " + s.isAbstract());
			}
		}

		for (JCTree t: jdecl.defs) {
			if (t instanceof JmlMethodDecl) {
				binaryEnter(csym, (JmlMethodDecl)t, localEnv);
			} else if (t instanceof JmlVariableDecl) {
				binaryEnter(csym, (JmlVariableDecl)t, localEnv);
			}
		}
    }
    
    public boolean matchAsStrings(Type bin, JCExpression src) {
    	String binstr = bin.toString().replaceAll(" ","");
    	String srcstr = src.toString().replaceAll(" ","");
    	if (print) System.out.println("COMPARING-S " + binstr +":" + srcstr);
		if (binstr.equals(srcstr)) return true;
		if (binstr.endsWith("." + srcstr)) return true;
		return false;
    }
    
    boolean print = false;
    
    public MethodSymbol findMethod(ClassSymbol csym, JmlMethodDecl mdecl, Env<AttrContext> env) {
    	//print = Utils.debug() && mdecl.name.toString().equals("flatMap");
    	boolean hasTypeParams = csym.getTypeParameters().length() != 0 || mdecl.typarams.length() != 0;
    	boolean useStringComparison = false;
    	if (print) System.out.println("SEEKING " + mdecl.name + " " + hasTypeParams);
    	{
    		try {
    			Attr attr = Attr.instance(context);
    			// FIXME mdecl.mods.annotations?
    			if (mdecl.typarams != null) attr.attribTypeVariables(mdecl.typarams, env, true);
    			if (mdecl.recvparam != null) attr.attribType(mdecl.recvparam, env);
    			for (var a: mdecl.params) {
    				a.type = a.vartype.type = attr.attribType(a.vartype, env);
    			}
    			if (mdecl.restype != null) attr.attribType(mdecl.restype, env);
    			if (mdecl.thrown != null) attr.attribTypes(mdecl.thrown, env);
    		} catch (Exception e) {
    			//utils.warning(mdecl, "jml.message", "Failed to attribute types");
    			//e.printStackTrace(System.out);
    			useStringComparison = true;
    		}
    	}
		Symbol.MethodSymbol msym = null;
		MethodSymbol first = null;
		int count = 0;
		var iter = csym.members().getSymbolsByName(mdecl.name, s->(s instanceof Symbol.MethodSymbol)).iterator();
    	x: while (iter.hasNext()) {
    		var m = (MethodSymbol)iter.next();
    		if (print) System.out.println("TRYING " + m+ " " + m.params.length() + " " +  mdecl.params.length() + " " + m.getTypeParameters().length() + " " + mdecl.getTypeParameters().length());
    		if (m.params.length() != mdecl.params.length()) continue;
    		if (m.getTypeParameters().length() != mdecl.getTypeParameters().length()) continue;
			first = m;
			count++;
    		for (int i=0; i<m.params.length(); i++) {
    			if (hasTypeParams) {
    				// FIXME - When there are type parameters, the type resolution above is not working
    				// so we fall back to string comparison -- a hack that only partially works
    				// Probably has to do with getting the correct env
    				//if (Utils.debug()) System.out.println("TYPES " + m.params.get(i).type.toString() + " " + mdecl.params.get(i).vartype.toString());
    				if (!matchAsStrings(m.params.get(i).type, mdecl.params.get(i).vartype)) continue x;
    			} else {
    				if (print) System.out.println("COMPARING-T " + m.params.get(i).type + " " + mdecl.params.get(i).type + " " + types.isSameType(m.params.get(i).type,mdecl.params.get(i).type));
    				if (!types.isSameType(m.params.get(i).type,mdecl.params.get(i).type)) continue x;
    			}
    		}
    		if (msym != null) {
    			// It turns out that there sometimes are two method symbols with the same signature.
    			// cf. AbstractStringBuilder, StringBuffer
    			// So instead of doing this check, we just exit (via the return) on finding the first one.
    			utils.note(mdecl, "jml.message", "Unexpectedly found duplicate binary method symbols: " + msym + " " + msym.isAbstract() + " " + m.isAbstract());
        	} else {
        		msym = m;
        		break x;
    		}
    	}
		if (msym == null && count == 1 && !utils.isJML(mdecl)) {
			//utils.note(mdecl, "jml.message", "No match; could use the unique candidate " + first + " " + (!hasTypeParams?"": " (hasTypeParameters)"));
			msym = first;
		}
		if (msym != null && useStringComparison && !utils.isJML(mdecl)) {
			var mt = msym.type.asMethodType();
			mdecl.restype.type = mt.restype;
			for (int i = 0; i < mdecl.getTypeParameters().length(); ++i) {
				if (Utils.debug()) {
					System.out.println("TYPEP " + msym.owner + " " + msym + " " + i);
					var dt = mdecl.getTypeParameters().get(i);
					System.out.println("TYPEP-A " + dt + " " + dt.type + " " + dt.bounds);
					var st = mdecl.getTypeParameters().get(i);
					System.out.println("TYPEP-B " + st + " " + st.type + " " + st.bounds);
				}
				var mi = mdecl.getTypeParameters().get(i);
				var mj = msym.getTypeParameters().get(i);
				mi.type = mj.type;
				for (int j=0; j<mi.bounds.length(); ++j) mi.bounds.get(j).type = mj.getBounds().get(j);
			}
			for (int i = 0; i < mdecl.params.length(); ++i) mdecl.params.get(i).type = mt.argtypes.get(i);
		}
    	return msym;
    }
    
    public MethodSymbol makeAndEnterMethodSym(JmlMethodDecl tree, Env<AttrContext> env) {
    	MemberEnter memberEnter = JmlMemberEnter.instance(context);
    	var saved = memberEnter.env;
    	memberEnter.env = env;
    	memberEnter.visitMethodDef(tree); // This also calls putSpecs
    	memberEnter.env = saved;
    	return tree.sym;
    }
    
    public void binaryEnter(ClassSymbol csym, JmlMethodDecl mdecl, Env<AttrContext> env) {
		boolean isJML = utils.isJML(mdecl);
		boolean isGhostOrModel = utils.hasMod(mdecl.mods, Modifiers.GHOST) || utils.hasMod(mdecl.mods, Modifiers.MODEL);
		Symbol.MethodSymbol msym = findMethod(csym, mdecl, env);
    	if (msym == null) {
			// No corresponding binary method
    		if (!isJML) {
				utils.error(mdecl, "jml.message", "There is no binary method to match this Java declaration in the specification file: " + mdecl.name + " (owner: " + csym +")");
				for (var s: csym.members().getSymbolsByName(mdecl.name, s->(s instanceof MethodSymbol))) {
					utils.note(false, "    " + csym + " has " + s);
				}
				return;
    		}
			if (!isGhostOrModel && !utils.isJML(csym.flags())) {
				utils.error(mdecl, "jml.message", "A JML method declaration must be marked either ghost or model: " + mdecl.name + " (owner: " + csym +")");
				return;
			}
			// Enter the method in the parent class
			msym = makeAndEnterMethodSym(mdecl, env); // Also calls putSpecs
			utils.note(!print,  "Entered JML method: " + msym + " (owner: " + csym + ")" );
    	} else {
			// Found a matching binary method
    		boolean matchIsJML = utils.isJML(msym.flags());
			if (isJML && !utils.isJML(csym.flags())) {
				if (matchIsJML) {
		    		JmlSpecs.MethodSpecs mspecs = JmlSpecs.instance(context).getSpecs(msym);
					utils.error(mdecl, "jml.message", "This JML method declaration conflicts with a previous JML method: " + mdecl.name + " (owner: " + csym +")");
					utils.error(mspecs.cases.decl, "jml.associated.decl.cf", utils.locationString(mdecl.pos, log.currentSourceFile()));
				} else {
					utils.error(mdecl, "jml.message", "This JML method declaration conflicts with an existing binary method with the same name: " + mdecl.name + " (owner: " + csym +")");
				}
				return;
			}
			if (matchIsJML) {
	    		JmlSpecs.MethodSpecs mspecs = JmlSpecs.instance(context).getSpecs(msym);
				utils.error(mdecl, "jml.message", "This method declaration conflicts with a previous JML method: " + mdecl.name + " (owner: " + csym +")");
				utils.error(mspecs.cases.decl, "jml.associated.decl.cf", utils.locationString(mdecl.pos, log.currentSourceFile()));
				return;
			}
			if (isGhostOrModel) {
				var pos = utils.locMod(mdecl.mods, Modifiers.GHOST, Modifiers.MODEL);
				utils.error(pos, "jml.message", "A Java method declaration must not be marked either ghost or model: " + mdecl.name + " (owner: " + csym +")");
				return;
			}
			utils.note(!print,  "Matched method: " + msym + " (owner: " + csym +")" );
			mdecl.sym = msym;
			var mspecs = new JmlSpecs.MethodSpecs(mdecl);
			mspecs.env = JmlMemberEnter.instance(context).methodEnv(mdecl,env);
			if (msym != null) JmlSpecs.instance(context).putSpecs(msym, mspecs);
    	}
    }
    
    public VarSymbol findVar(ClassSymbol csym, JmlVariableDecl vdecl) {
    	Name vname = vdecl.name;
    	var iter = csym.members().getSymbolsByName(vname, s->(s instanceof VarSymbol)).iterator();
    	if (iter.hasNext()) {
    		var vsym = iter.next();
    		if (iter.hasNext()) {
    			var v = iter.next();
    			// This should never happen - two binary fields with the same name
    			utils.error(vdecl, "jml.message", "Unexpectedly found duplicate binary field symbols named " + vname + " (" + vsym + " vs. " + v + ")");
    		}
			return (VarSymbol)vsym;
    	}
    	return null;
    }
    
    public void binaryEnter(ClassSymbol csym, JmlVariableDecl vdecl, Env<AttrContext> env) {
		boolean isJML = utils.isJML(vdecl);
		boolean isGhostOrModel = utils.hasMod(vdecl.mods, Modifiers.GHOST) || utils.hasMod(vdecl.mods, Modifiers.MODEL);
    	Symbol.VarSymbol vsym = findVar(csym, vdecl);;
    	if (vsym == null) {
			// No corresponding binary field
    		if (!isJML) {
				utils.error(vdecl, "jml.message", "There is no binary field to match this Java declaration in the specification file: " + vdecl.name + " (owner: " + csym +")");
				return;
    		}
			if (!isGhostOrModel) {
				utils.error(vdecl, "jml.message", "A JML field declaration must be marked either ghost or model: " + vdecl.name + " (owner: " + csym +")");
				return;
			}
			// Enter the class in the package or the parent class
			vdecl.type = vdecl.vartype.type = Attr.instance(context).attribType(vdecl.vartype, env);
	        vsym = new VarSymbol(0, vdecl.name, vdecl.type, csym);
	        vsym.flags_field = chk.checkFlags(vdecl.pos(), vdecl.mods.flags, vsym, vdecl);
	        csym.members().enter(vsym);
	        utils.note(true,  "Entered JML field: " + vsym + " (owner: " + csym +")" );
    	} else {
			// Found a matching binary field
    		boolean matchIsJML = utils.isJML(vsym.flags());
			if (isJML) {
				if (matchIsJML) {
		    		JmlSpecs.FieldSpecs fspecs = JmlSpecs.instance(context).getSpecs(vsym);
					utils.error(vdecl, "jml.message", "This JML field declaration conflicts with a previous JML field: " + vdecl.name + " (owner: " + csym +")");
					utils.error(fspecs.decl, "jml.associated.decl.cf", utils.locationString(vdecl.pos, log.currentSourceFile()));
				} else {
					utils.error(vdecl, "jml.message", "This JML field declaration conflicts with an existing binary field with the same name: " + vdecl.name + " (owner: " + csym +")");
				}
				return;
			}
			if (matchIsJML) {
	    		JmlSpecs.FieldSpecs fspecs = JmlSpecs.instance(context).getSpecs(vsym);
				utils.error(vdecl, "jml.message", "This field declaration conflicts with a previous JML field: " + vdecl.name + " (owner: " + csym +")");
				utils.error(fspecs.decl, "jml.associated.decl.cf", utils.locationString(vdecl.pos, log.currentSourceFile()));
				return;
			}
			if (isGhostOrModel) {
				var pos = utils.locMod(vdecl.mods, Modifiers.GHOST, Modifiers.MODEL);
				utils.error(pos, "jml.message", "A Java field declaration must not be marked either ghost or model: " + vdecl.name + " (owner: " + csym +")");
				return;
			}
			utils.note(true,  "Matched field: " + vsym + " (owner: " + csym +")" );
    	}
		var vspecs = new JmlSpecs.FieldSpecs(vdecl);
		vdecl.sym = vsym;
		if (vsym != null) JmlSpecs.instance(context).putSpecs(vsym, vspecs);
    }

    
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
//    		if (org.jmlspecs.openjml.Main.useJML && jthat.name.toString().equals("String")) {
//    			System.out.println("EXPANDED " + that);
//    		}
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

        jthat.specsDecl.sym = that.sym;
        var typeSpecs = new JmlSpecs.TypeSpecs(jspec, typeEnvs.get(that.sym));
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

    private int nestingLevel = 0;
    
    /** Parses and enters specs for binary classes, given a ClassSymbol.  This is 
     * called when a name is resolved to a binary type; the Java type itself is
     * loaded (and symbols entered) by the conventional Java means.  Here we need
     * to add to that by parsing the specs and entering any new declarations
     * into the scope tables.
     * 
     * Note that a class can be loaded (and then this method called to get specs) whenever
     * a type is attributed, and txype attribution happens during spec loading, 
     * so spec requests can be recursive, hence the todo list to avoid that.
     * 
     * If ever a Java file is loaded by conventional means and gets its
     * source file through parsing, the specs will be obtained at that time, and not here.
     * 
     * @param csymbol the class whose specs are wanted
     */
    public void requestSpecs(ClassSymbol csymbol) {
    	// Requests for nested classes are changed to a request for their outermost class
    	while (csymbol.owner instanceof ClassSymbol) csymbol = (ClassSymbol)csymbol.owner;

    	JmlSpecs.SpecsStatus tsp = JmlSpecs.instance(context).status((ClassSymbol)csymbol);
    	if (tsp.less(JmlSpecs.SpecsStatus.QUEUED)) {
    		requestSpecsForSelfAndParents(csymbol);
    	} else {
    		utils.note(true,"Requesting specs " + csymbol + ", but specs already loaded or in progress");
    	}

    }

    private void requestSpecsForSelfAndParents(ClassSymbol csymbol) {
    	// The binary Java class itself is already loaded - it is needed to produce the classSymbol itself

    	if (!binaryEnterTodo.contains(csymbol)) {
    		nestingLevel++;
    		try {
    			// It can happen that the specs are loaded during the loading of the super class 
    			// since complete() may be called on the class in order to fetch its superclass,
    			// or during the loading of any other class that happens to mention the type.
    			// So we recheck here, before reentering the class in the todo list
    			// The presence of specs is a marker of intention to load, but not that they are yet loaded
    			if (JmlSpecs.instance(context).status(csymbol) != JmlSpecs.SpecsStatus.NOT_LOADED) return;

    			// Classes are prepended to the todo list in reverse order, so that parent classes
    			// have specs read first.

    			// Note that nested classes are specified in the same source file as their enclosing classes
    			// Everything within a specification text file is loaded together

    			//                for (Symbol t: csymbol.getEnclosedElements()) {
    			//                    if (t.isPrivate()) continue;
    			//                    if (t instanceof ClassSymbol) {
    			//                    	requestSpecsForParents((ClassSymbol)t);
    			//                    }
    			//                }

        		utils.note(true, "Queueing specs request for " + csymbol + " [" + nestingLevel + "]");
        		
    			JmlSpecs.instance(context).setStatus(csymbol, JmlSpecs.SpecsStatus.QUEUED);
    			binaryEnterTodo.prepend(csymbol);

    			for (Type t: csymbol.getInterfaces()) {
    				requestSpecsForSelfAndParents((ClassSymbol)t.tsym);
    			}
    			if (csymbol.getSuperclass() != Type.noType) { // Object has noType as a superclass
    				requestSpecsForSelfAndParents((ClassSymbol)csymbol.getSuperclass().tsym);
    			}

    		} finally {
    			nestingLevel --;
    		}
    	}

    	// This nesting level is used to be sure we do not start processing a class, 
    	// say a superclass, before we have finished loading specs for a given class
    	if (nestingLevel==0) completeBinaryEnterTodo();

    }

    ListBuffer<ClassSymbol> binaryEnterTodo = new ListBuffer<ClassSymbol>();
    
    private void completeBinaryEnterTodo() {
    	JmlSpecs specs = JmlSpecs.instance(context);
    	while (!binaryEnterTodo.isEmpty()) {
    		ClassSymbol csymbol = binaryEnterTodo.remove();
    		if (Utils.debug()) System.out.println("CBETODO " + csymbol + " " + csymbol.type + " " + specs.status(csymbol));
//    		if (csymbol.type instanceof Type.ErrorType) {
//        		if (Utils.debug()) System.out.println("CBETODO-ERR " + csymbol + " " + csymbol.type + " " + specs.status(csymbol));
//        		continue; // A bad type causes crashes later on
//    		}

    		// Last check to see if specs are already present
    		if (JmlSpecs.SpecsStatus.QUEUED.less(specs.status(csymbol))) continue;

    		nestingLevel++;
    		try {
    			JmlCompilationUnit speccu = JmlCompiler.instance(context).parseSpecs(csymbol);
    			if (speccu != null) {
    				speccu.sourceCU = null; // Indicates a binary + specs file
    				binaryEnter(speccu);
    			} else {
    				// No specs, or error?
    				recordEmptySpecs(csymbol);
    				utils.note(true, "No specs for " + csymbol);
    			}
    		} finally {
				utils.note(true, "Completed entering specs for " + csymbol);
    			nestingLevel--;
    		}
    	}
    }
    
    
}
