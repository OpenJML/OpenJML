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
import org.jmlspecs.openjml.ext.Modifiers;
import org.jmlspecs.openjml.ext.TypeInitializerClauseExtension;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
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
import com.sun.tools.javac.resources.CompilerProperties.Errors;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
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

    /** A cached value of the Utils tool */
    /*@non_null*/
    final protected Utils utils;

    /** Don't call this: use instance() instead.
     * Creates an instance of the JmlEnter tool in the given context; note that
     * any options must be already set in Options prior to creating the tool.
     * @param context the compilation context to use for this tool
     */
    //@ assignable this.*;
    protected JmlEnter(Context context) {
        super(context); // automatically registers the new object
        this.context = context;
        this.utils = Utils.instance(context);
    }
    
    /** Returns the unique instance of Enter for the given context. */
    public static JmlEnter instance(Context context) {
    	return (JmlEnter)Enter.instance(context);
    }
    
    
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
    	JavaFileObject prevSource = log.useSource(tree.sourcefile);
    	try {
    		super.visitTopLevel(tree);
        } finally {
            log.useSource(prevSource);
        }
    }

//    public void checkForUnmatched(JmlCompilationUnit jmltree) {
//        String pack = jmltree.pid == null ? "" : (jmltree.pid.toString() + ".");
//        ListBuffer<JCTree> newlist = new ListBuffer<>();
//        boolean removed = false;
//        for (JCTree d : jmltree.defs) {
//            if (d instanceof JmlClassDecl) {
//                JmlClassDecl cd = (JmlClassDecl)d;
//                if (!utils.isJML(cd.mods)) { 
//                    String cdn = pack + cd.name.toString();
//                    try {
//                        if (ClassReader.instance(context).enterClass(names.fromString(cdn)) == null) {
//                            utils.error(jmltree.sourcefile, cd.pos,
//                                    "jml.unmatched.type",cdn);
//                            removed = true;
//                            continue;
//                        }
//                    } catch (CompletionFailure ex) {
//                        utils.error(jmltree.sourcefile, cd.pos,
//                                "jml.unmatched.type",cdn);
//                        removed = true;
//                        continue;
//                    }
//                }
//            }
//            newlist.add(d);
//        }
//        if (removed) jmltree.defs = newlist.toList();
//    }
    
//    /** Returns true if two type expressions appear to match */
//    public boolean matches(JCExpression jtype, JCExpression stype) {
//    	String a = JmlPretty.write(jtype);
//    	String b = JmlPretty.write(stype);
//    	return a.equals(b) || a.endsWith("." + b) || b.endsWith("." + a);
//    }
//    
//    /** Returns true if name and signature match */
//    public boolean matches(JmlMethodDecl specsDecl, JmlMethodDecl javaDecl) {
//    	if (!specsDecl.name.equals(javaDecl.name)) return false;
//    	if (specsDecl.params.size() != javaDecl.params.size()) return false;
//    	var jiter = javaDecl.params.iterator();
//    	var siter = specsDecl.params.iterator();
//    	while (jiter.hasNext()) {
//    		if (!matches(jiter.next().vartype, siter.next().vartype)) return false;
//    	}
//    	return true;
//    }
    
//    public List<JCTree> matchMembers(/*@nullable*/ JCClassDecl owner, List<JCTree> javaDefs, List<JCTree> specsDefs, JavaFileObject javasource) {
//    	ListBuffer<JCTree> adds = new ListBuffer<>();
//    	if (javaDefs == specsDefs) {
//    		for (var decl: javaDefs) {
//    			if (decl instanceof JmlClassDecl) {
//    				((JmlClassDecl)decl).specsDecl = (JmlClassDecl)decl;
//    			} else if (decl instanceof JmlMethodDecl) {
//    				((JmlMethodDecl)decl).specsDecl = (JmlMethodDecl)decl;
//    			} else if (decl instanceof JmlVariableDecl) {
//    				((JmlVariableDecl)decl).specsDecl = (JmlVariableDecl)decl;
//    			}
//    		}
//    	} else {
//			//boolean compare = (org.jmlspecs.openjml.Main.useJML && owner != null && owner.toString().endsWith("Throwable"));
//        	var matched = new java.util.HashSet<JCTree>();
//    		for (var decl: javaDefs) {
//    			if (decl instanceof JmlClassDecl) {
//    				JmlClassDecl javaDecl = (JmlClassDecl)decl;
//    				x: {
//    					for (var sdecl: specsDefs) {
//    						if (!(sdecl instanceof JmlClassDecl)) continue;
//    						JmlClassDecl specsDecl = (JmlClassDecl)sdecl;
//    		    			boolean isSpecsJML = utils.isJML(specsDecl.mods);
//    						if (specsDecl.name.equals(javaDecl.name)) {
//    							matched.add(specsDecl);
//    							if (isSpecsJML) {
//        							// A specification declaration matches a java declaration,
//        							// but the specification declaration is in a JML annotation - error - but use it as a match anyway
//        							utils.error(specsDecl.source(), specsDecl.pos,
//        									"jml.duplicate.model",
//        									"type", specsDecl.name, javasource);
//        							String s = utils.locationString(specsDecl.pos, specsDecl.source());
//        							utils.error(javaDecl.source(), javaDecl.pos, "jml.associated.decl.cf", s);
//    							}
//    							javaDecl.specsDecl = specsDecl;
//    							break x;
//    						}
//    						// No specs found
//    					}
//    					javaDecl.specsDecl = javaDecl; // FIXME - should be default specs
//    				}
//    			} else if (decl instanceof JmlMethodDecl) {
//    				JmlMethodDecl javaDecl = (JmlMethodDecl)decl;
//	    			//if (compare) System.out.println("MATCHING " + javaDecl + " " + javaDecl.sourcefile);
//   				    x: {
//    					for (var sdecl: specsDefs) {
//    						if (!(sdecl instanceof JmlMethodDecl)) continue;
//    						JmlMethodDecl specsDecl = (JmlMethodDecl)sdecl;
//    		    			//if (compare) System.out.println("TRYING " + specsDecl.name);
//    						boolean isSpecsJML = utils.isJML(specsDecl.mods);
//    						if (matches(specsDecl,javaDecl)) {
//        		    			//if (compare) System.out.println("MATCHED " + specsDecl.hashCode() + " " + specsDecl);
//    							matched.add(specsDecl);
//    							if (isSpecsJML) {
//        							// A specification declaration matches a java declaration,
//        							// but the specification declaration is in a JML annotation - error - but use it as a match anyway
//        							utils.error(specsDecl.source(), specsDecl.pos,
//        									"jml.duplicate.model",
//        									"method",specsDecl.name,javasource);
//        							String s = utils.locationString(specsDecl.pos, specsDecl.source());
//        							utils.error(javaDecl.source(), javaDecl.pos, "jml.associated.decl.cf", s);
//    							}
//    							javaDecl.specsDecl = specsDecl;
//    							break x;
//    						}
//    						// No specs found
//    					}
//    					javaDecl.specsDecl = javaDecl; // FIXME - should be default specs
//    				}
//
//    			} else if (decl instanceof JmlVariableDecl) {
//    				JmlVariableDecl javaDecl = (JmlVariableDecl)decl;
//    				// The parser inserts some implicit JML declarations, so a Java compilation unit
//    				// may already have some JML declarations.
//    				boolean isJavaJML = utils.isJML(javaDecl.mods);
//    				x: {
//    					for (var sdecl: specsDefs) {
//    						if (!(sdecl instanceof JmlVariableDecl)) continue;
//    						JmlVariableDecl specsDecl = (JmlVariableDecl)sdecl;
//    		    			boolean isSpecsJML = utils.isJML(specsDecl.mods);
//    						if (specsDecl.name.equals(javaDecl.name)) {
//    							matched.add(specsDecl);
//    							if (isSpecsJML && !isJavaJML) {
//        							// A specification declaration matches a java declaration,
//        							// but the specification declaration is in a JML annotation - error - but use it as a match anyway
//        							utils.error(specsDecl.source(), specsDecl.pos,
//        									"jml.duplicate.model",
//        									"field",specsDecl.name,javasource);
//        							String s = utils.locationString(specsDecl.pos, specsDecl.source());
//        							utils.error(javaDecl.source(), javaDecl.pos, "jml.associated.decl.cf", s);
//    							} else if (!isSpecsJML && isJavaJML) {
//    								utils.warning(specsDecl.source(), specsDecl.pos,
//    										"jml.message",
//    										"This specification declaration should be in a JML comment to match the declaration in the Java file");
//        							String s = utils.locationString(specsDecl.pos, specsDecl.source());
//        							utils.error(javaDecl.source(), javaDecl.pos, "jml.associated.decl.cf", s);
//    							}
//    							javaDecl.specsDecl = specsDecl;
//    							break x;
//    						}
//    						// No specs found
//    					}
//    					javaDecl.specsDecl = javaDecl; // FIXME - should be default specs
//    				}
//    			}
//    		}
//    		x: for (var sdecl: specsDefs) {
//    			if (matched.contains(sdecl)) continue;
//    			//if (compare) System.out.println("UNMATCHED " + sdecl);
//    			if (sdecl instanceof JmlClassDecl) {
//    				var specDecl = (JmlClassDecl)sdecl;
//    				if (utils.isJML(specDecl.mods)) {
//    					adds.add(sdecl);
//    					specDecl.specsDecl = specDecl;
//    				} else {
//    		    		for (var sdecl2: specsDefs) {
//    		    			if (sdecl != sdecl2 && sdecl2 instanceof JmlVariableDecl && specDecl.name == ((JmlMethodDecl)sdecl2).name) {
//    	    					utils.error(specDecl.source(), sdecl.pos,
//    	    							"jml.duplicate.jml.class.decl",
//    	    							specDecl.name);
//    							String s = utils.locationString(sdecl2.pos, specDecl.source());
//    							utils.error(specDecl.source(), sdecl2.pos, "jml.associated.decl.cf", s);
//    		    				continue x;
//    		    			}
//    		    		}
//    					utils.error(specDecl.source(), specDecl.pos,
//    							"jml.orphan.jml.class.decl",
//    							specDecl.name,javasource);
//    				}
//    			} else if (sdecl instanceof JmlMethodDecl) {
//    				var specDecl = (JmlMethodDecl)sdecl;
//    				if (utils.isJML(specDecl.mods)) {
//    					adds.add(sdecl);
//    					specDecl.specsDecl = specDecl;
//    				} else if ((owner.mods.flags & Flags.RECORD) == 0) { // FIXME - handle records
//    		    		for (var sdecl2: specsDefs) {
//    		    			if (sdecl != sdecl2 && sdecl2 instanceof JmlMethodDecl && matches(specDecl,(JmlMethodDecl)sdecl2)) {
//    	    					utils.error(specDecl.source(), sdecl.pos,
//    	    							"jml.duplicate.jml.method.decl",
//    	    							specDecl.name);
//    							String s = utils.locationString(sdecl2.pos, specDecl.source());
//    							utils.error(specDecl.source(), sdecl2.pos, "jml.associated.decl.cf", s);
//    		    				continue x;
//    		    			}
//    		    		}
//    					utils.warning(specDecl.source(), specDecl.pos,
//    							"jml.no.method.match",
//    							specDecl.name);
//						String s = utils.locationString(specDecl.pos, specDecl.source());
//						utils.warning(((JmlClassDecl)owner).sourcefile, owner.pos, "jml.associated.decl.cf", s);
//    				}
//    			} else if (sdecl instanceof JmlVariableDecl) {
//    				var specDecl = (JmlVariableDecl)sdecl;
//    				if (utils.isJML(specDecl.mods)) {
//    					adds.add(sdecl);
//    					specDecl.specsDecl = specDecl;
//    				} else if ((owner.mods.flags & Flags.RECORD) == 0) { // FIXME - handle records
//    		    		for (var sdecl2: specsDefs) {
//    		    			if (sdecl != sdecl2 && sdecl2 instanceof JmlVariableDecl && specDecl.name == ((JmlMethodDecl)sdecl2).name) {
//    	    					utils.error(specDecl.source(), sdecl.pos,
//    	    							"jml.duplicate.jml.var.decl",
//    	    							specDecl.name);
//    							String s = utils.locationString(sdecl2.pos, specDecl.source());
//    							utils.error(specDecl.source(), sdecl2.pos, "jml.associated.decl.cf", s);
//    		    				continue x;
//    		    			}
//    		    		}
//    					utils.error(specDecl.source(), specDecl.pos,
//    							"jml.no.var.match",
//    							specDecl.name,javasource);
//    				}
//    			}
//    		}
//    	}
//    	return adds.toList();
//    }



    
    // FIXME - document
    public void specsEnter(JmlCompilationUnit speccu) {
    	if (utils.verbose()) utils.note("Entering declarations from specification file " + speccu.sourcefile);
    	if (utils.verbose()) utils.note("                          Linked to Java file " + (speccu.sourceCU == null ? "<null>" : speccu.sourceCU.sourcefile.toString()));
		boolean isSameFile = speccu.sourceCU == speccu;
    	var prev = log.useSource(speccu.sourcefile);
    	var specs = JmlSpecs.instance(context);
		try {

			String flatPackageName = speccu.pid == null ? "" : speccu.pid.pid.toString();
			Name packageName = names.fromString(flatPackageName);
			PackageSymbol p = speccu.pid == null ? syms.unnamedModule.unnamedPackage : syms.getPackage(syms.unnamedModule,packageName);
			if (p == null) p = syms.getPackage(syms.java_base,packageName);
			// FIXME - what about other modules, or user modules
			if (p == null) {
				utils.warning(speccu.pid, "jml.message", "Creating new package in unnamed module: " + flatPackageName); // FIXME - figure out haw to create it
				p = syms.enterPackage(syms.unnamedModule, packageName);
			}

			speccu.packge = p;
			Env<AttrContext> specEnv = topLevelEnv(speccu);
            TypeEnter.instance(context).completeClass.resolveImports(speccu, specEnv);

            JmlCompilationUnit javacu = speccu.sourceCU;
            JmlClassDecl javaDecl = null;
            
            Map<Symbol,JCTree> alreadyMatched = new HashMap<>();
            
            ListBuffer<JCTree> newdefs = new ListBuffer<>();
			for (JCTree decl: speccu.defs) {
				if (!(decl instanceof JmlClassDecl)) { newdefs.add(decl); continue; }
				var specDecl = (JmlClassDecl)decl;
				javaDecl = 	findClass(specDecl.name, javacu);
				var ok = specsClassEnter(p, specDecl, specEnv, javaDecl, alreadyMatched); // javaDecl matches specDecl, if javaDecl exists
				if (ok) newdefs.add(specDecl);
				if (ok && javacu != null && javaDecl != specDecl) {
					var env = specs.get(specDecl.sym).specsEnv;
					Todo.instance(context).add(env);
					javacu.defs = javacu.defs.append(specDecl);
				}
			}
			speccu.defs = newdefs.toList();

			for (JCTree decl: speccu.defs) {
				if (!(decl instanceof JmlClassDecl)) continue;
				var specDecl = (JmlClassDecl)decl;
				javaDecl = findClass(specDecl.name, javacu);
				specsMemberEnter(p, specDecl, javaDecl, isSameFile, alreadyMatched);
			}
			
			// If we have a Java CU, add specs for any top-level classes in the Java CU that
			// do not have specs given in the specs cu.
			if (javacu != null) for (JCTree decl: javacu.defs) {
				if (!(decl instanceof JmlClassDecl)) continue;
				var jDecl = (JmlClassDecl)decl;
				if (specs.status(jDecl.sym) == JmlSpecs.SpecsStatus.NOT_LOADED) {
					specsClassEnter(p, jDecl, specEnv, jDecl, alreadyMatched);
				}
			}
		} finally {
			log.useSource(prev);
		}
    }
    
    public boolean specsClassEnter(Symbol owner, JmlClassDecl specDecl, Env<AttrContext> specsEnv, /*@ nullable */JmlClassDecl javaDecl, Map<Symbol,JCTree> alreadyMatched) {
    	Name className = specDecl.name;
		boolean isJML = utils.isJML(specDecl);
		boolean isOwnerJML = utils.isJML(owner.flags());
		boolean isModel = utils.hasMod(specDecl.mods, Modifiers.MODEL);
		boolean isLocal = !(owner instanceof ClassSymbol || owner instanceof PackageSymbol);
		ClassSymbol csym = javaDecl == null ? null : javaDecl.sym;
		// FIXME - the following may not work correctly for top-level classes whose u=owner is a package, at least in the test environment
		if (csym == null) csym = (ClassSymbol)owner.members().findFirst(className, s->(s instanceof ClassSymbol && s.owner == owner));
		boolean ok = false;
		try {
			if (isOwnerJML && isModel) {
				utils.error(specDecl, "jml.message", "A model type may not contain model declarations: " + specDecl.name + " in " + owner);
				// Attempt recovery by removing the offending annotation
				utils.removeAnnotation(specDecl.mods,  Modifiers.MODEL);
			} else if (isJML && !isModel && !isOwnerJML) {
				utils.error(specDecl, "jml.message", "A JML class declaration must be marked model: " + className + " (owner: " + owner +")");
				// Attempt recovery by adding a model annotation
				JmlTreeUtils.instance(context).addAnnotation(specDecl.mods, specDecl.mods.pos, specDecl.mods.pos, Modifiers.MODEL, null);
			} else if (!isJML && isModel) {
				var pos = utils.locMod(specDecl.mods, Modifiers.GHOST, Modifiers.MODEL);
				utils.error(pos, "jml.message", "A Java class declaration must not be marked either ghost or model: " + className + " (owner: " + owner +")");
				// Attempt recovery by removing the offending annotation
				utils.removeAnnotation(specDecl.mods,  Modifiers.MODEL);
			}
			if (csym == null) {
				// owner has no binary/source class corresponding to specDecl
				if (!isJML) {
					utils.error(specDecl, "jml.message", "There is no binary class to match this Java declaration in the specification file: " + className + " (owner: " + owner +")");
					return ok;
				}
				// Enter the class in the package or the parent class
				if (owner instanceof PackageSymbol) {
					PackageSymbol powner = (PackageSymbol)owner;
					csym = syms.enterClass(specsEnv.toplevel.modle, specDecl.name, powner);
					csym.completer = Completer.NULL_COMPLETER;
					csym.sourcefile = powner.sourcefile;
					// The following cloned from Enter.java
					if ((specDecl.mods.flags & PUBLIC) != 0 && !classNameMatchesFileName(csym, specsEnv)) {
						KindName topElement = KindName.CLASS;
						if ((specDecl.mods.flags & ENUM) != 0) {
							topElement = KindName.ENUM;
						} else if ((specDecl.mods.flags & INTERFACE) != 0) {
							topElement = KindName.INTERFACE;
						}
						log.error(specDecl.pos(),
								Errors.ClassPublicShouldBeInFile(topElement, specDecl.name));
					}
				} else { // owner is a ClassSymbol
					ClassSymbol cowner = (ClassSymbol)owner;
					csym = syms.enterClass(specsEnv.toplevel.modle, specDecl.name, cowner);
					csym.completer = Completer.NULL_COMPLETER;
					csym.sourcefile = cowner.sourcefile;
					((ClassType)csym.type).typarams_field = List.from(cowner.type.getTypeArguments());
				}
				csym.flags_field = specDecl.mods.flags | Flags.UNATTRIBUTED;
				var ct = (ClassType)csym.type;
				if (specDecl.extending != null) ct.supertype_field = specDecl.extending.type;
				else if ((specDecl.mods.flags & Flags.INTERFACE) == 0) ct.supertype_field = syms.objectType;
//				specDecl.implementing.forEach(t -> Attr.instance(context).attribType(t,env));
//				specDecl.permitting.forEach(t -> Attr.instance(context).attribType(t,env));
//				specDecl.typarams.forEach(t -> Attr.instance(context).attribType(t,env));
				csym.members_field = WriteableScope.create(csym);
				owner.members().enter(csym);
				if (utils.verbose()) utils.note("Entering JML class: " + csym + " (owner: " + owner +")" + " super: " + csym.getSuperclass());
				specDecl.sym = csym;
				specDecl.type = ct;
			} else {
				// owner has a binary/source class corresponding to specDecl, namely csym
				boolean matchIsJML = utils.isJML(csym.flags());
				if (isJML) {
					if (matchIsJML) {
						if (javaDecl != specDecl) {
							JmlSpecs.TypeSpecs tspecs = JmlSpecs.instance(context).get(csym);
							utils.error(specDecl, "jml.message", "This JML class declaration conflicts with a previous JML class: " + specDecl.name + " (owner: " + owner +")");
							if (tspecs != null && tspecs.decl != null) {
								utils.error(tspecs.decl.sourcefile, tspecs.decl, "jml.associated.decl.cf", utils.locationString(specDecl.pos, log.currentSourceFile()));
								owner.members().remove(csym);
							}
							return ok;
						}
					} else {
						utils.error(specDecl, "jml.message", "This JML class declaration conflicts with an existing binary class with the same name: " + className + " (owner: " + owner +")");
						if (javaDecl != null) utils.error(javaDecl.sourcefile, javaDecl, "jml.associated.decl.cf", utils.locationString(specDecl.pos, log.currentSourceFile()));
						owner.members().remove(csym);
						return ok;
					}
				}
				if (!isJML && matchIsJML) {
					JmlSpecs.TypeSpecs tspecs = JmlSpecs.instance(context).get(csym);
					utils.error(specDecl, "jml.message", "This class declaration conflicts with a previous JML method: " + specDecl.name + " (owner: " + csym +")");
					if (tspecs != null) {
						utils.error(tspecs.decl, "jml.associated.decl.cf", utils.locationString(specDecl.pos, log.currentSourceFile()));
						owner.members().remove(csym);
						return ok;
					}
				}
				if (!isJML && !matchIsJML && alreadyMatched.containsKey(csym)) {
					utils.error(specDecl, "jml.message", "This declaration duplicates an earlier declaration");
					var match = (JmlClassDecl)alreadyMatched.get(csym);
					utils.error(match.source(), match, "jml.associated.decl.cf", utils.locationString(specDecl.pos, specDecl.source()));
					return ok;
				}
//				{
//					var ct = (ClassType)csym.type;
//					if (specDecl.extending != null) {
//						//if (specDecl.extending instanceof JCTypeApply) ((JCTypeApply)specDecl.extending).arguments.forEach(t -> t.type = Attr.instance(context).attribType(t,env));
//						ct.supertype_field = specDecl.extending.type;
//						System.out.println("SUPERTYPE " + ct.supertype_field + " " + csym.getSuperclass());
//					}
//					else if ((specDecl.mods.flags & Flags.INTERFACE) == 0) ct.supertype_field = syms.objectType;
//				}
				if (specDecl == javaDecl) {
					// Defensive check
					if (csym != javaDecl.sym) utils.error(specDecl.sourcefile,  specDecl, "jml.internal", "class symbol does not match : " + csym + " vs. " + javaDecl.sym); 
					specDecl.specsDecl = specDecl;
					if (utils.verbose()) utils.note("Matched class: (self) " + csym + " (owner: " + csym.owner +")" );
				} else {
					checkAndEnterTypeParameters(csym,specDecl,specsEnv); // FIXME - just does checking
					if (utils.verbose()) utils.note("Matched class: " + csym + " (owner: " + csym.owner +")" );
					specDecl.sym = csym;
					specDecl.type = csym.type;
					{
//						if (specDecl.extending != null) {
//							//if (specDecl.extending instanceof JCTypeApply) ((JCTypeApply)specDecl.extending).arguments.forEach(t -> t.type = Attr.instance(context).attribType(t,env));
//							specDecl.extending.type = Attr.instance(context).attribType(specDecl.extending,specsEnv);
//							specDecl.implementing.forEach(t -> t.type = Attr.instance(context).attribType(t, specsEnv));
//							System.out.println("SUPERTYPE " + specDecl.extending.type + " # " + specDecl.implementing);
//						}
					}
				}
//				System.out.println("TYES "+ csym.type + " " + csym.getSuperclass());
				if (!checkClassMatch(javaDecl, specDecl)) return ok;
				alreadyMatched.put(csym, specDecl);
			}
			if (specDecl.typarams.size() == csym.type.getTypeArguments().size()) {
				for (int i = 0; i < specDecl.typarams.length(); ++i) {
					specDecl.typarams.get(i).type = csym.type.getTypeArguments().get(i).tsym.type;
				}
			}
			Env<AttrContext> localEnv = classEnv(specDecl, specsEnv);
			TypeEnter.instance(context).new MembersPhase().enterThisAndSuper(csym,  localEnv);
			if (typeEnvs.get(csym) == null) {
				((ClassType)csym.type).typarams_field = classEnter(specDecl.typarams, localEnv); // FIXME - what does this do???
				typeEnvs.put(csym, localEnv);
			}
			var tspecs = new JmlSpecs.TypeSpecs(specDecl, localEnv);
			if (csym != null) JmlSpecs.instance(context).putSpecs(csym, tspecs);

			// Do all nested classes, so their names are known later when attributing types of methods and fields
			ListBuffer<JCTree> newdefs = new ListBuffer<JCTree>();
			for (JCTree t: specDecl.defs) {
				if (t instanceof JmlClassDecl) {
					JmlClassDecl st = (JmlClassDecl)t;
					JmlClassDecl jt = findClass(st.name, javaDecl);
					var okk = specsClassEnter(csym, st, localEnv, jt, alreadyMatched);
					if (okk) newdefs.add(t);
					if (okk && javaDecl != null && st != jt && utils.isJML(st.mods)) javaDecl.defs = javaDecl.defs.append(st);
				} else {
					newdefs.add(t);
				}
			}
			specDecl.defs = newdefs.toList();
			ok = true;
		} catch (Exception e) {
			utils.unexpectedException("JmlEnterspecsClassEnter", e);
		} finally {
			if (!ok && csym != null) {
				JmlSpecs.instance(context).setStatus(csym, JmlSpecs.SpecsStatus.ERROR);
				owner.members().remove(csym);
			}
		}
		return ok;
    }
    
    public <T> T find(List<T> list, java.util.function.Predicate<T> pred) {
    	if (list != null) for (var item: list) {
    		if (pred.test(item)) return item;
    	}
    	return null;
    }
    
    public JmlClassDecl findClass(Name n, JmlClassDecl javaDecl) {
		JmlClassDecl jt = null;
		if (javaDecl != null) {
			for (var d: javaDecl.defs) {
				if (d instanceof JmlClassDecl && ((JmlClassDecl)d).name == n) {
					jt = (JmlClassDecl)d;
					break;
				}
			}
		}
		return jt;
    }
    
    public JmlClassDecl findClass(Name n, JmlCompilationUnit javaDecl) {
		JmlClassDecl jt = null;
		if (javaDecl != null) {
			for (var d: javaDecl.defs) {
				if (d instanceof JmlClassDecl && ((JmlClassDecl)d).name == n) {
					jt = (JmlClassDecl)d;
					break;
				}
			}
		}
		return jt;
    }
    
    public void specsMemberEnter(Symbol owner, JmlClassDecl specDecl, JmlClassDecl javaDecl, boolean isSameCU, Map<Symbol,JCTree> alreadyMatched) {
		// Already know that jdecl.name matches jdecl.sym.name
		ClassSymbol csym = specDecl.sym;
		JmlSpecs specs = JmlSpecs.instance(context);
		var tspecs = JmlSpecs.instance(context).get(csym);
		if (Utils.debug() && tspecs == null) utils.note("No specs for " + csym + " " + specDecl.name + " " + (specDecl==javaDecl));
		var specsEnv = tspecs.specsEnv;
		if (Utils.debug() && specsEnv == null) utils.note("No specs ENV for " + csym + " " + specDecl.name + " " + (specDecl==javaDecl));
		
		if (specDecl.extending != null) {
			Type t = specDecl.extending.type = JmlAttr.instance(context).attribType(specDecl.extending, specsEnv);
			if (!JmlTypes.instance(context).isSameType(t, csym.getSuperclass())) {
				utils.error(specDecl.extending, "jml.message", "Supertype in specification differs from supertype in source/binary: " + csym + " " + t + " " + csym.getSuperclass() + " " + owner + " " + specDecl);
			}
		} else if (!csym.isInterface() && !csym.isEnum() && !csym.isRecord()) {
			// jdecl has no declared supertype so either 
			// (a) it is Object and csym is also java.lang.Object
			// or (b) the superclass of csym is Object
			if (!JmlTypes.instance(context).isSameType(syms.objectType, csym.type) && 
			    !JmlTypes.instance(context).isSameType(syms.objectType, csym.getSuperclass())) {
				utils.error(specDecl, "jml.message", "Supertype in specification differs from supertype in source/binary: " + "Object" + " " + csym.getSuperclass());
			}
		}
		// FIXME - check type parameters, interfaces, permitted, flags, annotations, enclosing class
		
		boolean hasStaticInit = false;
		boolean hasInstanceInit = false;
		for (JCTree t: specDecl.defs) {
			if (t instanceof JmlMethodDecl) {
				specsEnter(csym, (JmlMethodDecl)t, specsEnv, javaDecl, isSameCU, alreadyMatched);
			} else if (t instanceof JmlVariableDecl) {
				specsEnter(csym, (JmlVariableDecl)t, specsEnv, javaDecl, isSameCU, alreadyMatched);
			} else if (t instanceof JmlBlock) {
				if (specDecl != javaDecl) {
					utils.error(t, "jml.initializer.block.allowed");
				}
			} else if (t instanceof JmlTypeClauseInitializer) {
				if (((JmlTypeClauseInitializer)t).keyword == TypeInitializerClauseExtension.staticinitializerID) {
					if (hasStaticInit) utils.error(t, "jml.one.initializer.spec.only");
					else hasStaticInit = true;
				}
				if (((JmlTypeClauseInitializer)t).keyword == TypeInitializerClauseExtension.initializerID) {
					if (hasInstanceInit) utils.error(t, "jml.one.initializer.spec.only");
					else hasInstanceInit = true;
				}
			}
		}
		
		var classIsPure = utils.findMod(specDecl.mods, Modifiers.PURE);
		
		// Add specifications for Java declarations that do not have specification declarations
		for (Symbol m: specDecl.sym.members().getSymbols(s->s instanceof MethodSymbol)) {
			MethodSymbol ms = (MethodSymbol)m;
			if (specs.get(ms) == null) {
				//utils.note("Method " + specDecl.sym + "." + m + " has no specifications -- using defaults");
				JmlMethodDecl mdecl = javaDecl == null ? null : (JmlMethodDecl)find(javaDecl.defs, t->(t instanceof JmlMethodDecl && ((JmlMethodDecl)t).sym == m));
				if (classIsPure != null && mdecl != null) {
					mdecl.mods.annotations = mdecl.mods.annotations.append(classIsPure);
				}
				specs.putSpecs(ms, specs.defaultSpecs(mdecl,ms,com.sun.tools.javac.util.Position.NOPOS), null); // FIXME - what to use for specsEnv -- there might be parameters to attribute
			}
		}

 		for (JCTree t: specDecl.defs) {
			if (t instanceof JmlClassDecl) {
				JmlClassDecl st = (JmlClassDecl)t;
				specsMemberEnter(csym, st, findClass(st.name, javaDecl), isSameCU, alreadyMatched);
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
    
    public void addAttribute(JCAnnotation a, Type t, Env<AttrContext> env) {
    	a.attribute = annotate.attributeTypeAnnotation(a, t, env);
    }
    
    public void addAttribute(List<JCAnnotation> alist, Type t, Env<AttrContext> env) {
    	for (var a: alist) {
    		a.attribute = annotate.attributeTypeAnnotation(a, t, env);
    	}
    }
    
    public void addAttribute(JCExpression at, Type t, Env<AttrContext> env) {
    	if (at instanceof JCAnnotatedType) {
    		addAttribute(((JCAnnotatedType)at).annotations, t, env);
    		addAttribute(((JCAnnotatedType)at).underlyingType, t, env);
    	}
    }
    
    public MethodSymbol findMethod(ClassSymbol csym, JmlMethodDecl mdecl, Env<AttrContext> env) {
    	//print = mdecl.name.toString().equals("equals");
    	boolean hasTypeParams =  mdecl.typarams.length() != 0;
    	boolean useStringComparison = false;
    	if (print) System.out.println("SEEKING " + csym + " " + mdecl.name + " " + mdecl.sym + " " + mdecl.type + " " + hasTypeParams + " " + csym.members());
    	if (print && mdecl.sym != null) System.out.println("       SYMTYPE " + mdecl.sym.type);
    	for (var p: mdecl.params) {
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
		var iter = csym.members().getSymbolsByName(mdecl.name, s->(s instanceof Symbol.MethodSymbol)).iterator();
    	x: while (iter.hasNext()) {
    		var m = (MethodSymbol)iter.next();
    		if (print) System.out.println("CONSIDERING " + m + " " + m.type + " " + m.params.length() + " " + mdecl.params.length() + " " + m.getTypeParameters().length() + " " + mdecl.getTypeParameters().length());
    		if (m.params.length() != mdecl.params.length()) continue;
    		if (m.getTypeParameters().length() != mdecl.getTypeParameters().length()) continue;
    		if (print) System.out.println("CONSIDERING-A " + m);
			first = m;
			count++;
			if (hasTypeParams) {
				if (print) System.out.println("COMPARING-TP " + m.type + " " + mdecl.sym.type + " " + types.isSameType(m.type,mdecl.sym.type));
//				var atypes = m.type.getTypeArguments();
//				var btypes = mdecl.sym.type.getTypeArguments();
//				var ntype = types.subst(m.type, atypes, btypes);
				if (!types.isSameType(m.type, mdecl.sym.type)) continue x;
//				for (int i=0; i<m.params.length(); i++) {
//					// FIXME - When there are type parameters, the type resolution above is not working
//					// so we fall back to string comparison -- a hack that only partially works
//					// Probably has to do with getting the correct env
//					//if (Utils.debug()) System.out.println("TYPES " + m.params.get(i).type.toString() + " " + mdecl.params.get(i).vartype.toString());
//					if (!matchAsStrings(m.params.get(i).type, mdecl.params.get(i).vartype)) continue x;
//				}
			} else {
				if (print) System.out.println("COMPARING-T " + m.type + " " + mdecl.sym.type + " " + types.isSameType(m.type,mdecl.sym.type));
				if (!types.isSameType(m.type,mdecl.sym.type)) continue x;
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
				var mi = mdecl.getTypeParameters().get(i);
				var mj = msym.getTypeParameters().get(i);
				mi.type = mj.type;
				for (int j=0; j<mi.bounds.length(); ++j) mi.bounds.get(j).type = mj.getBounds().get(j);
			}
			for (int i = 0; i < mdecl.params.length(); ++i) mdecl.params.get(i).type = mt.argtypes.get(i);
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
    
    public void specsEnter(ClassSymbol csym, JmlMethodDecl mdecl, Env<AttrContext> specsEnv, JmlClassDecl javaDecl, boolean isSameCU, Map<Symbol,JCTree> alreadyMatched) {
		boolean isJML = utils.isJML(mdecl);
		boolean isOwnerJML = utils.isJML(csym.flags());
		boolean isModel = utils.hasMod(mdecl.mods, Modifiers.MODEL);
		var specs = JmlSpecs.instance(context);
		if (isOwnerJML && isModel) {
			utils.error(mdecl, "jml.message", "A model type may not contain model declarations: " + mdecl.name + " in " + csym);
			// Attempt recovery by removing the offending annotation
			utils.removeAnnotation(mdecl.mods,  Modifiers.MODEL);
		} else if (!isJML && isModel ) {
			var pos = utils.locMod(mdecl.mods, Modifiers.MODEL);
			utils.error(pos, "jml.message", "A Java method declaration must not be marked model: " + mdecl.name + " (owner: " + csym +")");
			// Attempt recovery by removing the offending annotation
			utils.removeAnnotation(mdecl.mods,  Modifiers.MODEL);
		} else if (isJML && !isModel && !isOwnerJML) {
			utils.error(mdecl, "jml.message", "A JML method declaration must be marked model: " + mdecl.name + " (owner: " + csym +")");
			// Attempt recovery by adding a model annotation
			JmlTreeUtils.instance(context).addAnnotation(mdecl.mods, mdecl.mods.pos, mdecl.mods.pos, Modifiers.MODEL, null);
		}

		WriteableScope enclScope = enterScope(specsEnv);
		Symbol.MethodSymbol msym = mdecl.sym; // Nonnull if specs and java decls are the same file
		if (mdecl.sym == null) {
			var saved = JmlMemberEnter.instance(context).enterJML;
			JmlMemberEnter.instance(context).enterJML = false;
			makeAndEnterMethodSym(mdecl, specsEnv);
			JmlMemberEnter.instance(context).enterJML = saved;
			for (int i=0; i<mdecl.params.length(); ++i) { // One would think that the attribution of mdecl would set the parameter types, but it just sets the types in the parameter sym
				mdecl.params.get(i).type = mdecl.sym.params.get(i).type;
			}
			msym = findMethod(csym, mdecl, specsEnv);
		}
    	if (msym == null) {
			// No corresponding Java method
    		if (!isJML) {
    			String msg = "There is no binary method to match this Java declaration in the specification file: " + mdecl.name + " (owner: " + csym + ")";
				for (var s: csym.members().getSymbolsByName(mdecl.name, s->(s instanceof MethodSymbol))) {
					msg = msg + "\n    " + csym + " has " + s;
				}
				utils.error(mdecl, "jml.message", msg);
				return;
    		}
			// Enter the method in the parent class
			msym = mdecl.sym; // makeAndEnterMethodSym(mdecl, specsEnv); // Also calls putSpecs
			enclScope.enter(msym);
			var sp = specs.getLoadedSpecs(msym);
			sp.javaDecl = null;
			sp.specDecl = mdecl;
			sp.javaSym = null;
			sp.specSym = mdecl.sym;
			sp.javaEnv = null;
			
			if (javaDecl != null && !isSameCU && isJML && !isOwnerJML) {
				javaDecl.defs = javaDecl.defs.append(mdecl);
			}
			if (!isModel && mdecl.body != null) {
				utils.error(mdecl.body, "jml.message", "The specification of the method " + csym + "." + msym + " must not have a body");
			}
			if (utils.verbose()) utils.note("Entered JML method: " + msym + " (owner: " + csym + ")" );
    	} else {
			// Found a matching Java method
    		final var mmsym = msym;
    		JmlMethodDecl javaMDecl = javaDecl == null ? null : (JmlMethodDecl)find(javaDecl.defs, t->(t instanceof JmlMethodDecl && ((JmlMethodDecl)t).sym == mmsym));
    		boolean matchIsJML = utils.isJML(msym.flags());

    		if (isJML && !utils.isJML(csym.flags())) {
    			if (matchIsJML) {
    				if (javaMDecl == null) {
    					JmlSpecs.MethodSpecs mspecs = JmlSpecs.instance(context).getSpecs(msym);
    					utils.error(mdecl, "jml.message", "This JML method declaration conflicts with a previous JML method: " + msym + " (owner: " + csym +")");
    					utils.error(mspecs.cases.decl, "jml.associated.decl.cf", utils.locationString(mdecl.pos, log.currentSourceFile()));
    					return;
    				}
    			} else {
    				// If isSameCU, already reported as duplicate during MemberEnter
    				if (!isSameCU) utils.error(mdecl, "jml.message", "This JML method declaration conflicts with an existing binary method with the same name: " + mdecl.name + " (owner: " + csym +")");
    				return;
    			}
    		}
    		if (!isJML && matchIsJML) {
    			JmlSpecs.MethodSpecs mspecs = JmlSpecs.instance(context).getSpecs(msym);
    			utils.error(mdecl, "jml.message", "This Java method declaration conflicts with a previous JML method: " + mdecl.name + " (owner: " + csym +")");
    			utils.error(mspecs.cases.decl, "jml.associated.decl.cf", utils.locationString(mdecl.pos, log.currentSourceFile()));
    			return;
    		}
    		if (mdecl != javaMDecl && mdecl.restype != null) {
    			Type t = Attr.instance(context).attribType(mdecl.restype,csym);
    			// The difficulty here is that TypeVars show up as different types,
    			// and that binary types are erased, so do not have type arguments.
    			try {
    				msym.getReturnType();
    			} catch (Exception e) {
    				System.out.println("RETTYPE " + msym + " " + t + " " + mdecl.sym + " " + (msym.type != null) + " " + msym.type + " " + mdecl.sym.type);
    			}
    			if (!specsTypeSufficientlyMatches(t, msym.getReturnType(), javaMDecl == null, msym)) {
    				utils.error(mdecl.restype,  "jml.mismatched.return.type", 
    						msym.enclClass().fullname + "." + msym.toString(),t,msym.getReturnType());
    			}
    		}
    		if (!isModel && mdecl.body != null && !isSameCU && ((msym.flags() & Flags.GENERATEDCONSTR) == 0)) {
    			utils.error(mdecl.body, "jml.message", "The specification of the method " + csym + "." + msym + " must not have a body");;
    		}
    		
    		// Either
    		// 0) There is no Java declaration, just a (model/ghost) spec declaration -- that is the case above with msym == null
    		// 1) Just binary, no source Java declaration, and a jml declaration: javaMDecl == null
    		// 2) Java and JML are the same file: javaMDecl == mdecl
    		// 3) Java and JML are different files: javaMDecl != null, javaMDecl != mdecl
    		// Note that the javaSym may have already been used for attribution of other code, so we have to use it
    		// as the MethodSymbol to retrive information from the specs database.
    		if (mdecl == javaMDecl) {
    			// In this case we did not do a separate attribution of the method signature
    			// Defensive check
    			if (mdecl.sym != msym) utils.error(mdecl.sourcefile, mdecl, "jml.internal.notsobad", "msym values do not match: " + mdecl.sym + " " + msym);
    			if (utils.verbose()) utils.note("Matched method: (self) " + msym + " (owner: " + msym.owner +")");
    			var sp = specs.getLoadedSpecs(msym);
    			sp.javaDecl = javaMDecl;
    			sp.specDecl = mdecl;
    			sp.javaSym = msym;
    			sp.specSym = mdecl.sym;
    			sp.javaEnv = sp.specsEnv;
    		} else if (javaMDecl == null) {
    			if (utils.verbose()) utils.note("Matched method: (binary) " + msym + " (owner: " + msym.owner +")");
    			// No specs entry for msym -- msym is just the symbol created on loading the binary class file
    			var ssp = specs.getLoadedSpecs(mdecl.sym);
//    			if (msym.toString().contains("arraycopy")) {
//    				System.out.println("JMLENTER-J " + msym + " " + msym.params.head + " " + msym.params.head.hashCode());
//    				System.out.println("JMLENTER-S " + mdecl.sym + " " + mdecl.sym.params.head + " " + mdecl.sym.params.head.hashCode());
//    				System.out.println("JMLENTER-SS " + mdecl.params.head.sym + " " + mdecl.params.head.sym.hashCode());
//    				System.out.println("SPECENV " + specs.getLoadedSpecs(mdecl.sym).specsEnv.info.scope().getSymbolsByName(mdecl.sym.params.head.name).iterator().next().hashCode());
//    				//System.out.println("JAVAENV " + specs.getLoadedSpecs(msym).specsEnv.info.scope().getSymbolsByName(msym.params.head.name).iterator().next().hashCode());
//    			}
    			ssp.javaDecl = javaMDecl;
    			ssp.specDecl = mdecl;
    			ssp.javaSym = msym;
    			ssp.specSym = mdecl.sym;
    			ssp.javaEnv = null;
    			specs.setStatus(msym, ssp.status);
    			specs.dupSpecs(msym,  mdecl.sym);
    			checkMethodMatch(javaMDecl,msym,mdecl,csym);
    		} else { // javaMDecl != mdecl
    			if (utils.verbose()) utils.note("Matched method: (java) " + msym + " (owner: " + msym.owner +")");
    			var jsp = specs.getLoadedSpecs(msym);
    			var ssp = specs.getLoadedSpecs(mdecl.sym);
    			jsp.javaDecl = ssp.javaDecl = javaMDecl;
    			jsp.specDecl = ssp.specDecl = mdecl;
    			jsp.javaSym = ssp.javaSym = msym;
    			jsp.specSym = ssp.specSym = mdecl.sym;
    			javaMDecl.specsDecl = mdecl;
    			ssp.javaEnv = jsp.specsEnv;
    			jsp.specsEnv = ssp.specsEnv;
    			jsp.cases = ssp.cases;
    			jsp.status = ssp.status;
    			specs.setStatus(msym, ssp.status);
    			checkMethodMatch(javaMDecl,msym,mdecl,csym);
    		}
    		alreadyMatched.put(msym,mdecl);
    	}
    	var iter = msym.params.iterator();
    	VarSymbol vs = null;
    	for (var v: mdecl.params) {
    		if (iter.hasNext()) specs.putSpecs(vs = iter.next(), new JmlSpecs.FieldSpecs((JmlVariableDecl)v));
    		specs.putSpecs(v.sym, new JmlSpecs.FieldSpecs((JmlVariableDecl)v));
    		
    	}
    }
    
    public boolean specsTypeSufficientlyMatches(Type specsType, Type javaType, boolean isBinary, Symbol sym) {
		// The difficulty here is that TypeVars show up as different types,
		// and that binary types are erased, so do not have type arguments.
    	//if (sym.name.toString().equals("k")) System.out.println("COMPARING " + sym + " " + isBinary + " " + specsType + " " + javaType + " " + (specsType.getClass()));
    	if (types.isSameType(specsType, javaType)) return true;
//    	if ((specsType instanceof Type.TypeVar) != (javaType instanceof Type.TypeVar)) return false;
//    	if (specsType instanceof Type.TypeVar) return specsType.toString().equals(javaType.toString()); 
//    	if (!isBinary) return false;
    	
    	if (specsType.toString().startsWith(javaType.toString())) return true;
		return  false; // types.isSubtype(specsType, javaType);
    }
    
    public VarSymbol findVar(ClassSymbol csym, JmlVariableDecl vdecl, Env<AttrContext> env) {
    	Name vname = vdecl.name;
    	var iter = csym.members().getSymbolsByName(vname, s->(s instanceof VarSymbol && s.owner == csym)).iterator();
    	if (iter.hasNext()) {
    		var vsym = iter.next();
    		if (iter.hasNext()) {
    			var v = iter.next();
    			// This should never happen - two binary fields with the same name
    			if (vsym.name != names.error) utils.error(vdecl, "jml.message", "Unexpectedly found duplicate binary field symbols named " + vname + " (" + vsym + " vs. " + v + ")");
    		}
			if (vdecl.vartype instanceof JCAnnotatedType) {
				for (var a: ((JCAnnotatedType)vdecl.vartype).annotations) {
					a.attribute = annotate.attributeTypeAnnotation(a, syms.annotationType, env);
				}
			}
    		Attr.instance(context).attribType(vdecl.vartype, env);
    		annotate.flush();
			return (VarSymbol)vsym;
    	}
    	return null;
    }
    
    public void specsEnter(ClassSymbol csym, JmlVariableDecl vdecl, Env<AttrContext> specsEnv, JmlClassDecl javaDecl, boolean isSameCU, Map<Symbol,JCTree> alreadyMatched) {
		boolean isJML = utils.isJML(vdecl);
		boolean isOwnerJML = utils.isJML(csym.flags());
		boolean isGhost = utils.hasMod(vdecl.mods, Modifiers.GHOST);
		boolean isGhostOrModel = isGhost || utils.hasMod(vdecl.mods, Modifiers.MODEL);
		boolean ok = false;
		Symbol.VarSymbol vsym = findVar(csym, vdecl, specsEnv);
		try {
			if (isOwnerJML && isGhostOrModel) {
				utils.error(vdecl, "jml.message", "A model type may not contain " + (isGhost?"ghost":"model") + " declarations: " + vdecl.name + " in " + csym);
				// Attempt recovery by removing the offending annotation
				utils.removeAnnotation(vdecl.mods,  Modifiers.MODEL);
			} else if (isJML && !isGhostOrModel && !isOwnerJML) {
				utils.error(vdecl, "jml.message", "A JML field declaration must be marked either ghost or model: " + vdecl.name + " (owner: " + csym +")");
				// Attempt recovery by adding a ghost annotation
				JmlTreeUtils.instance(context).addAnnotation(vdecl.mods, vdecl.mods.pos, vdecl.mods.pos, Modifiers.GHOST, null);
			} else if (!isJML && isGhostOrModel) {
				var pos = utils.locMod(vdecl.mods, Modifiers.GHOST, Modifiers.MODEL);
				utils.error(pos, "jml.message", "A Java field declaration must not be marked either ghost or model: " + vdecl.name + " (owner: " + csym +")");
				// Attempt recovery by removing the offending annotation
				utils.removeAnnotation(vdecl.mods,  Modifiers.MODEL);
				utils.removeAnnotation(vdecl.mods,  Modifiers.GHOST);
			}

			if (vsym == null) {
				// No corresponding binary field
				if (!isJML) {
					utils.error(vdecl, "jml.message", "There is no binary field to match this Java declaration in the specification file: " + vdecl.name + " (owner: " + csym +")");
					return;
				}
				// Enter the class in the package or the parent class

				//				boolean declaredFinal = (vdecl.mods.flags & Flags.FINAL) != 0;
				MemberEnter me = MemberEnter.instance(context);
				var savedEnv = me.env;
				me.env = specsEnv;
				me.visitVarDef(vdecl);
				vdecl.vartype.type = vdecl.type = vdecl.sym.type;
				vsym = vdecl.sym;
				//				if (isGhostOrModel && vsym.owner.isInterface()) {
				//					// not final by default; no static if declared instance
				//					System.out.println("UNDOING FINAL " + !declaredFinal + (vsym.flags()&63));
				//					if (!declaredFinal && (vsym.flags() & Flags.FINAL)!= 0) vsym.flags_field &= ~Flags.FINAL; 
				//					if (utils.hasMod(vdecl.mods, Modifiers.INSTANCE)) vsym.flags_field &= ~Flags.STATIC; 
				//				}
				me.env = savedEnv;
				if (javaDecl != null && !isSameCU && isJML && !isOwnerJML) {
					javaDecl.defs = javaDecl.defs.append(vdecl);
				}

				if (utils.verbose()) utils.note("Entered JML field: " + vsym.type + " " + vsym + " (owner: " + vsym.owner + ")");
				ok = true;
			} else if (vsym.name != names.error) {
				// Found a matching binary field
				final var vvsym = vsym;
				JmlVariableDecl javaVDecl = javaDecl == null ? null : (JmlVariableDecl)find(javaDecl.defs,t->(t instanceof JmlVariableDecl && ((JmlVariableDecl)t).sym == vvsym));
				boolean matchIsJML = utils.isJML(vsym.flags());

				if (isJML) {
					if (matchIsJML) {
						if (javaVDecl == null) {
							JmlSpecs.FieldSpecs fspecs = JmlSpecs.instance(context).getSpecs(vsym);
							utils.error(vdecl, "jml.message", "This JML field declaration conflicts with a previous JML field: " + vdecl.name + " (owner: " + csym +")");
							utils.error(fspecs.decl, "jml.associated.decl.cf", utils.locationString(vdecl.pos, log.currentSourceFile()));
							return;
						}
					} else {
						if (!isSameCU) {
							utils.error(vdecl, "jml.message", "This JML field declaration conflicts with an existing field with the same name: " + vdecl.name + " (owner: " + csym +")");
							utils.error(javaVDecl.source(),javaVDecl, "jml.associated.decl.cf", utils.locationString(vdecl.pos, log.currentSourceFile()));
						}
						return;
					}
				}
				if (!isJML && matchIsJML) {
					JmlSpecs.FieldSpecs fspecs = JmlSpecs.instance(context).getSpecs(vsym);
					utils.error(vdecl, "jml.message", "This Java field declaration conflicts with a previous JML field: " + vdecl.name + " (owner: " + csym +")");
					utils.error(fspecs.decl, "jml.associated.decl.cf", utils.locationString(vdecl.pos, log.currentSourceFile()));
					return;
				}
				ok = true;

				if (vdecl == javaVDecl) {
					if (vdecl.sym != vsym) utils.error(vdecl.sourcefile, vdecl, "jml.message", "vsym values do not match: " + vdecl.sym + " " + vsym);
					vdecl.specsDecl = vdecl;
					vdecl.type = vdecl.vartype.type = vsym.type;
					//vdecl.type = vdecl.sym.type;
					if (utils.verbose()) utils.note("Matched field: (self) " + vsym + " (owner: " + csym +")" );
				} else {
					Type t = Attr.instance(context).attribType(vdecl.vartype, specsEnv);
					if (vsym.owner instanceof ClassSymbol) {
						if (!isSameCU && javaVDecl != null && alreadyMatched.containsKey(vsym)) { // if isSameCU==true, there already is a error about duplicate definition in MemberEnter
							utils.error(vdecl, "jml.message", "This specification declaration of field " + vdecl.name + " has the same name as a previous field declaration");
							JmlVariableDecl v = (JmlVariableDecl)alreadyMatched.get(vsym);
							utils.error(v.source(), v.pos, "jml.associated.decl.cf", utils.locationString(vdecl.pos, vdecl.source()));
						} else if ((!isJML && !matchIsJML) && !specsTypeSufficientlyMatches(t, vsym.type, javaVDecl == null, vsym)) {
							String msg = "Type of field " + vdecl.name + " in specification differs from type in source/binary: " + t + " vs. " + vsym.type;
							if (javaVDecl != null) {
								utils.error(vdecl.vartype, "jml.message", msg, javaVDecl.pos(), javaVDecl.sourcefile);
								utils.note(javaVDecl.source(), javaVDecl, "jml.associated.decl.cf", utils.locationString(vdecl.pos, vdecl.source()));
							} else {
								utils.error(vdecl.vartype, "jml.message", msg);
							}
							ok = false;
						}
					}
					vdecl.type = vdecl.vartype.type = vsym.type;
					vdecl.sym = vsym;
					checkVarMatch(javaVDecl,vsym,vdecl,csym);
					// Note - other checks are done in JmlAttr

					if (ok && utils.verbose()) utils.note("Matched field: " + vsym + " (owner: " + csym +")" );
				}
				alreadyMatched.put(vsym,vdecl);
			} else {
				ok = false;
				vdecl.type = vdecl.vartype.type = vsym.type;
			}
		} catch (Throwable t) {
			utils.error("Exception while entering field: " + vdecl.name);
			t.printStackTrace(System.out);
			ok = false;
		} finally {
			if (vsym != null) {
				JmlSpecs.instance(context).putSpecs(vsym, vdecl.fieldSpecs);
				if (!ok) JmlSpecs.instance(context).setStatus(vsym, JmlSpecs.SpecsStatus.ERROR);
			}
		}
    }

    
//    protected JCExpression findPackageDef(JCCompilationUnit that) {
//    	for (var tree: that.defs) {
//    		if (tree instanceof JCPackageDecl) return ((JCPackageDecl)tree).pid;
//    	}
//    	return null;
//    }
//

    

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
    public boolean checkAndEnterTypeParameters(ClassSymbol csym, JmlClassDecl specTypeDeclaration, Env<AttrContext> classEnv) {
    	Env<AttrContext> localEnv = classEnv;
    	//Scope enterScope = enterScope(classEnv);
    	boolean result = true;
    	int numSpecTypeParams = specTypeDeclaration.typarams.size();
    	int numJavaTypeParams = csym.type.getTypeArguments().size();
    	if (numSpecTypeParams != numJavaTypeParams) {
    		utils.error(specTypeDeclaration.source(),specTypeDeclaration.pos(),"jml.mismatched.type.arguments",specTypeDeclaration.name,csym.type.toString());
    		//log.error(specTypeDeclaration.pos(),"jml.mismatched.type.parameters", specTypeDeclaration.name, csym.fullname, n, javaN);
    		result = false;
    	}
        int nn = numSpecTypeParams; if (numJavaTypeParams < nn) nn = numJavaTypeParams;
        for (int i = 0; i<nn; i++) {
            JCTree.JCTypeParameter specTV = specTypeDeclaration.typarams.get(i);
            var javaTV = (Type.TypeVar)((ClassType)csym.type).getTypeArguments().get(i);
            if (specTV.name != javaTV.tsym.name) {
                utils.error(specTV.pos(),"jml.mismatched.type.parameter.name", specTypeDeclaration.name, csym.fullname, specTV.name, javaTV.tsym.name);
                result = false;
            } 
            // classEnter will set the type of the Type Variable, but it sets it to 
            // something new for each instance, which causes trouble in type mathcing
            // that I have not figured out. Here we preemptively set the type to be the
            // same as the Java type that it matches in the specification.
            specTV.type = javaTV;
            //if (localEnv != null) classEnter(specTV,localEnv); // FIXME - wouldn't this be a duplicate - or is localEnv always null
            //enterScope.enter(javaTV.tsym);
        }
//        for (int i = nn; i<numSpecTypeParams; i++) {
//            JCTree.JCTypeParameter specTV = specTypeDeclaration.typarams.get(i);
//            if (localEnv != null) classEnter(specTV,localEnv);
//        }
//        // FIXME need to check that the types have the same bounds
        return result;
    }


    protected boolean classNameMatchesFileName(ClassSymbol c, Env<AttrContext> env) {
    	boolean b =  env.toplevel.sourcefile.isNameCompatible(c.name.toString(),
                JavaFileObject.Kind.SOURCE);
    	if (!b) b = env.toplevel.sourcefile.isNameCompatible(c.name.toString(),
                JavaFileObject.Kind.JML);
    	return b;
    }

    private int nestingLevel = 0;
    
    public void hold() { 
    	nestingLevel++;
    }
    
    public void release() { 
    	nestingLevel--;
    }
    
    public void flush() {
    	if (nestingLevel == 0) completeBinaryEnterTodo();
    }
    
    /** Queues a class for loading specs. Once loaded, JmlSpecs contains the specs for each class, method,
     * and field, but they are not yet attributed. This is called to load specs for either binarh or source classes.
     * 
     * @param csymbol the class whose specs are wanted
     */
    public void requestSpecs(ClassSymbol csymbol) {
    	// Requests for nested classes are changed to a request for their outermost class
    	while (csymbol.owner instanceof ClassSymbol) csymbol = (ClassSymbol)csymbol.owner;

    	JmlSpecs.SpecsStatus tsp = JmlSpecs.instance(context).status(csymbol);
    	if (utils.verbose()) System.out.println("Requesting for " + csymbol + " " + tsp + " " + binaryEnterTodo.contains(csymbol) + " " + System.identityHashCode(csymbol) + " " + csymbol.hashCode() +  " " + System.identityHashCode(ClassReader.instance(context).enterClass(names.fromString("java.lang.Object"))));
    	if (!tsp.less(JmlSpecs.SpecsStatus.QUEUED)) {
    		if (utils.verbose()) {
    			if (tsp == JmlSpecs.SpecsStatus.QUEUED) utils.note(true,"Requesting specs " + csymbol + ", but specs already in progress");
    			else                                    utils.note(true,"Requesting specs " + csymbol + ", but specs already loaded or attributed");
    		}
    	} else {
        	// The binary Java class itself is already loaded - it is needed to produce the classSymbol itself

        	if (!binaryEnterTodo.contains(csymbol)) {
        		nestingLevel++;
        		try {
        			// It can happen that the specs are loaded during the loading of the super class 
        			// since complete() may be called on the class in order to fetch its superclass,
        			// or during the loading of any other class that happens to mention the type.
        			// So we recheck here, before reentering the class in the todo list
        			if (JmlSpecs.instance(context).status(csymbol) != JmlSpecs.SpecsStatus.NOT_LOADED) return;

        			// Classes are prepended to the todo list in reverse order, so that parent classes
        			// have specs read first.

        			// Note that nested classes are specified in the same source file as their enclosing classes
        			// Everything within a specification text file is loaded together

            		
        			JmlSpecs.instance(context).setStatus(csymbol, JmlSpecs.SpecsStatus.QUEUED);
            		if (utils.verbose()) utils.note("Queueing specs request for " + csymbol + " [" + nestingLevel + "]" + " " + binaryEnterTodo.contains(csymbol) + " " + csymbol.hashCode());
        			binaryEnterTodo.prepend(csymbol);

        			for (Type t: csymbol.getInterfaces()) {
        				requestSpecs((ClassSymbol)t.tsym);
        			}
        			if (csymbol.getSuperclass() != Type.noType) { // Object has noType as a superclass
        				requestSpecs((ClassSymbol)csymbol.getSuperclass().tsym);
        			}

        		} finally {
        			nestingLevel --;
        		}
        	}

        	// This nesting level is used to be sure we do not start processing a class, 
        	// say a superclass, before we have finished loading specs for a given class
        	if (nestingLevel==0) completeBinaryEnterTodo();
    	}
    }


    ListBuffer<ClassSymbol> binaryEnterTodo = new ListBuffer<ClassSymbol>();
    
    private void completeBinaryEnterTodo() {
    	JmlSpecs specs = JmlSpecs.instance(context);
    	while (!binaryEnterTodo.isEmpty()) {
    		ClassSymbol csymbol = binaryEnterTodo.remove();
    		// Specs may be loaded here for either source or binary classes.
    		// We can tell the difference by (a) whether a env has been stored (on entering the source)
    		// or whether csymbol.sourcefile is a ClassReader.SourceFileObject or something else.
			var sourceEnv = getEnv(csymbol);
			JmlCompilationUnit javaCU = sourceEnv == null ? null : (JmlCompilationUnit)sourceEnv.toplevel;
			JmlClassDecl javaDecl = sourceEnv == null ? null : (JmlClassDecl)sourceEnv.tree;
			if (utils.verbose()) utils.note("Dequeued to enter specs: " + csymbol + " " + specs.status(csymbol) + " " + csymbol.hashCode() + " " + (javaCU==null?" (binary)":(" (" + javaCU.sourcefile + ")")));
//    		if (csymbol.type instanceof Type.ErrorType) {
//        		continue; // A bad type causes crashes later on
//    		}

    		// Last check to see if specs are already present
    		if (JmlSpecs.SpecsStatus.QUEUED.less(specs.status(csymbol))) continue;

    		nestingLevel++;
    		JmlCompilationUnit speccu = null;
    		try {
    			speccu = JmlCompiler.instance(context).parseSpecs(csymbol);
    			if (speccu == null) speccu = javaCU; // If nothing in the specspath, use the Java source as specs
    			if (speccu != null) {
    				speccu.sourceCU = javaCU; // null indicates a binary; non-null a source Java file
    				specsEnter(speccu);
    			} else {
    				// No specs -- binary with no .jml file
    				recordEmptySpecs(csymbol);
    				if (org.jmlspecs.openjml.JmlOptions.instance(context).warningKeys.getOrDefault("missing-specs",false))
    					utils.warning("jml.message","[missing-specs] No specifications file found for binary " + csymbol);
    			}
    		} finally {
				if (utils.verbose()) utils.note("Completed entering specs for " + csymbol + (javaCU==null?" (binary)":(" (" + javaCU.sourcefile + ")" + " spec: " + speccu.sourcefile)));
//    			if (speccu != null) for (var d: speccu.defs) {
//    				if (d instanceof JmlClassDecl) { JmlClassDecl cd = (JmlClassDecl)d; System.out.println("    "  + cd.name + " " + cd.sym + " " + cd.type); }
//    			}
				nestingLevel--;
    		}
    	}
    }
    
    // FIXME - unify the recording of empty specs with default specs??
    public void recordEmptySpecs(ClassSymbol csymbol) {
    	JmlSpecs.TypeSpecs typespecs = new JmlSpecs.TypeSpecs(csymbol, csymbol.sourcefile, (JmlTree.JmlModifiers)JmlTree.Maker.instance(context).Modifiers(csymbol.flags(),List.<JCTree.JCAnnotation>nil()), null);
    	JmlSpecs.instance(context).putSpecs(csymbol,typespecs);
    }

    @Override
    public void unenter(JCCompilationUnit topLevel, JCTree tree) {
        new JmlUnenterScanner(topLevel.modle).scan(tree);
    }
    class JmlUnenterScanner extends UnenterScanner implements org.jmlspecs.openjml.visitors.IJmlVisitor {

        public JmlUnenterScanner(ModuleSymbol msym) {
        	super(msym);
        }

    }
    
    // FIXME - what about checking vs. binary
    public void checkVarMatch(/*@nullable*/ JmlVariableDecl javaMatch, VarSymbol match, JmlVariableDecl specVarDecl, ClassSymbol javaClassSymbol) {
    	if (javaMatch == null || javaMatch == specVarDecl) return;
    	checkAnnotations(javaMatch.mods, specVarDecl.mods, match);
        // Check that the modifiers are the same
      	VarSymbol javaSym = match;
      	long javaFlags = match.flags();
      	boolean isInterface = javaSym.owner.isInterface();
  		long specFlags = specVarDecl.mods.flags;
      	if (isInterface) {
      		if (isInterface && (specFlags&Flags.AccessFlags)== 0) specFlags |= Flags.PUBLIC;
      		long wasFinal = specFlags & Flags.FINAL;
      		if ((specVarDecl.mods.flags&Flags.AccessFlags) == 0) specVarDecl.mods.flags |= Flags.PUBLIC;
      		if (utils.isJML(specFlags)) {
      			if (wasFinal == 0) specVarDecl.mods.flags &= ~Flags.FINAL;
      			if (utils.hasMod(specVarDecl.mods, Modifiers.INSTANCE)) specVarDecl.mods.flags &= ~Flags.STATIC; 
      		}
      	}

      	// check for no initializer
      	if (specVarDecl.getInitializer() != null && specVarDecl != javaMatch && javaMatch != null &&
      			!utils.isJML(specVarDecl.mods) && !specVarDecl.sym.owner.isEnum()) {
      		utils.error(specVarDecl.getInitializer().pos(),"jml.no.initializer.in.specs",javaSym.enclClass().getQualifiedName()+"."+javaSym.name);
      	}

      	long diffs = (javaFlags ^ specFlags)&(isInterface? Flags.InterfaceVarFlags : Flags.VarFlags);
      	if (diffs != 0) {
      		utils.error(specVarDecl.sourcefile,specVarDecl,"jml.mismatched.field.modifiers", specVarDecl.name, javaClassSymbol+"."+javaSym.name,Flags.toString(diffs));
      	}
    	
    }
    
    /** If thre are specifications in a file separate from the .java file, then any annotations in the .java
     * file are ignored. This condition is checked and warned about here.
     */
    public void checkAnnotations(JCModifiers javaMods, JCModifiers specMods, Symbol owner) {
    	if (javaMods == specMods) return;
    	for (var a: javaMods.annotations) {
    		if (a instanceof JmlAnnotation) {
    			var aa = (JmlAnnotation)a;
    			if (aa.kind == null) continue;
    			if (!utils.hasMod(specMods, aa.kind)) {
    				String k = owner instanceof ClassSymbol? "class": owner instanceof MethodSymbol? "method":
    					owner instanceof VarSymbol? "var" : "";
    				utils.warning(aa.sourcefile, aa, "jml.java.annotation.superseded", k, owner, aa.kind.toString());
    				return;
    			}
    		}
    	}
    }
    
    /** Checks for consistency between the java and specification declarations.
     * This is only for reporting differences between the declarations. Any 
     * consistency checks within the specifications themselves are reported during attribution (JmlAttr).
     */
    public boolean checkClassMatch(JmlClassDecl javaDecl, JmlClassDecl specsDecl) {
    	if (javaDecl == null || javaDecl == specsDecl) return true;
    	int n = log.nerrors;
    	checkAnnotations(javaDecl.mods, specsDecl.mods, javaDecl.sym);
    	if (javaDecl.typarams.size() != specsDecl.typarams.size()) return false;
//    		System.out.println("TY MISMATCH");
//    		var p = specsDecl.typarams.size() == 0 ? specsDecl : specsDecl.typarams.head;
//    		String nm = specsDecl.typarams.size() == 0 ? specsDecl.name.toString()
//    				: (specsDecl.name + "<" + specsDecl.typarams.toString() + ">");
//    		utils.error(p, "jml.mismatched.type.arguments", nm, javaDecl.sym.type.toString());
//    	}
    	return n == log.nerrors;
    }

    
//  /** Checks that the modifiers and annotations in the .java and .jml declarations match appropriately,
//  * for both the method declaration and any parameter declarations;
//  * does not do any semantic checks of whether the modifiers or annotations are allowed.
//  */
    public void checkMethodMatch(/*@nullable*/ JmlMethodDecl javaMatch, MethodSymbol match, JmlMethodDecl specMethodDecl, ClassSymbol javaClassSymbol) {
    	if (javaMatch == null || javaMatch == specMethodDecl) return;
    	checkAnnotations(javaMatch.mods, specMethodDecl.mods, match);
    	JavaFileObject prev = log.currentSourceFile();
    	log.useSource(specMethodDecl.sourcefile); // All logged errors are with respect to positions in the jml file
    	try {
    		if (javaMatch != specMethodDecl) {
    			boolean isInterface = match.owner.isInterface();
    			// Check that modifiers are the same
    			long matchf = match.flags();
    			long specf = specMethodDecl.mods.flags;
    			matchf |= (specf & Flags.SYNCHRONIZED); // binary files do not seem to always have the synchronized modifier?  FIXME
    			long diffs = (matchf ^ specf)&Flags.MethodFlags;
    			if (diffs != 0) {
    				boolean isEnum = (javaClassSymbol.flags() & Flags.ENUM) != 0;
    				if ((Flags.NATIVE & matchf & ~specf)!= 0) diffs &= ~Flags.NATIVE;
    				if (isInterface) diffs &= ~Flags.PUBLIC & ~Flags.ABSTRACT;
    				if (isEnum && match.isConstructor()) { specMethodDecl.mods.flags |= (matchf & 7); diffs &= ~7; } // FIXME - should only do this if specs are default
    				if ((matchf & specf & Flags.ANONCONSTR)!= 0 && isEnum) { diffs &= ~2; specMethodDecl.mods.flags |= 2; } // enum constructors can have differences
    				if (diffs != 0 && !(match.isConstructor() && diffs == 3)) {
    					// FIXME - hide this case for now because of default constructors in binary files
    					utils.error(specMethodDecl.pos(),"jml.mismatched.method.modifiers", specMethodDecl.name, match.toString(), Flags.toString(diffs));
    				}
    			}
    		}

    		if (javaMatch != null) {
    			// Check that parameters have the same modifiers - FIXME - should check this in the symbol, not just in the Java
    			Iterator<JCVariableDecl> javaiter = javaMatch.params.iterator();
    			Iterator<JCVariableDecl> jmliter = specMethodDecl.params.iterator();
    			while (javaiter.hasNext() && jmliter.hasNext()) {
    				JmlVariableDecl javaparam = (JmlVariableDecl)javaiter.next();
    				JmlVariableDecl jmlparam = (JmlVariableDecl)jmliter.next();
    				javaparam.specsDecl = jmlparam;
    				jmlparam.sym = javaparam.sym;
    				long diffs = (javaparam.mods.flags ^ jmlparam.mods.flags);
    				if (diffs != 0) {
    					utils.errorAndAssociatedDeclaration(specMethodDecl.sourcefile, jmlparam.pos(),
    							javaMatch.sourcefile, javaparam.pos(),
    							"jml.mismatched.parameter.modifiers", 
    							jmlparam.name, 
    							javaClassSymbol.getQualifiedName()+"."+match.name,Flags.toString(diffs));
    				}
    			}
    			// FIXME - should check names of parameters, names of type parameters
    			if (javaiter.hasNext() || jmliter.hasNext()) {
    				// Just in case -- should never have made a match if the signatures are different
    				log.error("jml.internal", "Java and jml declarations have different numbers of arguments, even though they have been type matched");
    			}
    		}
//
//         // FIXME - we do need to exclude some anonymous classes,  but all of them?
//         if (!javaClassSymbol.isAnonymous()) checkSameAnnotations(match,specMethodDecl.mods,prev); // FIXME - is prev really the file object for Java
//         Iterator<JCVariableDecl> jmliter = specMethodDecl.params.iterator();
//         Iterator<Symbol.VarSymbol> javaiter = match.getParameters().iterator();
//         while (javaiter.hasNext() && jmliter.hasNext()) {
//             Symbol.VarSymbol javaparam = javaiter.next();
//             JmlVariableDecl jmlparam = (JmlVariableDecl)jmliter.next();
//             checkSameAnnotations(javaparam,jmlparam.mods,prev); // FIXME - is prev really the file object for Java
//         }
//
//
//
//         // Check that the return types are the same
//         if (specMethodDecl.restype != null) { // not a constructor
//             if (specMethodDecl.restype.type == null) Attr.instance(context).attribType(specMethodDecl.restype, match.enclClass());
////             if (match.name.toString().equals("defaultEmpty")) {
////                 log.noticeWriter.println(match.name);
////             }
//             Type javaReturnType = match.type.getReturnType();
//             Type specReturnType = specMethodDecl.restype.type;
//             if (!Types.instance(context).isSameType(javaReturnType,specReturnType)) {
//                 // FIXME - when the result type is parameterized in a static method, the java and spec declarations
//                 // end up with different types for the parameter.  Is this also true for the regular parameters?  
//                 // FIXME - avoud the probloem for now.
//                 if (!(specReturnType instanceof Type.TypeVar) && specReturnType.getTypeArguments().isEmpty()
//                         && (!(specReturnType instanceof Type.ArrayType) || !(((Type.ArrayType)specReturnType).elemtype instanceof Type.TypeVar)) )
//                     utils.error(specMethodDecl.restype.pos(),"jml.mismatched.return.type",
//                             match.enclClass().fullname + "." + match.toString(),
//                             specReturnType, javaReturnType);
//             }
//         }
//
    		
    		// Check that parameter names are the same (a JML requirement to avoid having to rename within specs)
    		if (javaMatch != null) {
//    			for (int i = 0; i<javaMatch.getParameters().size(); i++) {
//    				JCTree.JCVariableDecl javaparam = javaMatch.getParameters().get(i);
//    				JCTree.JCVariableDecl jmlparam = specMethodDecl.params.get(i);
//    				if (!javaparam.name.equals(jmlparam.name)) {
//    					utils.error(jmlparam.pos(),"jml.mismatched.param.names",i,
//    							match.enclClass().fullname + "." + match.toString(),
//    							javaparam.name, jmlparam.name);
//    				}
//    			}

//    		} else {
//    			// FIXME - do not really need this alternative since without a java Decl there is no body
//    			for (int i = 0; i<match.getParameters().size(); i++) {
//    				Symbol.VarSymbol javasym = match.getParameters().get(i);
//    				JCTree.JCVariableDecl jmlparam = specMethodDecl.params.get(i);
//    				if (!javasym.name.equals(jmlparam.name)) {
//    					utils.error(jmlparam.pos(),"jml.mismatched.param.names",i,
//    							match.enclClass().fullname + "." + match.toString(),
//    							javasym.name, jmlparam.name);
//    				}
//    			}
    		}
//
//         // Check that the specification method has no body if it is not a .java file
//         if (specMethodDecl.body != null && specMethodDecl.sourcefile.getKind() != Kind.SOURCE
//                 && !((JmlAttr)attr).isModel(specMethodDecl.mods)
//                 && !inModelTypeDeclaration
//                 && match.owner == javaClassSymbol   // FIXME - this is here to avoid errors on methods of anonymous classes within specifications within a .jml file - it might not be fully robust
//                 // FIXME - should test other similar locations - e.g. model classes, model methods, methods within local class declarations in model methods or methods of model classes
//                 && (specMethodDecl.mods.flags & (Flags.GENERATEDCONSTR|Flags.SYNTHETIC)) == 0) {
//             utils.error(specMethodDecl.body.pos(),"jml.no.body.allowed",match.enclClass().fullname + "." + match.toString());
//         }
//
//
//         // FIXME - from a previous comparison against source
////         // A specification method may not have a body.  However, the spec
////         // method declaration may also be identical to the java method (if the
////         // java file is in the specification sequence) - hence the second test.
////         // There is an unusual case in which a method declaration is duplicated
////         // in a .java file (same signature).  In that case, there is already
////         // an error message, but the duplicate will be matched against the
////         // first declaration at this point, though they are different
////         // delcarations (so the second test will be true).  Hence we include the
////         // 3rd test as well. [ TODO - perhaps we need just the third test and not the second.]
////         if (specMethodDecl.body != null && match != specMethodDecl
////                 && match.sourcefile != specMethodDecl.sourcefile
////                 && (specMethodDecl.mods.flags & (Flags.GENERATEDCONSTR|Flags.SYNTHETIC)) == 0) {
////             log.error(specMethodDecl.body.pos(),"jml.no.body.allowed",match.sym.enclClass().fullname + "." + match.sym.toString());
////         }
////         
////         // Check that the return types are the same
////         if (specMethodDecl.restype != null) { // not a constructor
////             if (specMethodDecl.restype.type == null) Attr.instance(context).attribType(specMethodDecl.restype, match.sym.enclClass());
//////             if (match.name.toString().equals("defaultEmpty")) {
//////                 log.noticeWriter.println(match.name);
//////             }
////             if (!Types.instance(context).isSameType(match.restype.type,specMethodDecl.restype.type)) {
////                 // FIXME - when the result type is parameterized in a static method, the java and spec declarations
////                 // end up with different types for the parameter.  Is this also true for the regular parameters?  
////                 // FIXME - avoud the probloem for now.
////                 if (!(specMethodDecl.restype.type.getTypeArguments().head instanceof Type.TypeVar))
////                 log.error(specMethodDecl.restype.pos(),"jml.mismatched.return.type",
////                         match.sym.enclClass().fullname + "." + match.sym.toString(),
////                         specMethodDecl.restype.type,match.restype.type);
////             }
////         }
//
    	} finally {
    		log.useSource(prev);
    	}
    	// FIXME - what about covariant return types ?????

    	// FIXME - check that JML annotations are ok
}

    
}
