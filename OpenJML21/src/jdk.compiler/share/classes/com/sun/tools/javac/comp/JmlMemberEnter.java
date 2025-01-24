/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.comp;

import static com.sun.tools.javac.code.Flags.ABSTRACT;
import static com.sun.tools.javac.code.Flags.DEFAULT;
import static com.sun.tools.javac.code.Flags.FINAL;
import static com.sun.tools.javac.code.Flags.HASINIT;
import static com.sun.tools.javac.code.Flags.INTERFACE;
import static com.sun.tools.javac.code.Flags.SIGNATURE_POLYMORPHIC;
import static com.sun.tools.javac.code.Flags.STATIC;
import static com.sun.tools.javac.code.Kinds.*;
import static com.sun.tools.javac.code.Kinds.Kind.*;

import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import javax.tools.JavaFileObject;
import javax.tools.JavaFileObject.Kind;

import org.jmlspecs.openjml.IJmlClauseKind.ModifierKind;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.MethodSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlAnnotation;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlModifiers;
import org.jmlspecs.openjml.JmlTree.JmlSource;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.ext.Modifiers;
import org.jmlspecs.openjml.ext.TypeInitializerClauseExtension;

import com.sun.tools.javac.code.Attribute.Compound;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Lint;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Scope.WriteableScope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.CompletionFailure;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotatedType;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCTypeParameter;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Assert;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.FatalError;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticFlag;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;

/**
 * This class extends MemberEnter to add some JML processing to the process of
 * entering the members of a class into the class definition.  The Enter 
 * process has already happened, creating a ClassSymbol and an Env for the class.
 * Now the contents of the class have to be filled in.
 * <P>
 * MemberEnter does the following when it 'completes' a class:
 * <UL>
 * <LI>makes sure imports have been read into the class environment
 * <LI>marks the class as not yet attributed
 * <LI>completes any enclosing classes
 * <LI>attributes any declared super types
 * <LI>attributes the annotation types
 * <LI>sets the annotations for later processing
 * <LI>attributes any type variables the class has
 * <LI>puts the class on the 'halfcompleted' list for finishing
 * </UL>
 * The finishing process, for each method and field of the class, defines a 
 * symbol, puts it into the AST, puts the symbol in the class's scope(Env).
 * Field Declarations: type is attributed, symbol defined, annotations put on 
 * annotateLater list.  Method Declarations: creates method symbol and type; in 
 * the process attributes type variables, result, parameter, and exception types.
 * Annotations are put on the annotateLater list.
 * <P>
 * JmlMemberEnter adds to the above.  When a class is completed, it enters any
 * ghost variables and model methods that were declared in the specifications;
 * it also parses up the specifications and fills in the TypeSpecs, MethodSpecs
 * and FieldSpecs corresponding to the various declarations.
 * <P>
 * Note that when specs are read for a binary class, we also need to do all the
 * matching up of members to Java elements and then create all of the same 
 * specification infrastructure.
 */
public class JmlMemberEnter extends MemberEnter  {// implements IJmlVisitor {

    final protected Context context;
    final protected Utils utils;
    final protected JmlEnter enter;
    final protected JmlResolve resolve;
    final protected Names names;
    final protected JmlTree.Maker jmlF;
    final protected Symtab syms;
    final protected JmlSpecs specs;
    final protected Log log;
    
    /** True when we are processing declarations that are in a specification file;
     * false when we are in a Java file (even if we are processing specifications)
     */
    boolean inSpecFile;
    
    public JmlMemberEnter(Context context) {
        super(context);
        this.context = context;
        this.utils = Utils.instance(context);
        this.resolve = JmlResolve.instance(context);
        this.enter = JmlEnter.instance(context);
        this.names = Names.instance(context);
        this.jmlF = JmlTree.Maker.instance(context);
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.log = Log.instance(context);
    }

    public static void preRegister(final Context context) {
        context.put(memberEnterKey, new Context.Factory<MemberEnter>() {
            public MemberEnter make(Context context) {
                return new JmlMemberEnter(context);
            }
        });
    }
    
    public static JmlMemberEnter instance(Context context) {
        return (JmlMemberEnter)MemberEnter.instance(context);
    }

    
    @Override
    // Presumes that the list of trees comes from a class, and that we need to match and enter any JML members
    // env corresponds to the class that owns the list of trees
    void memberEnter(List<? extends JCTree> trees, Env<AttrContext> env) {
    	if ( trees == null || env == null) throw new AssertionError("UNEXPECTED NULLS");
    	if ( env.enclClass.defs != trees ) {
    	    // The equality tested above is not true for a record class.
    	    // FIXME - not sure why of how that will be important
    	    if (env.enclClass.sym.isRecord()) {
//    	        System.out.println("TREES");
//    	        for (var t: trees) System.out.println(t);
//    	        System.out.println("ENV");
//    	        for (var d: env.enclClass.defs)System.out.println(d); 
    	    } else {
    	        throw new AssertionError("List of trees does not match the env" );
    	    }
    	}
    	
    	JmlClassDecl sourceDecl = (JmlClassDecl)env.enclClass;
        JmlClassDecl specsDecl = sourceDecl.specsDecl;
        if (specsDecl == null) throw new AssertionError("UNEXPECTED NULL SPECSDECL");
        
        TypeEnter.instance(context).new MembersPhase().enterThisAndSuper(sourceDecl.sym, env);
		
    	// It would be easier if we could match all the members, and then give a resolved list to super.memberEnter
    	// However, we need attributed methods in order to match them (fields can be done solely by name).
    	super.memberEnter(trees, env);
    	if (specsDecl == sourceDecl) {
    	    // Simple case: source and spec file are the same (both are the .java file)
    		// Any duplicates have already been reported
    		boolean hasInstanceInit = false;
    		boolean hasStaticInit = false;
        	for (var t: specsDecl.defs) {
        		if (t instanceof JmlVariableDecl vd) {
					specs.putSpecs(vd.sym, vd.fieldSpecs);
        		} else if (t instanceof JmlMethodDecl md) {
        			var msp = new JmlSpecs.MethodSpecs(md);
            		md.specsDecl = md;
            		msp.javaDecl = md;
            		msp.javaEnv = msp.specsEnv = methodEnv(md, env); // FIXME - review this -- needs formals, type parameters
					specs.putSpecs(md.sym, msp);
        		} else if (t instanceof JmlTree.JmlBlock block) {
        			if (block.isInitializerBlock && utils.isSpecFile(block.sourcefile) && !utils.isJML(env.enclClass.mods)) {
        				utils.error(block.source(), t, "jml.initializer.block.allowed");
        			}
    			} else if (t instanceof JmlTree.JmlTypeClauseInitializer init) {
    				if (init.keyword == TypeInitializerClauseExtension.staticinitializerID) {
    					if (hasStaticInit) {
    						utils.error(init, "jml.one.initializer.spec.only");
    					} else {
    						hasStaticInit = true;
    					}
    				}
    				if (init.keyword == TypeInitializerClauseExtension.initializerID) {
    					if (hasInstanceInit) {
    						utils.error(t, "jml.one.initializer.spec.only");
    					} else {
    						hasInstanceInit = true;
    					}
    				}
    			}
        	}
        	return;
    	}
    	//System.out.println("MATCHING MEMBERS "+ cd.name);
    	var revisedDefs = new ListBuffer<JCTree>();
		boolean hasStaticInit = false;
		boolean hasInstanceInit = false;
		var prev = log.useSource(specsDecl.source());
    	for (var t: specsDecl.defs) {
    		//System.out.println("MATCHING " + t);
    		boolean ok = true;
    		if (t instanceof JmlVariableDecl specVarDecl) {
    			var match = trees.stream().filter(tt -> (tt instanceof JmlVariableDecl vd && vd.name == specVarDecl.name)).findFirst();
    			if (utils.isJML(specVarDecl)) {
    				// Specification field is ghost or model
    				if (match.isEmpty()) {
    					// OK: A ghost/model field declaration with no matching name
    					super.memberEnter(specVarDecl, env);
    					specVarDecl.type = specVarDecl.sym.type;
    					if (specVarDecl.fieldSpecs == null) specVarDecl.fieldSpecs = new JmlSpecs.FieldSpecs(specVarDecl);
    					specs.putSpecs(specVarDecl.sym, specVarDecl.fieldSpecs);
    					sourceDecl.defs = sourceDecl.defs.append(specVarDecl);
    					//System.out.println("NEW JML FIELD " + cd.name + " " + specVarDecl.name + " " + specVarDecl.sym + " " + specVarDecl.type + " " + specVarDecl.vartype + " " + specVarDecl.vartype.type );
    				} else {
    				    // error: ghost or model specification field matches a Java field
						JmlVariableDecl javaVarDecl = (JmlVariableDecl)match.get();
						utils.errorAndAssociatedDeclaration(specVarDecl.sourcefile, specVarDecl, javaVarDecl.sourcefile, javaVarDecl, "jml.message", "This JML field declaration conflicts with an existing field with the same name: " + sourceDecl.sym.flatname + "." + specVarDecl.name);
						ok = false;
    				}
    			} else {
    				// Specification field is a Java declaration (in the .jml file)
    				if (match.isEmpty()) {
    				    // Error: but there is no match for it
    					utils.error(specVarDecl.sourcefile, specVarDecl, "jml.message", "There is no field to match this Java declaration in the specification file: " + sourceDecl.sym.flatname + "." + specVarDecl.name);
    				} else {
    				    // There is a matching declaration in the .java file
						JmlVariableDecl javaVarDecl = (JmlVariableDecl)match.get();
    					if (javaVarDecl.specsDecl == null) {
    				        boolean prevcu = JmlResolve.instance(context).setInJMLCU(specVarDecl.isInJMLCU());
                        	Type specType = (specVarDecl.vartype.type == null) ? attr.attribType(specVarDecl.vartype, env) : specVarDecl.vartype.type;
                        	JmlResolve.instance(context).setInJMLCU(prevcu);
                        	if (!types.isSameType(javaVarDecl.vartype.type, specType)) {
    							String msg = "Type of field " + sourceDecl.sym + "." + specVarDecl.name + " in specification differs from type in source/binary: " + specType + " vs. " + javaVarDecl.sym.type;
    							if (javaVarDecl != null) {
    								utils.errorAndAssociatedDeclaration(specVarDecl.sourcefile, specVarDecl.vartype, javaVarDecl.source(), javaVarDecl, 
    										"jml.message", msg, javaVarDecl.pos(), javaVarDecl.sourcefile);
    							} else {
    								utils.error(specVarDecl.vartype, "jml.message", msg);
    							}
    							ok = false;
                        	} else {
                        		javaVarDecl.specsDecl = specVarDecl;
        						specVarDecl.sym = javaVarDecl.sym;
        						specVarDecl.type = javaVarDecl.type;
        						specVarDecl.vartype.type = javaVarDecl.type;
        						specs.putSpecs(javaVarDecl.sym, specVarDecl.fieldSpecs);
            					//System.out.println("MATCHED JAVA FIELD " + cd.name + " " + vd.name);
                        	}
    					} else {
    						utils.errorAndAssociatedDeclaration(specVarDecl.sourcefile, specVarDecl, javaVarDecl.specsDecl.sourcefile, javaVarDecl.specsDecl, 
    								"jml.duplicate.var.match", sourceDecl.sym.flatname + "." + specVarDecl.name);
    						ok = false;
    					}
    				}
    			}
    		} else if (t instanceof JmlMethodDecl specMethodDecl) {
    			var matchSym = matchMethod(specMethodDecl, sourceDecl.sym, env, false);
    			var decl = matchSym == null ? null : sourceDecl.defs.stream().filter(tt->(tt instanceof JmlMethodDecl md && md.sym == matchSym)).findFirst().orElse(null);
    			JmlMethodDecl javaMethodDecl = (JmlMethodDecl)decl;
    			if (utils.isJML(specMethodDecl)) {
    				// A JML model method
    				if (matchSym == null) {
    					super.memberEnter(specMethodDecl, env);
    					specMethodDecl.type = specMethodDecl.sym.type;
    					var msp = new JmlSpecs.MethodSpecs(specMethodDecl);
    					msp.javaDecl = javaMethodDecl;
//    					msp.javaEnv = methodEnv(javaMethodDecl, env);
//    					msp.specsEnv = methodEnv(specMethodDecl, env); // FIXME - should use a specEnv here?
    					msp.javaEnv = msp.specsEnv = env;
//    					enter.classEnter(specMethodDecl.params, msp.specsEnv); // FIXME - also enter type parameters?
    					specs.putSpecs(specMethodDecl.sym, msp);
    					sourceDecl.defs = sourceDecl.defs.append(specMethodDecl);
    					//System.out.println("NEW JML METHOD " + cd.name + " " + specMethodDecl.name + " " + specMethodDecl.sym  );
    				} else {
						utils.errorAndAssociatedDeclaration(specMethodDecl.sourcefile, specMethodDecl, javaMethodDecl.sourcefile, javaMethodDecl, 
								"jml.message", "This JML method declaration conflicts with an existing method with the same signature: " + sourceDecl.sym + "." + specMethodDecl.sym);
						ok = false;
    				}
    			} else {
    				// A Java method declaration in the specification file
    				if (matchSym == null) {
    					utils.error(specMethodDecl.sourcefile, specMethodDecl, "jml.message", "There is no method to match this Java declaration in the specification file: " + sourceDecl.sym + "." + specMethodDecl.sym);
						ok = false;
    				} else {
    					if (javaMethodDecl.specsDecl == null) {
                        	// FIXME - fix matching of method types
    						Type specResultType = (specMethodDecl.restype == null) ? null : attr.attribType(specMethodDecl.restype, env); // FIXME - should use the env for the specCU
                        	if (specResultType != null && !types.isSameType(javaMethodDecl.restype.type, specResultType)) {
    							String msg = "The result type of method " + specMethodDecl.sym.owner + "." + specMethodDecl.sym 
    							                        + " in the specification differs from the type in the source/binary: " 
    							                        + specMethodDecl.restype.type + " vs. " + matchSym.getReturnType();
    							utils.errorAndAssociatedDeclaration(specMethodDecl.sourcefile, specMethodDecl.restype, javaMethodDecl.source(), javaMethodDecl, 
    									"jml.message", msg, javaMethodDecl.pos(), javaMethodDecl.sourcefile);
    							ok = false;
                        	} else {
                        		javaMethodDecl.specsDecl = specMethodDecl;
                        		specMethodDecl.sym = javaMethodDecl.sym;
                        		specMethodDecl.type = javaMethodDecl.type;
                        		var msp = new JmlSpecs.MethodSpecs(specMethodDecl);
                        		msp.javaDecl = javaMethodDecl;
                        		msp.javaEnv = msp.specsEnv = env;
        						specs.putSpecs(javaMethodDecl.sym, msp);
            					//System.out.println("MATCHED JAVA METHOD " + cd.name + " " + specMethodDecl.sym + " " + specMethodDecl.sym.hashCode() + " " + specMethodDecl.restype + " " + javaMethodDecl.sym + " " + javaMethodDecl.sym.hashCode());
                        	}
    					} else {
    						utils.errorAndAssociatedDeclaration(specMethodDecl.sourcefile, specMethodDecl, javaMethodDecl.specsDecl.sourcefile, javaMethodDecl.specsDecl, 
    								"jml.duplicate.method.match", specMethodDecl.sym, sourceDecl.sym);
    						ok = false;
    					}
    				}
    			}
    	        
    		} else if (t instanceof JmlTree.JmlBlock block) {
    			if (block.isInitializerBlock && block.sourcefile.getKind() != JavaFileObject.Kind.SOURCE && !utils.isJML(env.enclClass.mods)) {
    	        	utils.error(block.sourcefile, block, "jml.initializer.block.allowed");
    	        	ok = false;
    	        }
			} else if (t instanceof JmlTree.JmlTypeClauseInitializer init) {
				if (init.keyword == TypeInitializerClauseExtension.staticinitializerID) {
					if (hasStaticInit) {
						utils.error(specsDecl.source(), t, "jml.one.initializer.spec.only");
						ok = false;
					} else {
						hasStaticInit = true;
					}
				}
				if (init.keyword == TypeInitializerClauseExtension.initializerID) {
					if (hasInstanceInit) {
						utils.error(specsDecl.source(), t, "jml.one.initializer.spec.only");
						ok = false;
					} else {
						hasInstanceInit = true;
					}
				}
    		}
    		if (ok) revisedDefs.add(t);
    	}
    	log.useSource(prev);
    	specsDecl.defs = revisedDefs.toList();
    	
    	// Now check for any unmatched Java declarations
    	for (var t: trees) {
    		if (t instanceof JmlVariableDecl vd) {
    			if (vd.specsDecl == null) {
    				vd.specsDecl = vd;
    				// Relying on the fact that no JML declarations are included in the .java file
    				specs.putSpecs(vd.sym, vd.fieldSpecs = new JmlSpecs.FieldSpecs(vd));
    			}
    		} else if (t instanceof JmlMethodDecl md) {
    			if (md.specsDecl == null) {
    				// FIXME - does this stop the addition of default specs?
    				var msp = new JmlSpecs.MethodSpecs(md);
    				md.specsDecl = md;
    				msp.javaDecl = md;
            		msp.javaEnv = msp.specsEnv = methodEnv(md, env);
    				specs.putSpecs(md.sym, msp);
    			}
    		}
    	}
    	// FIXME - this is not correct here, but we need to adjust.call addRacmethods somewhere
//    	if (utils.rac && sourceDecl != null) addRacMethods(sourceDecl.sym, env);
    	// Expected properties:
    	//   The member list may still have duplicates; duplicates have different symbols but the same sym.type
    	//   vd.type and md.type are not set; vd.sym and md.sym are set, as are vd.sym.type and md.sym.type
    	//   d.specsDecl is set for each member; iot may be equal to d
    	//   if d.specsDecl is different than d then d.specsDecl.specsDecl is null
    	//   putSpecs has been called for each legitimate member
    }
    
    public boolean enterJML = true; // Set to false to just create the sym and type, but not enter or check duplicates
    
    /**  FIXME: still true, useful?:Returns true if there is a duplicate, whether or not it was warned about */
    protected boolean visitMethodDefHelper(JCMethodDecl tree, MethodSymbol m, WriteableScope enclScope, Env<AttrContext> localEnv) {
//        boolean was = ((JmlCheck)chk).noDuplicateWarn;
//        if (m.isConstructor() && (m.flags() & Utils.JMLBIT) != 0 && m.params().isEmpty()) {
//            ((JmlCheck)chk).noDuplicateWarn = true;
//        }
////        if (m.owner.isEnum() && m.toString().equals("valueOf(java.lang.String)")) {
////            ((JmlCheck)chk).noDuplicateWarn = true;
////        }  // FIXME
//        if (chk.checkUnique(tree.pos(), m, enclScope)) {
//            if (!noEntering) {
//                if (tree.body == null && m.owner.isInterface() && utils.isJML(m.flags())) {
//                    m.flags_field |= (Flags.ABSTRACT | Utils.JMLADDED);
//                    m.enclClass().flags_field |= Utils.JMLADDED;
//                }
//                enclScope.enter(m);
//            }
//            ((JmlCheck)chk).noDuplicateWarn = was;
//            return true;
//        } else {
//            if (!((JmlCheck)chk).noDuplicateWarn) tree.sym = null;  // FIXME - this needs some testing
//            ((JmlCheck)chk).noDuplicateWarn = was;
//            return false;
//        }
//    	var st = specs.status(m.owner);
//    	if (st != JmlSpecs.SpecsStatus.NOT_LOADED || !enterJML) {
//    		// The check above is to avoid calling putSpecs during the processing of source files
//    		// FIXME - it presumes that source files are completely processed before aspec files are queued
//    	var sp = new MethodSpecs((JmlMethodDecl)tree);
//    	sp.specsEnv = localEnv;
//    		specs.putSpecs(m, sp);
//    	}
    	JmlEnter.instance(context).methodEnv = localEnv;
    	if (!enterJML) return true; // FIXME - enterJML can be done away with, I think
    	boolean b = super.visitMethodDefHelper(tree, m, enclScope, localEnv);
    	if (JmlEnter.debugEnter && b) System.out.println("enter: entered method " + m + " " + org.jmlspecs.openjml.Utils.instance(context).isJML(m.flags()));
        return b;
    }
    

//    /** Finds a Java method declaration matching the given specsMethodDecl in the given class
//     * <br>returns false if the declaration is to be ignored because it is in error
//     * <br>if no match and specsVarDecl is not ghost or model, error message issued, null returned
//     * <br>if match is duplicate, error message issued, match returned
//     * <br>if non-duplicate match, and javaDecl defined, set javaDecl.specsDecl field
//     * <br>if non-duplicate match, set specs database
//     * <br>if non-duplicate match, set specsVarDecl.sym field
//     * */
//    protected boolean matchAndSetMethodSpecs(/*@nullable*/ JmlClassDecl javaDecl, ClassSymbol csym, JmlMethodDecl specsMethodDecl, Env<AttrContext> env, Map<Symbol,JCTree> matchesSoFar, boolean sameTree) {
//
//        // Find the counterpart to specsMethodDecl (from the .jml file) in the Java class declaration (javaDecl or csym)
//        // Note that if the class is binary, javaDecl will be null, but csym will not
//
//        MethodSymbol matchSym = false ? specsMethodDecl.sym : matchMethod(specsMethodDecl,csym,env,false);
//        if (matchSym != null && matchSym.owner != csym && !sameTree) {
//            utils.warning("jml.message", "Unexpected location (ASD): " + csym);
//            matchSym = specsMethodDecl.sym;
//        }
//        
//        // matchsym == null ==> no match or duplicate; otherwise matchSym is the matching symbol
//        
//        if (matchSym == null) {
//            
//            // DO we need to do any cross-linking? and in field specs?
////            combinedSpecs.cases.decl = specsMethodDecl;
////            specsMethodDecl.methodSpecsCombined = combinedSpecs;
//
//            JmlAnnotation a = ((JmlAttr)attr).findMod(specsMethodDecl.mods,Modifiers.GHOST);
//            if (a == null) a = ((JmlAttr)attr).findMod(specsMethodDecl.mods,Modifiers.MODEL);
//            boolean classIsModel = ((JmlAttr)attr).isModel(javaDecl.getModifiers()); // FIXME - should really be recursive
//            if (!utils.isJML(specsMethodDecl.mods)) {
//                // Method is not (directly) in a JML declaration. So it should not have ghost or model annotations
//                // We are going to discard this declaration because of the error, so we do extra checking
//                if (a != null) {
//                    utils.error(specsMethodDecl.sourcefile, a.pos(),"jml.ghost.model.on.java",specsMethodDecl.name);
//                }
//                // Non-matching java declaration - an error
//                if (!classIsModel) {
//                    utils.error(specsMethodDecl.sourcefile, specsMethodDecl.pos(),"jml.no.method.match",
//                            csym.flatName() + "." + specsMethodDecl.sym);
//                }
//                return false;
//            } else {
//                // Non-matching ghost or model declaration; this is OK - there is no symbol yet
//                // This should have a model or ghost declaration - that is checked in JmlAttr
//                return true;
//            }
//        }
//
//        // The matches map holds any previous matches found - all to specification declarations
//        JCTree prevMatch = matchesSoFar.get(matchSym);
//        if ((matchSym.flags() & Flags.GENERATEDCONSTR) != 0 && prevMatch instanceof JmlMethodDecl && utils.findMod(((JmlMethodDecl)prevMatch).mods, Modifiers.MODEL) == null)  prevMatch = null;
//        if (prevMatch != null) {
//            // DO extra checking since we are discarding this declaration because it is already matched
//            if (!utils.isJML(specsMethodDecl.mods)) {
//                JmlAnnotation a = ((JmlAttr)attr).findMod(specsMethodDecl.mods,Modifiers.GHOST);
//                if (a == null) a = ((JmlAttr)attr).findMod(specsMethodDecl.mods,Modifiers.MODEL);
//                if (a != null) {
//                    utils.error(specsMethodDecl.sourcefile, a.pos(),"jml.ghost.model.on.java",specsMethodDecl.name);
//                }
//            }
//            // Previous match - give error - duplicate already reported if the specsMethodDecl is JML
//            if (!utils.isJML(specsMethodDecl.mods) && !sameTree) {
//                utils.errorAndAssociatedDeclaration(specsMethodDecl.sourcefile, specsMethodDecl.pos, ((JmlMethodDecl)prevMatch).sourcefile, prevMatch.pos,"jml.duplicate.method.match",specsMethodDecl.sym.toString(), csym.flatName());
//            }
//            return false;
//        }
//
//        {
//            // New match - save it; also set the specs database
//            matchesSoFar.put(matchSym,  specsMethodDecl);
//            JmlSpecs.MethodSpecs mspecs = new JmlSpecs.MethodSpecs(specsMethodDecl);
//            specs.putSpecs(matchSym,mspecs);
//            specsMethodDecl.sym = matchSym;
//            specsMethodDecl.methodSpecsCombined = mspecs;
//        }
//
//        // If we have actual source, then find the source declaration
//        JmlMethodDecl javaMatch = null;
//        if (javaDecl != null) {
//            // TODO - is there a better way to find the declaration for a method symbol?
//            if (sameTree) {
//                javaMatch = specsMethodDecl;
//            } else {
//                for (JCTree t: javaDecl.defs) {
//                    if (t instanceof JmlMethodDecl && ((JmlMethodDecl)t).sym == matchSym) {
//                        javaMatch = (JmlMethodDecl)t;
//                        break;
//                    }
//                }
//            }
//
//            if (javaMatch == null) {
//                log.error("jml.internal", "Unexpected absent Java method declaration, without a matching symbol: " + matchSym);
//            } else if (javaMatch.specsDecl == null) {
//                // The specs file declaration corresponds to
//                // MethodSymbol matchSym and
//                // to a Java source method declaration javaMatch
//                // Cross link them and set the specs field for the parameters as well
//                javaMatch.specsDecl = specsMethodDecl;
//                javaMatch.methodSpecsCombined = specsMethodDecl.methodSpecsCombined;
//                javaMatch.methodSpecsCombined.cases.decl = javaMatch; // FIXME - is this needed?
//                
//            } else if (javaMatch != specsMethodDecl) {
//                javaMatch = null;
//                log.error("jml.internal", "Unexpected duplicate Java method declaration, without a matching symbol: " + matchSym);
//            }
//        }
//
//        { // Check the match only if it is not a duplicate
//            checkMethodMatch(javaMatch,matchSym,specsMethodDecl,csym);
//            addAnnotations(matchSym,env,specsMethodDecl.mods);
//        }
//
//
//        return true;
//    }
//
//    
   
//    public void addInitializerBlocks(ClassSymbol sym, Env<AttrContext> env) {
//        JmlClassDecl classDecl = (JmlClassDecl)env.tree;
//        
//        JCTree.JCBlock block = jmlF.Block(Flags.SYNTHETIC, List.<JCStatement>nil());
//        classDecl.defs = classDecl.defs.append(block);
//        classDecl.initializerBlock = block;
//    
//        block = jmlF.Block(Flags.STATIC|Flags.SYNTHETIC, List.<JCStatement>nil());
//        classDecl.defs = classDecl.defs.append(block);
//        classDecl.staticInitializerBlock = block;
//    
//    }

    public void addRacMethods(ClassSymbol sym, Env<AttrContext> env) {
        if (!utils.rac) return;
        // We can't add methods to a binary class, can we?
//        if (((JmlCompilationUnit)env.toplevel).mode == JmlCompilationUnit.SPEC_FOR_BINARY) return;
        
        if (sym.isAnnotationType()) return;
        if (sym.isAnonymous()) return;
        
        var newdefs = addInvariantInitiallyMethods(sym, env);
        
        JmlSpecs.TypeSpecs tsp = JmlSpecs.instance(context).getLoadedSpecs(sym);
        JCExpression vd = jmlF.Type(syms.voidType);
        JmlClassDecl jtree = (JmlClassDecl)env.tree;
//        JmlClassDecl specstree = jtree.toplevel.mode == JmlCompilationUnit.SPEC_FOR_BINARY ? jtree : jtree.specsDecl;
        JmlClassDecl specstree = jtree.specsDecl;
        long defflag = sym.isInterface() ? Flags.DEFAULT : 0L;
        JmlTree.JmlMethodDecl m = jmlF.MethodDef(
                jmlF.Modifiers(Flags.PUBLIC|Flags.SYNTHETIC|defflag),
                names.fromString("_JML$$$checkInvariant"),
                vd,
                List.<JCTypeParameter>nil(),
                null,
                List.<JCVariableDecl>nil(),
                List.<JCExpression>nil(),
                jmlF.Block(0,List.<JCStatement>nil()), 
                null);
        m.specsDecl = m;
        // Inner (non-static) classes may not have static members
        long staticFlag = Flags.STATIC;
        if (sym.getEnclosingElement() instanceof ClassSymbol && !sym.isStatic()) staticFlag = 0;
        JmlTree.JmlMethodDecl ms = jmlF.MethodDef(
                jmlF.Modifiers(Flags.PUBLIC|staticFlag|Flags.SYNTHETIC),
                names.fromString("_JML$$$checkStaticInvariant"),
                vd,
                List.<JCTypeParameter>nil(),
                null,
                List.<JCVariableDecl>nil(),
                List.<JCExpression>nil(),
                jmlF.Block(0,List.<JCStatement>nil()), 
                null);
        ms.specsDecl = ms;
        
        utils.setJML(m.mods);
        utils.setJML(ms.mods);
        specs.addModifier(Position.NOPOS, Modifiers.HELPER, (JmlModifiers)m.mods);
        specs.addModifier(Position.NOPOS, Modifiers.PURE, (JmlModifiers)m.mods);
        specs.addModifier(Position.NOPOS, Modifiers.MODEL, (JmlModifiers)m.mods);
        specs.addModifier(Position.NOPOS, Modifiers.HELPER, (JmlModifiers)ms.mods);
        specs.addModifier(Position.NOPOS, Modifiers.PURE, (JmlModifiers)ms.mods);
        specs.addModifier(Position.NOPOS, Modifiers.MODEL, (JmlModifiers)ms.mods);
        
        newdefs.add(m);
        newdefs.add(ms);
                
        // We can't use the annotations on the symbol because the annotations are not 
        // necessarily completed. We could force it, but in the interest of least disruption
        // of the OpenJDK processing, we just use the AST instead.
        JmlAttr attr = JmlAttr.instance(context);
        Map<Name,JmlVariableDecl> modelMethodNames = new HashMap<>();
        //Symbol modelSym = attr.modToAnnotationSymbol.get(Modifiers.MODEL);
        if (specstree != null) for (JCTree decl: specstree.defs) {  // FIXME - should specstree ever be null
            if (decl instanceof JmlMethodDecl md) {
                if (!utils.rac) continue;
                if (!md.isJML() || md.body != null) continue;
                boolean isModel = utils.hasModifier(md.mods,Modifiers.MODEL);
                if (!isModel) continue;
                if ((md.mods.flags & Flags.DEFAULT) != 0 || (md.mods.flags & Flags.ABSTRACT) == 0) {
                    JmlTreeUtils treeutils = JmlTreeUtils.instance(context);
                    JCExpression expr = treeutils.makeUtilsMethodCall(md.pos, "noModelMethodImplementation",
                            treeutils.makeStringLiteral(md.pos, md.name.toString()));
                    JCStatement stat = jmlF.Exec(expr);
                    JCStatement stat2 = jmlF.Return(treeutils.makeZeroEquivalentLit(decl,md.sym.getReturnType()));
                    md.body = jmlF.Block(0L, List.<JCStatement>of(stat,stat2));
                    md.body.flags = utils.setJML(md.body.flags);
                } 
                continue;
            }
            if (!(decl instanceof JmlVariableDecl vdecl)) continue;

            if (!utils.hasModifier(vdecl.mods, Modifiers.MODEL)) continue;
            if (vdecl.sym.type.toString().equals("\\datagroup")) continue; // FIXME - use a better way to test this
            VarSymbol vsym = vdecl.sym;
            
            JCExpression init = vdecl.init;
            if (init == null) init = JmlTreeUtils.instance(context).makeZeroEquivalentLit(vdecl,vdecl.sym.type);
            
            JCTree.JCReturn returnStatement = jmlF.Return(init);
            JCTree.JCThrow throwStatement = jmlF.Throw(jmlF.NewClass(null, List.<JCExpression>nil(), utils.nametree(decl.pos,-1,Strings.jmlSpecsPackage + ".NoModelFieldMethod",null), List.<JCExpression>nil(), null));
            boolean isAbstract = (vdecl.mods.flags & ABSTRACT) != 0;
            
            modelMethodNames.put(vsym.name,vdecl);
            JmlMethodDecl mr = makeModelFieldMethod(vdecl,tsp);
            boolean print = false;//vdecl.name.toString().equals("i");
            if (print) System.out.println("MM " + vdecl + " " + mr);
            newdefs.add(mr);
            if (vdecl.init == null) mr.mods.flags |= Utils.JMLADDED; // Marks this as needing a representation
            
            JCTree found = vdecl.init;
            for (JCTree ddecl: tsp.clauses) {
                if (!(ddecl instanceof JmlTypeClauseRepresents rep)) continue;
                if (((JCTree.JCIdent)rep.ident).name != vdecl.name) continue;
                if (utils.isJMLStatic(vdecl.sym) != utils.isJMLStatic(rep.modifiers,sym)) continue;
                if (rep.suchThat) {
                    continue;
                }
                if (found != null) {
                    utils.warning(rep.source,ddecl.pos,"jml.duplicate.represents");
                    // FIXME - the duplicate is at found.pos
                    continue;
                }
                returnStatement.expr = rep.expression;
                found = rep;
                mr.mods.flags &= ~Utils.JMLADDED; // Has a representation
            }
            if (mr.body == null) mr.body = jmlF.Block(0,null);
            mr.body.stats = List.<JCStatement>of(returnStatement);

            // NOTE: Various conditions on model fields and represents clauses are checked later during attribution
            //if (vdecl.name.toString().equals("theFloat")) System.out.println("theFloat rep = " + (found != null) + " " + isAbstract + " " + ((mr.mods.flags & Utils.JMLADDED) == 0));
            if (found == null) {
                String fieldName = vdecl.name.toString();
                String opt = JmlOption.value(context, JmlOption.RAC_MISSING_MODEL_FIELD_REP);
                if  (isAbstract) {
                    // no complaint if model field is abstract
                } else if ("skip".equals(opt)) {
                    utils.warning(vdecl.source(), vdecl, "jml.no.model.method.implementation", fieldName);
                } else if ("skip-quiet".equals(opt)) {
                } else if ("fail".equals(opt)) {
                    utils.error(vdecl.source(), vdecl, "jml.no.model.method.implementation", fieldName);
                } else if ("zero-quiet".equals(opt)) {
                } else if ("zero".equals(opt)) {
                    utils.warning(vdecl.source(), vdecl, "jml.no.model.method.default", fieldName);
                } else {
                    utils.error(vdecl.source(), vdecl, "jml.internal", "Missing case for a value of " + JmlOption.RAC_MISSING_MODEL_FIELD_REP + ": " + opt);
                }
            }

        }
        
        List<JCTree> nd = newdefs.toList();
        var saved = this.env;
        this.env= env;
        for (var mem: nd) visitMethodDef((JCMethodDecl)mem); // FIXME - what happends here?
        this.env = saved;
        jtree.defs = jtree.defs.appendList(nd); // FIXME - why are these added here instead of to the specstree
        // The call to set the specs must come after the the method symbol is set, so after memberEnter
//        for (JCTree md: nd) {  setDefaultCombinedMethodSpecs((JmlMethodDecl)md); }
    }
    
    public ListBuffer<JCTree> addInvariantInitiallyMethods(ClassSymbol sym, Env<AttrContext> env) {
        ListBuffer<JCTree> newdefs = new ListBuffer<>();
        if (!utils.rac) return newdefs;
        if (sym.isAnonymous()) return newdefs;
        if (sym.isInterface()) return newdefs;  // FIXME - deal with interfaces.  ALso, no methods added to annotations

        JmlSpecs.TypeSpecs tsp = JmlSpecs.instance(context).getLoadedSpecs(sym);
        JmlClassDecl jtree = (JmlClassDecl)env.tree;
        JmlClassDecl specstree = jtree.specsDecl;
        long defflag = sym.isInterface() ? Flags.DEFAULT : 0L;
        
        for (JmlTree.JmlTypeClause clause: tsp.clauses.toList()) {
            if (clause instanceof JmlTree.JmlTypeClauseExpr inv) {
                Name n;
                if (inv.clauseType == org.jmlspecs.openjml.ext.TypeExprClauseExtension.invariantClause) {
                    n = names.fromString(Strings.makeInvariantMethodName(inv));
                } else if (inv.clauseType == org.jmlspecs.openjml.ext.TypeExprClauseExtension.initiallyClause) {
                    n = names.fromString(Strings.makeInitiallyMethodName(inv));
                } else {
                    continue;
                }
                var ret = jmlF.at(inv).Return(inv.expression);
                JmlTree.JmlMethodDecl m = jmlF.MethodDef(
                        jmlF.Modifiers(inv.modifiers.flags|Flags.SYNTHETIC|(utils.isJMLStatic(inv.modifiers,sym)?0L:defflag)),
                        n,
                        jmlF.Type(syms.booleanType),
                        List.<JCTypeParameter>nil(),
                        null,
                        List.<JCVariableDecl>nil(),
                        List.<JCExpression>nil(),
                        jmlF.Block(0,List.<JCStatement>of(ret)), 
                        null);
                m.specsDecl = m;
                m.setSource(inv.source());
                inv.racmethod = m;

                utils.setJML(m.mods);
                specs.addModifier(Position.NOPOS, Modifiers.HELPER, (JmlModifiers)m.mods);
                specs.addModifier(Position.NOPOS, Modifiers.SPEC_PURE, (JmlModifiers)m.mods);
                specs.addModifier(Position.NOPOS, Modifiers.MODEL, (JmlModifiers)m.mods);
                newdefs.add(m);
           }
        }
        return newdefs;
    }
    
    public java.util.Map<Symbol, JmlMethodDecl> modelMethods = new java.util.HashMap<>();
            
    public JmlMethodDecl makeModelFieldMethod(JmlVariableDecl modelVarDecl, JmlSpecs.TypeSpecs tsp) {
        boolean nobody = (modelVarDecl.mods.flags & Flags.ABSTRACT) != 0;
        long defflag = modelVarDecl.sym.owner.isInterface() && !utils.isJMLStatic(modelVarDecl.sym) && !nobody ? Flags.DEFAULT : 0L;
        long flags = Flags.SYNTHETIC | defflag;
        flags |= (modelVarDecl.sym.flags() & (Flags.STATIC|Flags.AccessFlags));
        JCTree.JCReturn returnStatement = jmlF.Return(JmlTreeUtils.instance(context).makeZeroEquivalentLit(modelVarDecl,modelVarDecl.sym.type));
        Name name = names.fromString(Strings.modelFieldMethodPrefix + modelVarDecl.name);
        JmlTree.JmlMethodDecl mr = (JmlTree.JmlMethodDecl)jmlF.MethodDef(jmlF.Modifiers(flags),name, jmlF.Type(modelVarDecl.sym.type),
                List.<JCTypeParameter>nil(),List.<JCVariableDecl>nil(),List.<JCExpression>nil(), nobody ? null : jmlF.Block(0,List.<JCStatement>of(returnStatement)), null);
        mr.pos = modelVarDecl.pos;
        utils.setJML(mr.mods);
        JavaFileObject p = log.useSource(modelVarDecl.sourcefile);
        int endpos = modelVarDecl.getEndPosition(log.currentSource().getEndPosTable());
        log.useSource(p);
        specs.addModifier(modelVarDecl.pos, endpos, Modifiers.MODEL, mr.mods);
        specs.addModifier(modelVarDecl.pos, endpos, Modifiers.PURE, mr.mods);
        JmlSpecs.FieldSpecs fspecs = specs.getLoadedSpecs(modelVarDecl.sym);
        JmlTypeClauseDecl tcd = jmlF.JmlTypeClauseDecl(mr);
        tcd.pos = mr.pos;
        tcd.source = fspecs.source();
        tcd.modifiers = mr.mods;
        tsp.modelFieldMethods.append(tcd);
        modelMethods.put(modelVarDecl.sym, mr);
        return mr;
    }
        
    
    /** Find the method symbol in the class csym that corresponds to the method declared as specMethod;
     * if complain is true, then an error is reported if there is no match.
     * Does not presume that the parameter and return types and annotations have been attributed.
     * Presumes that specMethod.sym == null unless specMethod is part of the JmlClassDecl in the Java declaration.
     */
    public MethodSymbol matchMethod(JmlMethodDecl specMethod, ClassSymbol csym, Env<AttrContext> env, boolean complain) {

        JCMethodDecl tree = specMethod;

        MethodSymbol msym = tree.sym;
        MethodSymbol mtemp = msym;
        Env<AttrContext> localEnv = null;
//        Env<AttrContext> localEnvSpec = null;
        Type computedResultType = null;
//        Env<AttrContext> savedEnv = null;
        if (msym != null) {
            localEnv = methodEnv(tree, env); // FIXME - or getMethodEnv?
            computedResultType = msym.getReturnType();
        } else {
            // Copied from MemberEnter.visitMethodDef which can't be called directly
            Scope enclScope = enter.enterScope(env);
            mtemp = new MethodSymbol(0, tree.name, null, enclScope.owner);
            //m.flags_field = chk.checkFlags(tree.pos(), tree.mods.flags, m, tree);
            tree.sym = mtemp;
            localEnv = methodEnv(tree, env);

            var speccu = ((JmlCompilationUnit)env.toplevel).specsCompilationUnit;
            if (speccu != null) {
                env = speccu.topLevelEnv;
            }
            // Compute the method type
            boolean prevallow = resolve.addAllowJML(utils.isJML(tree.mods));
            boolean prevcu = resolve.setInJMLCU(specMethod.isInJMLCU());
            mtemp.type = signature(msym, tree.typarams, tree.params,
                               tree.restype, tree.recvparam, tree.thrown,
                               localEnv);
            resolve.setInJMLCU(prevcu);
            resolve.setAllowJML(prevallow);
            computedResultType = mtemp.type.getReturnType();
            
            // Set m.params
            ListBuffer<VarSymbol> params = new ListBuffer<VarSymbol>();
            JCVariableDecl lastParam = null;
            for (List<JCVariableDecl> l = tree.params; l.nonEmpty(); l = l.tail) {
                JCVariableDecl param = lastParam = l.head;
                assert param.sym != null;
                params.append(param.sym);
            }
            mtemp.params = params.toList();

            // mark the method varargs, if necessary
            if (lastParam != null && (lastParam.mods.flags & Flags.VARARGS) != 0)
                mtemp.flags_field |= Flags.VARARGS;

            localEnv.info.scope.leave();
//            if (chk.checkUnique(tree.pos(), m, enclScope)) {
//                enclScope.enter(m);
//            }
            annotate.annotateLater(tree.mods.annotations, localEnv, mtemp, tree.pos()); // FIXME - is this the right position
            if (tree.defaultValue != null)
                annotate.annotateDefaultValueLater(tree.defaultValue, localEnv, mtemp, tree);
        }

        MethodSymbol match = null;
        
        ListBuffer<Type> typaramTypes = new ListBuffer<Type>();
        for (List<JCTypeParameter> l = tree.typarams; l.nonEmpty(); l = l.tail) {
            typaramTypes.append(l.head.type);
        }

        ListBuffer<Type> paramTypes = new ListBuffer<Type>();
        JCVariableDecl lastParam = null;
        for (List<JCVariableDecl> l = tree.params; l.nonEmpty(); l = l.tail) {
            JCVariableDecl param = lastParam = l.head;
            JmlVariableDecl jparam = (JmlVariableDecl)param;
            if (jparam.originalType != null) paramTypes.append(jparam.originalType);
            else paramTypes.append(param.vartype.type);
        }

        // JmlResolve.findMethod is designed for matching a method call to some
        // declaration.  Here however, we are trying to match to method signatures.
        // We use this as a start, but then have to check that we have exact matches
        // for parameter types.  Also, we make the match using varargs=false - 
        // the parameter types themselves are already arrays if they were declared
        // as varargs parameters.

 //       Symbol lookupMethod(Env<AttrContext> env, DiagnosticPosition pos, Symbol location, MethodCheck methodCheck, LookupHelper lookupHelper) {

        Symbol s;
        JmlResolve jmlResolve = JmlResolve.instance(context);
        boolean prevSilentErrors = jmlResolve.silentErrors;
        jmlResolve.silentErrors = true;
//        jmlResolve.errorOccurred = false;
        try {
            s = jmlResolve.resolveMethod(tree.pos(), localEnv, tree.name, paramTypes.toList(),typaramTypes.toList());
        } finally {
            jmlResolve.silentErrors = prevSilentErrors;
//            if (jmlResolve.errorOccurred) s = null;
        }
//        Symbol s = JmlResolve.instance(context).findMethod(env,csym.asType(),
//                tree.name,paramTypes.toList(),typaramTypes.toList(),
//                /*allowBoxing*/false,/*varargs*/false,/*is an operator*/false);
        if (s instanceof MethodSymbol) {
            match = (MethodSymbol)s;
            // Require exact type match [findMethod returns best matches ]
            List<VarSymbol> params = match.getParameters();
            List<Type> paramT = paramTypes.toList();
            Types types = Types.instance(context);
            boolean hasTypeArgs = !typaramTypes.isEmpty();
            while (params.nonEmpty()) {
                if (!types.isSameType(params.head.type,paramT.head) &&
                        // FIXME - this is a hack to cover lots of cases
                        // We actually need to map type arguments in order to compare for eqauality with isSameType
                        (paramT.head.isPrimitive())) {
                    match = null;
                    break;
                }
                params = params.tail;
                paramT = paramT.tail;
            }
        }
        
        if (msym == null && match != null) {
            tree.sym = match;
// FIXME            if (localEnv != null) localEnv.info.scope.owner = match;
            for (List<JCVariableDecl> l = tree.params; l.nonEmpty(); l = l.tail) {
                JCVariableDecl param = l.head;
                param.sym.owner = match;
            }
        }

        if (match == null) {
            if (complain && (specMethod.mods.flags & Flags.GENERATEDCONSTR) == 0 && !inModelTypeDeclaration
                    && utils.findMod(specMethod.mods,Modifiers.MODEL) == null) {
                utils.error(specMethod.pos(),"jml.no.method.match",
                    csym.flatName() + "." + mtemp);
            }
        } else {
            // FIXME - do we need to check for model methods, and that they match?
//            boolean isModel = JmlAttr.instance(context).findMod(specMethod.mods,JmlToken.MODEL) != null;
//            boolean isMatchModel = match.attribute(((JmlAttr)attr).tokenToAnnotationSymbol.get(JmlToken.MODEL)) != null;
//            if (isModel == isMatchModel) {
            
                // Attributes the annotations and adds them to the given MethodSymbol, if they are not already present
 //               addAnnotations(match,env,specMethod.mods);  // Might repeat annotations, so we use the conditional call  // FIXME - we aren't using the conditional call
//            } else {
//                // We have a model and non-model method with matching signatures.  Declare them
//                // non-matching and wait for an error when the model method is entered.
//                match = null;
//            }
        }
        localEnv.info.scope.leave();
        return match;


    }

    /////////////////// DON'T USE BUT REVIEW FOR ACTIONS THAT HAVE BEEN FORGOTTEN /////////////////////////
//    public MethodSymbol matchMethod(JmlMethodDecl specMethod, ClassSymbol javaClassSymbol) {
//        // FIXME - set env properly for the following call?  Is it really attribBOunds?
//
//        Env<AttrContext> localenv = Enter.instance(context).getEnv(javaClassSymbol);
//        //Env<AttrContext> localenv = methodEnv(specMethod, env);
//        
//        //Scope enclScope = enter.enterScope(env);
////        MethodSymbol m = new MethodSymbol(0, specMethod.name, null, javaClassSymbol);
////        m.flags_field = specMethod.mods.flags;
////        specMethod.sym = m;
////        Env<AttrContext> localEnv = methodEnv(specMethod, env);
//        
//        Env<AttrContext> prevEnv = env;
//        env = localenv;
//        
//        Attr attr = Attr.instance(context);
//        
//        // Enter and attribute type parameters.
//        {   // From Enter.visitTypeParameter
//            for (JCTypeParameter tree: specMethod.typarams) {
//                TypeVar a = (tree.type != null)
//                ? (TypeVar)tree.type
//                        : new TypeVar(tree.name, env.info.scope.owner, syms.botType);
//                tree.type = a;
//                //if (Check.instance(context).checkUnique(tree.pos(), a.tsym, localenv.info.scope)) {
//                    env.info.scope.enter(a.tsym);
//                //}
//            }
//        }
//        attr.attribTypeVariables(specMethod.typarams, localenv);
//
//        ListBuffer<Type> tatypes = ListBuffer.<Type>lb();
//        for (JCTypeParameter tp: specMethod.typarams) {
//            tatypes.append(tp.type);
//        }
//        
//        // attribute value parameters.
//        int n = specMethod.getParameters().size();
//        ListBuffer<Type> ptypes = ListBuffer.<Type>lb();
//        for (List<JCVariableDecl> l = specMethod.params; l.nonEmpty(); l = l.tail) {
//            attr.attribType(l.head.vartype,javaClassSymbol);
//            ptypes.append(l.head.vartype.type);
//        }
//
//        // Attribute result type, if one is given.
//        if (specMethod.restype != null) attr.attribType(specMethod.restype, env);
//
//        // Attribute thrown exceptions.
//        ListBuffer<Type> thrownbuf = new ListBuffer<Type>();
//        for (List<JCExpression> l = specMethod.thrown; l.nonEmpty(); l = l.tail) {
//            Type exc = attr.attribType(l.head, env);
////            if (exc.tag != TYPEVAR)
//// FIXME               exc = chk.checkClassType(l.head.pos(), exc);
//            thrownbuf.append(exc);
//        }
//        
////        int n = specMethod.getParameters().size();
////        for (int i=0; i<n; i++) {
////            // FIXME - should the following use getEnv, getClassEnv? should it use the env of the javaClassSymbol or the spec decl?
////            Attr.instance(context).attribType(specMethod.getParameters().get(i).vartype, localenv);
////        }
//        boolean hasTypeParameters = specMethod.getTypeParameters().size() != 0;
//        MethodSymbol match = null;
//        try {
//            if (utils.jmldebug) {
//                log.noticeWriter.println("  CLASS " + javaClassSymbol.name + " SPECS HAVE METHOD " + specMethod.name);
//                if (specMethod.name.toString().equals("equals")) {
//                    log.noticeWriter.println("  CLASS " + javaClassSymbol.name + " SPECS HAVE METHOD " + specMethod.name);
//                }
//            }
//            JmlResolve rs = (JmlResolve)Resolve.instance(context);
//            try {
//                rs.noSuper = true;
//                Symbol sym = rs.findMatchingMethod(specMethod.pos(), env, specMethod.name, ptypes.toList(), tatypes.toList());
//                if (sym instanceof MethodSymbol) {
//                    match = (MethodSymbol)sym;
//                } else if (sym == null) {
//                    match = null;
//                } else {
//                    log.warning("jml.internal","Match found was not a method: " + sym + " " + sym.getClass());
//                    return  null;
//                }
//            } finally {
//                rs.noSuper = false;
//            }
//
////            Entry e = javaClassSymbol.members().lookup(specMethod.name);
////            loop: while (true) {
////                //if (e.sym != null && e.sym.kind != Kinds.MTH && e.sym.owner == javaClassSymbol) e = e.next();
////                //if (!(e.sym != null && e.sym.owner == javaClassSymbol)) break;
////                // Allow to match inherited methods
////                if (e.sym != null && e.sym.kind != Kinds.MTH) e = e.next();
////                if (e.sym == null) break;
////                MethodSymbol javaMethod = (Symbol.MethodSymbol)e.sym;
////                if (javaMethod.getParameters().size() != specMethod.getParameters().size()) { e = e.next(); continue; }
////                if (javaMethod.getTypeParameters().size() != specMethod.getTypeParameters().size()) { e = e.next(); continue; }
////                n = javaMethod.getParameters().size();
////                if (!hasTypeParameters) for (int i=0; i<n; i++) {  // FIXME - need to do actual matching for parameters with types
////                    if (!Types.instance(context).isSameType(javaMethod.getParameters().get(i).type,specMethod.getParameters().get(i).vartype.type)) { e = e.next(); continue loop; }
////                }
////                match = javaMethod;
////                break;
////            }
////            if (match == null && javaClassSymbol.isInterface()) {
////                // Check for a match against Object methods
////                e = Symtab.instance(context).objectType.tsym.members().lookup(specMethod.name);
////                loop: while (true) {
////                    //if (e.sym != null && e.sym.kind != Kinds.MTH && e.sym.owner == javaClassSymbol) e = e.next();
////                    //if (!(e.sym != null && e.sym.owner == javaClassSymbol)) break;
////                    // Allow to match inherited methods
////                    if (e.sym != null && e.sym.kind != Kinds.MTH) e = e.next();
////                    if (e.sym == null) break;
////                    MethodSymbol javaMethod = (Symbol.MethodSymbol)e.sym;
////                    if (javaMethod.getParameters().size() != specMethod.getParameters().size()) { e = e.next(); continue; }
////                    if (javaMethod.getTypeParameters().size() != specMethod.getTypeParameters().size()) { e = e.next(); continue; }
////                    // FIXME - need to check that type parameters have the same names and put them in scope so that we can test whether the
////                    // parameters have the same type; also check the bounds
////                    int n = javaMethod.getParameters().size();
////                    for (int i=0; i<n; i++) {
////                        if (!Types.instance(context).isSameType(javaMethod.getParameters().get(i).type,specMethod.getParameters().get(i).vartype.type)) { e = e.next(); continue loop; }
////                    }
////                    match = javaMethod;
////                    break;
////                }
////            }
//            
//            if (match == null) {
//
//                // Make a string of the signatures of the Java methods that we are comparing against
//                // and that do not match, to make a nice error message
//                StringBuilder sb = new StringBuilder();
//                sb.append("\n    Signatures found:");
//                int len = sb.length();
//                Entry e = javaClassSymbol.members().lookup(specMethod.name);
//                while (sb.length() < 500) {
//                    //if (e.sym != null && e.sym.kind != Kinds.MTH && e.sym.owner == javaClassSymbol) e = e.next();
//                    //if (!(e.sym != null && e.sym.owner == javaClassSymbol)) break;
//                    // Allow to match inherited methods
//                    if (e.sym != null && e.sym.kind != Kinds.MTH) e = e.next();
//                    if (e.sym == null) break;
//                    MethodSymbol javaMethod = (Symbol.MethodSymbol)e.sym;
//                    sb.append("\n\t\t\t").append(javaMethod.toString());
//                    e = e.next();
//                }
//                if (sb.length() >= 500) sb.append(" .....");
//                if (len == sb.length()) sb.append("   <none>");
//                log.error(specMethod.pos(),"jml.no.method.match",
//                        javaClassSymbol.fullname + "." + specMethod.name,
//                        sb.toString());
//            } else {
//                checkMethodMatch(match,specMethod,javaClassSymbol);
//                specMethod.sym = match;
//                Env<AttrContext> localEnv = methodEnv(specMethod, env);
//                // FIXME - are the annotations attributed?
//                //attr.attribAnnotationTypes(specMethod.mods.annotations,localenv);
//                addAnnotations(match,localEnv,specMethod.mods);
//                for (int i = 0; i<specMethod.typarams.size(); i++) {
//                    specMethod.typarams.get(i).type = match.getTypeParameters().get(i).type;
//                }
//            }
//        } catch (Exception e) {
//            log.noticeWriter.println("METHOD EXCEOPTION " + e);
//        }
//        env = prevEnv;
//        return match;
//    }


    
    /** Attributes the annotations and adds them to the given Symbol, if they are not already present */
    public void addAnnotations(Symbol sym, Env<AttrContext> env, JCTree.JCModifiers mods) {
        if (env == null) {
            log.error("jml.internal","Unexpected NULL ENV in JmlMemberEnter.addAnnotations" + sym);
        }
        annotate.annotateLater(mods.annotations, env, sym, mods.pos()); // FIXME - used to be annotateLaterConditional
    }

    
     
//    /** Set in visitiMethodDef so that all chlidren can know which method they are part of */
//    JmlMethodDecl currentMethod = null;
    
//    @Override 
//    public void visitMethodDef(JCMethodDecl tree) {
//        JmlMethodDecl prevMethod = currentMethod; // FIXME - why do we need to stack calls?
//        currentMethod = (JmlMethodDecl) tree;
////        boolean prevAllowJml = resolve.allowJML();
////        boolean isJMLMethod = utils.isJML(tree.mods);
//        try {
//            super.visitMethodDef(tree);
//
//            if (currentMethod.specsDecl == null) currentMethod.specsDecl = currentMethod; // FIXME - why is this not already set?
//            var ms = currentMethod.specsDecl.methodSpecsCombined = new JmlSpecs.MethodSpecs(currentMethod.specsDecl);
//            currentMethod.specsDecl.sym = tree.sym;
//            if (tree.sym != null) JmlSpecs.instance(context).putSpecs(tree.sym, ms);
//            ms.env = methodEnv(tree, env);
//        } finally {
////            if (isJMLMethod) resolve.setAllowJML(prevAllowJml);
//            currentMethod = prevMethod;
//        }
//        
//    }


//    // This is a duplicate of super.vistMethodDef -- with some stuff elided for handling specs of binarys
//    public void visitMethodDefBinary(JCMethodDecl tree) {
//        WriteableScope enclScope = enter.enterScope(env);
//        MethodSymbol m = new MethodSymbol(0, tree.name, null, enclScope.owner);
//        m.flags_field = chk.checkFlags(tree.pos(), tree.mods.flags, m, tree);
//        tree.sym = m;
//
//        //if this is a default method, add the DEFAULT flag to the enclosing interface
//        if ((tree.mods.flags & DEFAULT) != 0) {
//            m.enclClass().flags_field |= DEFAULT;
//        }
//
//        Env<AttrContext> localEnv = methodEnv(tree, env);
//
//        DiagnosticPosition prevLintPos = deferredLintHandler.setPos(tree.pos());
//        try {
//            // Compute the method type
//            m.type = signature(m, tree.typarams, tree.params,
//                               tree.restype, tree.recvparam,
//                               tree.thrown,
//                               localEnv);
//        } finally {
//            deferredLintHandler.setPos(prevLintPos);
//        }
//
//        if (types.isSignaturePolymorphic(m)) {
//            m.flags_field |= SIGNATURE_POLYMORPHIC;
//        }
//
//        // Set m.params
//        ListBuffer<VarSymbol> params = new ListBuffer<VarSymbol>();
//        JCVariableDecl lastParam = null;
//        for (List<JCVariableDecl> l = tree.params; l.nonEmpty(); l = l.tail) {
//            JCVariableDecl param = lastParam = l.head;
//            params.append(Assert.checkNonNull(param.sym));
//        }
//        m.params = params.toList();
//
//        // mark the method varargs, if necessary
//        if (lastParam != null && (lastParam.mods.flags & Flags.VARARGS) != 0)
//            m.flags_field |= Flags.VARARGS;
//
//        localEnv.info.scope.leave();
//        boolean prevCheck = ((JmlCheck)chk).noDuplicateWarn;
//        ((JmlCheck)chk).noDuplicateWarn = true;
//        if (chk.checkUnique(tree.pos(), m, enclScope)) {
//            // Not a duplicate - OK if the declaration is JML - if not, then ignore it
//            if (!utils.isJML(m.flags())) {
//                // This is an error, but it is reported later
//                //utils.error(((JmlMethodDecl)tree).sourcefile, tree, "jml.no.method.match", enclScope.owner.flatName() + "." + m);
//            } else {
//                enclScope.enter(m);
//            }
//        } else {
//            // A duplicate - OK if the declaration is not JML
//            if (utils.isJML(m.flags())) {
//                // FIXME
//            }
//        }
//        ((JmlCheck)chk).noDuplicateWarn = prevCheck;
//
//        // FIXME
////        annotateLater(tree.mods.annotations, localEnv, m, tree.pos());
////        // Visit the signature of the method. Note that
////        // TypeAnnotate doesn't descend into the body.
////        typeAnnotate(tree, localEnv, m, tree.pos());
////
////        if (tree.defaultValue != null)
////            annotateDefaultValueLater(tree.defaultValue, localEnv, m);
//    }

    

    
    
    /** True when we are processing declarations within a model type; false
     * otherwise.  This is to distinguish behaviors of Java declarations within
     * model types from those not in model types.
     */
    public boolean inModelTypeDeclaration = false;
    

    @Override
    public void visitMethodDef(JCMethodDecl tree) {
        boolean prev = resolve.setAllowJML(utils.isJML(tree.mods));
        boolean prevcu = resolve.setInJMLCU(((JmlSource)tree).isInJMLCU());
        try {
            super.visitMethodDef(tree);
        } finally {
            resolve.setAllowJML(prev);
            resolve.setInJMLCU(prevcu);
        }
    }

    @Override
    public void visitVarDef(JCVariableDecl tree) {
        var jtree = (JmlVariableDecl)tree;
        // FIXME - should we be using allowJML for both types?
        // We use add... rather than set...  in the statement below because these might be formals within a model method
        //System.out.println("VVD " + tree + " " + utils.isJML(tree.mods) + " " + jtree.jmltype);
        boolean prev = resolve.addAllowJML(utils.isJML(tree.mods) || jtree.jmltype);
        boolean prevcu = resolve.setInJMLCU(((JmlSource)tree).isInJMLCU());
        try {
            super.visitVarDef(tree);
            if (jtree.originalVartype != null) {
                jtree.originalType = attr.attribType(jtree.originalVartype, env); // FIXME - not correct if static
            }
            if (JmlEnter.debugEnter) System.out.println("enter: Entered field " + tree.sym.owner + " " + tree.name);
        } finally {
            resolve.setAllowJML(prev);
            resolve.setInJMLCU(prevcu);
    	}
    }

    @Override
    public boolean visitVarDefIsStatic(JCVariableDecl tree, Env<AttrContext> env) {
        boolean b = super.visitVarDefIsStatic(tree,env);
        if (!utils.isJML(tree.mods)) return b;
        if ((env.info.scope.owner.flags() & INTERFACE) != 0 &&
                utils.hasMod(tree.mods,Modifiers.INSTANCE)) return false;
        if ((tree.mods.flags & STATIC) != 0) return true;
        return b;
    }


    
    protected void visitFieldDefHelper(JCVariableDecl tree, VarSymbol v, WriteableScope enclScope, Env<AttrContext> env, List<JCAnnotation> annotations) {
       	if (tree.sym.owner instanceof ClassSymbol && tree != ((JmlVariableDecl)tree).specsDecl && null != ((JmlVariableDecl)tree).specsDecl) {
       		annotations = annotations.appendList(((JmlVariableDecl)tree).specsDecl.mods.annotations);
    	}
    	super.visitFieldDefHelper(tree, v, enclScope, env, annotations);
    	tree.type = v.type;
    	// Caution: tree.vartype is null if the declared type is 'var'
    }    
    
    

}
