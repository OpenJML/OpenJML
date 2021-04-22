/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.comp;

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
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlSpecs.MethodSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlAnnotation;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
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

    protected Context context;
    
    protected Utils utils;
    protected JmlEnter enter;
    protected JmlResolve resolve;
    protected Names names;
    protected JmlTree.Maker jmlF;
    protected Symtab syms;
    protected JmlSpecs specs;
    protected Name modelName;
    protected Log log;
    
    Name org_jmlspecs_lang;
    
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
        this.org_jmlspecs_lang = names.fromString(Strings.jmlSpecsPackage);
        this.jmlF = JmlTree.Maker.instance(context);
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.modelName = names.fromString(Modifiers.MODEL.keyword);
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

    
    /** Overridden simply to catch null first arguments.  The super class will crash
     * but the first argument may be null if we continue after parsing with
     * input files that contain parse errors.
     * @param trees
     * @param env
     */
    @Override
    void memberEnter(List<? extends JCTree> trees, Env<AttrContext> env) {
        if (trees != null) super.memberEnter(trees,env);
    }
    
    public boolean dojml = false; // FIXME - can get rid of this.
    
//    @Override
//    public void memberEnter(JCTree tree, Env<AttrContext> env) {
//        if (tree instanceof JmlTypeClause) return;
//        super.memberEnter(tree, env);
//        if (tree instanceof JmlCompilationUnit) {  // FIXME - this is also called with tree being a JmlClassDecl - then nothing is done; also part of the below is done already??
//            JmlCompilationUnit javacu = (JmlCompilationUnit)tree;
//            JmlCompilationUnit specscu = javacu.specsCompilationUnit;
//            // Normally, a Java CU has attached a specs CU, even if it is the same as itself.
//            // However, memberEnter is called when completing a class symbol to complete the package declaration
//            // in its top level environment; so for a model class in a specs compilation unit the toplevel is
//            // the specs compilation unit, which may have a null specscu field
//            
//            // FIXME - not sure this is what we want. We need the normal env (without model imports),
//            // and an env for the specs file (which may be either the .jml or .java file) that includes
//            // model imports org.jmlspecs.lang and model declarations.
//            if (specscu != null) {
//                Env<AttrContext> specenv = specscu.topLevelEnv;
//                if (specenv == null) specenv = env;
//                if (specenv != env) importAll(tree.pos, syms.enterPackage(null, names.java_lang), specenv);
//                super.memberEnter(specscu, specenv);
//                importAll(tree.pos, syms.enterPackage(null, names.fromString(Strings.jmlSpecsPackage)), specenv);
//            }
//        }
//    }

//    public void visitMethodDef(JCMethodDecl tree) {
//    	if (!enterJML && utils.isJML(tree.mods.flags)) return;
//    	super.visitMethodDef(tree);
//    }
//
//        
//    
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
    		specs.putSpecs(m, new MethodSpecs((JmlMethodDecl)tree), localEnv);
//    	}
    	if (!enterJML) return true;
    	boolean b = super.visitMethodDefHelper(tree, m, enclScope, localEnv);
        return b;
    }

//    // FIXME _ not currently used
//    public void checkForGhostModel(JCModifiers mods, JavaFileObject source, DiagnosticPosition pos) {
//        JmlAnnotation a = utils.findMod(mods, Modifiers.MODEL);
//        if (a == null) a = utils.findMod(mods, Modifiers.GHOST);
//        if (!utils.isJML(mods)) {
//            if (a != null) utils.error(source, pos, "jml.ghost.model.on.java");
//        } else {
//            if (a == null) utils.error(source, pos , "jml.missing.ghost.model");
//        }
//    }  
//    
//    protected List<JCTree> matchStuff(/*@nullable*/ JmlClassDecl jtree, ClassSymbol csym, Env<AttrContext> env, JmlClassDecl specsDecl) {
//        Map<Symbol,JCTree> matches = new HashMap<Symbol,JCTree>();
//        ListBuffer<JCTree> newlist = new ListBuffer<>();
//        ListBuffer<JCTree> toadd = new ListBuffer<>();
////        ListBuffer<JCTree> toremove = new ListBuffer<>();
////        Env<AttrContext> prevEnv = this.env;
////        this.env = env;
////
////        for (JCTree specsMemberDecl: specsDecl.defs) {
////            if (specsMemberDecl instanceof JmlVariableDecl) {
////                JmlVariableDecl specsVarDecl = (JmlVariableDecl)specsMemberDecl;
////                boolean ok = matchAndSetFieldSpecs(jtree, csym, specsVarDecl, matches, jtree == specsDecl);
////                if (ok) {
////                    newlist.add(specsVarDecl); // FIXME - are we actually using newlist? should we?
////                } else {
////                    toremove.add(specsVarDecl); 
////                }
////            } else if (specsMemberDecl instanceof JmlMethodDecl) {
////                JmlMethodDecl specsMethodDecl = (JmlMethodDecl)specsMemberDecl;
////                boolean ok = matchAndSetMethodSpecs(jtree, csym, specsMethodDecl, env, matches, jtree == specsDecl);
////                if (!ok) {
////                    toremove.add(specsMethodDecl); 
////                }
////            } else {
//////                newlist.add(specsMemberDecl);
////            }
////        }
////        // The following is somewhat inefficient, but it is only called when there are errors
////        for (JCTree t: toremove.toList()) {
////            jtree.defs = Utils.remove(jtree.defs, t);
////        }
////
////        this.env = prevEnv;
////        matches.clear();
//        return toadd.toList();
//    }


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
//    public void checkFinalTypeSpecs(JmlSpecs.TypeSpecs tspecs) {
//        for (JmlTypeClause tc: tspecs.clauses) {
//            if (tc instanceof JmlTypeClauseInitializer) {
//            }
//        }
//    }
    
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
        
        if (sym.isAnonymous()) return;
        if (sym.isInterface()) return;  // FIXME - deal with interfaces.  ALso, no methods added to annotations
        JmlSpecs.TypeSpecs tsp = JmlSpecs.instance(context).getLoadedSpecs(sym);
        JCExpression vd = jmlF.Type(syms.voidType);
        JmlClassDecl jtree = (JmlClassDecl)env.tree;
//        JmlClassDecl specstree = jtree.toplevel.mode == JmlCompilationUnit.SPEC_FOR_BINARY ? jtree : jtree.specsDecl;
        JmlClassDecl specstree = jtree.specsDecl;
        
        JmlTree.JmlMethodDecl m = jmlF.MethodDef(
                jmlF.Modifiers(Flags.PUBLIC|Flags.SYNTHETIC),
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
        JCAnnotation a = utils.modToAnnotationAST(Modifiers.HELPER,0,1);
        m.mods.annotations = m.mods.annotations.append(a);
        ms.mods.annotations = ms.mods.annotations.append(a);
        a = utils.modToAnnotationAST(Modifiers.PURE,0,1);
        m.mods.annotations = m.mods.annotations.append(a);
        ms.mods.annotations = ms.mods.annotations.append(a);
        a = utils.modToAnnotationAST(Modifiers.MODEL,0,1);
        m.mods.annotations = m.mods.annotations.append(a);
        ms.mods.annotations = ms.mods.annotations.append(a);
        
        ListBuffer<JCTree> newdefs = new ListBuffer<>();
        newdefs.add(m);
        newdefs.add(ms);
                
        // We can't use the annotations on the symbol because the annotations are not 
        // necessarily completed. We could force it, but in the interest of least disruption
        // of the OpenJDK processing, we just use the AST instead.
        JmlAttr attr = JmlAttr.instance(context);
        Map<Name,JmlVariableDecl> modelMethodNames = new HashMap<>();
        Symbol modelSym = attr.modToAnnotationSymbol.get(Modifiers.MODEL);
        if (specstree != null) for (JCTree decl: specstree.defs) {  // FIXME - should specstree ever be null
            if (decl instanceof JmlMethodDecl) {
                if (!utils.rac) continue;
                JmlMethodDecl md = (JmlMethodDecl)decl;
                if (!md.isJML() || md.body != null) continue;
                boolean isModel = utils.findMod(md.mods,Modifiers.MODEL)!= null;
                if (!isModel) continue;
                if ((md.mods.flags & Flags.DEFAULT) != 0 || (md.mods.flags & Flags.ABSTRACT) == 0) {
                    JmlTreeUtils treeutils = JmlTreeUtils.instance(context);
                    JCExpression expr = treeutils.makeUtilsMethodCall(md.pos, "noModelMethodImplementation",
                            treeutils.makeStringLiteral(md.pos, md.name.toString()));
                    JCStatement stat = jmlF.Exec(expr);
                    JCStatement stat2 = jmlF.Return(treeutils.makeZeroEquivalentLit(decl.pos,md.sym.getReturnType()));
                    md.body = jmlF.Block(0L, List.<JCStatement>of(stat,stat2));
                } 
                continue;
            }
            if (!(decl instanceof JmlVariableDecl)) continue;
            JmlVariableDecl vdecl = (JmlVariableDecl)decl;
            JCAnnotation annotation = utils.findMod(vdecl.mods, modelSym);
            if (annotation == null) continue;
            VarSymbol vsym = vdecl.sym;
            
            JCTree.JCReturn returnStatement = jmlF.Return(JmlTreeUtils.instance(context).makeZeroEquivalentLit(vdecl.pos,vdecl.sym.type));
            JCTree.JCThrow throwStatement = jmlF.Throw(jmlF.NewClass(null, List.<JCExpression>nil(), utils.nametree(decl.pos,-1,Strings.jmlSpecsPackage + ".NoModelFieldMethod",null), List.<JCExpression>nil(), null));
            
            modelMethodNames.put(vsym.name,vdecl);
            JmlMethodDecl mr = makeModelFieldMethod(vdecl,tsp);
            
            newdefs.add(mr);
            
            JmlTypeClauseRepresents found = null;
            for (JCTree ddecl: tsp.clauses) {
                if (!(ddecl instanceof JmlTypeClauseRepresents)) continue;
                JmlTypeClauseRepresents rep = (JmlTypeClauseRepresents)ddecl;
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
                mr.body.stats = List.<JCStatement>of(returnStatement);
                mr.mods.flags &= ~Utils.JMLADDED;
                found = rep;
            }
        }

        List<JCTree> nd = newdefs.toList();
        memberEnter(nd,env);
        jtree.defs = jtree.defs.appendList(nd);
        // The call to set the specs must come after the the method symbol is set, so after memberEnter
//        for (JCTree md: nd) {  setDefaultCombinedMethodSpecs((JmlMethodDecl)md); }


    }
            
    public JmlMethodDecl makeModelFieldMethod(JmlVariableDecl modelVarDecl, JmlSpecs.TypeSpecs tsp) {
        long flags = Flags.SYNTHETIC;
        flags |= (modelVarDecl.sym.flags() & (Flags.STATIC|Flags.AccessFlags));
        JCTree.JCReturn returnStatement = jmlF.Return(JmlTreeUtils.instance(context).makeZeroEquivalentLit(modelVarDecl.pos,modelVarDecl.sym.type));
        Name name = names.fromString(Strings.modelFieldMethodPrefix + modelVarDecl.name);
        JmlTree.JmlMethodDecl mr = (JmlTree.JmlMethodDecl)jmlF.MethodDef(jmlF.Modifiers(flags),name, jmlF.Type(modelVarDecl.sym.type),
                List.<JCTypeParameter>nil(),List.<JCVariableDecl>nil(),List.<JCExpression>nil(), jmlF.Block(0,List.<JCStatement>of(returnStatement)), null);
        mr.mods.flags |= Utils.JMLADDED;   // FIXME - why?
        mr.pos = modelVarDecl.pos;
        utils.setJML(mr.mods);
        JavaFileObject p = log.useSource(modelVarDecl.sourcefile);
        int endpos = modelVarDecl.getEndPosition(log.currentSource().getEndPosTable());
        log.useSource(p);
        mr.mods.annotations = List.<JCAnnotation>of(utils.modToAnnotationAST(Modifiers.MODEL,modelVarDecl.pos,endpos),
                                                    utils.modToAnnotationAST(Modifiers.PURE,modelVarDecl.pos,endpos)
                );
        JmlSpecs.FieldSpecs fspecs = specs.getSpecs(modelVarDecl.sym);
        JmlTypeClauseDecl tcd = jmlF.JmlTypeClauseDecl(mr);
        tcd.pos = mr.pos;
        tcd.source = fspecs.source();
        tcd.modifiers = mr.mods;
        tsp.modelFieldMethods.append(tcd);
        return mr;
    }
    
//    /** For synthetic methods or methods that do not have occasion to declare
//     * specs in a specification file, this sets the combined specs to be those
//     * that are associated with the method declaration itself.
//     * @param mdecl
//     */
//    protected void setDefaultCombinedMethodSpecs(JmlMethodDecl mdecl) {
//        mdecl.methodSpecsCombined = new JmlSpecs.MethodSpecs(mdecl);
//        specs.putSpecs(mdecl.sym,mdecl.methodSpecsCombined);
//    }

//    /** Checks that the jml annotations match Java annotations for annotations not in org.jmlspecs.annotation
//     * and are a superset of the Java annotations for annotations in org.jmlspecs.annotation) */
//    // MUST HAVE log.useSource set to specs file!
//    protected void checkSameAnnotations(Symbol sym, JCModifiers specsmods, JavaFileObject javaSource) {
//        // FIXME - check for null in annotations?
//        if (sym.isAnonymous()) return;
//        boolean saved1 = JmlPretty.useFullAnnotationTypeName, saved2 = JmlPretty.useJmlModifier;
//        JmlPretty.useFullAnnotationTypeName = JmlPretty.useJmlModifier = false;
//        PackageSymbol p = ((JmlAttr)attr).annotationPackageSymbol;
//        for (Compound a  : sym.getAnnotationMirrors()) {
//            if (a.type.tsym.owner.equals(p)) {
//                if (utils.findMod(specsmods,a.type.tsym) == null) {
//                    JavaFileObject prev = log.useSource(javaSource);
//                    log.error(specsmods.pos,"jml.java.annotation.superseded",a);
//                    log.useSource(prev);
//                }
//            } else {
//                if (utils.findMod(specsmods,a.type.tsym) == null && !a.toString().startsWith("@sun")) {
//                    log.error(specsmods.pos,"jml.missing.annotation",a);
//                }
//            }
//        }
//        JmlPretty.useFullAnnotationTypeName = saved1; JmlPretty.useJmlModifier = saved2;
//    }
//
//    /** Checks that the jml annotations are a superset of the Java annotations (for annotations in org.jmlspecs.annotation) */
//    // MUST HAVE log.useSource set to specs file!
//    protected void checkSameAnnotations(JCModifiers javaMods, JCModifiers specsmods, JavaFileObject javaSource) { // FIXME - don't need last argument
//        PackageSymbol p = ((JmlAttr)attr).annotationPackageSymbol;
//        boolean saved1 = JmlPretty.useFullAnnotationTypeName, saved2 = JmlPretty.useJmlModifier;
//        JmlPretty.useFullAnnotationTypeName = JmlPretty.useJmlModifier = false;
//        for (JCAnnotation a: javaMods.getAnnotations()) {
//            if (a.type.tsym.owner.equals(p)) {
//                if (utils.findMod(specsmods,a.type.tsym) == null) {
//                    JavaFileObject prev = log.useSource(((JmlTree.JmlAnnotation)a).sourcefile);
//                    log.error(specsmods.pos,"jml.java.annotation.superseded",a);
//                    log.useSource(prev);
//                }
//            } else {
//                if (utils.findMod(specsmods,a.type.tsym) == null && !a.toString().startsWith("@sun")) {
//                    log.error(specsmods.pos,"jml.missing.annotation",a);
//                }
//            }
//        }
//        JmlPretty.useFullAnnotationTypeName = saved1; JmlPretty.useJmlModifier = saved2;
//    }
//
//    public void checkFieldMatch(JmlVariableDecl javaField, VarSymbol javaSym, JmlVariableDecl specField) {
//        if (javaField == specField) return;
//        // Presume that we can't get here unless the names are the same
//        JavaFileObject prev = log.currentSourceFile();
//        log.useSource(specField.sourcefile);
//
//        // Check that the modifiers are the same
//        long javaFlags = javaSym.flags();
//        long specFlags = specField.mods.flags;
//        boolean isInterface = (javaFlags & Flags.INTERFACE) != 0;
//        long diffs = (javaFlags ^ specFlags)&(isInterface? Flags.InterfaceVarFlags : Flags.VarFlags);
//        if (diffs != 0) {
//            utils.error(specField.pos(),"jml.mismatched.field.modifiers", specField.name, javaSym.enclClass().getQualifiedName()+"."+javaSym.name,Flags.toString(diffs));  // FIXME - test this
//        }
//
//        // check for no initializer
//        if (specField.getInitializer() != null && specField != javaField &&
//                !utils.isJML(specField.mods) && !specField.sym.owner.isEnum()) {
//            utils.error(specField.getInitializer().pos(),"jml.no.initializer.in.specs",javaSym.enclClass().getQualifiedName()+"."+javaSym.name);
//        }
//        
//        // Match in the types is checked in JmlAttr.checkVarMods
//
//// FIXME - attribAnnotations, compare annotations
//        //  FIXME _ this needs to be implements
//        // FIXME - what if an annotation is declared within the class?
//        //            attr.attribAnnotationTypes(javaField.mods.annotations, env);
//        //            checkSameAnnotations(javaField.mods,specField.mods);
//
//        log.useSource(prev);
//    }
    
    
    
//    /** Find the method symbol in the class csym that corresponds to the method declared as specMethod;
//     * if complain is true, then an error is reported if there is no match.
//     * Does not presume that the parameter and return types and annotations have been attributed.
//     * Presumes that specMethod.sym == null unless specMethod is part of the JmlClassDecl in the Java declaration.
//     */
//    public MethodSymbol matchMethod(JmlMethodDecl specMethod, ClassSymbol csym, Env<AttrContext> env, boolean complain) {
//
//        JCMethodDecl tree = specMethod;
//
//        MethodSymbol msym = tree.sym;
//        MethodSymbol mtemp = msym;
//        Type computedResultType = null;
//        Env<AttrContext> localEnv = null;
//        if (msym != null) {
//            localEnv = methodEnv(tree, env);
//            computedResultType = msym.getReturnType();
//        } else {
//            // Copied from MemberEnter.visitMethodDef which can't be called directly
//            Scope enclScope = enter.enterScope(env);
//            mtemp = new MethodSymbol(0, tree.name, null, enclScope.owner);
//            //m.flags_field = chk.checkFlags(tree.pos(), tree.mods.flags, m, tree);
//            tree.sym = mtemp;
//            localEnv = methodEnv(tree, env);
//
//            // Compute the method type
//            mtemp.type = signature(msym, tree.typarams, tree.params,
//                               tree.restype, tree.recvparam, tree.thrown,
//                               localEnv);
//            computedResultType = mtemp.type.getReturnType();
//            
//            // Set m.params
//            ListBuffer<VarSymbol> params = new ListBuffer<VarSymbol>();
//            JCVariableDecl lastParam = null;
//            for (List<JCVariableDecl> l = tree.params; l.nonEmpty(); l = l.tail) {
//                JCVariableDecl param = lastParam = l.head;
//                assert param.sym != null;
//                params.append(param.sym);
//            }
//            mtemp.params = params.toList();
//
//            // mark the method varargs, if necessary
//            if (lastParam != null && (lastParam.mods.flags & Flags.VARARGS) != 0)
//                mtemp.flags_field |= Flags.VARARGS;
//
//            localEnv.info.scope.leave();
////            if (chk.checkUnique(tree.pos(), m, enclScope)) {
////                enclScope.enter(m);
////            }
//            annotate.annotateLater(tree.mods.annotations, localEnv, mtemp, tree.pos()); // FIXME - is this the right position
//            if (tree.defaultValue != null)
//                annotate.annotateDefaultValueLater(tree.defaultValue, localEnv, mtemp, tree);
//        }
//
//        MethodSymbol match = null;
//        
//        ListBuffer<Type> typaramTypes = new ListBuffer<Type>();
//        for (List<JCTypeParameter> l = tree.typarams; l.nonEmpty(); l = l.tail) {
//            typaramTypes.append(l.head.type);
//        }
//
//        ListBuffer<Type> paramTypes = new ListBuffer<Type>();
//        JCVariableDecl lastParam = null;
//        for (List<JCVariableDecl> l = tree.params; l.nonEmpty(); l = l.tail) {
//            JCVariableDecl param = lastParam = l.head;
//            paramTypes.append(param.vartype.type);
//        }
//
//        // JmlResolve.findMethod is designed for matching a method call to some
//        // declaration.  Here however, we are trying to match to method signatures.
//        // We use this as a start, but then have to check that we have exact matches
//        // for parameter types.  Also, we make the match using varargs=false - 
//        // the parameter types themselves are already arrays if they were declared
//        // as varargs parameters.
//
// //       Symbol lookupMethod(Env<AttrContext> env, DiagnosticPosition pos, Symbol location, MethodCheck methodCheck, LookupHelper lookupHelper) {
//
//        Symbol s;
//        JmlResolve jmlResolve = JmlResolve.instance(context);
//        boolean prevSilentErrors = jmlResolve.silentErrors;
//        jmlResolve.silentErrors = true;
////        jmlResolve.errorOccurred = false;
//        try {
//            s = jmlResolve.resolveMethod(tree.pos(), localEnv, tree.name, paramTypes.toList(),typaramTypes.toList());
//        } finally {
//            jmlResolve.silentErrors = prevSilentErrors;
////            if (jmlResolve.errorOccurred) s = null;
//        }
////        Symbol s = JmlResolve.instance(context).findMethod(env,csym.asType(),
////                tree.name,paramTypes.toList(),typaramTypes.toList(),
////                /*allowBoxing*/false,/*varargs*/false,/*is an operator*/false);
//        if (s instanceof MethodSymbol) {
//            match = (MethodSymbol)s;
//            // Require exact type match [findMethod returns best matches ]
//            List<VarSymbol> params = match.getParameters();
//            List<Type> paramT = paramTypes.toList();
//            Types types = Types.instance(context);
//            boolean hasTypeArgs = !typaramTypes.isEmpty();
//            while (params.nonEmpty()) {
//                if (!types.isSameType(params.head.type,paramT.head) &&
//                        // FIXME - this is a hack to cover lots of cases
//                        // We actually need to map type arguments in order to compare for eqauality with isSameType
//                        (paramT.head.isPrimitive())) {
//                    match = null;
//                    break;
//                }
//                params = params.tail;
//                paramT = paramT.tail;
//            }
//        }
//        
//        if (msym == null && match != null) {
//            tree.sym = match;
//// FIXME            if (localEnv != null) localEnv.info.scope.owner = match;
//            for (List<JCVariableDecl> l = tree.params; l.nonEmpty(); l = l.tail) {
//                JCVariableDecl param = l.head;
//                param.sym.owner = match;
//            }
//        }
//
//        if (match == null) {
//            if (complain && (specMethod.mods.flags & Flags.GENERATEDCONSTR) == 0 && !inModelTypeDeclaration
//                    && utils.findMod(specMethod.mods,Modifiers.MODEL) == null) {
//                utils.error(specMethod.pos(),"jml.no.method.match",
//                    csym.flatName() + "." + mtemp);
//            }
//        } else {
//            // FIXME - do we need to check for model methods, and that they match?
////            boolean isModel = JmlAttr.instance(context).findMod(specMethod.mods,JmlToken.MODEL) != null;
////            boolean isMatchModel = match.attribute(((JmlAttr)attr).tokenToAnnotationSymbol.get(JmlToken.MODEL)) != null;
////            if (isModel == isMatchModel) {
//            
//                // Attributes the annotations and adds them to the given MethodSymbol, if they are not already present
// //               addAnnotations(match,env,specMethod.mods);  // Might repeat annotations, so we use the conditional call  // FIXME - we aren't using the conditional call
////            } else {
////                // We have a model and non-model method with matching signatures.  Declare them
////                // non-matching and wait for an error when the model method is entered.
////                match = null;
////            }
//        }
//        localEnv.info.scope.leave();
//        return match;
//
//
//    }

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

    
//    VarSymbol findVarMatch(ClassSymbol csym, Name name) {
//        var e = csym.members().getSymbolsByName(name);  // FIXME - can have variables and methods with the same name
//        for (Symbol sy: e) {
//        	if (sy instanceof VarSymbol) return (VarSymbol)sy;
//        }
//        return null;
//    }
    
    
     
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
    
    private boolean isInJml = false;
    public boolean setInJml(boolean inJml) {
        boolean b = isInJml;
        isInJml = inJml;
        return b;
    }

    @Override
    public void visitMethodDef(JCMethodDecl tree) {
    	boolean prev = JmlResolve.instance(context).setAllowJML(utils.isJML(tree.mods));
    	try {
    		super.visitMethodDef(tree);
    	} finally {
    		JmlResolve.instance(context).setAllowJML(prev);
    	}
    }

    @Override
    public void visitVarDef(JCVariableDecl tree) {
//    	JCAnnotatedType atype = null;
//    	if (tree.vartype instanceof JCAnnotatedType) atype = (JCAnnotatedType)tree.vartype;
//    	if (atype != null) {
//    		if (specs.findAnnotation(atype.annotations, Modifiers.NON_NULL) != null) return;
//    		if (specs.findAnnotation(atype.annotations, Modifiers.NULLABLE) != null) return;
//    	}
//    	var nn = specs.defaultNullity(env.enclClass.sym);
//    	JCAnnotation ann = utils.modToAnnotationAST(nn, tree.pos, tree.pos); // FIXME - better position
//    	if (atype != null) {
//    		atype.annotations = atype.annotations.append(ann);
//    	} else {
//    		tree.vartype = jmlF.at(tree).AnnotatedType(List.<JCAnnotation>of(ann), tree.vartype);
//    	}
    	boolean prev = JmlResolve.instance(context).setAllowJML(utils.isJML(tree.mods));
    	try {
    		super.visitVarDef(tree);
    	} finally {
    		JmlResolve.instance(context).setAllowJML(prev);
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


//    @Override
//    public void visitVarDef(JCVariableDecl tree) {
//        long flags = tree.mods.flags;
//        boolean wasFinal = (flags&Flags.FINAL) != 0;
//        boolean wasStatic = (flags&Flags.STATIC) != 0;
//        if ((env.enclClass.mods.flags & INTERFACE) != 0  && utils.isJML(tree.mods)) {
//            // FIXME - but the @Instance declaration might be in the .jml file
//            boolean isInstance = JmlAttr.instance(context).isInstance(tree.mods);
//            if (isInstance && !wasStatic) {
//            	tree.mods.flags &= ~Flags.STATIC;
//            	if (tree.sym != null) tree.sym.flags_field = tree.sym.flags() & ~Flags.STATIC;
//            }
//        }
////        boolean prev = resolve.allowJML();
////        boolean isReplacementType = ((JmlVariableDecl)tree).jmltype;
////        
////        if (utils.isJML(tree.mods) || isReplacementType) resolve.setAllowJML(true);
////        
//////        boolean prevChk = ((JmlCheck)chk).noDuplicateWarn;
//////        ((JmlCheck)chk).noDuplicateWarn = false;
//        JavaFileObject prevSource = log.useSource( ((JmlVariableDecl)tree).source());
//        super.visitVarDef(tree);
//        
//        if (tree.sym.owner instanceof ClassSymbol) {
//        	// local variables and parameters do not have entries in specs
//        	var jtree = (JmlVariableDecl)tree;
//        	var fs = jtree.specsDecl.fieldSpecs;
//        	((JmlVariableDecl)tree).specsDecl.sym = tree.sym;
//        	if (tree.sym != null) JmlSpecs.instance(context).putSpecs(tree.sym, fs);
//        }
//        log.useSource(prevSource);
//
//
//
//////        ((JmlCheck)chk).noDuplicateWarn = prevChk;
////        if (utils.isJML(tree.mods)) resolve.setAllowJML(prev);
////        if (tree.sym == null) {
////            // A duplicate
////            env.enclClass.defs = List.filter(env.enclClass.defs,tree);
////            return;
////        }
//        Symbol sym = tree.sym;
// //       if (specs.getSpecs(tree.sym) != null) utils.warning("jml.internal","Expected null field specs here: " + tree.sym.owner + "." + tree.sym);
//        JmlVariableDecl jtree = (JmlVariableDecl)tree;
//    }
    
    protected void visitFieldDefHelper(JCVariableDecl tree, VarSymbol v, WriteableScope enclScope, Env<AttrContext> env, List<JCAnnotation> annotations) {
       	if (tree.sym.owner instanceof ClassSymbol && tree != ((JmlVariableDecl)tree).specsDecl && null != ((JmlVariableDecl)tree).specsDecl) {
       		System.out.println("VFDH " + tree.sym + " " + tree.sym.owner + " " + annotations + ":: " + ((JmlVariableDecl)tree).specsDecl.mods.annotations
       				+ " " + tree + "::" + ((JmlVariableDecl)tree).specsDecl + " " + tree.hashCode() + "::" + ((JmlVariableDecl)tree).specsDecl.hashCode());
       		annotations = annotations.appendList(((JmlVariableDecl)tree).specsDecl.mods.annotations);
    	}
    	super.visitFieldDefHelper(tree, v, enclScope, env, annotations);
    }    
    
    
    // FIXME - ressurrect these checks and corresponding tests

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


//    // Only used for binary enter
//
//    // Only used for entering binary classes
//    // FIXME - REVIEW
//
//
//    protected void importHelper(JCCompilationUnit tree) {
//        // Import-on-demand java.lang.   // FIXME - module
//        importAll(tree.pos, syms.enterPackage(null, names.java_lang), env);
//        importAll(tree.pos, syms.enterPackage(null, names.fromString(Strings.jmlSpecsPackage)), env);
//
//        // Process all import clauses.
//        memberEnter(tree.defs, env);
//    }
//
//    // FIXME
//    protected void importAll(int pos,
//            final TypeSymbol tsym,
//            Env<AttrContext> env) {
////        if (tsym.kind == PCK && tsym.members().elems == null && !tsym.exists()) {
////            // If we can't find org.jmlspecs.lang, exit immediately.
////            if (((PackageSymbol)tsym).fullname.toString().equals(Strings.jmlSpecsPackage)) {
////                JCDiagnostic msg = JCDiagnostic.Factory.instance(context).fragment("fatal.err.no." + Strings.jmlSpecsPackage);
////                throw new FatalError(msg);
////            }
////        }
////        // FIXME - taken from Java8 implementation -- how are imports handled now?
////        if (tsym.kind == PCK && !tsym.exists()) {
////            // If we can't find java.lang, exit immediately.
////            if (((PackageSymbol)tsym).fullname.equals(names.java_lang)) {
////                JCDiagnostic msg = Log.instance(context).factory().fragment("fatal.err.no.java.lang");
////                throw new FatalError(msg);
////            } else {
////                utils.error(DiagnosticFlag.RESOLVE_ERROR, pos, "doesnt.exist", tsym);
////            }
////        }
////// FIXME        super.importAll(null, tsym, env);
//    }


}
