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
import static com.sun.tools.javac.code.Flags.UNATTRIBUTED;
import static com.sun.tools.javac.code.Kinds.PCK;
import static com.sun.tools.javac.code.Kinds.TYP;
import static com.sun.tools.javac.code.Kinds.kindName;
import static com.sun.tools.javac.code.TypeTag.CLASS;
import static com.sun.tools.javac.tree.JCTree.Tag.TOPLEVEL;

import java.io.PrintWriter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import javax.tools.JavaFileObject;
import javax.tools.JavaFileObject.Kind;

import org.eclipse.jdt.annotation.Nullable;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlSpecs.MethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlAnnotation;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import com.sun.tools.javac.code.Attribute.Compound;
import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.CompletionFailure;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.comp.Resolve.LookupHelper;
import com.sun.tools.javac.comp.Resolve.MethodCheck;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
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
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

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
        this.enter = (JmlEnter)JmlEnter.instance(context);
        this.names = Names.instance(context);
        this.org_jmlspecs_lang = names.fromString("org.jmlspecs.lang");
        this.jmlF = JmlTree.Maker.instance(context);
        this.syms = Symtab.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.modelName = names.fromString(JmlTokenKind.MODEL.internedName());
        this.log = Log.instance(context);
    }

    public static void preRegister(final Context context) {
        context.put(memberEnterKey, new Context.Factory<MemberEnter>() {
            public MemberEnter make(Context context) {
                return new JmlMemberEnter(context);
            }
        });
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
    
    public boolean dojml = false;
    
    @Override
    public void memberEnter(JCTree tree, Env<AttrContext> env) {
        if (tree instanceof JmlTypeClause) return;
        if (!dojml && tree instanceof JmlMethodDecl && utils.isJML(((JmlMethodDecl)tree).mods)) return;
        if (!dojml && tree instanceof JmlVariableDecl && utils.isJML(((JmlVariableDecl)tree).mods)) return;
        super.memberEnter(tree, env);
        if (tree instanceof JmlCompilationUnit) {  // FIXME - this is also called with tree being a JmlClassDecl - then nothing is done; also part of the below is done already??
            JmlCompilationUnit javacu = (JmlCompilationUnit)tree;
            JmlCompilationUnit specscu = javacu.specsCompilationUnit;
            // Normally, a Java CU has attached a specs CU, even if it is the same as itself.
            // However, memberEnter is called when completing a class symbol to complete the package declaration
            // in its top level environment; so for a model class in a specs compilation unit the toplevel is
            // the specs compilation unit, which may have a null specscu field
            
            // FIXME - not sure this is what we want. We need the normal env (without model imports),
            // and an env for the specs file (which may be either the .jml or .java file) that includes
            // model imports org.jmlspecs.lang and model declarations.
            if (specscu != null) {
                Env<AttrContext> specenv = specscu.topLevelEnv;
                if (specenv == null) specenv = env;
                if (specenv != env) importAll(tree.pos, reader.enterPackage(names.java_lang), specenv);
                super.memberEnter(specscu, specenv);
                importAll(tree.pos, reader.enterPackage(names.fromString("org.jmlspecs.lang")), specenv);
            }
        }
    }

    
    int modeOfFileBeingChecked = 0;
    
    protected JmlClassDecl currentClass = null;
    
    @Override
    protected void finishClass(JCClassDecl tree, Env<AttrContext> env) {
        PrintWriter noticeWriter = log.getWriter(WriterKind.NOTICE);
        JmlClassDecl jtree = (JmlClassDecl)tree;
        JavaFileObject prevSource = log.useSource(jtree.source());;
        JmlClassDecl prevClass = currentClass;
        currentClass = (JmlClassDecl)tree;
        int prevMode = modeOfFileBeingChecked;  // FIXME _ suspect this is not accurate
        modeOfFileBeingChecked = ((JmlCompilationUnit)env.toplevel).mode;
        boolean prevAllowJML = resolve.allowJML();
        if (utils.isJML(tree.mods)) resolve.setAllowJML(true);

        super.finishClass(tree, env);

        if (utils.isJML(tree.mods)) resolve.setAllowJML(prevAllowJML);
        
        if ((JmlCompilationUnit.isForBinary(modeOfFileBeingChecked)) && !JmlAttr.instance(context).isModel(tree.mods)
                && !(tree.sym.toString().startsWith("$anonymous$"))) { // FIXME - do something more robust than checking the name
            finishSpecClass((JmlClassDecl)tree,env); 
            modeOfFileBeingChecked = prevMode;
            currentClass = prevClass;
            return; 
        }
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("    MEMBER ENTER FINISHING CLASS " + tree.sym.fullname);
        // This is the case of a java source file, with a possibly-null
        // specification file.  Besides entering all the Java
        // field and method and initializer(?) members in the usual way (done above in the super call), 
        // we need to:
        //  connect specifications of Java members with the members
        //  enter ghost and model fields, methods, initializers, along with
        //      their specifications

        ClassSymbol csym = jtree.sym;
        
        boolean prevInSpecFile = inSpecFile;

        inSpecFile = jtree.source() == null ? false : jtree.source().getKind() != Kind.SOURCE;  // should always be false (?)

        currentClass = prevClass;

        // Now go through everything in the specifications, finding the
        // JML fields and methods.  These need to be entered.

        prevAllowJML = resolve.allowJML();
        boolean prevInModel = inModelTypeDeclaration;
        try {
            JmlClassDecl specsDecl = jtree.specsDecls;
            if (specsDecl == null) {
                if (utils.jmlverbose >= Utils.JMLDEBUG) noticeWriter.println("FINISHING CLASS - NO SPECS " + tree.sym.fullname);
                checkTypeMatch(jtree,jtree); // Still need to check modifiers
                return;
            }

            if (utils.jmlverbose >= Utils.JMLDEBUG) noticeWriter.println("FINISHING CLASS - JML PHASE " + tree.sym.fullname);
            
            // First we scan through the Java parts of the spec file
            // Various checks happen in the appropriate visitMethods
            
            boolean isModel = JmlAttr.instance(context).isModel(specsDecl.mods) || JmlAttr.instance(context).implementationAllowed;
            inModelTypeDeclaration = isModel;
            
            log.useSource(specsDecl.source());
            // TODO : need to do something to distinguish hand created parse trees
            inSpecFile = specsDecl.source() == null ? false : specsDecl.source().getKind() != Kind.SOURCE; // Could be a Java file in the specs sequence
            prevClass = currentClass;
            currentClass = jtree;
            
            // Misc checks on the Java declarations
            for (JCTree that: specsDecl.defs) {
                if (that instanceof JCTree.JCBlock) {
                    if (inSpecFile && currentMethod == null && !utils.isJML(currentClass.mods)) {
                        // initializer block is not allowed in a specification, unless it is a model class
                        log.error(that.pos,"jml.initializer.block.allowed");
                    }
                } else if (that instanceof JmlVariableDecl) {
                    // FIXME - anything here - or for other cases?
                }
            }

            resolve.setJML(true);
            
            
//            JmlSpecs.TypeSpecs tsp = jtree.typeSpecs;
//            if (tsp == null) {
//                tsp = jtree.typeSpecs = new JmlSpecs.TypeSpecs();
//                JmlSpecs.instance(context).putSpecs(jtree.sym,tsp);
//            }
//            tsp.modifiers = specsDecl.mods;
//            tsp.decl = specsDecl;
//            tsp.file = specsDecl.sourcefile;
//
//            prevSource = log.useSource(specsDecl.sourcefile);
//            JmlMethodSpecs savedMethodSpecs = null;
//            JmlSpecs.FieldSpecs mostRecentFieldSpecs = null;
//            JmlVariableDecl mostRecentVarDecl = null;
            
            for (JCTree clause: jtree.specsDecls.defs) {
                if (clause instanceof JmlTypeClauseDecl) {
                    // These are JML declarations
                    JmlTypeClauseDecl cl = (JmlTypeClauseDecl)clause;
                    JCTree tr = cl.decl;
                    // We have already entered any model classes
                    // but we need to enter model methods and ghost and model fields
                    if (tr instanceof JmlVariableDecl) {
                        if (utils.jmlverbose >= Utils.JMLDEBUG) noticeWriter.println("JML VAR ENTER FOR " + jtree.name + " " + ((JmlVariableDecl)tr).name);
                        int n = log.nerrors;
                        JmlVariableDecl vtr = (JmlVariableDecl)tr;
                        if (vtr.sym == null) {
                            noticeWriter.println("Expected " + jtree.name + " " + vtr.name + " to be entered already");
                            memberEnter(tr,env); // don't reenter - should already be entered
                            if (n == log.nerrors) {
                                jtree.defs = jtree.defs.append(tr);
                                vtr.specsDecl = vtr;
                            } else {
                                checkForGhostModel(vtr.mods, vtr.source(), vtr.pos());
                            }
                        } else {
                            //checkForGhostModel(vtr.mods, vtr.source(), vtr.pos());
                        }
//                        if (vtr.sym == null) {
//                            memberEnter(tr,env);
//                            if (n == log.nerrors) {
//                                jtree.defs = jtree.defs.append(tr);
//                                vtr.specsDecl = vtr;
//                                checkForGhostModel(vtr.mods, vtr.source(), vtr.pos());
//                            } else {
//                                // duplicate error issued
//                            }
//                        }
                    } else if (tr instanceof JmlMethodDecl) {
                        if (utils.jmlverbose >= Utils.JMLDEBUG) noticeWriter.println("JML METH ENTER FOR " + jtree.name + " " + ((JmlMethodDecl)tr).name);
                        int n = log.nerrors;
                        JmlMethodDecl mtr = (JmlMethodDecl)tr;
                        if (mtr.sym == null) { // This should not happen
                            noticeWriter.println("Expected " + jtree.name + " " + mtr.name + " to be entered already");
                            memberEnter(tr,env);
                            if (n == log.nerrors) {
                                jtree.defs = jtree.defs.append(tr);
                                mtr.specsDecl = mtr;

                            } else {
                                checkForGhostModel(mtr.mods, mtr.source(), mtr.pos());
                            }
                        } else {
                            //checkForGhostModel(mtr.mods, mtr.source(), mtr.pos());
                        }
                    }
                }
            }
            {
//                ListBuffer<JmlTypeClauseDecl> newlist = new ListBuffer<>();
//                for (JmlTypeClauseDecl t: tsp.decls) {
//                    if (!duplicates.contains(t)) {
//                        newlist.append(t);
//                    }
//                }
//                tsp.decls = newlist;
//                newlist = new ListBuffer<>();
//                for (JmlTypeClauseDecl t: specsDecl.typeSpecs.decls) {
//                    if (!duplicates.contains(t)) {
//                        newlist.append(t);
//                    }
//                }
//                specsDecl.typeSpecs.decls = newlist;
            }
            
            // At this point, all java and spec members are entered
            // We still need to connect specs of fields and methods with their Java counterparts

            // FIXME - what about blocks

            // First for Java fields and methods
            
            List<JCTree> addedDecls = matchStuff(jtree, jtree.sym, env, specsDecl);
            boolean savedojml = dojml;
            dojml = true;
            memberEnter(addedDecls,env);
            dojml = savedojml;
            matchRest(addedDecls);
            ListBuffer<JCTree> newdefs = new ListBuffer<JCTree>();
            for (JCTree t: jtree.defs) {
                if (t instanceof JmlMethodDecl && utils.isJML(((JmlMethodDecl)t).mods)) continue;
                if (t instanceof JmlVariableDecl && utils.isJML(((JmlVariableDecl)t).mods)) continue;
                //if (t instanceof JmlClassDecl && utils.isJML(((JmlClassDecl)t).mods)) continue;
                if (t instanceof JmlTypeClause) continue;
                newdefs.add(t);
            }
            newdefs.appendList(addedDecls);
            jtree.defs = newdefs.toList();
//            Map<Symbol,JCTree> matches = new HashMap<Symbol,JCTree>();
//            ListBuffer<JCTree> newlist = new ListBuffer<>();
//            for (JCTree specsMemberDecl: specsDecl.defs) {
//                if (specsMemberDecl instanceof JmlVariableDecl) {
//                    JmlVariableDecl specsVarDecl = (JmlVariableDecl)specsMemberDecl;
//                    VarSymbol vsym = matchAndSetFieldSpecs(jtree,jtree.sym,specsVarDecl, matches);
//                    if (vsym != null) newlist.add(specsVarDecl);
////                    if (vsym == null) {
////                        // A declaration in the specs file that is unmatched, so we add it in -- FIXME - should we?
////                        memberEnter(specsMemberDecl,env);
////                        jtree.defs = jtree.defs.append(specsMemberDecl);
////                        vsym = specsVarDecl.sym;
////                        specsVarDecl.specsDecl = specsVarDecl;
////                    }
//                } else if (specsMemberDecl instanceof JmlMethodDecl) {
//                    JmlMethodDecl specsMethodDecl = (JmlMethodDecl)specsMemberDecl;
//                    MethodSymbol msym = matchAndSetMethodSpecs(jtree,jtree.sym,specsMethodDecl,env, matches);
//                    if (msym != null) newlist.add(specsMethodDecl);
////                    if (msym == null) {
////                        // A declaration in the specs file that is unmatched, so we add it in -- FIXME - should we?
////                        jtree.defs = jtree.defs.append(specsMethodDecl);
////                        memberEnter(specsMemberDecl,env);
////                        msym = specsMethodDecl.sym;
////                        specsMethodDecl.specsDecl = specsMethodDecl;
////                    }
////                    if (msym != null && specsDecl != jtree // If specsDecl == jtree, Java itself has already issued an error message
////                            && (matchpos=matches.put(msym,((JmlMethodDecl)specsMemberDecl).pos)) != null) {
////                        int p = ((JmlMethodDecl)specsMemberDecl).pos;
////                        utils.error(specsMethodDecl.sourcefile,p,"jml.duplicate.method.match",specsMethodDecl.name);
////                        utils.error(specsMethodDecl.sourcefile,matchpos,"jml.associated.decl.cf",
////                        		utils.locationString(p,specsMethodDecl.sourcefile));
////                    } else {
////                        newlist.add(specsMemberDecl);
////                        JmlSpecs.MethodSpecs methodSpecs = specsMethodDecl.methodSpecsCombined;
////                        if (methodSpecs != null && msym != null) JmlSpecs.instance(context).putSpecs(msym,methodSpecs);
////                    }
//                } else {
//                    newlist.add(specsMemberDecl);
//                }
//            }
//            specsDecl.defs = newlist.toList();
//            
//            // Then for specs fields and methods
//            
//            // Duplicates among JML declarations of fields and methods are caught 
//            // as they are entered into the enclosing scope
//            ListBuffer<JmlTypeClauseDecl> newlist2 = new ListBuffer<>();
//            for (JmlTypeClauseDecl tcd: specsDecl.typeSpecs.decls) {
//                if (tcd.decl instanceof JmlVariableDecl) {
//                    VarSymbol vsym = matchAndSetFieldSpecs(jtree,jtree.sym,(JmlVariableDecl)tcd.decl,matches);
//                    if (vsym != null) newlist2.add(tcd);
//                } else if (tcd.decl instanceof JmlMethodDecl) {
//                    MethodSymbol msym = matchAndSetMethodSpecs(jtree,jtree.sym,(JmlMethodDecl)tcd.decl,env, matches);
//                    if (msym != null) newlist2.add(tcd);
//                }
//            }
//            specsDecl.typeSpecs.decls = newlist2;
//            matches.clear();
            
            // Now we fill in the convenience fields - we could not do this
            // earlier without prematurely overwriting what might be in the
            // Java file and used as part of the specs seqeuence

            // Also fill in default method specs for anything that does not have them
            // FIXME - same for other kinds of fields? Or should we just interpret absence as default everywhere?
            
            // First for Java fields and methods
            
            for (JCTree t: jtree.defs) {
                if (t instanceof JmlVariableDecl) {
                    JmlVariableDecl v = (JmlVariableDecl)t;
                    v.fieldSpecsCombined = specs.getSpecs(v.sym);
                } else if (t instanceof JmlMethodDecl) {
                    JmlMethodDecl m = (JmlMethodDecl)t;
                    MethodSpecs ms;
                    if (m.specsDecl == null) {
                        ms = specs.defaultSpecs(m);
                    } else {
                        ms = new MethodSpecs(m.specsDecl);
                    }
                    m.methodSpecsCombined = ms;
                    JmlSpecs.instance(context).putSpecs(m.sym, ms);
                }
            }
            
            // FIXME = use a visitor to be more O-O ?
            // FIXME - unify this method with the near duplicate below

            // Then for specs fields and methods
            
//            for (JmlTypeClauseDecl tcd: specsDecl.typeSpecs.decls) {
//                    if (tcd.decl instanceof JmlVariableDecl) {
//                        JmlVariableDecl v = (JmlVariableDecl)tcd.decl;
//                        v.fieldSpecsCombined = specs.getSpecs(v.sym);
//                    } else if (tcd.decl instanceof JmlMethodDecl && !duplicates.contains(tcd)) {
//                        JmlMethodDecl m = (JmlMethodDecl)tcd.decl;
//                        m.methodSpecsCombined = specs.getSpecs(m.sym);
//                        if (m.methodSpecsCombined == null) {
//                            JmlSpecs.MethodSpecs defaultSpecs = JmlSpecs.defaultSpecs(context,m.sym,m.pos);
//                            m.methodSpecsCombined = defaultSpecs;
//                            defaultSpecs.cases.decl = m;
//                            JmlSpecs.instance(context).putSpecs(m.sym, m.methodSpecsCombined);
//                        }
//                   }
//            }
            

//            ListBuffer<JCTree> newdefs = ListBuffer.lb();
//            for (JCTree t: specsDecl.defs) {
//                if (!(t instanceof JmlTypeClauseIn || t instanceof JmlTypeClauseMaps)) {
//                    mostRecentFieldSpecs = null;
//                }
//                if (t instanceof JmlVariableDecl) {
//                    // make the match, check it, link it
//                    JmlVariableDecl vardecl = (JmlVariableDecl)t;
//                    JmlVariableDecl match = null;
//                    for (JCTree jt: jtree.defs) {
//                        if (jt instanceof JmlVariableDecl) {
//                            if (((JmlVariableDecl)jt).name.equals(vardecl.name)) {
//                                // matched
//                                match = (JmlVariableDecl)jt;
//                                if (match.specsDecl != null) {
//                                    log.error(vardecl.pos(),"jml.duplicate.var.match",vardecl.name);
//                                } else {
//                                    match.specsDecl = vardecl;
//                                    JmlSpecs.instance(context).putSpecs(match.sym,mostRecentFieldSpecs=new JmlSpecs.FieldSpecs(specsDecl.mods));
//                                    mostRecentVarDecl = vardecl;
//                                }
//                            }
//                        }
//                    }
//                    if (match == null) {
//                        log.error(vardecl.pos(),"jml.no.var.match",vardecl.name);
//                    } else {
//                        checkFieldMatch(match,vardecl);
//                        vardecl.sym = match.sym;
//                        newdefs.append(t);
//                    }
//                } else if (t instanceof JmlMethodDecl) {
//                    JmlMethodDecl match = matchMethod((JmlMethodDecl)t,jtree,env);
//                    // make the match, check it, link it
//                    if (match == null) {
//                        // Error already issued in matchMethod
//                        // Ignore any specs
//                        savedMethodSpecs = null; // FIXME - do we really want to completely ignore this method and its specs - it won't get type checked for example
//                    } else {
//                        // FIXME - if a method matched against a superclass, we have to be careful
//                        if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
//                        savedMethodSpecs.decl = ((JmlMethodDecl)t);
//                        match.specsDecl = (JmlMethodDecl)t;
//                        match.methodSpecs = savedMethodSpecs;
//                        JmlSpecs.instance(context).putSpecs(match.sym, match.methodSpecs);
//                        savedMethodSpecs = null;
//                        newdefs.append(t);
//                    }
//                } else if (t instanceof JmlMethodSpecs) {
//                    savedMethodSpecs = (JmlMethodSpecs)t;
//                } else if (t instanceof JmlTypeClauseIn || t instanceof JmlTypeClauseMaps) {
//                    if (mostRecentFieldSpecs == null) {
//                        log.error(t.pos(),"jml.misplaced.var.spec",((JmlTypeClause)t).token.internedName());
//                    } else {
//                        mostRecentFieldSpecs.list.append((JmlTypeClause)t);
//                        if (t instanceof JmlTypeClauseIn) ((JmlTypeClauseIn)t).parentVar = mostRecentVarDecl;
//                    }
//                } else if (t instanceof JmlTypeClauseInitializer) {
//                    if (((JmlTypeClauseInitializer)t).token == JmlToken.INITIALIZER) {
//                        if (tsp.initializerSpec != null) {
//                            log.error(t.pos,"jml.one.initializer.spec.only");
//                        } else {
//                            if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
//                            ((JmlTypeClauseInitializer)t).specs = savedMethodSpecs;
//                            tsp.initializerSpec = ((JmlTypeClauseInitializer)t);
//                        }
//                    } else {
//                        if (tsp.staticInitializerSpec != null) {
//                            log.error(t.pos,"jml.one.initializer.spec.only");
//                        } else {
//                            if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
//                            ((JmlTypeClauseInitializer)t).specs = savedMethodSpecs;
//                            tsp.staticInitializerSpec = ((JmlTypeClauseInitializer)t);
//                        }
//                    }
//                    savedMethodSpecs = null;
//                } else if (t instanceof JmlTypeClause) {
//                    if (t instanceof JmlTypeClauseDecl) {
//                        // These are JML declarations
//                        JmlTypeClauseDecl cl = (JmlTypeClauseDecl)t;
//                        JCTree tr = cl.decl;
//                        // We have already entered any model classes
//                        if (tr instanceof JmlVariableDecl) {
//                            if (utils.jmldebug) log.noticeWriter.println("JML VAR ENTER FOR " + jtree.name + " " + ((JmlVariableDecl)tr).name);
//                            memberEnter(tr,env);
//                            JmlSpecs.instance(context).putSpecs(((JmlVariableDecl)tr).sym,mostRecentFieldSpecs=new JmlSpecs.FieldSpecs(((JmlVariableDecl)tr).mods));
//                        } else if (tr instanceof JmlMethodDecl) {
//                            if (utils.jmldebug) log.noticeWriter.println("JML METH ENTER FOR " + jtree.name + " " + ((JmlMethodDecl)tr).name);
//                            memberEnter(tr,env);
//                            JmlMethodDecl match = (JmlMethodDecl)tr;
//                            if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
//                            savedMethodSpecs.decl = match;
//                            match.methodSpecs = savedMethodSpecs;
//                            JmlSpecs.instance(context).putSpecs(match.sym, match.methodSpecs);
//                            savedMethodSpecs = null;
//                        }
//                        newdefs.append(t);
//                    }
//                    // All JML declarations, invariants, etc. are put in tsp.clauses
//                    tsp.clauses.append((JmlTypeClause)t);
//                } else if (t instanceof JmlClassDecl) {
//                    // skip this - classes were already handled in Enter/JmlEnter
//                    newdefs.append(t);
//                } else if (t instanceof JCTree.JCBlock){
//                    if (savedMethodSpecs != null) JmlSpecs.instance(context).putSpecs((ClassSymbol)specsDecl.sym, (JCTree.JCBlock)t, savedMethodSpecs);
//                    savedMethodSpecs = null;
//                    if (specsDecl.sym == null) {
//                        // Initializer blocks are not allowed in specs (but are in model classes)
//                        log.error(t.pos(),"jml.initializer.block.allowed");
//                    }
//                    newdefs.append(t);
//                } else {
//                    log.noticeWriter.println("  FOUND & NOT SUPPORTED " + t.getClass());  // FIXME
//                    newdefs.append(t);
//                }
//                if (savedMethodSpecs != null && !(t instanceof JmlMethodSpecs)) {
//                    log.error(savedMethodSpecs.pos(),"jml.misplaced.method.specs",specsDecl.name);
//                    savedMethodSpecs = null;
//                }
//            }
//            specsDecl.defs = newdefs.toList();
//            if (savedMethodSpecs != null) {
//                log.error(savedMethodSpecs.pos(),"jml.misplaced.method.specs",specsDecl.name);
//                savedMethodSpecs = null;
//            }
            checkFinalTypeSpecs(specs.get(csym));

        } finally {
            inSpecFile = prevInSpecFile;
            inModelTypeDeclaration = prevInModel;
            addRacMethods(tree.sym,env);
            resolve.setJML(prevAllowJML);
            log.useSource(prevSource);
            if (utils.jmlverbose >= Utils.JMLDEBUG) {
                noticeWriter.println("FINISHING CLASS - COMPLETE " + tree.sym.fullname);
                noticeWriter.println("   SCOPE IS " + tree.sym.members());
            }
            modeOfFileBeingChecked = prevMode;
            currentClass = prevClass;
        }
    }
    
    public void checkForGhostModel(JCModifiers mods, JavaFileObject source, DiagnosticPosition pos) {
        JmlAnnotation a = utils.findMod(mods, JmlTokenKind.MODEL);
        if (a == null) a = utils.findMod(mods, JmlTokenKind.GHOST);
        if (!utils.isJML(mods)) {
            if (a != null) utils.error(source, pos, "jml.ghost.model.on.java");
        } else {
            if (a == null) utils.error(source, pos , "jml.missing.ghost.model");
        }
    }
    
    protected void matchRest(List<JCTree> added) {
        for (JCTree t: added) {
            if (t instanceof JmlMethodDecl) {
                JmlMethodDecl specsMethodDecl =(JmlMethodDecl)t;
                MethodSymbol msym = specsMethodDecl.sym;
                JmlSpecs.MethodSpecs methodSpecs = new JmlSpecs.MethodSpecs(specsMethodDecl);
                specsMethodDecl.methodSpecsCombined = methodSpecs;
                JmlSpecs.instance(context).putSpecs(msym,methodSpecs);
                specsMethodDecl.sym = msym;
                specsMethodDecl.specsDecl = specsMethodDecl;
            } else if (t instanceof JmlVariableDecl) {
                
            }
        }
    }
    
    
    protected List<JCTree> matchStuff(@Nullable JmlClassDecl jtree, ClassSymbol csym, Env<AttrContext> env, JmlClassDecl specsDecl) {
        Map<Symbol,JCTree> matches = new HashMap<Symbol,JCTree>();
        ListBuffer<JCTree> newlist = new ListBuffer<>();
        ListBuffer<JCTree> added = new ListBuffer<>();
        for (JCTree specsMemberDecl: specsDecl.defs) {
            if (specsMemberDecl instanceof JmlVariableDecl) {
                JmlVariableDecl specsVarDecl = (JmlVariableDecl)specsMemberDecl;
                    boolean ok = matchAndSetFieldSpecs(jtree, csym, specsVarDecl, matches, jtree == specsDecl);
                    if (ok) {
                        if (utils.isJML(specsVarDecl.mods)) added.add(specsVarDecl);
                        newlist.add(specsVarDecl);
                    }
            } else if (specsMemberDecl instanceof JmlMethodDecl) {
                JmlMethodDecl specsMethodDecl = (JmlMethodDecl)specsMemberDecl;
                boolean ok = matchAndSetMethodSpecs(jtree, csym, specsMethodDecl, env, matches, jtree == specsDecl);
                if (ok) {
                    if (specsMethodDecl.sym == null) {
//                    // FIXME - consolidate this into matchAndSetMethodSpecs
//                    MethodSymbol msym = specsMethodDecl.sym;
//                    JmlSpecs.MethodSpecs methodSpecs = new JmlSpecs.MethodSpecs(specsMethodDecl);
//                    specsMethodDecl.methodSpecsCombined = methodSpecs;
//                    JmlSpecs.instance(context).putSpecs(msym,methodSpecs);
//                    specsMethodDecl.sym = msym;
//                    specsMethodDecl.specsDecl = specsMethodDecl;
//                    // checkFieldmatch? addAnnotations?
                        newlist.add(specsMethodDecl);
                        added.add(specsMethodDecl);
                    } else {
                        if (utils.isJML(specsMethodDecl.mods)) added.add(specsMethodDecl);
                        newlist.add(specsMethodDecl);
                    }
                }
            } else {
                newlist.add(specsMemberDecl);
            }
        }
        specsDecl.defs = newlist.toList();
        
        // Then for specs fields and methods
        
//        // Duplicates among JML declarations of fields and methods are caught 
//        // as they are entered into the enclosing scope
//        ListBuffer<JmlTypeClauseDecl> newlist2 = new ListBuffer<>();
//        for (JmlTypeClauseDecl tcd: specsDecl.typeSpecs.decls) {
//            if (tcd.decl instanceof JmlVariableDecl) {
//                boolean ok = matchAndSetFieldSpecs(jtree,jtree.sym,(JmlVariableDecl)tcd.decl,matches, false);
//                if (ok) newlist2.add(tcd);
//            } else if (tcd.decl instanceof JmlMethodDecl) {
//                boolean ok = matchAndSetMethodSpecs(jtree,jtree.sym,(JmlMethodDecl)tcd.decl,env, matches, false);
//                if (ok) newlist2.add(tcd);
//            }
//        }
//        specsDecl.typeSpecs.decls = newlist2;
        matches.clear();
        return added.toList();
    }

    /** Finds a Java declaration matching the given specsVarDecl in the given class
     * <br>the matching symbol, if any, is returned 
     * <br>if no match and specsVarDecl is not ghost or model, error message issued, null returned
     * <br>if match is duplicate, error message issued, match returned
     * <br>if non-duplicate match, and javaDecl defined, set javaDecl.specsDecl field
     * <br>if non-duplicate match, set specs database
     * <br>if non-duplicate match, set specsVarDecl.sym field
     * */
    protected boolean matchAndSetFieldSpecs(JmlClassDecl javaDecl, ClassSymbol csym, JmlVariableDecl specsVarDecl, Map<Symbol,JCTree> matchesSoFar, boolean sameTree) {
        // Find any specsVarDecl counterpart in the javaDecl
        // For fields it is sufficient to match by name
        Name id = specsVarDecl.name;
        VarSymbol matchSym = null;
        if (!sameTree) {
            Scope.Entry entry = csym.members().lookup(id);
            while (entry != null && entry.sym != null) {
                if (entry.sym instanceof VarSymbol && entry.sym.name == id) {
                    matchSym = (VarSymbol)entry.sym;
                    break;
                }
                entry = entry.next();
            }
        } else {
            matchSym = specsVarDecl.sym;
        }
        
        // matchsym == null ==> no match; otherwise matchSym is the matching symbol
        
        if (matchSym == null) {
            JmlAnnotation a = ((JmlAttr)attr).findMod(specsVarDecl.mods,JmlTokenKind.GHOST);
            if (a == null) a = ((JmlAttr)attr).findMod(specsVarDecl.mods,JmlTokenKind.MODEL);
            if (!utils.isJML(specsVarDecl.mods)) {
                // We are going to discard this declaration because of the error, so we do extra checking
                if (a != null) {
                    utils.error(specsVarDecl.sourcefile, a.pos(),"jml.ghost.model.on.java",specsVarDecl.name);
                }
                // Non-matching java declaration - an error
                utils.error(specsVarDecl.sourcefile, specsVarDecl.pos(),"jml.no.var.match",specsVarDecl.name);
                return false;
            } else {
                // Non-matching ghost or model declaration; this is OK - there is no symbol yet
                // This should have a model or ghost declaration
                return true;
            }
        }
        
        // The matches map holds any previous matches found - all to specification declarations
        JCTree prevMatch = matchesSoFar.get(matchSym);
        if (prevMatch != null && prevMatch != specsVarDecl) {
            // DO extra checking since we are discarding this declaration
            if (!utils.isJML(specsVarDecl.mods)) {
                JmlAnnotation a = ((JmlAttr)attr).findMod(specsVarDecl.mods,JmlTokenKind.GHOST);
                if (a == null) a = ((JmlAttr)attr).findMod(specsVarDecl.mods,JmlTokenKind.MODEL);
                if (a != null) {
                    utils.error(specsVarDecl.sourcefile, a.pos(),"jml.ghost.model.on.java",specsVarDecl.name);
                }
            }
            // Previous match - give error
            utils.errorAndAssociatedDeclaration(specsVarDecl.sourcefile, specsVarDecl.pos, ((JmlVariableDecl)prevMatch).sourcefile, prevMatch.pos,"jml.duplicate.var.match",specsVarDecl.name);
            return false;
        }

        {
            // New match - save it; also set the specs database
            matchesSoFar.put(matchSym,  specsVarDecl);
            JmlSpecs.FieldSpecs fieldSpecs = specsVarDecl.fieldSpecs;
            if (fieldSpecs != null) JmlSpecs.instance(context).putSpecs(matchSym,fieldSpecs);
            specsVarDecl.sym = matchSym;
        }

        // If there is a Java AST, find the match and set the specsDecl field
        
        JmlVariableDecl javaMatch = null;
        if (sameTree) {
            javaMatch = specsVarDecl;
        } else if (javaDecl != null) {
            // TODO - is there a better way to find a declaration for a symbol?
            for (JCTree t: javaDecl.defs) {
                if (t instanceof JmlVariableDecl && ((JmlVariableDecl)t).sym == matchSym) {
                    javaMatch = (JmlVariableDecl)t;
                    break;
                }
            }
            if (javaMatch == null) {
                log.error("jml.internal", "Unexpected absent Java field declaration, without a matching symbol: " + matchSym);
            } else if (javaMatch.specsDecl == null) {
                javaMatch.specsDecl = specsVarDecl;
                javaMatch.fieldSpecsCombined = specsVarDecl.fieldSpecs;
            } else if (javaMatch.specsDecl != javaMatch && javaMatch != specsVarDecl) {
                javaMatch = null;
                log.error("jml.internal", "Unexpected duplicate Java field declaration, without a matching symbol: " + matchSym);
            }
        }
        { // Check the match only if it is not a duplicate
            checkFieldMatch(javaMatch,matchSym,specsVarDecl);
            addAnnotations(matchSym,enter.getEnv(csym),specsVarDecl.mods);
        }
        return true;
    }

    /** Finds a Java method declaration matching the given specsMethodDecl in the given class
     * <br>returns false if the declaration is to be ignored because it is in error
     * <br>if no match and specsVarDecl is not ghost or model, error message issued, null returned
     * <br>if match is duplicate, error message issued, match returned
     * <br>if non-duplicate match, and javaDecl defined, set javaDecl.specsDecl field
     * <br>if non-duplicate match, set specs database
     * <br>if non-duplicate match, set specsVarDecl.sym field
     * */
    protected boolean matchAndSetMethodSpecs(@Nullable JmlClassDecl javaDecl, ClassSymbol csym, JmlMethodDecl specsMethodDecl, Env<AttrContext> env, Map<Symbol,JCTree> matchesSoFar, boolean sameTree) {

        // Find the counterpart to specsMethodDecl (from the .jml file) in the Java class declaration (javaDecl or csym)
        // Note that if the class is binary, javaDecl will be null, but csym will not

        MethodSymbol matchSym = sameTree ? specsMethodDecl.sym : matchMethod(specsMethodDecl,csym,env,false);
        
        // matchsym == null ==> no match or duplicate; otherwise matchSym is the matching symbol
        
        if (matchSym == null) {
//            if (((JmlAttr)attr).findMod(specsMethodDecl.mods,JmlTokenKind.GHOST) == null &&
//                    ((JmlAttr)attr).findMod(specsMethodDecl.mods,JmlTokenKind.MODEL) == null) {
//                utils.error(specsMethodDecl.sourcefile, specsMethodDecl.pos(),"jml.no.method.match",specsMethodDecl.name);
//            }
            // Non-matching ghost or model declaration; this is OK - there is no symbol yet
            
            // DO we need to do any cross-linking? and in field specs?
//            combinedSpecs.cases.decl = specsMethodDecl;
//            specsMethodDecl.methodSpecsCombined = combinedSpecs;

            JmlAnnotation a = ((JmlAttr)attr).findMod(specsMethodDecl.mods,JmlTokenKind.GHOST);
            if (a == null) a = ((JmlAttr)attr).findMod(specsMethodDecl.mods,JmlTokenKind.MODEL);
            if (!utils.isJML(specsMethodDecl.mods)) {
                // We are going to discard this declaration because of the error, so we do extra checking
                if (a != null) {
                    utils.error(specsMethodDecl.sourcefile, a.pos(),"jml.ghost.model.on.java",specsMethodDecl.name);
                }
                // Non-matching java declaration - an error
                utils.error(specsMethodDecl.sourcefile, specsMethodDecl.pos(),"jml.no.method.match",
                        csym.flatName() + "." + specsMethodDecl.sym);
                return false;
            } else {
                // Non-matching ghost or model declaration; this is OK - there is no symbol yet
                // This should have a model or ghost declaration - that is checked in JmlAttr
                return true;
            }
        }

        // The matches map holds any previous matches found - all to specification declarations
        JCTree prevMatch = matchesSoFar.get(matchSym);
        if (prevMatch != null) {
            // DO extra checking since we are discarding this declaration because it is already matched
            if (!utils.isJML(specsMethodDecl.mods)) {
                JmlAnnotation a = ((JmlAttr)attr).findMod(specsMethodDecl.mods,JmlTokenKind.GHOST);
                if (a == null) a = ((JmlAttr)attr).findMod(specsMethodDecl.mods,JmlTokenKind.MODEL);
                if (a != null) {
                    utils.error(specsMethodDecl.sourcefile, a.pos(),"jml.ghost.model.on.java",specsMethodDecl.name);
                }
            }
            // Previous match - give error
            utils.errorAndAssociatedDeclaration(specsMethodDecl.sourcefile, specsMethodDecl.pos, ((JmlMethodDecl)prevMatch).sourcefile, prevMatch.pos,"jml.duplicate.method.match",specsMethodDecl.name);
            return false;
        }

        {
            // New match - save it; also set the specs database
            matchesSoFar.put(matchSym,  specsMethodDecl);
            JmlSpecs.MethodSpecs mspecs = new JmlSpecs.MethodSpecs(specsMethodDecl);
            specs.putSpecs(matchSym,mspecs);
            specsMethodDecl.sym = matchSym;
            specsMethodDecl.methodSpecsCombined = mspecs;
        }

        // If we have actual source, then find the source declaration
        JmlMethodDecl javaMatch = null;
        if (javaDecl != null) {
            // TODO - is there a better way to find the declaration for a method symbol?
            if (sameTree) {
                javaMatch = specsMethodDecl;
            } else {
                for (JCTree t: javaDecl.defs) {
                    if (t instanceof JmlMethodDecl && ((JmlMethodDecl)t).sym == matchSym) {
                        javaMatch = (JmlMethodDecl)t;
                        break;
                    }
                }
            }

            if (javaMatch == null) {
                log.error("jml.internal", "Unexpected absent Java method declaration, without a matching symbol: " + matchSym);
            } else if (javaMatch.specsDecl == null) {
                // The specs file declaration corresponds to
                // MethodSymbol matchSym and
                // to a Java source method declaration javaMatch
                // Cross link them and set the specs field for the parameters as well
                javaMatch.specsDecl = specsMethodDecl;
                javaMatch.methodSpecsCombined = specsMethodDecl.methodSpecsCombined;
                javaMatch.methodSpecsCombined.cases.decl = javaMatch; // FIXME - is this needed?
                
            } else {
                javaMatch = null;
                log.error("jml.internal", "Unexpected duplicate Java method declaration, without a matching symbol: " + matchSym);
            }
        }

        { // Check the match only if it is not a duplicate
            checkMethodMatch(javaMatch,matchSym,specsMethodDecl,csym);
            addAnnotations(matchSym,env,specsMethodDecl.mods);
        }

        // FIXME - this stuff is all about query and secret - do we need any of it?
//        JCAnnotation query = ((JmlAttr)attr).findMod(specsMethodDecl.mods,JmlToken.QUERY);
//        VarSymbol queryDatagroup = null;
//        if (query != null) {
//            List<JCExpression> args = query.getArguments();
//            Name datagroup = null;
//            int pos = 0;
//            if (args.isEmpty()) {
//                // No argument - use the name of the method
//                datagroup = specsMethodDecl.name;
//                pos = query.pos;
//            } else {
//                // The expression is an assignment of a Literal string to an identifier
//                // We only care about the literal string
//                // FIXME - what if the string is a qualified name?
//                JCExpression e = args.get(0);
//                pos = e.pos;
//                if (e instanceof JCAssign) {
//                    e = ((JCAssign)e).rhs;
//                } 
//                if (e instanceof JCLiteral) {
//                    JCLiteral lit = (JCLiteral)e;
//                    // Non-string cases will already have error messages
//                    if (lit.value instanceof String)
//                            datagroup = names.fromString(lit.value.toString());
//                }
//            }
//            if (datagroup != null) {
//                // Find the model field with that name
//                boolean prev = resolve.allowJML;
//                resolve.allowJML = true;
//                Symbol v =
//                Symbol v = resolve.findField(env,env.enclClass.type,datagroup,env.enclClass.sym);
//                resolve.allowJML = prev;
//                if (v instanceof VarSymbol) {
//                    //OK
//                    queryDatagroup = (VarSymbol)v;
//                    if (!((JmlAttr)attr).isModel(v)) {
//                        // TODO - ideally would like this to point to the declaration of the VarSymbol - but it might not exist and we have to find it
//                        log.error(pos,"jml.datagroup.must.be.model");
//                    }
//                } else if (args.size() == 0) {
//                    // Create a default: public model secret JMLDataGroup
//                    JmlTree.Maker maker = (JmlTree.Maker)JmlTree.Maker.instance(context);
//                    JCTree.JCModifiers nmods = maker.Modifiers(Flags.PUBLIC);
//                    JCTree.JCAnnotation a = maker.Annotation(maker.Type(((JmlAttr)attr).tokenToAnnotationSymbol.get(JmlToken.MODEL).type),List.<JCExpression>nil());
//                    JCTree.JCAnnotation aa = maker.Annotation(maker.Type(((JmlAttr)attr).tokenToAnnotationSymbol.get(JmlToken.SECRET).type),List.<JCExpression>nil());
//                    nmods.annotations = List.<JCAnnotation>of(a,aa);
//                    JCTree.JCExpression type = maker.Type(((JmlAttr)attr).datagroupClass.type);
//                    JCTree.JCVariableDecl vd = maker.VarDef(nmods,datagroup,type,null);
//                    JmlMemberEnter.instance(context).memberEnter(vd,env);
//                    JmlTree.JmlTypeClauseDecl td = maker.JmlTypeClauseDecl(vd);
//                    utils.setJML(vd.mods);
//                    vd.accept(this); // attribute it
//                    queryDatagroup = vd.sym;
//                    specs.getSpecs(currentClass.sym).clauses.append(td);
//                } else {
//                    log.error(pos,"jml.no.such.model.field",datagroup);
//                }
//            }
//        }
//        if (combinedSpecs != null) combinedSpecs.queryDatagroup = queryDatagroup;


        return true;
    }

    void finishSpecClass(JmlClassDecl specsDecl, Env<AttrContext> env) {
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("FINISHING SPEC CLASS " + specsDecl.sym.fullname);
        // Now go through everything in the spec file.  Some of it
        // will be duplicates of the stuff in the java file.  Some of
        // it will be ghost/model declarations that need to be entered 
        // into the class's scope.  All class declarations are already matched
        // and/or entered.

        JavaFileObject prevSource = null;
        Env<AttrContext> prevEnv = this.env;
        this.env = env;
        boolean prevAllowJML = resolve.setAllowJML(true);// This allows JML identifiers to be matched when lookup occurs
        try {
            if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("FINISHING SPEC CLASS - JML PHASE " + specsDecl.sym.fullname);
            JmlSpecs.TypeSpecs tsp = specs.get(specsDecl.sym);
            if (tsp == null) {
                tsp = new JmlSpecs.TypeSpecs();
                specs.putSpecs(specsDecl.sym,tsp);
                todo.append(env);
            }
            tsp.decl = specsDecl;
            tsp.modifiers = specsDecl.mods;
            tsp.file = specsDecl.source();
            
            JmlClassDecl jtree = null; // This is a binary class - no java class declaration
            ClassSymbol csym = specsDecl.sym; // just a symbol

            prevSource = log.useSource(specsDecl.source());
            checkTypeMatch(csym,specsDecl);
            log.useSource(prevSource);

            ListBuffer<JmlTypeClauseDecl> newlist = new ListBuffer<>();
            for (JmlTypeClauseDecl cl: tsp.decls) {
                // These are JML declarations
                JCTree tr = cl.decl;
                // We have already entered any model classes
                // but we need to enter model methods and ghost and model fields
                int n = log.nerrors;
                if (tr instanceof JmlVariableDecl) {
                    if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("JML VAR ENTER FOR " + specsDecl.name + " " + ((JmlVariableDecl)tr).name);
                    memberEnter(tr,env);
                } else if (tr instanceof JmlMethodDecl) {
                    if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("JML METH ENTER FOR " + specsDecl.name + " " + ((JmlMethodDecl)tr).name);
                    memberEnter(tr,env);
                }
                if (n != log.nerrors) {
                    // An error occurred on entering the model/ghost field or method
                    // Drop it from the list
                } else {
                    newlist.add(cl);
                }
            }
            tsp.decls = newlist;
            
            // At this point, all java and spec members are entered
            // and types have their combined specs defined
            // We still need to combine the field and method specs

            // FIXME - what about blocks

            
            matchStuff(jtree, csym, env, specsDecl);
            // First for Java fields and methods
            
//            Integer matchpos;
//            Map<Symbol,JCTree> matches = new HashMap<Symbol,JCTree>();
//            for (JCTree t: specsDecl.defs) {
//                if (t instanceof JmlVariableDecl) {
//                    VarSymbol vsym = matchAndSetFieldSpecs(jtree,csym,(JmlVariableDecl)t,matches);
//                } else if (t instanceof JmlMethodDecl) {
////                    visitMethodDef((JmlMethodDecl)t);
////                    attr.attribTypeVariables(((JmlMethodDecl)t).typarams, env); // FIXME - or  baseEnv(jtree,env)
////                    // Do this here, where we have the symbol.
////                    for (JCTypeParameter tp : ((JmlMethodDecl)t).typarams)
////                        typeAnnotate(tp, env, csym, t.pos());
////                    
////                    ListBuffer<Type> argbuf = new ListBuffer<Type>();
////                    for (List<JCVariableDecl> l = ((JmlMethodDecl)t).params; l.nonEmpty(); l = l.tail) {
////                        memberEnter(l.head, env);
////                        argbuf.append(l.head.vartype.type);
////                    }
//
//                    MethodSymbol msym = matchAndSetMethodSpecs(jtree,csym,(JmlMethodDecl)t,env, matches);
////                    if (msym != null && (matchpos=matches.put(msym,((JmlMethodDecl)t).pos)) != null) {
////                        int p = ((JmlMethodDecl)t).pos;
////                        log.error(p,"jml.duplicate.method.match",((JmlMethodDecl)t).name);
////                        log.error(matchpos,"jml.associated.decl.cf",
////                        		utils.locationString(p));
////                    }
//                }
//            }
//            
//            // Then for specs fields and methods
//            
//            for (JmlTypeClauseDecl tcd: specsDecl.typeSpecs.decls) {
//                    if (tcd.decl instanceof JmlVariableDecl) {
//                        matchAndSetFieldSpecs(jtree,csym,(JmlVariableDecl)tcd.decl, matches);
//                    } else if (tcd.decl instanceof JmlMethodDecl) {
//                        MethodSymbol msym = matchAndSetMethodSpecs(jtree,csym,(JmlMethodDecl)tcd.decl,env, matches);
////                        JmlSpecs.MethodSpecs methodSpecs = ((JmlMethodDecl)tcd.decl).methodSpecsCombined;
////                        if (methodSpecs != null && msym != null) JmlSpecs.instance(context).putSpecs(msym,methodSpecs);
//                    }
//            }
//            matches.clear();
            
            // Now we fill in the convenience fields - we could not do this
            // earlier without prematurely overwriting what might be in the
            // Java file and used as part of the specs seqeuence

            // Also fill in default method specs for anything that does not have them
            // FIXME - same for other kinds of fields? Or should we just interpret absence as default everywhere?
            
            // First for Java fields and methods
            
            if (jtree != null) for (JCTree t: jtree.defs) {
                if (t instanceof JmlVariableDecl) {
                    JmlVariableDecl v = (JmlVariableDecl)t;
                    v.fieldSpecsCombined = specs.getSpecs(v.sym);
                } else if (t instanceof JmlMethodDecl) {
                    JmlMethodDecl m = (JmlMethodDecl)t;
                    m.methodSpecsCombined = specs.getSpecs(m.sym);
                    if (m.methodSpecsCombined == null) {
                        JmlSpecs.MethodSpecs defaultSpecs = specs.defaultSpecs(m);
                        m.methodSpecsCombined = defaultSpecs;
                        defaultSpecs.cases.decl = m;
                        JmlSpecs.instance(context).putSpecs(m.sym, m.methodSpecsCombined);
                    }
                }
            }
            
            // FIXME = use a visitor to be more O-O ?
            // FIXME - unify this method with the near duplicate below

            // Then for specs fields and methods
            
            for (JmlTypeClauseDecl tcd: specsDecl.typeSpecs.decls) {
                    if (tcd.decl instanceof JmlVariableDecl) {
                        JmlVariableDecl v = (JmlVariableDecl)tcd.decl;
                        v.fieldSpecsCombined = specs.getSpecs(v.sym);
                    } else if (tcd.decl instanceof JmlMethodDecl) {
                        JmlMethodDecl m = (JmlMethodDecl)tcd.decl;
                        m.methodSpecsCombined = specs.getSpecs(m.sym);
                        if (m.methodSpecsCombined == null) {
                            JmlSpecs.MethodSpecs defaultSpecs = JmlSpecs.defaultSpecs(context,m.sym,m.pos);
                            m.methodSpecsCombined = defaultSpecs;
                            defaultSpecs.cases.decl = m;
                            JmlSpecs.instance(context).putSpecs(m.sym, m.methodSpecsCombined);
                        }
                   }
            }
            
            checkFinalTypeSpecs(specs.get(csym));
            
            
            
            
//            JmlMethodSpecs savedMethodSpecs = null;
//            JmlSpecs.FieldSpecs mostRecentFieldSpecs = null;
//            JmlVariableDecl mostRecentVarDecl = null;
//            ListBuffer<JCTree> newdefs = ListBuffer.lb();
//            for (JCTree t: specsDecl.defs) {
//                if (t instanceof JmlVariableDecl) {
//                    // make the match, check it, link it
//                    mostRecentFieldSpecs = null;
//                    JmlVariableDecl vardecl = (JmlVariableDecl)t;
//                    Symbol.VarSymbol match = null;
//                    Entry e = csym.members().lookup(vardecl.name);
//                    if (e.sym != null && e.sym.kind != Kinds.VAR && e.sym.owner == csym) {
//                        e = e.next();
//                    }
//                    if (e.sym != null && e.sym.owner == csym) {
//                        match = (Symbol.VarSymbol)e.sym;
//                    }
//                    if (match == null) {
//                        log.error(vardecl.pos(),"jml.no.var.match",vardecl.name);
//                    } else {
//                        JmlSpecs.instance(context).putSpecs(match,mostRecentFieldSpecs=new JmlSpecs.FieldSpecs(vardecl.mods));
//                        checkFieldMatch(match,vardecl);
//                        vardecl.sym = match;
//                        mostRecentVarDecl = vardecl;
//                        newdefs.append(t);
//                    }
//                } else if (t instanceof JmlMethodDecl) {
//                    mostRecentFieldSpecs = null;
//                    MethodSymbol match = matchMethod((JmlMethodDecl)t,csym);
//                    // make the match, check it, link it
//                    if (match == null) {
//                        // Error already issued
//                        // Ignore the declaration and its spec
//                        savedMethodSpecs = null;
//                    } else {
//                        if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
//                        savedMethodSpecs.decl = ((JmlMethodDecl)t);
//                        ((JmlMethodDecl)t).methodSpecs = savedMethodSpecs;
//                        if (match.owner == csym) {
//                            JmlSpecs.instance(context).putSpecs(match, savedMethodSpecs);
//                        }
//                        savedMethodSpecs = null;
//                        newdefs.append(t);
//                    }
//                } else if (t instanceof JmlMethodSpecs) {
//                    mostRecentFieldSpecs = null;
//                    savedMethodSpecs = (JmlMethodSpecs)t;
//                } else if (t instanceof JmlTypeClauseIn || t instanceof JmlTypeClauseMaps) {
//                    if (mostRecentFieldSpecs == null) {
//                        log.error(t.pos(),"jml.misplaced.var.spec",((JmlTypeClause)t).token.internedName());
//                    } else {
//                        mostRecentFieldSpecs.list.append((JmlTypeClause)t);
//                        if (t instanceof JmlTypeClauseIn) ((JmlTypeClauseIn)t).parentVar = mostRecentVarDecl;
//                    }
//                } else if (t instanceof JmlTypeClauseInitializer) {
//                    mostRecentFieldSpecs = null;
//                    if (((JmlTypeClauseInitializer)t).token == JmlToken.INITIALIZER) {
//                        if (tsp.initializerSpec != null) {
//                            log.error(t.pos,"jml.one.initializer.spec.only");
//                        } else {
//                            if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
//                            ((JmlTypeClauseInitializer)t).specs = savedMethodSpecs;
//                            tsp.initializerSpec = ((JmlTypeClauseInitializer)t);
//                        }
//                    } else {
//                        if (tsp.staticInitializerSpec != null) {
//                            log.error(t.pos,"jml.one.initializer.spec.only");
//                        } else {
//                            if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
//                            ((JmlTypeClauseInitializer)t).specs = savedMethodSpecs;
//                            tsp.staticInitializerSpec = ((JmlTypeClauseInitializer)t);
//                        }
//                    }
//                    savedMethodSpecs = null;
//                    newdefs.append(t);
//                } else if (t instanceof JmlTypeClause) {
//                    mostRecentFieldSpecs = null;
//                    // These are JML declarations
//                    if (t instanceof JmlTypeClauseDecl) {
//                        JmlTypeClauseDecl cl = (JmlTypeClauseDecl)t;
//                        JCTree tr = cl.decl;
//                        // We have already entered any model classes
//                        if (tr instanceof JmlVariableDecl) {
//                            if (utils.jmldebug) log.noticeWriter.println("JML VAR ENTER FOR " + ((JmlVariableDecl)tr).name);
//                            memberEnter(tr,env);
//                            JmlSpecs.instance(context).putSpecs(((JmlVariableDecl)tr).sym,mostRecentFieldSpecs=new JmlSpecs.FieldSpecs(((JmlVariableDecl)tr).mods));
//                        } else if (tr instanceof JmlMethodDecl) {
//                            if (utils.jmldebug) log.noticeWriter.println("JML METH ENTER FOR " + ((JmlMethodDecl)tr).name);
//                            memberEnter(tr,env);
//                            JmlMethodDecl match = (JmlMethodDecl)tr;
//                            if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
//                            savedMethodSpecs.decl = match;
//                            match.methodSpecs = savedMethodSpecs;
//                            JmlSpecs.instance(context).putSpecs(match.sym, match.methodSpecs);
//                            savedMethodSpecs = null;
//                        }
//                        newdefs.append(t);
//                    }
//                    {
//                        tsp.clauses.append((JmlTypeClause)t);
//                    }
//                } else if (t instanceof JmlClassDecl) {
//                    mostRecentFieldSpecs = null;
//                    // skip this - classes were already handled in Enter/JmlEnter
//                    newdefs.append(t);
//                } else if (t instanceof JCTree.JCBlock){
//                    // Simple semicolons turn up as empty blocks - ignore them if they do not have specs
//                    mostRecentFieldSpecs = null;
//                    if (savedMethodSpecs != null) JmlSpecs.instance(context).putSpecs((ClassSymbol)specsDecl.sym, (JCTree.JCBlock)t, savedMethodSpecs);
//                    // Initializer blocks are not allowed in specs (but are in model classes)
//                    if (savedMethodSpecs != null || !((JCTree.JCBlock)t).stats.isEmpty()) {
//                        log.error(t.pos(),"jml.initializer.block.allowed");
//                        newdefs.append(t);
//                    }
//                    savedMethodSpecs = null;
//                } else {
//                    mostRecentFieldSpecs = null;
//                    log.noticeWriter.println("  FOUND & NOT SUPPORTED " + t.getClass());  // FIXME
//                    newdefs.append(t);
//                }
//                if (savedMethodSpecs != null && !(t instanceof JmlMethodSpecs) && !(t instanceof JCTree.JCBlock)) {
//                    log.error(savedMethodSpecs.pos(),"jml.misplaced.method.specs",specsDecl.name);
//                    savedMethodSpecs = null;
//                }
//            }
//            specsDecl.defs = newdefs.toList();
//            if (savedMethodSpecs != null) {
//                log.error(savedMethodSpecs.pos(),"jml.misplaced.method.specs",specsDecl.name);
//                savedMethodSpecs = null;
//            }
                // FIXME - are method and field specs already where they belong?
                // FIXME = use a visitor to be more O-O ?
            // FIXME - unify this method with the near duplicate above
        } finally {
            addRacMethods(specsDecl.sym,env);
            resolve.setAllowJML(prevAllowJML);
            log.useSource(prevSource);
            if (utils.jmlverbose >= Utils.JMLDEBUG) {
                PrintWriter noticeWriter = log.getWriter(WriterKind.NOTICE);
                noticeWriter.println("FINISHING SPEC CLASS - COMPLETE " + specsDecl.sym.fullname);
                noticeWriter.println("   SCOPE IS " + specsDecl.sym.members());
            }
            this.env = prevEnv;
        }
    }
    
    public void checkFinalTypeSpecs(JmlSpecs.TypeSpecs tspecs) {
        for (JmlTypeClause tc: tspecs.clauses) {
            if (tc instanceof JmlTypeClauseInitializer) {
            }
        }
    }
    
    public void addRacMethods(ClassSymbol sym, Env<AttrContext> env) {
        if (!utils.rac) return;
        
        if ((sym.flags() & Flags.INTERFACE) != 0) return;  // FIXME - deal with interfaces.  ALso, no methods added to annotations
        JmlSpecs.TypeSpecs tsp = JmlSpecs.instance(context).get(sym);
        JCExpression vd = jmlF.Type(syms.voidType);
            
        JmlTree.JmlMethodDecl m = jmlF.MethodDef(
                jmlF.Modifiers(Flags.PUBLIC|Flags.SYNTHETIC),
                names.fromString(org.jmlspecs.utils.Utils.invariantMethodString),
                vd,
                List.<JCTypeParameter>nil(),
                null,
                List.<JCVariableDecl>nil(),
                List.<JCExpression>nil(),
                jmlF.Block(0,List.<JCStatement>nil()), 
                null);
        m.specsDecl = m;
        JmlTree.JmlMethodDecl ms = jmlF.MethodDef(
                jmlF.Modifiers(Flags.PUBLIC|Flags.STATIC|Flags.SYNTHETIC),
                names.fromString(org.jmlspecs.utils.Utils.staticinvariantMethodString),
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
        JCAnnotation a = tokenToAnnotationAST(JmlTokenKind.HELPER);
        m.mods.annotations = m.mods.annotations.append(a);
        ms.mods.annotations = ms.mods.annotations.append(a);
        a = tokenToAnnotationAST(JmlTokenKind.PURE);
        m.mods.annotations = m.mods.annotations.append(a);
        ms.mods.annotations = ms.mods.annotations.append(a);
        a = tokenToAnnotationAST(JmlTokenKind.MODEL);
        m.mods.annotations = m.mods.annotations.append(a);
        ms.mods.annotations = ms.mods.annotations.append(a);
        
//        tsp.clauses.append(jmlF.JmlTypeClauseDecl(m));
//        tsp.clauses.append(jmlF.JmlTypeClauseDecl(ms));
//        tsp.checkInvariantDecl = m;
//        tsp.checkStaticInvariantDecl = ms;
//        memberEnter(m,env);
//        memberEnter(ms,env);
//        setDefaultCombinedMethodSpecs(m);
//        setDefaultCombinedMethodSpecs(ms);
        
        HashSet<Name> modelMethodNames = new HashSet<Name>();
        for (JmlTypeClauseDecl td : tsp.decls) {
            if (!(td.decl instanceof JCVariableDecl)) continue;
            JCVariableDecl vdecl = (JCVariableDecl)td.decl;
            JCAnnotation modelAnnotation = JmlAttr.instance(context).findMod(vdecl.mods,JmlTokenKind.MODEL);
            if (modelAnnotation == null) continue;  // FIXME -check for model on the symbol?
            long flags = Flags.SYNTHETIC;
            flags |= (vdecl.mods.flags & (Flags.STATIC|Flags.AccessFlags));
            modelMethodNames.add(vdecl.name);
            Name name = names.fromString(Strings.modelFieldMethodPrefix + vdecl.name);
            JmlTree.JmlMethodDecl mr = (JmlTree.JmlMethodDecl)jmlF.MethodDef(jmlF.Modifiers(flags),name,vdecl.vartype,
                    List.<JCTypeParameter>nil(),List.<JCVariableDecl>nil(),List.<JCExpression>nil(),jmlF.Block(0,List.<JCStatement>nil()), null);
            mr.pos = vdecl.pos;
            utils.setJML(mr.mods);
            mr.mods.annotations = List.<JCAnnotation>of(modelAnnotation);
            memberEnter(mr,env);
            setDefaultCombinedMethodSpecs(mr);
            JmlTypeClauseDecl tcd = jmlF.JmlTypeClauseDecl(mr);
            tcd.pos = mr.pos;
            tcd.source = td.source;
            tcd.modifiers = mr.mods;
            tsp.modelFieldMethods.append(tcd);
            tsp.decls.append(tcd);
        }
    }
    
    /** For synthetic methods or methods that do not have occasion to declare
     * specs in a specification file, this sets the combined specs to be those
     * that are associated with the method declaration itself.
     * @param mdecl
     */
    protected void setDefaultCombinedMethodSpecs(JmlMethodDecl mdecl) {
        mdecl.methodSpecsCombined = new JmlSpecs.MethodSpecs(mdecl);
        specs.putSpecs(mdecl.sym,mdecl.methodSpecsCombined);
    }

    /** Checks that the jml annotations are a superset of the Java annotations (for annotations in org.jmlspecs.annotation) */
    // MUST HAVE log.useSource set to specs file!
    protected void checkSameAnnotations(Symbol sym, JCModifiers specsmods) {
        // FIXME - check for null in annotations?
        PackageSymbol p = ((JmlAttr)attr).annotationPackageSymbol;
        for (Compound a  : sym.getAnnotationMirrors()) {
            if (a.type.tsym.owner.equals(p) && utils.findMod(specsmods,a.type.tsym) == null) {
                // Only complain about mismatches of JML annotations
                log.error(specsmods.pos,"jml.missing.annotation",a);
            }
        }
    }

    /** Checks that the jml annotations are a superset of the Java annotations (for annotations in org.jmlspecs.annotation) */
    // MUST HAVE log.useSource set to specs file!
    protected void checkSameAnnotations(JCModifiers javaMods, JCModifiers specsmods) {
        PackageSymbol p = ((JmlAttr)attr).annotationPackageSymbol;
        for (JCAnnotation a: javaMods.getAnnotations()) {
            if (a.type.tsym.owner.equals(p) && utils.findMod(specsmods,a.type.tsym) == null) {
                // Only complain about mismatches of JML annotations
                log.error(specsmods.pos,"jml.missing.annotation",a);
            }
        }
    }

    public void checkFieldMatch(JmlVariableDecl javaField, VarSymbol javaSym, JmlVariableDecl specField) {
        if (javaField == specField) return;
        // Presume that we can't get here unless the names are the same
        JavaFileObject prev = log.currentSourceFile();
        log.useSource(specField.sourcefile);

        // Check that the modifiers are the same
        long javaFlags = javaSym.flags();
        long specFlags = specField.mods.flags;
        boolean isInterface = (javaFlags & Flags.INTERFACE) != 0;
        long diffs = (javaFlags ^ specFlags)&(isInterface? Flags.InterfaceVarFlags : Flags.VarFlags);
        if (diffs != 0) {
            log.error(specField.pos(),"jml.mismatched.field.modifiers", specField.name, javaSym.enclClass().getQualifiedName()+"."+javaSym.name,Flags.toString(diffs));  // FIXME - test this
        }

        // check for no initializer
        if (specField.getInitializer() != null && specField != javaField &&
                !utils.isJML(specField.mods)) {
            log.error(specField.getInitializer().pos(),"jml.no.initializer.in.specs",javaSym.enclClass().getQualifiedName()+"."+javaSym.name);
        }
        
        // Match in the types is checked in JmlAttr.checkVarMods

// FIXME - attribAnnotations, compare annotations
        //  FIXME _ this needs to be implements
        // FIXME - what if an annotation is declared within the class?
        //            attr.attribAnnotationTypes(javaField.mods.annotations, env);
        //            checkSameAnnotations(javaField.mods,specField.mods);

        log.useSource(prev);
    }
    
    
    public void checkTypeMatch(JmlClassDecl javaDecl, JmlClassDecl specsClassDecl) {
        
        ClassSymbol javaClassSym = javaDecl.sym;
        JmlSpecs.TypeSpecs combinedTypeSpecs = specs.get(javaClassSym);
        
        // If these are the same declaration we don't need to check 
        // that the spec decl matches the java decl
        //if (javaDecl == specsClassDecl) return;

        // Check annotations
        
        if (javaDecl != specsClassDecl) {
            // Check that modifiers are the same
            long matchf = javaClassSym.flags();
            long specf = combinedTypeSpecs.modifiers.flags;
            long diffs = (matchf ^ specf)&Flags.ClassFlags; // Includes whether both are class or both are interface
            if (diffs != 0) {
                boolean isInterface = (matchf & Flags.INTERFACE) != 0;
                boolean isEnum = (matchf & Flags.ENUM) != 0;
                if ((Flags.ABSTRACT & matchf & ~specf) != 0 && isInterface) diffs &= ~Flags.ABSTRACT; 
                if ((Flags.STATIC & matchf & ~specf) != 0 && isEnum) diffs &= ~Flags.STATIC; 
                if ((Flags.FINAL & matchf & ~specf) != 0 && isEnum) diffs &= ~Flags.FINAL; 
                if (diffs != 0) log.error(specsClassDecl.pos(),"jml.mismatched.modifiers", specsClassDecl.name, javaClassSym.fullname, Flags.toString(diffs));  // FIXME - test this
                // FIXME - how can we tell where in which specs file the mismatched modifiers are
                // SHould probably check this in the combining step
            }
            // FIXME - this is needed, but it is using the environment from the java class, not the 
            // spec class, and so it is using the import statements in the .java file, not those in the .jml file
            attr.attribAnnotationTypes(specsClassDecl.mods.annotations, baseEnv(javaDecl,env));  // FIXME - this is done later; is it needed here?

            JavaFileObject prev = log.useSource(specsClassDecl.source());
            checkSameAnnotations(javaDecl.mods,specsClassDecl.mods);
            log.useSource(prev);
            // FIXME - check that both are Enum; check that both are Annotation
        }
        if (specsClassDecl.source() == null || specsClassDecl.source().getKind() == JavaFileObject.Kind.SOURCE){
            // This is already checked in enterTypeParametersForBinary (for binary classes)
            List<Type> t = ((Type.ClassType)javaClassSym.type).getTypeArguments();
            List<JCTypeParameter> specTypes = specsClassDecl.typarams;
            if (t.size() != specTypes.size()) {
                log.error(specsClassDecl.pos(),"jml.mismatched.type.arguments",javaClassSym.fullname,javaClassSym.type.toString());
            }
            // FIXME - check that the names and bounds are the same
        }
    }
    
    public void checkTypeMatch(ClassSymbol javaClassSym, JmlClassDecl specsClassDecl) {
        
        // Check annotations
        JmlSpecs.TypeSpecs combinedTypeSpecs = specs.get(javaClassSym);
        JavaFileObject prev = log.useSource(specsClassDecl.source());
        
        {
            // Check that modifiers are the same
            long matchf = javaClassSym.flags();
            long specf = combinedTypeSpecs.modifiers.flags;
            long diffs = (matchf ^ specf)&Flags.ClassFlags; // Includes whether both are class or both are interface
            if (diffs != 0) {
                boolean isInterface = (matchf & Flags.INTERFACE) != 0;
                boolean isEnum = (matchf & Flags.ENUM) != 0;
                if ((Flags.ABSTRACT & matchf & ~specf) != 0 && isInterface) diffs &= ~Flags.ABSTRACT; 
                if ((Flags.STATIC & matchf & ~specf) != 0 && isEnum) diffs &= ~Flags.STATIC; 
                if ((Flags.FINAL & matchf & ~specf) != 0 && isEnum) diffs &= ~Flags.FINAL; 
                if ((diffs & Flags.FINAL) != 0 && javaClassSym.isAnonymous()) diffs &= ~Flags.FINAL;
                if (diffs != 0) log.error(specsClassDecl.pos(),"jml.mismatched.modifiers", specsClassDecl.name, javaClassSym.fullname, Flags.toString(diffs));  // FIXME - test this
            }
            // FIXME - check that both are Enum; check that both are Annotation
            checkSameAnnotations(javaClassSym,specsClassDecl.mods);
        }
        {
            List<Type> t = ((Type.ClassType)javaClassSym.type).getTypeArguments();
            List<JCTypeParameter> specTypes = specsClassDecl.typarams;
            if (t.size() != specTypes.size()) {
                log.error(specsClassDecl.pos(),"jml.mismatched.type.arguments",javaClassSym.fullname,javaClassSym.type.toString());
            }
            // FIXME - check that the names and bounds are the same
        }
        log.useSource(prev);
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
        Type computedResultType = null;
        Env<AttrContext> localEnv = null;
        if (msym != null) {
            localEnv = methodEnv(tree, env);
            computedResultType = msym.getReturnType();
        } else {
            // Copied from MemberEnter.visitMethodDef which can't be called directly
            Scope enclScope = enter.enterScope(env);
            mtemp = new MethodSymbol(0, tree.name, null, enclScope.owner);
            //m.flags_field = chk.checkFlags(tree.pos(), tree.mods.flags, m, tree);
            tree.sym = mtemp;
            localEnv = methodEnv(tree, env);

            // Compute the method type
            mtemp.type = signature(msym, tree.typarams, tree.params,
                               tree.restype, tree.recvparam, tree.thrown,
                               localEnv);
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
            annotateLater(tree.mods.annotations, localEnv, mtemp, tree.pos()); // FIXME - is this the right position
            if (tree.defaultValue != null)
                annotateDefaultValueLater(tree.defaultValue, localEnv, mtemp);
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
            paramTypes.append(param.vartype.type);
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
        jmlResolve.errorOccurred = false;
        try {
            s = jmlResolve.resolveMethod(tree.pos(), env, tree.name, paramTypes.toList(),typaramTypes.toList());
        } finally {
            jmlResolve.silentErrors = prevSilentErrors;
            if (jmlResolve.errorOccurred) s = null;
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
            if (localEnv != null) localEnv.info.scope.owner = match;
            for (List<JCVariableDecl> l = tree.params; l.nonEmpty(); l = l.tail) {
                JCVariableDecl param = l.head;
                param.sym.owner = match;
            }
        }
        
        if (match != null) {
            // Check that the return types are the same
            boolean hasTypeParameters = specMethod.getTypeParameters().size() != 0;  // FIXME - figure out how to do proper type matching with type parameters; may require they be names the same (if both are source)
            if (!hasTypeParameters && specMethod.restype != null) { // not a constructor
                if (!Types.instance(context).isSameType(match.getReturnType(),computedResultType)) {
                    utils.error(specMethod.sourcefile,specMethod.restype.pos(),
                            "jml.mismatched.return.type",
                            match.enclClass().fullname + "." + match.toString(),
                            computedResultType, match.getReturnType());
                    // FIXME - add an associated declaration
                }
            }

        }
        
        if (match == null) {
            if (complain && (specMethod.mods.flags & Flags.GENERATEDCONSTR) == 0 && !inModelTypeDeclaration
                    && utils.findMod(specMethod.mods,JmlTokenKind.MODEL) == null) {
                log.error(specMethod.pos(),"jml.no.method.match",
                    csym.flatName() + "." + mtemp);
            }
        } else {
            // FIXME - do we need to check for model methods, and that they match?
//            boolean isModel = JmlAttr.instance(context).findMod(specMethod.mods,JmlToken.MODEL) != null;
//            boolean isMatchModel = match.attribute(((JmlAttr)attr).tokenToAnnotationSymbol.get(JmlToken.MODEL)) != null;
//            if (isModel == isMatchModel) {
            
                // Attributes the annotations and adds them to the given MethodSymbol, if they are not already present
                addAnnotations(match,env,specMethod.mods);  // Might repeat annotations, so we use the conditional call  // FIXME - we aren't using the conditional call
//            } else {
//                // We have a model and non-model method with matching signatures.  Declare them
//                // non-matching and wait for an error when the model method is entered.
//                match = null;
//            }
        }
        localEnv.info.scope.leave();
        return match;


//        if (match != null) return match;
//
//        //attribAnnotations(javaClass,method.mods); // FIXME
//
//        //        List<Type> tvars = enter.classEnter(specMethod.typarams, env);
//        //        Attr.instance(context).attribTypeVariables(specMethod.typarams, env);
//
//        //        ListBuffer<Type> tatypes = ListBuffer.<Type>lb();  // FIXME - use TreeInfo method
//        //        for (JCTypeParameter tp: specMethod.typarams) {
//        //            tatypes.append(tp.type);
//        //        }
//
//        //Attr.instance(context).attribBounds(specMethod.typarams); //, Enter.instance(context).getEnv(javaClassDecl.sym));
//        int n = specMethod.getParameters().size();
//        //        ListBuffer<Type> ptypes = ListBuffer.<Type>lb();
//        //        for (int i=0; i<n; i++) {
//        //            Attr.instance(context).attribType(specMethod.getParameters().get(i).vartype, Enter.instance(context).getEnv(javaClassDecl.sym));
//        //            ptypes.append(specMethod.getParameters().get(i).vartype.type);
//        //        }
//        match = null;
//        try {
//            if (utils.jmldebug) log.noticeWriter.println("  CLASS " + csym + " SPECS HAVE METHOD " + specMethod.name);
//            boolean bbb = false;
//            //            if (msym != null && msym.name.toString().startsWith("compareTo")) {
//            //                System.out.println(msym + " " + csym); bbb = true;
//            //            }
//
//            java.util.List<MethodSymbol> checked = new java.util.LinkedList<MethodSymbol>();
//            loop: for (Scope.Entry te = csym.members().lookup(specMethod.name); te.sym != null; te = te.next()) {
//                MethodSymbol t = (MethodSymbol)te.sym;
//                checked.add(t);
//                // FIXME - check that this does not match inherited methods
//                if (t == specMethod.sym) {  // Unfortunately SYmbol does not have a nice equals method defined
//                    match = t;
//                    break;
//                }
//                if (Types.instance(context).isSameType(t.type,specMethod.sym.type)) {
//                    match = t;
//                    break;
//                }
////                if (t instanceof MethodSymbol  && false) {
////                    MethodSymbol javaSym = (MethodSymbol)t;
////                    checked.add(javaSym);
////                    //if (t.name.toString().startsWith("compareTo")) {
////                    //   if (bbb) System.out.println("ZZZ " + javaSym);
////                    //}
////                    if (javaSym.equals(msym)) {
////                        match = javaSym;
////                        break;
////                    }
////                    if (!javaSym.name.equals(specMethod.name)) continue;
////                    if (javaSym.getParameters().size() != specMethod.getParameters().size()) continue;
////                    if (javaSym.getTypeParameters().size() != specMethod.getTypeParameters().size()) continue;
////
////                    // If there are type parameters we don't know how to do the comparison
////
////                    if (javaSym.getTypeParameters().size() == 0) {
////
////                        for (int i=0; i<n; i++) {
////                            if (!Types.instance(context).isSameType(javaSym.getParameters().get(i).type,
////                                    specMethod.getParameters().get(i).vartype.type)) continue loop;
////                        }
////
////                        if (javaSym.getTypeParameters().size() != 0) {
////                            Iterator<TypeSymbol> jtpi = javaSym.getTypeParameters().iterator();
////                            Iterator<JCTypeParameter> stpi = specMethod.getTypeParameters().iterator();
////                            while (jtpi.hasNext()) {
////                                TypeSymbol jtp = jtpi.next();
////                                JCTypeParameter stp = stpi.next();
////                                if (!jtp.name.equals(stp.getName())) {
////                                    log.noticeWriter.println("NAMES NOT SAME " + jtp + " " + stp);  // FIXME _ test this
////                                }
////                                // FIXME check bounds as well
////
////                                stp.type = jtp.type;  // Make sure they have precisely the same type
////                            }
////                        }
////                    }
////                    match = javaSym;
////                }
//            }
//
//            // Check for a match against Object methods
//            if (match == null) {
//                // Make a string of the signatures of the Java methods that we are comparing against
//                // and that do not match, to make a nice error message
//                StringBuilder sb = new StringBuilder();
//                sb.append("\n    Signatures found:");
//                for (MethodSymbol m : checked) {
//                    sb.append("\n\t\t\t").append(m.toString());
//                }
//                if (checked.isEmpty()) sb.append("   <none>");
//                log.error(specMethod.pos(),"jml.no.method.match",
//                        msym.enclClass().flatName() + "." + msym ,
//                        sb.toString());
//                checked.clear();
//            } else if (match != specMethod.sym) { // If they are equal there is nothing to do
//                checkMethodMatch(match,specMethod,csym);
//                addAnnotations(match,env,specMethod.mods);  // Might repeat annotations, so we use the conditional call  // FIXME - we aren't using the conditional call
//            }
//        } catch (Exception e) {
//            log.noticeWriter.println("METHOD EXCEOPTION " + e);
//        }
//        return match;
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


    /** Checks that the modifiers and annotations in the .java and .jml declarations match appropriately,
     * for both the method declaration and any parameter declarations;
     * does not do any semantic checks of whether the modifiers or annotations are allowed.
     */
    public void checkMethodMatch(@Nullable JmlMethodDecl javaMatch, MethodSymbol match, JmlMethodDecl specMethodDecl, ClassSymbol javaClassSymbol) {
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
                        log.error(specMethodDecl.pos(),"jml.mismatched.method.modifiers", specMethodDecl.name, match.toString(), Flags.toString(diffs));
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
                    log.error("jml.internal", "Java and jml declarations have different numbers of arguments, even though they have been type matched");
                }
            }

            checkSameAnnotations(match,specMethodDecl.mods);
            Iterator<JCVariableDecl> jmliter = specMethodDecl.params.iterator();
            Iterator<Symbol.VarSymbol> javaiter = match.getParameters().iterator();
            while (javaiter.hasNext() && jmliter.hasNext()) {
                Symbol.VarSymbol javaparam = javaiter.next();
                JmlVariableDecl jmlparam = (JmlVariableDecl)jmliter.next();
                checkSameAnnotations(javaparam,jmlparam.mods);
            }


            boolean isGhost = JmlAttr.instance(context).findMod(specMethodDecl.mods,JmlTokenKind.GHOST) != null;
            boolean isModel = JmlAttr.instance(context).findMod(specMethodDecl.mods,JmlTokenKind.MODEL) != null;

            //            if (!utils.isJML(specMethodDecl.mods)
            //                    && (isGhost||isModel)) {
            //                // The declaration in the spec file is a Java declaration, but has either ghost or model annotations
            //                log.error(specMethodDecl.pos,"jml.ghost.model.on.java");   // FIXME - methods are never ghost!!!
            //            }  // Tested during attribution
            //            if (utils.isJML(specMethodDecl.mods)
            //                    && !(isGhost||isModel)) {
            //                // The declaration in the spec file is a Java declaration, but has either ghost or model annotations
            //                log.error(specMethodDecl.pos,"jml.missing.ghost.model");
            //            }


            // Check that parameter names are the same (a JML requirement to avoid having to rename within specs)
            if (javaMatch != null) {
                for (int i = 0; i<javaMatch.getParameters().size(); i++) {
                    JCTree.JCVariableDecl javaparam = javaMatch.getParameters().get(i);
                    JCTree.JCVariableDecl jmlparam = specMethodDecl.params.get(i);
                    if (!javaparam.name.equals(jmlparam.name)) {
                        log.error(jmlparam.pos(),"jml.mismatched.param.names",i,
                                match.enclClass().fullname + "." + match.toString(),
                                javaparam.name, jmlparam.name);
                    }
                }

            } else if (JmlCompilationUnit.isForSource(modeOfFileBeingChecked)) {
                for (int i = 0; i<match.getParameters().size(); i++) {
                    Symbol.VarSymbol javasym = match.getParameters().get(i);
                    JCTree.JCVariableDecl jmlparam = specMethodDecl.params.get(i);
                    if (!javasym.name.equals(jmlparam.name)) {
                        log.error(jmlparam.pos(),"jml.mismatched.param.names",i,
                                match.enclClass().fullname + "." + match.toString(),
                                javasym.name, jmlparam.name);
                    }
                }
            }

            // Check that the specification method has no body if it is not a .java file
            if (specMethodDecl.body != null && specMethodDecl.sourcefile.getKind() != Kind.SOURCE
                    && !((JmlAttr)attr).isModel(specMethodDecl.mods)
                    && !inModelTypeDeclaration
                    && match.owner == javaClassSymbol   // FIXME - this is here to avoid errors on methods of anonymous classes within specifications within a .jml file - it might not be fully robust
                    // FIXME - should test other similar locations - e.g. model classes, model methods, methods within local class declarations in model methods or methods of model classes
                    && (specMethodDecl.mods.flags & (Flags.GENERATEDCONSTR|Flags.SYNTHETIC)) == 0) {
                log.error(specMethodDecl.body.pos(),"jml.no.body.allowed",match.enclClass().fullname + "." + match.toString());
            }


            // FIXME - from a previous comparison against source
//            // A specification method may not have a body.  However, the spec
//            // method declaration may also be identical to the java method (if the
//            // java file is in the specification sequence) - hence the second test.
//            // There is an unusual case in which a method declaration is duplicated
//            // in a .java file (same signature).  In that case, there is already
//            // an error message, but the duplicate will be matched against the
//            // first declaration at this point, though they are different
//            // delcarations (so the second test will be true).  Hence we include the
//            // 3rd test as well. [ TODO - perhaps we need just the third test and not the second.]
//            if (specMethodDecl.body != null && match != specMethodDecl
//                    && match.sourcefile != specMethodDecl.sourcefile
//                    && (specMethodDecl.mods.flags & (Flags.GENERATEDCONSTR|Flags.SYNTHETIC)) == 0) {
//                log.error(specMethodDecl.body.pos(),"jml.no.body.allowed",match.sym.enclClass().fullname + "." + match.sym.toString());
//            }
//            
//            // Check that the return types are the same
//            if (specMethodDecl.restype != null) { // not a constructor
//                if (specMethodDecl.restype.type == null) Attr.instance(context).attribType(specMethodDecl.restype, match.sym.enclClass());
////                if (match.name.toString().equals("defaultEmpty")) {
////                    log.noticeWriter.println(match.name);
////                }
//                if (!Types.instance(context).isSameType(match.restype.type,specMethodDecl.restype.type)) {
//                    // FIXME - when the result type is parameterized in a static method, the java and spec declarations
//                    // end up with different types for the parameter.  Is this also true for the regular parameters?  
//                    // FIXME - avoud the probloem for now.
//                    if (!(specMethodDecl.restype.type.getTypeArguments().head instanceof Type.TypeVar))
//                    log.error(specMethodDecl.restype.pos(),"jml.mismatched.return.type",
//                            match.sym.enclClass().fullname + "." + match.sym.toString(),
//                            specMethodDecl.restype.type,match.restype.type);
//                }
//            }

        } finally {
            log.useSource(prev);
        }
            // FIXME - what about covariant return types ?????
            
            // FIXME - check that JML annotations are ok
    }
    
    /** Attributes the annotations and adds them to the given Symbol, if they are not already present */
    public void addAnnotations(Symbol sym, Env<AttrContext> env, JCTree.JCModifiers mods) {
        if (env == null) {
            log.error("jml.internal","Unexpected NULL ENV in JmlMemberEnter.addAnnotations" + sym);
        }
        annotateLaterConditional(mods.annotations, env, sym, mods.pos()); // FIXME - is this an OK position?
    }

//    
//    // We have to do the equivalent of complete, except that the Java class is
//    // already completed and all we want to do is the spec part.  Note that 
//    // super.complete is for class symbols.
//    public void completeSpecCUForBinary(Env<AttrContext> specEnv) {
//        Env<AttrContext> prevEnv = env;
//        env = specEnv;
//        JavaFileObject prev = log.useSource(specEnv.toplevel.sourcefile);
//        specEnv.toplevel.accept(this); // process imports into current env
//        
//        int prevMode = modeOfFileBeingChecked;
//        modeOfFileBeingChecked = ((JmlCompilationUnit)specEnv.toplevel).mode;
//
//        // FIXME - here we are doing primary and secondary types - is that what we want?
//        for (JCTree dd: ((JmlCompilationUnit)specEnv.toplevel).defs) {
//            // There are also import declarations in defs
//            if (dd instanceof JmlClassDecl) {
//                env = specEnv; //enter.typeEnvs.get(((JmlClassDecl)dd).sym); - binary sym does not have a toplevel tree
//                JmlClassDecl d = (JmlClassDecl)dd;
//                completeSpecClassForBinary(d);
//            }
//        }
//        todo.append(env); // So the .jml file is attributed
//
//        // Model declarations will already have been processed as regular source classes
//        
//        // We need to put the compilation unit on the todo list for attribution
//        // WAS: Todo.instance(context).append(enter.typeEnvs.get(((JmlCompilationUnit)env.tree).packge));
//        //Todo.instance(context).append(specEnv); - NO - we put the individual classes on, in completeSpecClassForBInary
//        env = prevEnv;
//        log.useSource(prev);
//        modeOfFileBeingChecked = prevMode;
//    }
//    
//    public void completeSpecClassForBinary(JmlClassDecl classDecl) {
//        Env<AttrContext> prev = env;
//        ClassSymbol classSym = classDecl.sym;
//        if (classSym == null) {
//            // This happens when a Java class declaration in the spec file has no
//            // match in the binary class.  So we just skip it.  It has already
//            // been reported in JmlEnter.
//            return;
//        }
//        if (classSym.completer != null) {
//            classSym.completer.complete(classSym);
//        }
//        env = classDecl.env;
//        attr.attribAnnotationTypes(classDecl.mods.annotations, baseEnv(classDecl,env));  // FIXME - this is done later; is it needed here?
//        
//        { // Copied (and edited) from MemberEnter.java 
//            JmlAttr attr = JmlAttr.instance(context);
//            ClassSymbol c = classSym;
//            ClassType ct = (ClassType)c.type;
//            Env<AttrContext> env = classDecl.env;
//            JCClassDecl tree = classDecl;
////            boolean wasFirst = isFirst;
////            isFirst = false;
//
//            JavaFileObject prevv = log.useSource(env.toplevel.sourcefile);
//            try {
//                // Save class environment for later member enter (2) processing.
////                halfcompleted.append(env);
//
//                // Mark class as not yet attributed.
//                c.flags_field |= UNATTRIBUTED;
//
//                // If this is a toplevel-class, make sure any preceding import
//                // clauses have been seen.
////                if (c.owner.kind == PCK) {
////                    memberEnter(env.toplevel, env.enclosing(JCTree.TOPLEVEL));
////                    todo.append(env);
////                }
//
////                if (c.owner.kind == TYP)
////                    c.owner.complete();  // FIXME - should this force a loading of binary specs
//
//                // create an environment for evaluating the base clauses
//                Env<AttrContext> baseEnv = baseEnv(tree, env);
//
//                // Determine supertype.
//                Type supertype =
//                    (tree.extending != null)
//                    ? attr.attribBase(tree.extending, baseEnv, true, false, true)
////                    : ((tree.mods.flags & Flags.ENUM) != 0 && !target.compilerBootstrap(c))
////                    ? attr.attribBase(enumBase(tree.pos, c), baseEnv,
////                                      true, false, false)
//                    : (c.fullname == names.java_lang_Object)
//                    ? Type.noType
//                    : syms.objectType;
////                ct.supertype_field = supertype;
//
//                // Determine interfaces.
//                ListBuffer<Type> interfaces = new ListBuffer<Type>();
//                Set<Type> interfaceSet = new HashSet<Type>();
//                List<JCExpression> interfaceTrees = tree.implementing;
////              if ((tree.mods.flags & Flags.ENUM) != 0 && target.compilerBootstrap(c)) {
////                    // add interface Comparable<T>
////                    interfaceTrees =
////                        interfaceTrees.prepend(make.Type(new ClassType(syms.comparableType.getEnclosingType(),
////                                                                       List.of(c.type),
////                                                                       syms.comparableType.tsym)));
////                    // add interface Serializable
////                    interfaceTrees =
////                        interfaceTrees.prepend(make.Type(syms.serializableType));
////                }
//                for (JCExpression iface : interfaceTrees) {
//                    Type i = attr.attribBase(iface, baseEnv, false, true, true);
////                    if (i.tag == CLASS) {
////                        interfaces.append(i);
////                        chk.checkNotRepeated(iface.pos(), types.erasure(i), interfaceSet);
////                    }
//                }
////                if ((c.flags_field & ANNOTATION) != 0)
////                    ct.interfaces_field = List.of(syms.annotationType);
////                else
////                    ct.interfaces_field = interfaces.toList();
//
////                if (c.fullname == names.java_lang_Object) {
////                    if (tree.extending != null) {
////                        chk.checkNonCyclic(tree.extending.pos(),
////                                           supertype);
////                        ct.supertype_field = Type.noType;
////                    }
////                    else if (tree.implementing.nonEmpty()) {
////                        chk.checkNonCyclic(tree.implementing.head.pos(),
////                                           ct.interfaces_field.head);
////                        ct.interfaces_field = List.nil();
////                    }
////                }
//
//                // Annotations.
//                // In general, we cannot fully process annotations yet,  but we
//                // can attribute the annotation types and then check to see if the
//                // @Deprecated annotation is present.
//                attr.attribAnnotationTypes(tree.mods.annotations, baseEnv);
////                if (hasDeprecatedAnnotation(tree.mods.annotations))
////                    c.flags_field |= DEPRECATED;
//                annotateLater(tree.mods.annotations, baseEnv, c, tree.mods.pos());// FIXME - si this an OK position?
//                    // The call above nulls out the attributes field; it is recomputed
//                    // when annotate.flush() is called.  But this has the effect of
//                    // deleting any annotations that were recovered from the
//                    // binary file.  (FIXME) I'm not sure we want that.
//                
////                chk.checkNonCyclic(tree.pos(), c.type);
//
//                attr.attribTypeVariables(tree.typarams, baseEnv);
//
//                // Add default constructor if needed.
////                if ((c.flags() & INTERFACE) == 0 && !binary && // DRC added for now
////                    !TreeInfo.hasConstructors(tree.defs)) {
////                    List<Type> argtypes = List.nil();
////                    List<Type> typarams = List.nil();
////                    List<Type> thrown = List.nil();
////                    long ctorFlags = 0;
////                    boolean based = false;
////                    if (c.name.isEmpty()) {
////                        JCNewClass nc = (JCNewClass)env.next.tree;
////                        if (nc.constructor != null) {
////                            Type superConstrType = types.memberType(c.type,
////                                                                    nc.constructor);
////                            argtypes = superConstrType.getParameterTypes();
////                            typarams = superConstrType.getTypeArguments();
////                            ctorFlags = nc.constructor.flags() & VARARGS;
////                            if (nc.encl != null) {
////                                argtypes = argtypes.prepend(nc.encl.type);
////                                based = true;
////                            }
////                            thrown = superConstrType.getThrownTypes();
////                        }
////                    }
////                    JCTree constrDef = DefaultConstructor(make.at(tree.pos), c,
////                                                        typarams, argtypes, thrown,
////                                                        ctorFlags, based);
////                    tree.defs = tree.defs.prepend(constrDef);
////                }
//
//                // If this is a class, enter symbols for this and super into
//                // current scope.
//                if (true) {  // Allow this in interfaces
//                    VarSymbol thisSym =
//                        new VarSymbol(FINAL | HASINIT, names._this, c.type, c);
//                    thisSym.pos = Position.FIRSTPOS;
//                    env.info.scope.enter(thisSym);
//                }
//                if ((c.flags_field & INTERFACE) == 0) {
//                    if (ct.supertype_field.getTag() == CLASS) {
//                        VarSymbol superSym =
//                            new VarSymbol(FINAL | HASINIT, names._super,
//                                          ct.supertype_field, c);
//                        superSym.pos = Position.FIRSTPOS;
//                        env.info.scope.enter(superSym);
//                    }
//                }
//
//                // check that no package exists with same fully qualified name,
//                // but admit classes in the unnamed package which have the same
//                // name as a top-level package.
////                if (checkClash &&
////                    c.owner.kind == PCK && c.owner != syms.unnamedPackage &&
////                    reader.packageExists(c.fullname))
////                    {
////                        log.error(tree.pos, "clash.with.pkg.of.same.name", c);
////                    }
//
//            } catch (CompletionFailure ex) {
//                Check.instance(context).completionError(tree.pos(), ex);
//            } finally {
//                log.useSource(prevv);
//                annotate.flush();
//            }
//
//        }
//
//        //env = enter.classEnv(d,env);
//        //enter.typeEnvs.put(d.sym,env);
//        
//        if (classDecl.sym.members() instanceof Scope.ErrorScope) {
//            // Errors occured making this symbol unresolveable
//            // Catastrophes await if we proceed.  If errors have been reported
//            // we figure that is the cause.
//            if (log.nerrors == 0) log.error("jml.internal","Type " + classDecl.sym + " is unexpectedly lacking proper scope information");
//            return;
//        }
//        
//        // FIXME - use a tree walker?  do we need to do nested classes?
//        Map<Symbol,Integer> matchedSyms = new HashMap<Symbol,Integer>();
//        ListBuffer<JCTree> remove = null;
//        for (JCTree t: classDecl.defs) {
//            if (t instanceof JmlVariableDecl) {
//                JmlVariableDecl vd = (JmlVariableDecl)t;
//                VarSymbol vsym = findVarMatch(classDecl.sym,vd.name);
//                if (utils.isJML(vd.mods)) {
//                    // misplaced JML declaration
//                } else if (vsym == null) {
//                    // Java declaration in spec file does not match anything in the binary file
//                    log.error(vd.pos,"jml.no.var.match",vd.name);
//                    if (remove == null) remove = new ListBuffer<JCTree>();
//                    remove.append(t);
//                } else {
//                    Integer matchpos;
//                    if ((matchpos=matchedSyms.put(vsym,vd.pos)) != null) {
//                        log.error(vd.pos,"jml.duplicate.var.match",vd.name);
//                        log.error(matchpos,"jml.associated.decl.cf",
//                        		utils.locationString(vd.pos));
//                    }
//                    vd.sym = vsym;
//                    checkFieldMatch(vsym,vd);
//                    // FIXME - do we need to asjust the flags as in visitVarDef
//
//                    JmlSpecs.FieldSpecs fspecs = specs.getSpecs(vsym);
//                    if (fspecs == null) {
//                        specs.putSpecs(vsym, fspecs = new JmlSpecs.FieldSpecs(vd.mods));
//                    } else {
//                        fspecs.mods = vd.mods;
//                        if (vd.fieldSpecs != null) fspecs.list.appendList(vd.fieldSpecs.list);
//                    }
//                }
//
//            } else if (t instanceof JmlMethodDecl) {
//                JmlMethodDecl md = (JmlMethodDecl)t;
////                if (md.name.toString().equals("equals")) {
////                    log.noticeWriter.println(md.name);
////                }
//
//                MethodSymbol msym = matchAndCombineMethodSpecs(null,classDecl.sym,md,env);
//                //if (msym != null) checkMethodMatch(msym,md,d.sym);  // Done in the call above
//                //MethodSymbol msym = matchMethod(md,d.sym,env);
//                if (utils.isJML(md.mods)) {
//                    // misplaced JML declaration
//                } else if (msym == null) {
//                    // Already complained about in matchMethod via matchAndCombineMethodSpecs
//                    // Java declaration in spec file does not match anything in the binary file
//                    //log.error(md.pos,"jml.no.method.match",md.name,"");
//                    if (remove == null) remove = new ListBuffer<JCTree>();
//                    remove.append(t);
//                } else {
//                    md.sym = msym;
//                    // checkMethodMatch already called in matchMethod via matchAndCombineMethodSpecs
//                    //checkMethodMatch(msym,md,d.sym);
//                    
//                    JmlMethodSpecs mdspecs = md.cases;
//                    JmlSpecs.MethodSpecs mspecs = specs.getSpecs(msym);
//                    if (mspecs == null) {
//                        specs.putSpecs(msym, mspecs = new JmlSpecs.MethodSpecs(md.mods,mdspecs));
//                    } else {
//                        mspecs.cases.decl = md;
//                        mspecs.cases.cases = mdspecs != null ? mdspecs.cases : List.<JmlSpecificationCase>nil();
//                    }
//
//                    // FIXME - attach specs to symbol
//                }
//                
//                
//            } else if (t instanceof JmlClassDecl) {
//                
//                // skip - these are handled by their individual completion calls
//                
//            } else {
//                log.getWriter(WriterKind.NOTICE).println("Unhandled declaration in spec class for binary: " + t.getClass());
//            }
//        }
//        matchedSyms.clear();
//        if (remove != null) {
//            ListBuffer<JCTree> newdefs = new ListBuffer<JCTree>();
//            List<JCTree> rem = remove.toList();
//            for (JCTree t: classDecl.defs) {
//                if (t != rem.head) newdefs.append(t);
//                else rem = rem.tail;
//            }
//            classDecl.defs = newdefs.toList();
//        }
//        // JML fields and methods
//        
//        boolean previousAllow = resolve.setAllowJML(true);
//        if (classDecl.typeSpecsCombined == null) classDecl.typeSpecsCombined = specs.getSpecs(classDecl.sym);
//        for (JmlTypeClause t: classDecl.typeSpecsCombined.clauses) {
//            if (t instanceof JmlTypeClauseDecl) {
//                JmlTypeClauseDecl tcd = (JmlTypeClauseDecl)t;
//                if (tcd.decl instanceof JmlVariableDecl) {
//                    JmlVariableDecl vd = (JmlVariableDecl)tcd.decl;
//                    VarSymbol vsym = findVarMatch(classDecl.sym,vd.name);
//                    if (!utils.isJML(vd.mods)) {
//                        // INTENRAL ERROR
//                    } else if (vsym != null) {
//                        log.error(vd.pos,"jml.duplicate.var.binary.match",vd.name);
//                    } else {
//                        // Is ghost or model ?
//                        // Enter the field
//                        visitVarDef(vd);
//                        // Model/ghost fields have their own specs - FIXME: move this into visitVarDef?
//                        if (vd.fieldSpecs == null) {
//                            vd.fieldSpecs = vd.fieldSpecsCombined = specs.getSpecs(vd.sym);
//                        } else {
//                            vd.fieldSpecsCombined = vd.fieldSpecs;
//                            specs.putSpecs(vd.sym,vd.fieldSpecsCombined);
//                        }
//                    }
//
//                } else if (tcd.decl instanceof JmlMethodDecl) {
//                    JmlMethodDecl vd = (JmlMethodDecl)tcd.decl;
//                    MethodSymbol vsym = matchMethod(vd,classDecl.sym,env,false);
//                    if (!utils.isJML(vd.mods)) {
//                        // INTENRAL ERROR
//                    } else if (vsym != null) {// FIXME -=test this error message
//                        log.error(vd.pos,"jml.duplicate.method.binary.match",vd.name);
//                    } else {
//                        // Is ghost or model ?
//                        // Enter the method
//                        visitMethodDef(vd);
//                        
//                        // Model methods have their own specs
//                        if (vd.cases == null) vd.cases = specs.defaultSpecs(vd).cases;
//                        vd.methodSpecsCombined = new JmlSpecs.MethodSpecs(vd.mods,vd.cases);
//                        vd.cases.decl = vd;
//                        specs.putSpecs(vd.sym,vd.methodSpecsCombined);
//                    }
//                } else {
//                    log.getWriter(WriterKind.NOTICE).println("Unhandled declaration in spec class for binary: " + t.getClass());
//                }
//            }
//        }
//        
//        resolve.setAllowJML(previousAllow);
//        env = prev;
//        
//        // If we are completing a class with a Java source file then we walk the
//        // class declaration, attributing types, creating symbols for each
//        // class member (and entering them in the class scope), and noting the
//        // symbols in the class AST for each member.
//        
//        // Here we have a binary class with a spec file.  The binary class
//        // already has all the (java) members entered in the class scope.
//        // However, we still have to walk the AST for the spec file in order
//        // to do the following:
//        //      - attribute any types (including annotations)
//        //      - check that declarations match Java (binary) symbols
//        //      - add ghost/model declarations to the class
//
//        // OLD:
//        
////        if (d.mods.annotations.nonEmpty() && d.mods.annotations.head.annotationType.type == null) { // Check if already attributed
////            Env<AttrContext> baseEnv = env; // FIXME  baseEnv(d, env);
////            JmlAttr.instance(context).attribAnnotationTypes(d.mods.annotations, baseEnv);
////            if (hasDeprecatedAnnotation(d.mods.annotations))
////                d.sym.flags_field |= DEPRECATED;
////            annotateLaterConditional(d.mods.annotations, baseEnv, d.sym);
////        }
////
////        Env<AttrContext> cenv = enter.typeEnvs.get(d.sym);
////        // FIXME _ not sure the next four lines are needed
////        if (d.sym.owner.kind == PCK) {
////            Todo.instance(context).append(cenv);
////        }
////        log.noticeWriter.println("BSC " + d.sym + " " + ((d.sym.flags_field&UNATTRIBUTED)!=0?"unattributed":"attributed"));
////        d.sym.flags_field |= UNATTRIBUTED; // Binary classes start life already attributed
////                                // so we need to reset this so that the specifications get processed
////                                            
////        finishClass(d,cenv);
//
////        boolean prev = binary;
////        binary = true;
////        complete(d.sym);
////        binary = prev;
//    }
    
    VarSymbol findVarMatch(ClassSymbol csym, Name name) {
        Scope.Entry e = csym.members().lookup(name);  // FIXME - can have variables and methods with the same name
        while (e.sym != null && !(e.sym instanceof VarSymbol)) {
            e = e.next();
        }
        return (VarSymbol)e.sym;
    }
    
//    MethodSymbol findMethodMatch(ClassSymbol csym, JmlMethodDecl mdecl) {
//        Scope.Entry e = csym.members().lookup(mdecl.name);  // FIXME - can have variables and multiple methods with the same name
//        while (e.sym != null && !(e.sym instanceof MethodSymbol)
//                && Types.instance(context).isSameType(e.sym.type,mdecl.sym.type)) {
//            e = e.next();
//        }
//        return (MethodSymbol)e.sym;
//    }
    
    /** When we are handling the specs for a binary file, we have the situation
     * of performing an annotation given in the source that has already been
     * performed in loading the binary.  Thus we don't give an error about this.
     * However we don't know that all of the annotations are already present
     * (presumably just the ones retained in the class file are present), so we
     * proceed to do them anyway, at the risk of repeating some.  Repeating the
     * work does not appear to do any harm, though it may be that we should check
     * for those annotations already present and not repeat them. (TODO)
     * @param annotations
     * @param localEnv
     * @param s
     */
    // MAINTENANCE - modified from MemberEnter.annotateLater  // FIXME - currently the same as in the super class
    void annotateLaterConditional(final List<JCAnnotation> annotations,
            final Env<AttrContext> localEnv,
            final Symbol s,
            final DiagnosticPosition deferPos) {
        if (annotations.isEmpty()) return;
        if (s.kind != PCK) {
            s.resetAnnotations(); // mark Annotations as incomplete for now
        }
        annotate.normal(new Annotate.Worker() {
            @Override
            public String toString() {
                return "annotate " + annotations + " onto " + s + " in " + s.owner;
            }

            @Override
            public void run() {
//                Assert.check(s.kind == PCK || s.annotationsPendingCompletion()); // Removed check - why?
                JavaFileObject prev = log.useSource(localEnv.toplevel.sourcefile);
                DiagnosticPosition prevLintPos =
                    deferPos != null
                    ? deferredLintHandler.setPos(deferPos)
                    : deferredLintHandler.immediate();
                Lint prevLint = deferPos != null ? null : chk.setLint(lint);
                try {
//                    if (s.hasAnnotations() &&
//                        annotations.nonEmpty())
//                        log.error(annotations.head.pos,
//                                  "already.annotated",
//                                  kindName(s), s);
                    actualEnterAnnotations(annotations, localEnv, s);
                } finally {
                    if (prevLint != null)
                        chk.setLint(prevLint);
                    deferredLintHandler.setPos(prevLintPos);
                    log.useSource(prev);
                }
            }
        });

        annotate.validate(new Annotate.Worker() { //validate annotations
            @Override
            public void run() {
                JavaFileObject prev = log.useSource(localEnv.toplevel.sourcefile);
                try {
                    chk.validateAnnotations(annotations, s);
                } finally {
                    log.useSource(prev);
                }
            }
        });
    }

    
//    annotate.later(new Annotate.Annotator() {
//            public String toString() {
//                return "conditional annotate " + annotations + " onto " + s + " in " + s.owner;
//            }
//            public void enterAnnotation() {
//                assert s.kind == PCK || s.attributes_field == null; // FIXME - SF patch # says this assert triggers incorrectly when -ea option is used
//                JavaFileObject prev = log.useSource(localEnv.toplevel.sourcefile);
//                try {
//                    if (s.attributes_field != null &&
//                            s.attributes_field.nonEmpty() &&
//                            annotations.nonEmpty()) {
////                            log.error(annotations.head.pos,
////                                      "already.annotated",
////                                      kindName(s), s);
//                    } else enterAnnotations(annotations, localEnv, s);
//                } finally {
//                    log.useSource(prev);
//                }
//            }
//        });
//    }
//    
//    void annotateLater(final List<JCAnnotation> annotations,
//            final Env<AttrContext> localEnv,
//            final Symbol s) {
//        annotateLaterConditional(annotations,localEnv,s);
//    }

    
    /** This inherited method is overridden to do an automatic import of org.jmlspecs.lang.* */
//    @Override
//    public void visitTopLevel(JCTree.JCCompilationUnit tree) {
//        if (tree.starImportScope.elems == null) { // Check if already done
//            super.visitTopLevel(tree);
//            // Import-on-demand org.jmlspecs.lang.
//            importAll(tree.pos, ClassReader.instance(context).enterPackage(org_jmlspecs_lang), env);
//        }
//    }
    
    /** Set in visitiMethodDef so that all chlidren can know which method they are part of */
    JmlMethodDecl currentMethod = null;
    
    @Override 
    public void visitMethodDef(JCMethodDecl tree) {
        JmlMethodDecl prevMethod = currentMethod;
        currentMethod = (JmlMethodDecl) tree;
        boolean prevAllowJml = resolve.allowJML();
        long flags = tree.mods.flags;
        boolean isJMLMethod = utils.isJML(flags);
        try {
            boolean isSpecFile = currentMethod.sourcefile == null || currentMethod.sourcefile.getKind() != JavaFileObject.Kind.SOURCE;
//            boolean isClassModel = ((JmlAttr)attr).isModel(env.enclClass.mods);
            if (isSpecFile && tree.sym != null) return; //Sometimes this is called when the method already is entered
            if (isJMLMethod) resolve.setAllowJML(true);
            //super.visitMethodDef(tree);
            visitMethodDefBinary(tree);
        } finally {
            if (isJMLMethod) resolve.setAllowJML(prevAllowJml);
            currentMethod = prevMethod;
        }
        
//        JmlMethodDecl prevMethod = currentMethod;
//        currentMethod = (JmlMethodDecl) tree;
//        try {
//            // FIXME - I don't think the test on sourcefile is robust
//            boolean isSpecFile = currentMethod.sourcefile == null || currentMethod.sourcefile.getKind() != JavaFileObject.Kind.SOURCE;
//            boolean isClassModel = ((JmlAttr)attr).isModel(env.enclClass.mods);
//            long flags = tree.mods.flags;
//            boolean isJMLMethod = utils.isJML(flags);
//
//            // FIXME - explain why we do this
//            boolean removedStatic = false;
//            if (isJMLMethod && 
//                    (flags & Flags.STATIC) != 0) { // FIXME _ and in an interface?
//                removedStatic = true;
//                tree.mods.flags &= ~Flags.STATIC;
//            }
//
//            // Only enter the method if this is a JML method (e.g., a model method) or if we are processing
//            // a Java file. 
//            // FIXME - I suspect everything does the visit...
//
////            if (isJMLMethod || isClassModel || tree.sym == null) {
//                // The super call has the effect of attributing all the types and annotations
//                // and creating a MethodSymbol, which is set in tree.sym
////                super.visitMethodDef(tree);
////            } else {
////                log.warning("jml.internal","Is this really called? in JmlMemberEnter.visitMethodDef");
////            }
//                { // Copied from MemberEnter.visitMethodDef - to avoid re-entering a method while attributing its types
//                    Scope enclScope = enter.enterScope(env);
//                    MethodSymbol m = new MethodSymbol(0, tree.name, null, enclScope.owner);
//                    m.flags_field = chk.checkFlags(tree.pos(), tree.mods.flags, m, tree);
//                    tree.sym = m;
//
//                    //if this is a default method, add the DEFAULT flag to the enclosing interface
//                    if ((tree.mods.flags & DEFAULT) != 0) {
//                        m.enclClass().flags_field |= DEFAULT;
//                    }
//
//                    Env<AttrContext> localEnv = methodEnv(tree, env);
//
//                    DiagnosticPosition prevLintPos = deferredLintHandler.setPos(tree.pos());
//                    try {
//                        // Compute the method type
//                        m.type = signature(m, tree.typarams, tree.params,
//                                           tree.restype, tree.recvparam,
//                                           tree.thrown,
//                                           localEnv);
//                    } finally {
//                        deferredLintHandler.setPos(prevLintPos);
//                    }
//
//                    if (types.isSignaturePolymorphic(m)) {
//                        m.flags_field |= SIGNATURE_POLYMORPHIC;
//                    }
//
//                    // Set m.params
//                    ListBuffer<VarSymbol> params = new ListBuffer<VarSymbol>();
//                    JCVariableDecl lastParam = null;
//                    for (List<JCVariableDecl> l = tree.params; l.nonEmpty(); l = l.tail) {
//                        JCVariableDecl param = lastParam = l.head;
//                        params.append(Assert.checkNonNull(param.sym));
//                    }
//                    m.params = params.toList();
//
//                    // mark the method varargs, if necessary
//                    if (lastParam != null && (lastParam.mods.flags & Flags.VARARGS) != 0)
//                        m.flags_field |= Flags.VARARGS;
//                }
//
//            if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("      ENTERING MEMBER " + tree.sym + " IN " + tree.sym.owner);
//            if (removedStatic) {
//                tree.sym.flags_field |= Flags.STATIC;
//                tree.mods.flags |= Flags.STATIC;
//            }
//
//            // model methods in an interface are not implicitly abstract
//            if (isJMLMethod && (tree.sym.owner.flags_field & INTERFACE) != 0
//                    && (flags&Flags.ABSTRACT) == 0) {
//                tree.sym.flags_field &= ~Flags.ABSTRACT;
//                tree.mods.flags &= ~Flags.ABSTRACT;
//            }
//
//        } finally {
//            currentMethod = prevMethod;
//        }
    }
    
    // This is a duplicate of super.vistMethodDef -- with some stuff elided for handling specs of binarys
    public void visitMethodDefBinary(JCMethodDecl tree) {
        Scope enclScope = enter.enterScope(env);
        MethodSymbol m = new MethodSymbol(0, tree.name, null, enclScope.owner);
        m.flags_field = chk.checkFlags(tree.pos(), tree.mods.flags, m, tree);
        tree.sym = m;

        //if this is a default method, add the DEFAULT flag to the enclosing interface
        if ((tree.mods.flags & DEFAULT) != 0) {
            m.enclClass().flags_field |= DEFAULT;
        }

        Env<AttrContext> localEnv = methodEnv(tree, env);

        DiagnosticPosition prevLintPos = deferredLintHandler.setPos(tree.pos());
        try {
            // Compute the method type
            m.type = signature(m, tree.typarams, tree.params,
                               tree.restype, tree.recvparam,
                               tree.thrown,
                               localEnv);
        } finally {
            deferredLintHandler.setPos(prevLintPos);
        }

        if (types.isSignaturePolymorphic(m)) {
            m.flags_field |= SIGNATURE_POLYMORPHIC;
        }

        // Set m.params
        ListBuffer<VarSymbol> params = new ListBuffer<VarSymbol>();
        JCVariableDecl lastParam = null;
        for (List<JCVariableDecl> l = tree.params; l.nonEmpty(); l = l.tail) {
            JCVariableDecl param = lastParam = l.head;
            params.append(Assert.checkNonNull(param.sym));
        }
        m.params = params.toList();

        // mark the method varargs, if necessary
        if (lastParam != null && (lastParam.mods.flags & Flags.VARARGS) != 0)
            m.flags_field |= Flags.VARARGS;

        localEnv.info.scope.leave();
        ((JmlCheck)chk).noDuplicateWarn = true;
        if (chk.checkUnique(tree.pos(), m, enclScope)) {
            // Not a duplicate - OK if the declaration is JML
            if (!utils.isJML(m.flags_field)) {
                // FIXME
            }
            enclScope.enter(m);
        } else {
            // A duplicate - OK if the declaration is not JML
            if (utils.isJML(m.flags_field)) {
                // FIXME
            }
        }
        ((JmlCheck)chk).noDuplicateWarn = false;

        annotateLater(tree.mods.annotations, localEnv, m, tree.pos());
        // Visit the signature of the method. Note that
        // TypeAnnotate doesn't descend into the body.
        typeAnnotate(tree, localEnv, m, tree.pos());

        if (tree.defaultValue != null)
            annotateDefaultValueLater(tree.defaultValue, localEnv, m);
    }

    
//    public void visitBlock(JCTree.JCBlock that) {
//        super.visitBlock(that);
//        if (inSpecFile && currentMethod == null && !utils.isJML(currentClass.mods)) {
//            // initializer block is not allowed in a specification, unless it is a model class
//            log.error(that.pos,"jml.initializer.block.allowed");
//        }
//    }
        
//    // TODO - review this
//    // Duplicated from MemberEnter because it is declared private
//    protected void importAll(int pos,
//            final TypeSymbol tsym,
//            Env<AttrContext> env) {
////      Check that packages imported from exist (JLS ???).
//        if (tsym.kind == PCK && tsym.members().elems == null && !tsym.exists()) {
////          If we can't find java.lang, exit immediately.
//            if (((PackageSymbol)tsym).fullname.equals(Names.instance(context).java_lang)) {
//                JCDiagnostic msg = JCDiagnostic.fragment("fatal.err.no.java.lang");
//                throw new FatalError(msg);
//            } else {
//                log.error(pos, "doesnt.exist", tsym);
//            }
//        }
//        final Scope fromScope = tsym.members();
//        final Scope toScope = env.toplevel.starImportScope;
//        for (Scope.Entry e = fromScope.elems; e != null; e = e.sibling) {
//            if (e.sym.kind == TYP && !toScope.includes(e.sym))
//                toScope.enter(e.sym, fromScope);
//        }
//    }

    /** We override the superclass method in order to add the symbol for 'this'
     * into the environment for an interface.  The javac tool does not because
     * there is never a need - all expressions are static.  However, I have not
     * done the same for super.  (TODO)
     */
    @Override
    public void complete(Symbol sym) throws CompletionFailure {
        if (sym.toString().contains("Double")) Utils.stop();
        
        JmlResolve jresolve = JmlResolve.instance(context);
        boolean prevAllowJML = jresolve.setJML(utils.isJML(sym.flags()));
        try {
            Env<AttrContext> env = enter.typeEnvs.get(sym.type.tsym);
            if (env == null) {
                log.error("jml.internal","JmlMemberEnter.complete called with a null env, presumably from a binary class, which should not be the argument of this complete call: " + sym);
                return;
            }
            super.complete(sym);
            // If this is an interface, enter symbol for this into
            // current scope.
            ClassSymbol c = (ClassSymbol)sym;
            if ((c.flags_field & INTERFACE) == INTERFACE) {
                VarSymbol thisSym =
                        new VarSymbol(FINAL | HASINIT, Names.instance(context)._this, c.type, c);
                thisSym.pos = Position.FIRSTPOS;
                env.info.scope.enter(thisSym);
            }
        } finally {
            jresolve.setJML(prevAllowJML);
        }

    }
    
    
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
    public boolean visitVarDefIsStatic(JCVariableDecl tree, Env<AttrContext> env) {
        boolean b = super.visitVarDefIsStatic(tree,env);
        if (!isInJml && !utils.isJML(tree.mods)) return b; // FIXME - why isn't isInJml enough here - we need the second conjunct for ghost declarations in an interface
        if ((tree.mods.flags & STATIC) != 0) return true;
        
        // In the case where we are in an interface but within a JML expression
        // we can use type variables.
        return false; // FIXME - improve this
    }


    @Override
    public void visitVarDef(JCVariableDecl tree) {
        long flags = tree.mods.flags;
        boolean wasFinal = (flags&Flags.FINAL) != 0;
        boolean wasStatic = (flags&Flags.STATIC) != 0;
        if ((env.enclClass.mods.flags & INTERFACE) != 0  && utils.isJML(tree.mods)) {
            // FIXME - but the @Instance declaration might be in the .jml file
            boolean isInstance = JmlAttr.instance(context).findMod(tree.mods,JmlTokenKind.INSTANCE) != null;
            if (isInstance && !wasStatic) tree.mods.flags &= ~Flags.STATIC;
        }
        boolean prev = resolve.allowJML();
        if (utils.isJML(tree.mods)) resolve.setAllowJML(true);
        super.visitVarDef(tree);
        if (utils.isJML(tree.mods)) resolve.setAllowJML(prev);
        Symbol sym = tree.sym;
        if (specs.getSpecs(tree.sym) != null) log.warning("jml.internal","Expected null field specs here: " + tree.sym.owner + "." + tree.sym);
        specs.putSpecs(tree.sym,new JmlSpecs.FieldSpecs(tree.mods)); // This specs only has modifiers - field spec clauses are added later (FIXME - where? why not here?)
        if (sym.kind == Kinds.VAR && sym.owner.kind == TYP && (sym.owner.flags_field & INTERFACE) != 0
                && utils.isJML(tree.mods)) {
            // In the case of a JML ghost variable that is a field of an interface, the default is static and not final
            // (unless explicitly specified final)
            // FIXME _ the following is not robust because annotations are not attributed yet - test these as well
            boolean isInstance = utils.findMod(tree.mods,JmlTokenKind.INSTANCE) != null;
            //boolean isGhost = JmlAttr.instance(context).findMod(tree.mods,JmlToken.GHOST) != null;
            //boolean isModel = JmlAttr.instance(context).findMod(tree.mods,JmlToken.MODEL) != null;
            if (isInstance && !wasStatic) tree.sym.flags_field &= ~Flags.STATIC;  // FIXME - this duplicates JmlCheck
            if (!wasFinal) sym.flags_field &= ~FINAL; 
        }
    }
    
    /** Creates a JCAnnotation tree (without position, source, or type information) from a token; has limited use */
    protected JmlTree.JmlAnnotation tokenToAnnotationAST(JmlTokenKind jt) {
        Class<?> c = jt.annotationType;
        if (c == null) {
            log.warning("jml.internal","Expected annotation type to be defined when calling tokenToAnnotationAST");
            return null;
        }
        // FIXME - this is also repeated code and repeated fixed strings
        JCExpression t = jmlF.Ident(names.fromString("org"));
        t = jmlF.Select(t, names.fromString("jmlspecs"));
        t = jmlF.Select(t, names.fromString("annotation"));
        t = jmlF.Select(t, names.fromString(c.getSimpleName()));
        JmlTree.JmlAnnotation ann = jmlF.Annotation(t, List.<JCExpression>nil());
        return ann;
    }
    
    public void binaryEnter(JmlCompilationUnit specs) {
        Env<AttrContext> prevEnv = env;
        modeOfFileBeingChecked = specs.mode;
        env = specs.topLevelEnv;
        if (env == null) {
            
            env = specs.topLevelEnv = enter.topLevelEnv(specs);
            enter.visitTopLevel(specs);
            importHelper(specs);
//            super.memberEnter(specs, env);  // Does not do members for binary classes
//            env = specs.topLevelEnv;
            for (JCTree d: specs.defs) {
                if (!(d instanceof JmlClassDecl)) continue;
                JmlClassDecl cd = (JmlClassDecl)d;
                cd.specsDecls = cd;
                memberEnter(cd,cd.env);  // FIXME - does nothing
                Env<AttrContext> eeee = enter.typeEnvs.get(cd.sym);
                if (eeee == null) {
                    enter.typeEnvs.put(cd.sym, cd.env);
                }
            }
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
                enter.classEnter(cd,env);
            }
            Env<AttrContext> specClassenv = jcd.env;
            binaryMemberEnter(jcd.sym, jcd, specClassenv);
            // FIXME - need to handle any secondary classes and nested classes as well
        }
        env = prevEnv;
    }
    
    public void binaryMemberEnter(ClassSymbol c, JmlClassDecl specs, Env<AttrContext> env) {
        Env<AttrContext> prevenv = this.env;
        JavaFileObject prev = log.useSource(specs.source());
        try {
        JmlAttr attr = JmlAttr.instance(context);
        c.flags_field |= UNATTRIBUTED;
        attr.addTodo(c);
        Env<AttrContext> classenv = enter.getEnv(specs.sym);
        
        {
            ClassSymbol cs = c;
            ClassType ct = (ClassType)c.type;
            // enter symbols for 'this' into current scope.
            VarSymbol thisSym =
                    new VarSymbol(FINAL | HASINIT, names._this, cs.type, cs);
            thisSym.pos = Position.FIRSTPOS;
            env.info.scope.enter(thisSym);
            // if this is a class, enter symbol for 'super' into current scope.
            if ((cs.flags_field & INTERFACE) == 0 &&
                    ct.supertype_field.hasTag(CLASS)) {
                VarSymbol superSym =
                        new VarSymbol(FINAL | HASINIT, names._super,
                                ct.supertype_field, cs);
                superSym.pos = Position.FIRSTPOS;
                env.info.scope.enter(superSym);
            }
        }
        
        if (!specs.typarams.isEmpty() ||  !((ClassType)c.type).typarams_field.isEmpty() ) {
            // FIXME - not doing classes or methods with type argument for now
                enter.recordEmptySpecs(c);
        } else 

        for (JCTree t: specs.defs) {
            //env = prevenv;
            if (t instanceof JmlMethodDecl) {
                JmlMethodDecl md = (JmlMethodDecl)t;
//                if (!md.typarams.isEmpty() && !md.name.toString().equals("defaultEmpty")) {
//                    enter.recordEmptySpecs(c);  // FIXME _ not handling methods with type parameters
//                    break;
//                }
//                Env<AttrContext> localEnv = methodEnv(md, classenv);
//                env = classenv;
                boolean isJML = utils.isJML(md.mods);
                boolean isModel = isJML && utils.findMod(md.mods, JmlTokenKind.MODEL) != null;
                if (md.sym == null) {
                    this.env = classenv;
                    visitMethodDef(md);
//                    boolean hasTypeArgs = !md.typarams.isEmpty();
//                    
//                    ClassType ctype = (ClassType)c.type;
//                    hasTypeArgs = hasTypeArgs || !ctype.typarams_field.isEmpty();
//                    //Type mtype = signature(null,md.typarams,md.params,md.getReturnType(),null,md.thrown,env);
//                    ListBuffer<Type> tyargtypes = new ListBuffer<Type>();
//                    for (JCTypeParameter param : md.typarams) {
//                        Type tt = attr.attribType(param, env);
//                        tyargtypes.add(tt);
//                    }
//                    ListBuffer<Type> argtypes = new ListBuffer<Type>();
//                    for (JCVariableDecl param : md.params) {
//                        Type tt = attr.attribType(param.vartype, env); // FIXME _ this does not work for type parameters, such as in Comparable
//                        param.type = tt;
//                        argtypes.add(tt);
//                    }
//                    if (md.restype != null) {
//                        attr.attribType(md.restype, env);
//                    }
//                    if (md.thrown != null) {
//                        for (JCExpression th: md.thrown) attr.attribType(th, env);
//                    }
//                    // FIXME - don't want an error message - just an indication of whether such a method exists
//                    Scope.Entry e = c.members().lookup(md.name);
//                    int count = 0;
//                    Types types = Types.instance(context);
//                    while (e.sym != null && e.scope != null && e.sym.name == md.name) {
//                        if (e.sym instanceof Symbol.MethodSymbol) {
//                            Symbol.MethodSymbol msym = (Symbol.MethodSymbol)e.sym;
//                            x: if (msym.getParameters().length() == md.params.length()) {
//                                if (!hasTypeArgs) {
//                                    int k = md.params.length();
//                                    for (int i=0; i<k; i++) {
//                                        if (!types.isSameType(msym.getParameters().get(i).type,md.params.get(i).type)) {
//                                            break x;
//                                        }
//                                    }
//                                }
//                                md.sym = msym;
//                                count++;
//                            }
//                        }
//                        e = e.next();
//                        while (e.sym != null && e.scope != null && e.sym.name != md.name) e = e.next();
//                    }
                    
//                    if (count > 1) log.error(md.pos(),"jml.internal","Type comparison not implemented " + c.flatname + "." + md.name);

                    //md.sym = (MethodSymbol)JmlResolve.instance(context).findFun(env,md.name,argtypes.toList(),tyargtypes.toList(),false,false);
                    //md.sym = (MethodSymbol)JmlResolve.instance(context).resolveMethod(t.pos(),env,md.name,argtypes.toList(),tyargtypes.toList());
                }
                //if (md.name.toString().equals("defaultEmpty")) Utils.stop();
                if (md.sym != null) {
                    {
                        Env<AttrContext> localEnv = methodEnv(md, env);
                        annotateLater(md.mods.annotations, localEnv, md.sym, md.pos());
                    }

                    md.specsDecl = md;
                    md.methodSpecsCombined = new JmlSpecs.MethodSpecs(md);
                    JmlSpecs.instance(context).putSpecs(md.sym, md.methodSpecsCombined);
                    checkMethodMatch(null, md.sym, md, c);
                }
                if (isJML && !isModel) {
                    // Error: Non-model method declared within JML
                } else if (md.sym != null && !isJML) {
                    // Java method in spec matches the java declaration. Just add the specs.
                    JmlSpecs.instance(context).putSpecs(md.sym, md.methodSpecsCombined); // FIXME - duplicate line above
                } else if (md.sym == null && isJML) {
                    // Add the model method to the binary class
        // FIXME - need to sort out the env
                    this.env = env;
                    visitMethodDef(md);
//                    JmlSpecs.instance(context).putSpecs(md.sym, md.methodSpecsCombined);
                } else if (md.sym != null && isJML) {
                    // Error: model method matching a Java method 
                } else { // if (md.sym == null && !isModel) {
                    // Error: No method in class to match non-model specification method
                }
                
            } else if (t instanceof JmlClassDecl) {
                // FIXME - need symbol for nested class
                //binaryMemberEnter(c,(JmlClassDecl)t);
                JmlClassDecl tcd = (JmlClassDecl)t;
                ClassSymbol sym = tcd.sym;
                if (sym == null) {
                    sym = tcd.sym = reader.classExists(names.fromString(c.toString() + "$" + tcd.name.toString()));
                }
                if (sym != null) enterSpecsForBinaryClasses(sym, List.<JCTree>of(t));
                else {
                    // FIXME - no such class - is it a JML class? if so enter it
                }

            } else if (t instanceof JmlVariableDecl) {
                
                enterSpecsForBinaryFields(c,(JmlVariableDecl)t);

            }
        }
    } finally {
        env = prevenv;
        log.useSource(prev);
    }
        
    }

    /** This creates the specifications structures for a binary class.  We have
     * the list of lists of specification declarations owned by the parent of
     * 'csymbol' from which we extract our own declarations.
     * @param csymbol the class whose specs we need
     * @param specsdefs the list of specs declarations from the parent class or compilation unit
     */
    // FIXME - rename so as not to be confused with the 'enter' processing of OpenJDK
    public void enterSpecsForBinaryClasses(ClassSymbol csymbol, List<JCTree> specsdefs) {
        if (specs.get(csymbol) != null) return; // Already completed
        
        if (utils.jmlverbose >= Utils.PROGRESS) context.get(Main.IProgressListener.class).report(0,2,"entering (binary) " + csymbol);

        // FIXME _ fix the following comment
        // In the following call we (a) find any declarations in the specsdefs 
        // that match cysmbol by name (b) attach those to csymbol in the 
        // specs database (c) determine the model types directly nested in
        // csymbols's specs (d) combine csymbol's various specs into one
        // combinedTypeSpec (e) get the list of specs defs to use for nested 
        // classes.  The call also fixes the value of JmlClassDecl.env for 
        // each JmlClassDecl in newlist
        
        // NOTE: specsdefs is not null, but it may be empty for any particular class

        JmlClassDecl matched = matchSpecsToClasses(csymbol,specsdefs);

        // newlist is the list of definition lists that we pass on to 
        // nested classes

        // Here we recurse over nested classes -- they will already exist as
        // binary classes, so we just find them and match them to specs.
        // FIXME - are the nested classes necessarily loaded?
        for (Symbol nested: csymbol.getEnclosedElements()) {
            if (nested instanceof ClassSymbol) {
                enterSpecsForBinaryClasses((ClassSymbol)nested,matched.defs);
            }
        }

//        // Then enter this class's model types     // FIXME - should we use the combined list?
//        JmlSpecs.TypeSpecs combinedTypeSpecs = specs.getSpecs(csymbol);
//        JmlClassDecl cd = combinedTypeSpecs.refiningSpecDecls;
//        if (cd != null) {
//            enter.enterModelTypes(cd.typeSpecs.modelTypes,cd.env);
//        }

    }
    
    protected void enterSpecsForBinaryFields(ClassSymbol parent, JmlVariableDecl specstree) {
        Name nm = specstree.name;
        boolean isJML = utils.isJML(specstree.mods);
        boolean isModel = isJML && utils.findMod(specstree.mods, JmlTokenKind.MODEL) != null;
        boolean isGhost = isJML && utils.findMod(specstree.mods, JmlTokenKind.GHOST) != null;

        Scope.Entry e = parent.members().lookup(nm); // Presume there is just one declaration with a matching name, 
                                                     // or at least, that the first one to match is the one we want.
        Symbol.VarSymbol vsym = e.sym instanceof Symbol.VarSymbol ? (Symbol.VarSymbol)e.sym : null;
        specstree.sym = vsym;
        if (vsym == null) {
            // There is no match of a declaration in the specs file to the Java class
            // isJML --> OK, but it should be model or ghost (which is checked in JmlAttr.checkVarMods)
            // !isJML --> error - but we treat it as model or ghost
            if (!isJML) {
                JavaFileObject prev = log.currentSourceFile();
                log.useSource(specstree.source());
                log.error(specstree.pos,"jml.no.var.match",nm.toString());
                log.useSource(prev);
            }
            Env<AttrContext> prevenv = env;
            try {
                env = enter.typeEnvs.get(parent);
                visitVarDef(specstree);
            } finally {
                env = prevenv;
            }
            if (specstree.sym == null) log.error(specstree, "jml.internal", "Failed to set a variable declaration symbol as expected");
            JmlSpecs.instance(context).putSpecs(specstree.sym, specstree.fieldSpecsCombined);
            vsym = specstree.sym;
        }
        checkFieldMatch(null, specstree.sym, specstree);
        
        long flags = specstree.mods.flags;
        boolean wasFinal = (flags&Flags.FINAL) != 0;
        boolean wasStatic = (flags&Flags.STATIC) != 0;
        if ((parent.flags() & INTERFACE) != 0  && utils.isJML(specstree.mods)) {
            // FIXME - but the @Instance declaration might be in the .jml file
            boolean isInstance = JmlAttr.instance(context).findMod(specstree.mods,JmlTokenKind.INSTANCE) != null;
            if (isInstance && !wasStatic) specstree.mods.flags &= ~Flags.STATIC;
        }
        if (specs.getSpecs(specstree.sym) != null) log.warning("jml.internal","Expected null field specs here: " + specstree.sym.owner + "." + specstree.sym);
        specs.putSpecs(specstree.sym,new JmlSpecs.FieldSpecs(specstree.mods)); // This specs only has modifiers - field spec clauses are added later (FIXME - where? why not here?)

        if (vsym.kind == Kinds.VAR && vsym.owner.kind == TYP && (vsym.owner.flags_field & INTERFACE) != 0
                && isJML) {
            // In the case of a JML ghost variable that is a field of an interface, the default is static and not final
            // (unless explicitly specified final)
            // FIXME _ the following is not robust because annotations are not attributed yet - test these as well
            boolean isInstance = utils.findMod(specstree.mods,JmlTokenKind.INSTANCE) != null;
            if (isInstance && !wasStatic) specstree.sym.flags_field &= ~Flags.STATIC;  // FIXME - this duplicates JmlCheck
            if (!wasFinal) vsym.flags_field &= ~FINAL; 
        }
        
        
//        if (isJML && !isModel && !isGhost) {
//            // Error: Non-model non-ghost field declared within JML
//            // Checked and warned in JmlAttr.checkVarMods 
//        }
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


    // Only used for binary enter

    // Only used for entering binary classes
    // FIXME - REVIEW

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
    protected JmlClassDecl matchSpecsToClasses(ClassSymbol classToMatch, List<JCTree> specsDecls ) {
//        if (classToMatch.name.toString().equals("Content")) {
//            log.noticeWriter.println(classToMatch);
//        }
        // We find the list of matching spec declarations.  We also fix their
        // env fields, but only the ones that match - the others will be matched
        // in a separate call, or ignored.
        Name n = classToMatch.name;
        if (specsDecls == null) {
            // For these - model and local classes - attach self as specs
            Env<AttrContext> classesenv = enter.typeEnvs.get(classToMatch);
            if (classesenv != null && classesenv.tree != null) {
                specsDecls = List.<JCTree>of(classesenv.tree);
                ((JmlClassDecl)classesenv.tree).env = classesenv;
            }
        }
        JmlClassDecl matchedSpecClass = null;
        if (specsDecls != null) {   
            List<JCTree> list = specsDecls;
            for (JCTree t: list) {
                if (t instanceof JmlClassDecl) {
                    JmlClassDecl specClass = (JmlClassDecl)t;
                    if (specClass.name.equals(n)) {
                        JavaFileObject prev = log.useSource(specClass.source());
                        if (matchedSpecClass == null) {
                            boolean ok = enter.checkAndEnterTypeParameters(classToMatch,specClass,specClass.env);
                            if (ok) {
                                specClass.sym = classToMatch;
                                matchedSpecClass = specClass;
                                //specClass.env = classEnv(specClass, specClass.env); // FIXME - is this needed?
           //                     for (JCTree tt: specClass.defs) {
           //                         if (tt instanceof JmlClassDecl) ((JmlClassDecl)tt).env = classEnv((JmlClassDecl)tt,specClass.env);
           //                     }
                            }
                        } else {
                            log.error(specClass.pos,"jml.duplicate.jml.class.decl",specClass.name);
                            log.error(matchedSpecClass.pos,"jml.associated.decl.cf",
                                    utils.locationString(specClass.pos));
                        }
                        log.useSource(prev);
                    }
                }
            }
        }

        // selflist is the list of specification type declarations that are
        // a match to 'classToMatch'

        Env<AttrContext> localenv = enter.typeEnvs.get(classToMatch);
        boolean wasNull = localenv == null;
        if (localenv != null) {
            // Typically a java class with or without specs
            matchedSpecClass = (JmlClassDecl)localenv.tree;
        } else if (matchedSpecClass != null) {
            // A binary class with specs - JDK did not register an env because
            // there is no Java source.  We put in one for the most refined
            // spec file
            localenv = matchedSpecClass.env;
        } else {
            // This happens for a binary class with no specs for the given type
        }
            // The above is either the java declaration, or (if the class is
            // binary) the most refined specs declaration

        JmlSpecs.TypeSpecs combinedTypeSpecs = specs.getSpecs(classToMatch);
        if (matchedSpecClass == null) {
            combinedTypeSpecs.modifiers = null;
            combinedTypeSpecs.decl = null;
            combinedTypeSpecs.file = classToMatch.sourcefile;
        } else {
            matchedSpecClass.typeSpecsCombined = specs.combineSpecs(classToMatch,null,matchedSpecClass);
        }
        combinedTypeSpecs.refiningSpecDecls = matchedSpecClass;

        // Determine an env for this class if it does not have one
        // We need to have some sort of declaration to do so - we use the
        // most refined specs declaration
        if (wasNull && matchedSpecClass != null) {
            // This branch will not be taken for normal Java classes, since they have been
            // entered; similarly for model classes
            //log.noticeWriter.println("PUTTING TYPEENV " + classToMatch + " " + typeEnvs.get(classToMatch) + " " + env);
            enter.typeEnvs.put(classToMatch,matchedSpecClass.env);  // Binary classes with specs will have the environment be null;
                                        // we add an environment that holds the specs class declaration so if gets attributed
                                        // FIXME - we should handle this differently when we put in place envs for specs that 
                                        // are different than the envs for the corresponding java class - to handle, for example,
                                        // different lists of import statements
        }

        return matchedSpecClass;
    }

    @Override
    protected void importHelper(JCCompilationUnit tree) {
        // Import-on-demand java.lang.
        importAll(tree.pos, reader.enterPackage(names.java_lang), env);
        importAll(tree.pos, reader.enterPackage(names.fromString("org.jmlspecs.lang")), env);

        // Process all import clauses.
        memberEnter(tree.defs, env);
    }

}
