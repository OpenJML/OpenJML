/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.comp;

import static com.sun.tools.javac.code.Flags.FINAL;
import static com.sun.tools.javac.code.Flags.HASINIT;
import static com.sun.tools.javac.code.Flags.INTERFACE;
import static com.sun.tools.javac.code.Flags.STATIC;
import static com.sun.tools.javac.code.Flags.UNATTRIBUTED;
import static com.sun.tools.javac.code.Kinds.PCK;
import static com.sun.tools.javac.code.Kinds.TYP;
import static com.sun.tools.javac.code.TypeTags.CLASS;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import javax.tools.JavaFileObject;
import javax.tools.JavaFileObject.Kind;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.code.Attribute.Compound;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.CompletionFailure;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCTypeParameter;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.FatalError;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
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
        this.modelName = names.fromString(JmlToken.MODEL.internedName());
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

    
    int modeOfFileBeingChecked = 0;
    
    protected JmlClassDecl currentClass = null;
    
    @Override
    protected void finishClass(JCClassDecl tree, Env<AttrContext> env) {
        
        JmlClassDecl prevClass = currentClass;
        currentClass = (JmlClassDecl)tree;
        int prevMode = modeOfFileBeingChecked;  // FIXME _ suspect this is not accurate
        modeOfFileBeingChecked = ((JmlCompilationUnit)env.toplevel).mode;
        if ((JmlCompilationUnit.isForBinary(modeOfFileBeingChecked)) && !JmlAttr.instance(context).isModel(tree.mods)
                && !(tree.sym.toString().startsWith("$anonymous$"))) { // FIXME - do something more robust than checking the name
            finishSpecClass((JmlClassDecl)tree,env); 
            modeOfFileBeingChecked = prevMode;
            currentClass = prevClass;
            return; 
        }
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("    MEMBER ENTER FINISHING CLASS " + tree.sym.fullname);
        // This is the case of a java source file, with a possibly-empty
        // sequence of specification files.  Besides entering all the Java
        // field and method and initializer(?) members in the usual way, we
        // need to:
        //  connect specifications of Java members with the members
        //  enter ghost and model fields, methods, initializers, along with
        //      their specifications

        // First we do everything that Java does on regular Java fields 
        // that are directly members of this class
        
        JmlClassDecl jtree = (JmlClassDecl)tree;
        ClassSymbol csym = jtree.sym;
        
        JavaFileObject prevSource = log.useSource(jtree.source());;
        boolean prevInSpecFile = inSpecFile;

        inSpecFile = jtree.source() == null ? false : jtree.source().getKind() != Kind.SOURCE;  // should always be false (?)

        super.finishClass(tree,env);

        currentClass = prevClass;

        // Now go through everything in the specs sequence, finding the
        // JML fields and methods.  These need to be entered.

        boolean prevAllowJML = resolve.allowJML;
        boolean prevInModel = inModelTypeDeclaration;
        try {
            if (jtree.specsDecls == null) {
                if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("FINISHING CLASS - NO SPECS " + tree.sym.fullname);
                checkTypeMatch(jtree,jtree); // Still need to check modifiers
                return;
            }

            if (jtree.specsDecls == null) {
                // This happens for classes nested in org.jmlspecs.utils.Utils, since
                // they have no specs within the corresponding .jml file - perhaps they should.  TODO
                
                // In the meantime, we do not complain.
                //log.noticeWriter.println("NO SPECS FOR " + jtree.sym.flatName());
                
                // The class should at least have been given itself as specs
                // We try to recover at this point by doing so
                jtree.specsDecls = jtree;
            }
            
            
            JmlClassDecl specsDecl = jtree.specsDecls;

            if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("FINISHING CLASS - JML PHASE " + tree.sym.fullname);
            
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

            resolve.allowJML = true;
            
            
//            JmlSpecs.TypeSpecs tsp = jtree.typeSpecs;
//            if (tsp == null) {
//                tsp = jtree.typeSpecs = new JmlSpecs.TypeSpecs();
//                JmlSpecs.instance(context).putSpecs(jtree.sym,tsp);
//            }
//            tsp.modifiers = specsDecl.mods;
//            tsp.decl = specsDecl;
//            tsp.file = specsDecl.sourcefile;
//
//            prevSource = Log.instance(context).useSource(specsDecl.sourcefile);
//            JmlMethodSpecs savedMethodSpecs = null;
//            JmlSpecs.FieldSpecs mostRecentFieldSpecs = null;
//            JmlVariableDecl mostRecentVarDecl = null;
            
            JmlSpecs.TypeSpecs tsp = specs.get(tree.sym);
            LinkedList<JmlTypeClauseDecl> duplicates = new LinkedList<JmlTypeClauseDecl>();
            //for (JmlTypeClause clause: tsp.clauses) {
            for (JCTree clause: specsDecl.typeSpecs.clauses) {
                if (clause instanceof JmlTypeClauseDecl) {
                    // These are JML declarations
                    JmlTypeClauseDecl cl = (JmlTypeClauseDecl)clause;
                    JCTree tr = cl.decl;
                    // We have already entered any model classes
                    // but we need to enter model methods and ghost and model fields
                    if (tr instanceof JmlVariableDecl) {
                        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("JML VAR ENTER FOR " + jtree.name + " " + ((JmlVariableDecl)tr).name);
                        memberEnter(tr,env);
                        VarSymbol ms = ((JmlVariableDecl)tr).sym;
                        if (ms != null && !utils.isJML(ms.flags())) {
                            // Matched a non-JML method - remove it to avoid further confusion
                            duplicates.add(cl);
                        }
                    } else if (tr instanceof JmlMethodDecl) {
                        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("JML METH ENTER FOR " + jtree.name + " " + ((JmlMethodDecl)tr).name);
                        int n = log.nerrors;
                        memberEnter(tr,env);
                        if (n != log.nerrors) {
                            // Matched a non-JML method - remove it to avoid further confusion
                            duplicates.add(cl);
                        }
                    }
                }
            }
            if (duplicates.size() != 0) {
                ListBuffer<JmlTypeClause> newlist = new ListBuffer<JmlTypeClause>();
                for (JmlTypeClause t: tsp.clauses) {
                    if (!duplicates.contains(t)) {
                        newlist.append(t);
                    }
                }
                tsp.clauses = newlist;
            }
            
            // At this point, all java and spec members are entered
            // and types have their combined specs defined
            // We still need to combine the field and method specs

            // FIXME - what about blocks

            // First for Java fields and methods
            
            Integer matchpos;
            Map<Symbol,Integer> matches = new HashMap<Symbol,Integer>();
            for (JCTree t: specsDecl.defs) {
                if (t instanceof JmlVariableDecl) {
                    VarSymbol vsym = matchAndCombineFieldSpecs(jtree,jtree.sym,(JmlVariableDecl)t);
                    if (vsym != null && (matchpos=matches.put(vsym,((JmlVariableDecl)t).pos)) != null) {
                        int p = ((JmlVariableDecl)t).pos;
                    	log.error(p,"jml.duplicate.var.match",((JmlVariableDecl)t).name);
                        log.error(matchpos,"jml.associated.decl.cf",
                        		utils.locationString(p));
                    }
                } else if (t instanceof JmlMethodDecl) {
                    MethodSymbol msym = matchAndCombineMethodSpecs(jtree,jtree.sym,(JmlMethodDecl)t,env);
                    if (msym != null && (matchpos=matches.put(msym,((JmlMethodDecl)t).pos)) != null) {
                        int p = ((JmlMethodDecl)t).pos;
                        log.error(p,"jml.duplicate.method.match",((JmlMethodDecl)t).name);
                        log.error(matchpos,"jml.associated.decl.cf",
                        		utils.locationString(p));
                    }
                }
            }
            matches.clear();
            
            // Then for specs fields and methods
            
            // Duplicates among JML declarations of fields and methods are caught 
            // as they are entered into the enclosing scope
            for (JmlTypeClause t: specsDecl.typeSpecs.clauses) {
                if (t instanceof JmlTypeClauseDecl) {
                    JmlTypeClauseDecl tcd = (JmlTypeClauseDecl)t;
                    if (tcd.decl instanceof JmlVariableDecl) {
                        matchAndCombineFieldSpecs(jtree,jtree.sym,(JmlVariableDecl)tcd.decl);
                    } else if (tcd.decl instanceof JmlMethodDecl && !duplicates.contains(tcd)) {
                        matchAndCombineMethodSpecs(jtree,jtree.sym,(JmlMethodDecl)tcd.decl,env);
                    }
                }
            }
            
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
            
            for (JmlTypeClause t: specsDecl.typeSpecs.clauses) {
                if (t instanceof JmlTypeClauseDecl) {
                    JmlTypeClauseDecl tcd = (JmlTypeClauseDecl)t;
                    if (tcd.decl instanceof JmlVariableDecl) {
                        JmlVariableDecl v = (JmlVariableDecl)tcd.decl;
                        v.fieldSpecsCombined = specs.getSpecs(v.sym);
                    } else if (tcd.decl instanceof JmlMethodDecl && !duplicates.contains(tcd)) {
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
            }
            

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
//                                    Log.instance(context).error(vardecl.pos(),"jml.duplicate.var.match",vardecl.name);
//                                } else {
//                                    match.specsDecl = vardecl;
//                                    JmlSpecs.instance(context).putSpecs(match.sym,mostRecentFieldSpecs=new JmlSpecs.FieldSpecs(specsDecl.mods));
//                                    mostRecentVarDecl = vardecl;
//                                }
//                            }
//                        }
//                    }
//                    if (match == null) {
//                        Log.instance(context).error(vardecl.pos(),"jml.no.var.match",vardecl.name);
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
//                        Log.instance(context).error(t.pos(),"jml.misplaced.var.spec",((JmlTypeClause)t).token.internedName());
//                    } else {
//                        mostRecentFieldSpecs.list.append((JmlTypeClause)t);
//                        if (t instanceof JmlTypeClauseIn) ((JmlTypeClauseIn)t).parentVar = mostRecentVarDecl;
//                    }
//                } else if (t instanceof JmlTypeClauseInitializer) {
//                    if (((JmlTypeClauseInitializer)t).token == JmlToken.INITIALIZER) {
//                        if (tsp.initializerSpec != null) {
//                            Log.instance(context).error(t.pos,"jml.one.initializer.spec.only");
//                        } else {
//                            if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
//                            ((JmlTypeClauseInitializer)t).specs = savedMethodSpecs;
//                            tsp.initializerSpec = ((JmlTypeClauseInitializer)t);
//                        }
//                    } else {
//                        if (tsp.staticInitializerSpec != null) {
//                            Log.instance(context).error(t.pos,"jml.one.initializer.spec.only");
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
//                    Log.instance(context).error(savedMethodSpecs.pos(),"jml.misplaced.method.specs",specsDecl.name);
//                    savedMethodSpecs = null;
//                }
//            }
//            specsDecl.defs = newdefs.toList();
//            if (savedMethodSpecs != null) {
//                Log.instance(context).error(savedMethodSpecs.pos(),"jml.misplaced.method.specs",specsDecl.name);
//                savedMethodSpecs = null;
//            }
            checkFinalTypeSpecs(specs.get(csym));

        } finally {
            inSpecFile = prevInSpecFile;
            inModelTypeDeclaration = prevInModel;
            addRacMethods(tree.sym,env);
            resolve.allowJML = prevAllowJML;
            Log.instance(context).useSource(prevSource);
            if (utils.jmlverbose >= Utils.JMLDEBUG) {
                log.noticeWriter.println("FINISHING CLASS - COMPLETE " + tree.sym.fullname);
                log.noticeWriter.println("   SCOPE IS " + tree.sym.members());
            }
            modeOfFileBeingChecked = prevMode;
            currentClass = prevClass;
        }
    }

    protected VarSymbol matchAndCombineFieldSpecs(JmlClassDecl javaDecl, ClassSymbol csym, JmlVariableDecl specsVarDecl) {
        // Find any specsVarDecl counterpart in the javaDecl
        Name id = specsVarDecl.name;
        VarSymbol matchSym = null;
        Scope.Entry entry = csym.members().lookup(id);
        while (entry != null && entry.sym != null) {
            if (entry.sym instanceof VarSymbol) {
                matchSym = (VarSymbol)entry.sym;
                break;
            }
            entry = entry.next();
        }
        if (matchSym == null) {
            if (((JmlAttr)attr).findMod(specsVarDecl.mods,JmlToken.GHOST) == null &&
                    ((JmlAttr)attr).findMod(specsVarDecl.mods,JmlToken.MODEL) == null) {
                Log log = Log.instance(context);
                JavaFileObject prevSource = log.currentSourceFile();
                log.useSource(specsVarDecl.sourcefile);
                log.error(specsVarDecl.pos(),"jml.no.var.match",specsVarDecl.name);
                log.useSource(prevSource);
            }
            return null;
        }
        
        JmlSpecs.FieldSpecs fieldSpecs = specsVarDecl.fieldSpecs;
        if (fieldSpecs != null) JmlSpecs.instance(context).putSpecs(matchSym,fieldSpecs);

        JmlVariableDecl javaMatch = null;
        if (javaDecl != null) {
            // TODO - is there a better way to find a declaration for a symbol?
            for (JCTree t: javaDecl.defs) {
                if (t instanceof JmlVariableDecl && ((JmlVariableDecl)t).sym == matchSym) {
                    javaMatch=(JmlVariableDecl)t;
                    break;
                }
            }
            if (javaMatch == null) {
                for (JmlTypeClause t: javaDecl.typeSpecsCombined.clauses) {
                    if (t instanceof JmlTypeClauseDecl &&
                            ((JmlTypeClauseDecl)t).decl instanceof JmlVariableDecl && 
                            ((JmlVariableDecl)((JmlTypeClauseDecl)t).decl).sym == matchSym) {
                        javaMatch = (JmlVariableDecl)((JmlTypeClauseDecl)t).decl;
                        break;
                    }
                }
            }

           if (javaMatch != null)  javaMatch.specsDecl = specsVarDecl; // FIXME - should it ever be that javaMatch is null?
            
            if (javaMatch != specsVarDecl) {
                if (specsVarDecl.init != null) {
                    // FIXME - error ?
                }
            }
        }
        {
            checkFieldMatch(javaMatch,matchSym,specsVarDecl);
            specsVarDecl.sym = matchSym; // FIXME - is this needed or is it already entered?
        }
        return matchSym;
    }

    protected MethodSymbol matchAndCombineMethodSpecs(JmlClassDecl javaDecl, ClassSymbol csym, JmlMethodDecl specsMethodDecl, Env<AttrContext> env) {
//        if (specsMethodDecl.getName().toString().contains("value") && csym.toString().equals("A")) {
//            log.noticeWriter.println(specsMethodDecl.getName().toString());
//        }

        // Find any specsMethodDecl counterpart in the javaDecl

        MethodSymbol matchSym = matchMethod(specsMethodDecl,csym,env,true);
        JmlSpecs.MethodSpecs combinedSpecs = null;
        if (matchSym == null) {
            // Error already issued in matchMethod
            // Ignore any specs
            // FIXME - do we really want to completely ignore this method and its specs - it won't get type checked for example
        } else {
            
            if (specsMethodDecl == null) {
                combinedSpecs = JmlSpecs.defaultSpecs(context,matchSym,0);  // FIXME
            } else {
                combinedSpecs = new JmlSpecs.MethodSpecs(specsMethodDecl.mods,specsMethodDecl.cases);
            }

            if (javaDecl != null) {
                // TODO - is there a better way to find a declaration for a method symbol?
                JmlMethodDecl javaMatch = null;
                for (JCTree t: javaDecl.defs) {
                    if (t instanceof JmlMethodDecl && ((JmlMethodDecl)t).sym == matchSym) {
                        javaMatch = (JmlMethodDecl)t;
                        break;
                    }
                }
                if (javaMatch != null) {
                    // The specs file declaration corresponds to
                    // MethodSymbol matchSym and
                    // to a Java source method declaration javaMatch
                    // Cross link them:
                    javaMatch.specsDecl = specsMethodDecl;
                    javaMatch.methodSpecsCombined = combinedSpecs;
                    combinedSpecs.cases.decl = javaMatch;
                } else {
                    // Lack of match already complained about in matchMethod
                    // Could be because it is a model method.
                    combinedSpecs.cases.decl = specsMethodDecl;
                    specsMethodDecl.methodSpecsCombined = combinedSpecs;
                }
            } else {
                specsMethodDecl.methodSpecsCombined = combinedSpecs;
            }
            specs.putSpecs(matchSym,combinedSpecs);
        }
        
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


        return matchSym;
    }

    void finishSpecClass(JmlClassDecl specsDecl, Env<AttrContext> env) {
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("FINISHING SPEC CLASS " + specsDecl.sym.fullname);
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
            if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("FINISHING SPEC CLASS - JML PHASE " + specsDecl.sym.fullname);
            JmlSpecs.TypeSpecs tsp = specs.get(specsDecl.sym);
            if (tsp == null) {
                tsp = new JmlSpecs.TypeSpecs();
                specs.putSpecs(specsDecl.sym,tsp);
            }
            tsp.decl = specsDecl;
            tsp.modifiers = specsDecl.mods;
            tsp.file = specsDecl.source();
            
            JmlClassDecl jtree = null; // This is a binary class - no java class declaration
            ClassSymbol csym = specsDecl.sym; // just a symbol

            prevSource = log.useSource(specsDecl.source());
            checkTypeMatch(csym,specsDecl);
            log.useSource(prevSource);

            for (JmlTypeClause clause: tsp.clauses) {
                if (clause instanceof JmlTypeClauseDecl) {
                    // These are JML declarations
                    JmlTypeClauseDecl cl = (JmlTypeClauseDecl)clause;
                    JCTree tr = cl.decl;
                    // We have already entered any model classes
                    // but we need to enter model methods and ghost and model fields
                    if (tr instanceof JmlVariableDecl) {
                        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("JML VAR ENTER FOR " + specsDecl.name + " " + ((JmlVariableDecl)tr).name);
                        memberEnter(tr,env);
                    } else if (tr instanceof JmlMethodDecl) {
                        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("JML METH ENTER FOR " + specsDecl.name + " " + ((JmlMethodDecl)tr).name);
                        memberEnter(tr,env);
                    }
                }
            }
            
            // At this point, all java and spec members are entered
            // and types have their combined specs defined
            // We still need to combine the field and method specs

            // FIXME - what about blocks

            // First for Java fields and methods
            
            Integer matchpos;
            Map<Symbol,Integer> matches = new HashMap<Symbol,Integer>();
            for (JCTree t: specsDecl.defs) {
                if (t instanceof JmlVariableDecl) {
                    VarSymbol vsym = matchAndCombineFieldSpecs(jtree,csym,(JmlVariableDecl)t);
                    if (vsym != null && (matchpos=matches.put(vsym,((JmlVariableDecl)t).pos)) != null) {
                        int p = ((JmlVariableDecl)t).pos;
                        log.error(p,"jml.duplicate.var.match",((JmlVariableDecl)t).name);
                        log.error(matchpos,"jml.associated.decl.cf",
                        		utils.locationString(p));
                    }
                } else if (t instanceof JmlMethodDecl) {
                    MethodSymbol msym = matchAndCombineMethodSpecs(jtree,csym,(JmlMethodDecl)t,env);
                    if (msym != null && (matchpos=matches.put(msym,((JmlMethodDecl)t).pos)) != null) {
                        int p = ((JmlMethodDecl)t).pos;
                        log.error(p,"jml.duplicate.method.match",((JmlMethodDecl)t).name);
                        log.error(matchpos,"jml.associated.decl.cf",
                        		utils.locationString(p));
                    }
                }
            }
            matches.clear();
            
            // Then for specs fields and methods
            
            for (JmlTypeClause t: specsDecl.typeSpecs.clauses) {
                if (t instanceof JmlTypeClauseDecl) {
                    JmlTypeClauseDecl tcd = (JmlTypeClauseDecl)t;
                    if (tcd.decl instanceof JmlVariableDecl) {
                        matchAndCombineFieldSpecs(jtree,csym,(JmlVariableDecl)tcd.decl);
                    } else if (tcd.decl instanceof JmlMethodDecl) {
                        matchAndCombineMethodSpecs(jtree,csym,(JmlMethodDecl)tcd.decl,env);
                    }
                }
            }
            
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
            
            for (JmlTypeClause t: specsDecl.typeSpecs.clauses) {
                if (t instanceof JmlTypeClauseDecl) {
                    JmlTypeClauseDecl tcd = (JmlTypeClauseDecl)t;
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
//                        Log.instance(context).error(vardecl.pos(),"jml.no.var.match",vardecl.name);
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
//                        Log.instance(context).error(t.pos(),"jml.misplaced.var.spec",((JmlTypeClause)t).token.internedName());
//                    } else {
//                        mostRecentFieldSpecs.list.append((JmlTypeClause)t);
//                        if (t instanceof JmlTypeClauseIn) ((JmlTypeClauseIn)t).parentVar = mostRecentVarDecl;
//                    }
//                } else if (t instanceof JmlTypeClauseInitializer) {
//                    mostRecentFieldSpecs = null;
//                    if (((JmlTypeClauseInitializer)t).token == JmlToken.INITIALIZER) {
//                        if (tsp.initializerSpec != null) {
//                            Log.instance(context).error(t.pos,"jml.one.initializer.spec.only");
//                        } else {
//                            if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
//                            ((JmlTypeClauseInitializer)t).specs = savedMethodSpecs;
//                            tsp.initializerSpec = ((JmlTypeClauseInitializer)t);
//                        }
//                    } else {
//                        if (tsp.staticInitializerSpec != null) {
//                            Log.instance(context).error(t.pos,"jml.one.initializer.spec.only");
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
//                    Log.instance(context).error(savedMethodSpecs.pos(),"jml.misplaced.method.specs",specsDecl.name);
//                    savedMethodSpecs = null;
//                }
//            }
//            specsDecl.defs = newdefs.toList();
//            if (savedMethodSpecs != null) {
//                Log.instance(context).error(savedMethodSpecs.pos(),"jml.misplaced.method.specs",specsDecl.name);
//                savedMethodSpecs = null;
//            }
                // FIXME - are method and field specs already where they belong?
                // FIXME = use a visitor to be more O-O ?
            // FIXME - unify this method with the near duplicate above
        } finally {
            addRacMethods(specsDecl.sym,env);
            resolve.setAllowJML(prevAllowJML);
            Log.instance(context).useSource(prevSource);
            if (utils.jmlverbose >= Utils.JMLDEBUG) {
                log.noticeWriter.println("FINISHING SPEC CLASS - COMPLETE " + specsDecl.sym.fullname);
                log.noticeWriter.println("   SCOPE IS " + specsDecl.sym.members());
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
                List.<JCVariableDecl>nil(),
                List.<JCExpression>nil(),
                jmlF.Block(0,List.<JCStatement>nil()), 
                null);
        ms.specsDecl = ms;
        
        utils.setJML(m.mods);
        utils.setJML(ms.mods);
        JCAnnotation a = tokenToAnnotationAST(JmlToken.HELPER);
        m.mods.annotations = m.mods.annotations.append(a);
        ms.mods.annotations = ms.mods.annotations.append(a);
        a = tokenToAnnotationAST(JmlToken.PURE);
        m.mods.annotations = m.mods.annotations.append(a);
        ms.mods.annotations = ms.mods.annotations.append(a);
        a = tokenToAnnotationAST(JmlToken.MODEL);
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
        for (JmlTypeClause t : tsp.clauses) {
            if (!(t instanceof JmlTypeClauseDecl)) continue;
            JmlTypeClauseDecl td = (JmlTypeClauseDecl)t;
            if (!(td.decl instanceof JCVariableDecl)) continue;
            JCVariableDecl vdecl = (JCVariableDecl)td.decl;
            JCAnnotation modelAnnotation = JmlAttr.instance(context).findMod(vdecl.mods,JmlToken.MODEL);
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
            tsp.clauses.append(tcd);
        }
    }
    
    /** For synthetic methods or methods that do not have occasion to declare
     * specs in a specification file, this sets the combined specs to be those
     * that are associated with the method declaration itself.
     * @param mdecl
     */
    protected void setDefaultCombinedMethodSpecs(JmlMethodDecl mdecl) {
        mdecl.methodSpecsCombined = new JmlSpecs.MethodSpecs(mdecl.mods,mdecl.cases);
        specs.putSpecs(mdecl.sym,mdecl.methodSpecsCombined);
    }

    protected void checkSameAnnotations(Symbol sym, JCModifiers mods) {
        if (sym.getAnnotationMirrors() == null) return;
        PackageSymbol p = ((JmlAttr)attr).annotationPackageSymbol;
        for (Compound a  : sym.getAnnotationMirrors()) {
            if (a.type.tsym.owner.equals(p) && utils.findMod(mods,a.type.tsym) == null) {
                
                log.error(mods.pos,"jml.missing.annotation",a);
            }
        }
    }

    protected void checkSameAnnotations(JCModifiers javaMods, JCModifiers mods) {
        PackageSymbol p = ((JmlAttr)attr).annotationPackageSymbol;
        for (JCAnnotation a: javaMods.getAnnotations()) {
            if (a.type.tsym.owner.equals(p) && utils.findMod(mods,a.type.tsym) == null) {
                log.error(mods.pos,"jml.missing.annotation",a);
            }
        }
    }

    public void checkFieldMatch(JmlVariableDecl javaField, VarSymbol javaSym, JmlVariableDecl specField) {
        if (javaField == specField) return;
        // Presume that we can't get here unless the names are the same
        // FIXME - attribAnnotations, compare annotations
        JavaFileObject prev = log.currentSourceFile();
        log.useSource(specField.sourcefile);
        {
            // Check that modifiers are the same
            long javaFlags = javaSym.flags();
            long specFlags = specField.mods.flags;
            boolean isInterface = (javaFlags & Flags.INTERFACE) != 0;
            long diffs = (javaFlags ^ specFlags)&(isInterface? Flags.InterfaceVarFlags : Flags.VarFlags);
            if (diffs != 0) {
                Log.instance(context).error(specField.pos(),"jml.mismatched.field.modifiers", specField.name, javaSym.enclClass().getQualifiedName()+"."+javaSym.name,Flags.toString(diffs));  // FIXME - test this
            }
//  FIXME _ this needs to be implements
// FIXME - what if an annotation is declared within the class?
//            attr.attribAnnotationTypes(javaField.mods.annotations, env);
//            checkSameAnnotations(javaField.mods,specField.mods);
        }
        
        {
            // check for no initializer
            if (specField.getInitializer() != null && specField != javaField &&
                    !utils.isJML(specField.mods)) {
                log.error(specField.getInitializer().pos(),"jml.no.initializer.in.specs",javaSym.enclClass().getQualifiedName()+"."+javaSym.name);
            }
        }
        {
            // check that types are the same
            Attr.instance(context).attribType(specField.vartype, javaSym.enclClass());
            if (!Types.instance(context).isSameType(javaSym.type,specField.vartype.type)) {
                Log.instance(context).error(specField.vartype.pos(),"jml.mismatched.field.types",specField.name,javaSym.enclClass().getQualifiedName()+"."+javaSym.name,specField.vartype.type,javaField.vartype.type);
                // This seems like a serious error , can we continue - FIXME
            }
        }
        log.useSource(prev);
    }
    
    public void checkFieldMatch(VarSymbol javaFieldSymbol, JmlVariableDecl specField) {
        // Presume that we can't get here unless the names are the same
        // FIXME - attribAnnotations, compare annotations
        {
            // Check that modifiers are the same
            long javaFlags = javaFieldSymbol.flags();
            long specFlags = specField.mods.flags;
            boolean isInterface = (javaFlags & Flags.INTERFACE) != 0;
            long diffs = (javaFlags ^ specFlags)&(isInterface? Flags.InterfaceVarFlags : Flags.VarFlags);
            if (diffs != 0) {
                Log.instance(context).error(specField.pos(),"jml.mismatched.field.modifiers", specField.name, javaFieldSymbol.enclClass().getQualifiedName()+"."+javaFieldSymbol.name,Flags.toString(diffs));  // FIXME - test this
            }
// FIXME - this needs to be implemented
// checkSameAnnotations(javaFieldSymbol,specField.mods);
        }
        {
            // check for no initializer
            if (specField.getInitializer() != null && specField.sourcefile.getKind() != Kind.SOURCE &&
                    !utils.isJML(specField.mods)) {
                Log.instance(context).error(specField.getInitializer().pos(),"jml.no.initializer.in.specs",javaFieldSymbol.enclClass().getQualifiedName()+"."+javaFieldSymbol.name);
            }
        }
        {
            // check that types are the same
            //Attr.instance(context).attribType(specField.vartype, javaField.sym.enclClass());
            Attr.instance(context).attribType(specField.vartype, javaFieldSymbol.enclClass());
            if (!Types.instance(context).isSameType(javaFieldSymbol.type,specField.vartype.type)) {
                Log.instance(context).error(specField.vartype.pos(),"jml.mismatched.field.types",specField.name,javaFieldSymbol.enclClass().getQualifiedName()+"."+javaFieldSymbol.name,specField.vartype.type,javaFieldSymbol.type);
                // This seems like a serious error , can we continue - FIXME
            }
        }

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
                if (diffs != 0) Log.instance(context).error(specsClassDecl.pos(),"jml.mismatched.modifiers", specsClassDecl.name, javaClassSym.fullname, Flags.toString(diffs));  // FIXME - test this
                // FIXME - how can we tell where in which specs file the mismatched modifiers are
                // SHould probably check this in the combining step
            }
            // FIXME - this is needed, but it is using the environment from the java class, not the 
            // spec class, and so it is using the import statements in the .java file, not those in the .jml file
            attr.attribAnnotationTypes(specsClassDecl.mods.annotations, baseEnv(javaDecl,env));  // FIXME - this is done later; is it needed here?

            checkSameAnnotations(javaDecl.mods,specsClassDecl.mods);
            // FIXME - check that both are Enum; check that both are Annotation
        }
        if (specsClassDecl.source() == null || specsClassDecl.source().getKind() == JavaFileObject.Kind.SOURCE){
            // This is already checked in enterTypeParametersForBinary (for binary classes)
            List<Type> t = ((Type.ClassType)javaClassSym.type).getTypeArguments();
            List<JCTypeParameter> specTypes = specsClassDecl.typarams;
            if (t.size() != specTypes.size()) {
                Log.instance(context).error(specsClassDecl.pos(),"jml.mismatched.type.arguments",javaClassSym.fullname,javaClassSym.type.toString());
            }
            // FIXME - check that the names and bounds are the same
        }
    }
    
    public void checkTypeMatch(ClassSymbol javaClassSym, JmlClassDecl specsClassDecl) {
        
        // Check annotations
        JmlSpecs.TypeSpecs combinedTypeSpecs = specs.get(javaClassSym);
        
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
                if (diffs != 0) Log.instance(context).error(specsClassDecl.pos(),"jml.mismatched.modifiers", specsClassDecl.name, javaClassSym.fullname, Flags.toString(diffs));  // FIXME - test this
            }
            // FIXME - check that both are Enum; check that both are Annotation
            checkSameAnnotations(javaClassSym,specsClassDecl.mods);
        }
        {
            List<Type> t = ((Type.ClassType)javaClassSym.type).getTypeArguments();
            List<JCTypeParameter> specTypes = specsClassDecl.typarams;
            if (t.size() != specTypes.size()) {
                Log.instance(context).error(specsClassDecl.pos(),"jml.mismatched.type.arguments",javaClassSym.fullname,javaClassSym.type.toString());
            }
            // FIXME - check that the names and bounds are the same
        }
    }
    
    public MethodSymbol matchMethod(JmlMethodDecl specMethod, ClassSymbol csym, Env<AttrContext> env, boolean complain) {
//        if (csym.flatName().toString().equals("tt.TestJava")) {
//            System.out.println(csym);
//        }
        JCMethodDecl tree = specMethod;

        MethodSymbol msym = tree.sym;
        MethodSymbol mtemp = msym;
        Env<AttrContext> localEnv = null;
        if (msym != null) {
            localEnv = methodEnv(tree, env);
        } else {
            // Copied from MemberEnter.visitMethodDef which can't be called directly
            Scope enclScope = enter.enterScope(env);
            mtemp = new MethodSymbol(0, tree.name, null, enclScope.owner);
            //m.flags_field = chk.checkFlags(tree.pos(), tree.mods.flags, m, tree);
            tree.sym = mtemp;
            localEnv = methodEnv(tree, env);

            // Compute the method type
            mtemp.type = signature(tree.typarams, tree.params,
                               tree.restype, tree.thrown,
                               localEnv);

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
            annotateLater(tree.mods.annotations, localEnv, mtemp);
            if (tree.defaultValue != null)
                annotateDefaultValueLater(tree.defaultValue, localEnv, mtemp);
        }
        // If tree.sym != null, then it should be the case that specMethod is part of the javaClassDecl
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

        // mark the method varargs, if necessary
        //boolean varargs = (lastParam != null && (lastParam.mods.flags & Flags.VARARGS) != 0);
        //if (varargs) msym.flags_field |= Flags.VARARGS;
        
        // JmlResolve.findMethod is designed for matching a method call to some
        // declaration.  Here however, we are trying to match to method signatures.
        // We use this as a start, but then have to check that we have exact matches
        // for parameter types.  Also, we make the match using varargs=false - 
        // the parameter types themselves are already arrays if they were declared
        // as varargs parameters.

        Symbol s = JmlResolve.instance(context).findMethod(env,csym.asType(),
                tree.name,paramTypes.toList(),typaramTypes.toList(),
                /*allowBoxing*/false,/*varargs*/false,/*is an operator*/false);
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
        
        if (match == null) {
            if (complain && (specMethod.mods.flags & Flags.GENERATEDCONSTR) == 0 && !inModelTypeDeclaration) {
                Log.instance(context).error(specMethod.pos(),"jml.no.method.match",
                    csym.flatName() + "." + mtemp);
            }
        } else {
//            boolean isModel = JmlAttr.instance(context).findMod(specMethod.mods,JmlToken.MODEL) != null;
//            boolean isMatchModel = match.attribute(((JmlAttr)attr).tokenToAnnotationSymbol.get(JmlToken.MODEL)) != null;
//            if (isModel == isMatchModel) {
                checkMethodMatch(match,specMethod,csym);
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
//                Log.instance(context).error(specMethod.pos(),"jml.no.method.match",
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
//                Log.instance(context).error(specMethod.pos(),"jml.no.method.match",
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

    public void checkMethodMatch(JmlMethodDecl match, JmlMethodDecl specMethodDecl) {
        if (match == specMethodDecl) return;
        {
            boolean isInterface = match.sym.enclClass().isInterface();
            // Check that modifiers are the same
            long matchf = match.mods.flags;
            long specf = specMethodDecl.mods.flags;
            //matchf &= ~(~specf & Flags.SYNCHRONIZED); // Ignore synchronized modifiers on implementation
            long diffs = (matchf ^ specf)&Flags.MethodFlags;
            if (diffs != 0) {
                if ((Flags.NATIVE & matchf & ~specf)!= 0) diffs &= ~Flags.NATIVE;
                if (isInterface) diffs &= ~Flags.PUBLIC & ~Flags.ABSTRACT;
                if (diffs != 0) Log.instance(context).error(specMethodDecl.pos(),"jml.mismatched.method.modifiers", specMethodDecl.name, match.sym.toString(), Flags.toString(diffs));  // FIXME - test thi
            }
            
// FIXME - this needs to be implemented
//            // FIXME - what if an annotation is declared within the class?
//            attr.attribAnnotationTypes(match.mods.annotations, baseEnv(currentClass,env));
//            checkSameAnnotations(match.mods,specMethodDecl.mods);
            
            // Check that parameter names are the same (a JML requirement to avoid having to rename within specs)
            // FIXME - the modeOfFileBeingChecked is not reliable
            //if (modeOfFileBeingChecked != JmlCompilationUnit.SPEC_FOR_BINARY && modeOfFileBeingChecked != JmlCompilationUnit.SPEC_ALONE) {
            {
                for (int i = 0; i<match.getParameters().size(); i++) {
                    Symbol.VarSymbol javasym = match.getParameters().get(i).sym;
                    JCTree.JCVariableDecl vv = specMethodDecl.params.get(i);
                    if (!javasym.name.equals(vv.name)) {
                        Log.instance(context).error(vv.pos(),"jml.mismatched.param.names",i,
                                match.sym.enclClass().fullname + "." + match.sym.toString(),
                                vv.name, javasym.name);
                    }
                }
            }
            // A specification method may not have a body.  However, the spec
            // method declaration may also be identical to the java method (if the
            // java file is in the specification sequence) - hence the second test.
            // There is an unusual case in which a method declaration is duplicated
            // in a .java file (same signature).  In that case, there is already
            // an error message, but the duplicate will be matched against the
            // first declaration at this point, though they are different
            // delcarations (so the second test will be true).  Hence we include the
            // 3rd test as well. [ TODO - perhaps we need just the third test and not the second.]
            if (specMethodDecl.body != null && match != specMethodDecl
                    && match.sourcefile != specMethodDecl.sourcefile
                    && (specMethodDecl.mods.flags & (Flags.GENERATEDCONSTR|Flags.SYNTHETIC)) == 0) {
                Log.instance(context).error(specMethodDecl.body.pos(),"jml.no.body.allowed",match.sym.enclClass().fullname + "." + match.sym.toString());
            }
            
            // Check that the return types are the same
            if (specMethodDecl.restype != null) { // not a constructor
                if (specMethodDecl.restype.type == null) Attr.instance(context).attribType(specMethodDecl.restype, match.sym.enclClass());
//                if (match.name.toString().equals("defaultEmpty")) {
//                    log.noticeWriter.println(match.name);
//                }
                if (!Types.instance(context).isSameType(match.restype.type,specMethodDecl.restype.type)) {
                    // FIXME - when the result type is parameterized in a static method, the java and spec declarations
                    // end up with different types for the parameter.  Is this also true for the regular parameters?  
                    // FIXME - avoud the probloem for now.
                    if (!(specMethodDecl.restype.type.getTypeArguments().head instanceof Type.TypeVar))
                    Log.instance(context).error(specMethodDecl.restype.pos(),"jml.mismatched.return.type",
                            match.sym.enclClass().fullname + "." + match.sym.toString(),
                            specMethodDecl.restype.type,match.restype.type);
                }
            }
            
            // FIXME - check that JML annotations match
        }
    }

    public void checkMethodMatch(MethodSymbol match, JmlMethodDecl specMethodDecl, ClassSymbol javaClassSymbol) {
        JavaFileObject prev = log.currentSourceFile();
        log.useSource(specMethodDecl.sourcefile);
        {
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
                        //log.noticeWriter.println("MATCH: " + Flags.toString(matchf));
                        //log.noticeWriter.println("SPECS: " + Flags.toString(specf));
                        log.error(specMethodDecl.pos(),"jml.mismatched.method.modifiers", specMethodDecl.name, match.toString(), Flags.toString(diffs));  // FIXME - test thi
                }
            }
            
         // FIXME - this needs to be implemented
            //checkSameAnnotations(match,specMethodDecl.mods);
            
            boolean isGhost = JmlAttr.instance(context).findMod(specMethodDecl.mods,JmlToken.GHOST) != null;
            boolean isModel = JmlAttr.instance(context).findMod(specMethodDecl.mods,JmlToken.MODEL) != null;

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
            if (JmlCompilationUnit.isForSource(modeOfFileBeingChecked)) {
                for (int i = 0; i<match.getParameters().size(); i++) {
                    Symbol.VarSymbol javasym = match.getParameters().get(i);
                    JCTree.JCVariableDecl vv = specMethodDecl.params.get(i);
                    if (!javasym.name.equals(vv.name)) {
                        log.error(vv.pos(),"jml.mismatched.param.names",i,
                                match.enclClass().fullname + "." + match.toString(),
                                javasym.name, vv.name);
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
            
            // Check that the return types are the same
            boolean hasTypeParameters = specMethodDecl.getTypeParameters().size() != 0;  // FIXME - figure out how to do proper type matching 
            if (!hasTypeParameters && specMethodDecl.restype != null) { // not a constructor
                if (specMethodDecl.restype.type == null) attr.attribType(specMethodDecl.restype, match.enclClass());
                if (!Types.instance(context).isSameType(match.getReturnType(),specMethodDecl.restype.type)) {
                    log.error(specMethodDecl.restype.pos(),"jml.mismatched.return.type",
                            match.enclClass().fullname + "." + match.toString(),
                            specMethodDecl.restype.type,match.getReturnType());
                }
            }
            
            
            log.useSource(prev);
            // FIXME - what about covariant return types ?????
            
            // FIXME - check that JML annotations are ok
        }
    }
    
    public void addAnnotations(Symbol sym, Env<AttrContext> env, JCTree.JCModifiers mods) {
        if (env == null) {
            log.noticeWriter.println("NULL ENV " + sym);
        }
        annotateLaterConditional(mods.annotations, env, sym);
//        for (JCAnnotation a: mods.annotations) {
//            if (sym.attribute(a.type.tsym) == null) {
//                
//            }
//        }
    }

    public void completeBinaryTodo() {
        java.util.List<Env<AttrContext>> todo = ((JmlEnter)JmlEnter.instance(context)).binaryMemberTodo;
        Env<AttrContext> env;
        while (!todo.isEmpty()) {
            env = todo.remove(0);
            if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("DOING BINARY TODO " + 
                    (env.toplevel.sourcefile));
            
            completeSpecCUForBinary(env); // Might add more to to todo list
        }
    }
    
//    public void completeBinaryTodo(Context context) {
//        java.util.List<Env<AttrContext>> todo = ((JmlEnter)JmlEnter.instance(context)).binaryMemberTodo;
//        Env<AttrContext> env;
//        while (!todo.isEmpty()) {
//            env = todo.remove(0);
//            if (utils.jmldebug) log.noticeWriter.println("DOING BINARY TODO " + 
//                    (env.toplevel.sourcefile));
//            
//            completeSpecCUForBinary(env); // Might add more to to todo list
//        }
//    }
    
    // We have to do the equivalent of complete, except that the Java class is
    // already completed and all we want to do is the spec part.  Note that 
    // super.complete is for class symbols.
    public void completeSpecCUForBinary(Env<AttrContext> specEnv) {
        Env<AttrContext> prevEnv = env;
        env = specEnv;
        JavaFileObject prev = Log.instance(context).useSource(specEnv.toplevel.sourcefile);
        specEnv.toplevel.accept(this); // process imports into current env
        
        int prevMode = modeOfFileBeingChecked;
        modeOfFileBeingChecked = ((JmlCompilationUnit)specEnv.toplevel).mode;

        // FIXME - here we are doing primary and secondary types - is that what we want?
        for (JCTree dd: ((JmlCompilationUnit)specEnv.toplevel).defs) {
            // There are also import declarations in defs
            if (dd instanceof JmlClassDecl) {
                env = specEnv; //enter.typeEnvs.get(((JmlClassDecl)dd).sym); - binary sym does not have a toplevel tree
                JmlClassDecl d = (JmlClassDecl)dd;
                completeSpecClassForBinary(d);
            }
        }
        // Model declarations will already have been processed as regular source classes
        
        // We need to put the compilation unit on the todo list for attribution
        // WAS: Todo.instance(context).append(enter.typeEnvs.get(((JmlCompilationUnit)env.tree).packge));
        //Todo.instance(context).append(specEnv); - NO - we put the individual classes on, in completeSpecClassForBInary
        env = prevEnv;
        Log.instance(context).useSource(prev);
        modeOfFileBeingChecked = prevMode;
    }
    
    public void completeSpecClassForBinary(JmlClassDecl classDecl) {
        Env<AttrContext> prev = env;
        ClassSymbol classSym = classDecl.sym;
        if (classSym == null) {
            // This happens when a Java class declaration in the spec file has no
            // match in the binary class.  So we just skip it.  It has already
            // been reported in JmlEnter.
            return;
        }
        if (classSym.completer != null) {
            classSym.completer.complete(classSym);
        }
        env = classDecl.env;
        attr.attribAnnotationTypes(classDecl.mods.annotations, baseEnv(classDecl,env));  // FIXME - this is done later; is it needed here?
        
        { // Copied (and edited) from MemberEnter.java 
            JmlAttr attr = JmlAttr.instance(context);
            ClassSymbol c = classSym;
            ClassType ct = (ClassType)c.type;
            Env<AttrContext> env = classDecl.env;
            JCClassDecl tree = classDecl;
//            boolean wasFirst = isFirst;
//            isFirst = false;

            JavaFileObject prevv = log.useSource(env.toplevel.sourcefile);
            try {
                // Save class environment for later member enter (2) processing.
//                halfcompleted.append(env);

                // Mark class as not yet attributed.
                c.flags_field |= UNATTRIBUTED;

                // If this is a toplevel-class, make sure any preceding import
                // clauses have been seen.
//                if (c.owner.kind == PCK) {
//                    memberEnter(env.toplevel, env.enclosing(JCTree.TOPLEVEL));
//                    todo.append(env);
//                }

//                if (c.owner.kind == TYP)
//                    c.owner.complete();  // FIXME - should this force a loading of binary specs

                // create an environment for evaluating the base clauses
                Env<AttrContext> baseEnv = baseEnv(tree, env);

                // Determine supertype.
                Type supertype =
                    (tree.extending != null)
                    ? attr.attribBase(tree.extending, baseEnv, true, false, true)
//                    : ((tree.mods.flags & Flags.ENUM) != 0 && !target.compilerBootstrap(c))
//                    ? attr.attribBase(enumBase(tree.pos, c), baseEnv,
//                                      true, false, false)
                    : (c.fullname == names.java_lang_Object)
                    ? Type.noType
                    : syms.objectType;
//                ct.supertype_field = supertype;

                // Determine interfaces.
                ListBuffer<Type> interfaces = new ListBuffer<Type>();
                Set<Type> interfaceSet = new HashSet<Type>();
                List<JCExpression> interfaceTrees = tree.implementing;
//              if ((tree.mods.flags & Flags.ENUM) != 0 && target.compilerBootstrap(c)) {
//                    // add interface Comparable<T>
//                    interfaceTrees =
//                        interfaceTrees.prepend(make.Type(new ClassType(syms.comparableType.getEnclosingType(),
//                                                                       List.of(c.type),
//                                                                       syms.comparableType.tsym)));
//                    // add interface Serializable
//                    interfaceTrees =
//                        interfaceTrees.prepend(make.Type(syms.serializableType));
//                }
                for (JCExpression iface : interfaceTrees) {
                    Type i = attr.attribBase(iface, baseEnv, false, true, true);
//                    if (i.tag == CLASS) {
//                        interfaces.append(i);
//                        chk.checkNotRepeated(iface.pos(), types.erasure(i), interfaceSet);
//                    }
                }
//                if ((c.flags_field & ANNOTATION) != 0)
//                    ct.interfaces_field = List.of(syms.annotationType);
//                else
//                    ct.interfaces_field = interfaces.toList();

//                if (c.fullname == names.java_lang_Object) {
//                    if (tree.extending != null) {
//                        chk.checkNonCyclic(tree.extending.pos(),
//                                           supertype);
//                        ct.supertype_field = Type.noType;
//                    }
//                    else if (tree.implementing.nonEmpty()) {
//                        chk.checkNonCyclic(tree.implementing.head.pos(),
//                                           ct.interfaces_field.head);
//                        ct.interfaces_field = List.nil();
//                    }
//                }

                // Annotations.
                // In general, we cannot fully process annotations yet,  but we
                // can attribute the annotation types and then check to see if the
                // @Deprecated annotation is present.
                attr.attribAnnotationTypes(tree.mods.annotations, baseEnv);
//                if (hasDeprecatedAnnotation(tree.mods.annotations))
//                    c.flags_field |= DEPRECATED;
                annotateLater(tree.mods.annotations, baseEnv, c); 
                    // The call above nulls out the attributes field; it is recomputed
                    // when annotate.flush() is called.  But this has the effect of
                    // deleting any annotations that were recovered from the
                    // binary file.  (FIXME) I'm not sure we want that.
                
//                chk.checkNonCyclic(tree.pos(), c.type);

                attr.attribTypeVariables(tree.typarams, baseEnv);

                // Add default constructor if needed.
//                if ((c.flags() & INTERFACE) == 0 && !binary && // DRC added for now
//                    !TreeInfo.hasConstructors(tree.defs)) {
//                    List<Type> argtypes = List.nil();
//                    List<Type> typarams = List.nil();
//                    List<Type> thrown = List.nil();
//                    long ctorFlags = 0;
//                    boolean based = false;
//                    if (c.name.isEmpty()) {
//                        JCNewClass nc = (JCNewClass)env.next.tree;
//                        if (nc.constructor != null) {
//                            Type superConstrType = types.memberType(c.type,
//                                                                    nc.constructor);
//                            argtypes = superConstrType.getParameterTypes();
//                            typarams = superConstrType.getTypeArguments();
//                            ctorFlags = nc.constructor.flags() & VARARGS;
//                            if (nc.encl != null) {
//                                argtypes = argtypes.prepend(nc.encl.type);
//                                based = true;
//                            }
//                            thrown = superConstrType.getThrownTypes();
//                        }
//                    }
//                    JCTree constrDef = DefaultConstructor(make.at(tree.pos), c,
//                                                        typarams, argtypes, thrown,
//                                                        ctorFlags, based);
//                    tree.defs = tree.defs.prepend(constrDef);
//                }

                // If this is a class, enter symbols for this and super into
                // current scope.
                if (true) {  // Allow this in interfaces
                    VarSymbol thisSym =
                        new VarSymbol(FINAL | HASINIT, names._this, c.type, c);
                    thisSym.pos = Position.FIRSTPOS;
                    env.info.scope.enter(thisSym);
                }
                if ((c.flags_field & INTERFACE) == 0) {
                    if (ct.supertype_field.tag == CLASS) {
                        VarSymbol superSym =
                            new VarSymbol(FINAL | HASINIT, names._super,
                                          ct.supertype_field, c);
                        superSym.pos = Position.FIRSTPOS;
                        env.info.scope.enter(superSym);
                    }
                }

                // check that no package exists with same fully qualified name,
                // but admit classes in the unnamed package which have the same
                // name as a top-level package.
//                if (checkClash &&
//                    c.owner.kind == PCK && c.owner != syms.unnamedPackage &&
//                    reader.packageExists(c.fullname))
//                    {
//                        log.error(tree.pos, "clash.with.pkg.of.same.name", c);
//                    }

            } catch (CompletionFailure ex) {
                Check.instance(context).completionError(tree.pos(), ex);
            } finally {
                log.useSource(prevv);
                annotate.flush();
            }

        }

        //env = enter.classEnv(d,env);
        //enter.typeEnvs.put(d.sym,env);
        
        if (classDecl.sym.members() instanceof Scope.ErrorScope) {
            // Errors occured making this symbol unresolveable
            // Catastrophes await if we proceed.  If errors have been reported
            // we figure that is the cause.
            if (log.nerrors == 0) log.error("jml.internal","Type " + classDecl.sym + " is unexpectedly lacking proper scope information");
            return;
        }
        
        // FIXME - use a tree walker?  do we need to do nested classes?
        Map<Symbol,Integer> matchedSyms = new HashMap<Symbol,Integer>();
        ListBuffer<JCTree> remove = null;
        for (JCTree t: classDecl.defs) {
            if (t instanceof JmlVariableDecl) {
                JmlVariableDecl vd = (JmlVariableDecl)t;
                VarSymbol vsym = findVarMatch(classDecl.sym,vd.name);
                if (utils.isJML(vd.mods)) {
                    // misplaced JML declaration
                } else if (vsym == null) {
                    // Java declaration in spec file does not match anything in the binary file
                    log.error(vd.pos,"jml.no.var.match",vd.name);
                    if (remove == null) remove = new ListBuffer<JCTree>();
                    remove.append(t);
                } else {
                    Integer matchpos;
                    if ((matchpos=matchedSyms.put(vsym,vd.pos)) != null) {
                        log.error(vd.pos,"jml.duplicate.var.match",vd.name);
                        log.error(matchpos,"jml.associated.decl.cf",
                        		utils.locationString(vd.pos));
                    }
                    vd.sym = vsym;
                    checkFieldMatch(vsym,vd);
                    // FIXME - do we need to asjust the flags as in visitVarDef

                    JmlSpecs.FieldSpecs fspecs = specs.getSpecs(vsym);
                    if (fspecs == null) {
                        specs.putSpecs(vsym, fspecs = new JmlSpecs.FieldSpecs(vd.mods));
                    } else {
                        fspecs.mods = vd.mods;
                        if (vd.fieldSpecs != null) fspecs.list.appendList(vd.fieldSpecs.list);
                    }
                }

            } else if (t instanceof JmlMethodDecl) {
                JmlMethodDecl md = (JmlMethodDecl)t;
//                if (md.name.toString().equals("equals")) {
//                    log.noticeWriter.println(md.name);
//                }

                MethodSymbol msym = matchAndCombineMethodSpecs(null,classDecl.sym,md,env);
                //if (msym != null) checkMethodMatch(msym,md,d.sym);  // Done in the call above
                //MethodSymbol msym = matchMethod(md,d.sym,env);
                if (utils.isJML(md.mods)) {
                    // misplaced JML declaration
                } else if (msym == null) {
                    // Already complained about in matchMethod via matchAndCombineMethodSpecs
                    // Java declaration in spec file does not match anything in the binary file
                    //log.error(md.pos,"jml.no.method.match",md.name,"");
                    if (remove == null) remove = new ListBuffer<JCTree>();
                    remove.append(t);
                } else {
                    md.sym = msym;
                    // checkMethodMatch already called in matchMethod via matchAndCombineMethodSpecs
                    //checkMethodMatch(msym,md,d.sym);
                    
                    JmlMethodSpecs mdspecs = md.cases;
                    JmlSpecs.MethodSpecs mspecs = specs.getSpecs(msym);
                    if (mspecs == null) {
                        specs.putSpecs(msym, mspecs = new JmlSpecs.MethodSpecs(md.mods,mdspecs));
                    } else {
                        mspecs.cases.decl = md;
                        mspecs.cases.cases = mdspecs != null ? mdspecs.cases : List.<JmlSpecificationCase>nil();
                    }

                    // FIXME - attach specs to symbol
                }
                
                
            } else if (t instanceof JmlClassDecl) {
                
                // skip - these are handled by their individual completion calls
                
            } else {
                log.noticeWriter.println("Unhandled declaration in spec class for binary: " + t.getClass());
            }
        }
        matchedSyms.clear();
        if (remove != null) {
            ListBuffer<JCTree> newdefs = new ListBuffer<JCTree>();
            List<JCTree> rem = remove.toList();
            for (JCTree t: classDecl.defs) {
                if (t != rem.head) newdefs.append(t);
                else rem = rem.tail;
            }
            classDecl.defs = newdefs.toList();
        }
        // JML fields and methods
        
        boolean previousAllow = resolve.setAllowJML(true);
        if (classDecl.typeSpecsCombined == null) classDecl.typeSpecsCombined = specs.getSpecs(classDecl.sym);
        for (JmlTypeClause t: classDecl.typeSpecsCombined.clauses) {
            if (t instanceof JmlTypeClauseDecl) {
                JmlTypeClauseDecl tcd = (JmlTypeClauseDecl)t;
                if (tcd.decl instanceof JmlVariableDecl) {
                    JmlVariableDecl vd = (JmlVariableDecl)tcd.decl;
                    VarSymbol vsym = findVarMatch(classDecl.sym,vd.name);
                    if (!utils.isJML(vd.mods)) {
                        // INTENRAL ERROR
                    } else if (vsym != null) {
                        log.error(vd.pos,"jml.duplicate.var.binary.match",vd.name);
                    } else {
                        // Is ghost or model ?
                        // Enter the field
                        visitVarDef(vd);
                        // Model/ghost fields have their own specs - FIXME: move this into visitVarDef?
                        if (vd.fieldSpecs == null) {
                            vd.fieldSpecs = vd.fieldSpecsCombined = specs.getSpecs(vd.sym);
                        } else {
                            vd.fieldSpecsCombined = vd.fieldSpecs;
                            specs.putSpecs(vd.sym,vd.fieldSpecsCombined);
                        }
                    }

                } else if (tcd.decl instanceof JmlMethodDecl) {
                    JmlMethodDecl vd = (JmlMethodDecl)tcd.decl;
                    MethodSymbol vsym = matchMethod(vd,classDecl.sym,env,false);
                    if (!utils.isJML(vd.mods)) {
                        // INTENRAL ERROR
                    } else if (vsym != null) {// FIXME -=test this error message
                        log.error(vd.pos,"jml.duplicate.method.binary.match",vd.name);
                    } else {
                        // Is ghost or model ?
                        // Enter the method
                        visitMethodDef(vd);
                        
                        // Model methods have their own specs
                        if (vd.cases == null) vd.cases = specs.defaultSpecs(vd).cases;
                        vd.methodSpecsCombined = new JmlSpecs.MethodSpecs(vd.mods,vd.cases);
                        vd.cases.decl = vd;
                        specs.putSpecs(vd.sym,vd.methodSpecsCombined);
                    }
                } else {
                    log.noticeWriter.println("Unhandled declaration in spec class for binary: " + t.getClass());
                }
            }
        }
        
        resolve.setAllowJML(previousAllow);
        env = prev;
        
        // If we are completing a class with a Java source file then we walk the
        // class declaration, attributing types, creating symbols for each
        // class member (and entering them in the class scope), and noting the
        // symbols in the class AST for each member.
        
        // Here we have a binary class with a spec file.  The binary class
        // already has all the (java) members entered in the class scope.
        // However, we still have to walk the AST for the spec file in order
        // to do the following:
        //      - attribute any types (including annotations)
        //      - check that declarations match Java (binary) symbols
        //      - add ghost/model declarations to the class

        // OLD:
        
//        if (d.mods.annotations.nonEmpty() && d.mods.annotations.head.annotationType.type == null) { // Check if already attributed
//            Env<AttrContext> baseEnv = env; // FIXME  baseEnv(d, env);
//            JmlAttr.instance(context).attribAnnotationTypes(d.mods.annotations, baseEnv);
//            if (hasDeprecatedAnnotation(d.mods.annotations))
//                d.sym.flags_field |= DEPRECATED;
//            annotateLaterConditional(d.mods.annotations, baseEnv, d.sym);
//        }
//
//        Env<AttrContext> cenv = enter.typeEnvs.get(d.sym);
//        // FIXME _ not sure the next four lines are needed
//        if (d.sym.owner.kind == PCK) {
//            Todo.instance(context).append(cenv);
//        }
//        log.noticeWriter.println("BSC " + d.sym + " " + ((d.sym.flags_field&UNATTRIBUTED)!=0?"unattributed":"attributed"));
//        d.sym.flags_field |= UNATTRIBUTED; // Binary classes start life already attributed
//                                // so we need to reset this so that the specifications get processed
//                                            
//        finishClass(d,cenv);

//        boolean prev = binary;
//        binary = true;
//        complete(d.sym);
//        binary = prev;
    }
    
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
    // MAINTENANCE - modified from MemberEnter.annotateLater
    void annotateLaterConditional(final List<JCAnnotation> annotations,
            final Env<AttrContext> localEnv,
            final Symbol s) {
        if (annotations.isEmpty()) return;
        if (s.kind != PCK) s.attributes_field = null; // mark it incomplete for now
        annotate.later(new Annotate.Annotator() {
            public String toString() {
                return "conditional annotate " + annotations + " onto " + s + " in " + s.owner;
            }
            public void enterAnnotation() {
                assert s.kind == PCK || s.attributes_field == null;
                JavaFileObject prev = log.useSource(localEnv.toplevel.sourcefile);
                try {
                    if (s.attributes_field != null &&
                            s.attributes_field.nonEmpty() &&
                            annotations.nonEmpty()) {
//                            log.error(annotations.head.pos,
//                                      "already.annotated",
//                                      kindName(s), s);
                    } else enterAnnotations(annotations, localEnv, s);
                } finally {
                    log.useSource(prev);
                }
            }
        });
    }
    
    void annotateLater(final List<JCAnnotation> annotations,
            final Env<AttrContext> localEnv,
            final Symbol s) {
        annotateLaterConditional(annotations,localEnv,s);
    }

    
//    // duplicated from MemberEnter because it is private
//    private boolean hasDeprecatedAnnotation(List<JCAnnotation> annotations) {
//        Type dt = Symtab.instance(context).deprecatedType;
//        for (List<JCAnnotation> al = annotations; al.nonEmpty(); al = al.tail) {
//            JCAnnotation a = al.head;
//            if (a.annotationType.type == dt && a.args.isEmpty())
//                return true;
//        }
//        return false;
//    }
    
    @Override
    public void visitTopLevel(JCTree.JCCompilationUnit tree) {
        if (tree.starImportScope.elems == null) { // Check if already done
        super.visitTopLevel(tree);
//        if (binary) {
//            // process package annotations
//            annotateLater(tree.packageAnnotations, env, tree.packge);
//
//            // Import-on-demand java.lang.
//            //importAll(tree.pos, reader.enterPackage(names.java_lang), env);
//
//            // Process all import clauses.
//            memberEnter(tree.defs, env);
//        }
        // Import-on-demand org.jmlspecs.lang.
        importAll(tree.pos, ClassReader.instance(context).enterPackage(org_jmlspecs_lang), env);
        }
    }
    
    JmlMethodDecl currentMethod = null;
    
    @Override 
    public void visitMethodDef(JCMethodDecl tree) {
//        if (tree.name.toString().equals("containsObject")) {
//            log.noticeWriter.println(tree.name);
//        }
        JmlMethodDecl prevMethod = currentMethod;
        currentMethod = (JmlMethodDecl) tree;
        boolean isSpecFile = currentMethod.sourcefile == null || currentMethod.sourcefile.getKind() != JavaFileObject.Kind.SOURCE;
        boolean isClassModel = ((JmlAttr)attr).isModel(env.enclClass.mods);
        long flags = tree.mods.flags;
        boolean isJMLMethod = utils.isJML(flags);
        
        boolean removedStatic = false;
        if (isJMLMethod && 
            (flags & Flags.STATIC) != 0) { // FIXME _ and in an interface?
                removedStatic = true;
                tree.mods.flags &= ~Flags.STATIC;
        }
        
        // Only enter the method if this is a JML method or if we are processing
        // a Java file
        
        if (isJMLMethod || isClassModel || !isSpecFile || tree.sym == null) {
            super.visitMethodDef(tree);
        }
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("      ENTERING MEMBER " + tree.sym + " IN " + tree.sym.owner);
        if (removedStatic) {
            tree.sym.flags_field |= Flags.STATIC;
            tree.mods.flags |= Flags.STATIC;
        }
        
        // model methods in an interface are not implicitly abstract
        if (isJMLMethod && (tree.sym.owner.flags_field & INTERFACE) != 0
                && (flags&Flags.ABSTRACT) == 0) {
            tree.sym.flags_field &= ~Flags.ABSTRACT;
            tree.mods.flags &= ~Flags.ABSTRACT;
        }

        currentMethod = prevMethod;
    }
    
//    public void visitBlock(JCTree.JCBlock that) {
//        super.visitBlock(that);
//        if (inSpecFile && currentMethod == null && !utils.isJML(currentClass.mods)) {
//            // initializer block is not allowed in a specification, unless it is a model class
//            log.error(that.pos,"jml.initializer.block.allowed");
//        }
//    }
        
    // TODO - review this
    // Duplicated from MemberEnter because it is declared private
    protected void importAll(int pos,
            final TypeSymbol tsym,
            Env<AttrContext> env) {
//      Check that packages imported from exist (JLS ???).
        if (tsym.kind == PCK && tsym.members().elems == null && !tsym.exists()) {
//          If we can't find java.lang, exit immediately.
            if (((PackageSymbol)tsym).fullname.equals(Names.instance(context).java_lang)) {
                JCDiagnostic msg = JCDiagnostic.fragment("fatal.err.no.java.lang");
                throw new FatalError(msg);
            } else {
                Log.instance(context).error(pos, "doesnt.exist", tsym);
            }
        }
        final Scope fromScope = tsym.members();
        final Scope toScope = env.toplevel.starImportScope;
        for (Scope.Entry e = fromScope.elems; e != null; e = e.sibling) {
            if (e.sym.kind == TYP && !toScope.includes(e.sym))
                toScope.enter(e.sym, fromScope);
        }
    }

    /** We override the superclass method in order to add the symbol for 'this'
     * into the environment for an interface.  The javac tool does not because
     * there is never a need - all expressions are static.  However, I have not
     * done the same for super.  (TODO)
     */
    @Override
    public void complete(Symbol sym) throws CompletionFailure {
//        if (sym.name.toString().equals("Content")) {
//            log.noticeWriter.println(sym.name);
//        }
        //log.noticeWriter.println("completing " + sym);
        
        JmlResolve jresolve = JmlResolve.instance(context);
        boolean prevAllowJML = jresolve.allowJML;
        jresolve.allowJML = utils.isJML(sym.flags());
        try {
            Env<AttrContext> env = enter.typeEnvs.get(sym);
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
            jresolve.allowJML = prevAllowJML;
        }

    }
    
//    protected void finish(Env<AttrContext> env) {
//        if (env.tree instanceof JmlCompilationUnit) {
//            JmlCompilationUnit cu = (JmlCompilationUnit)env.tree;
//            if ((cu.mode&6)==6) return;  // FIXME   - why do this?  no finishing for binary classes?
//        }
//        super.finish(env);
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
    public boolean visitVarDefIsStatic(JCVariableDecl tree, Env<AttrContext> env) {
        boolean b = super.visitVarDefIsStatic(tree,env);
        if (!isInJml && !utils.isJML(tree.mods)) return b; // FIXME - why isn't isInJml enough here - we need the second conjunct for ghost declarations in an interface
        if ((tree.mods.flags & STATIC) != 0) return true;
        
        // In the case where we are in an interface but within a JML expression
        // we can use type variables.
        return false; // FIXME - improve this
    }

//    @Override
//    public void visitClassDef(JCClassDecl tree) {
//        super.visitClassDef(tree);
////        for (JCTree t: tree.defs) {
////            t.accept(this);
////        }
//    }

    @Override
    public void visitVarDef(JCVariableDecl tree) {
        long flags = tree.mods.flags;
        boolean wasFinal = (flags&Flags.FINAL) != 0;
        boolean wasStatic = (flags&Flags.STATIC) != 0;
        if ((env.enclClass.mods.flags & INTERFACE) != 0  && utils.isJML(tree.mods)) {
            boolean isInstance = JmlAttr.instance(context).findMod(tree.mods,JmlToken.INSTANCE) != null;
            if (isInstance && !wasStatic) tree.mods.flags &= ~Flags.STATIC;
        }
        super.visitVarDef(tree);
        Symbol sym = tree.sym;
        if (specs.getSpecs(tree.sym) != null) log.noticeWriter.println("Expected null field specs here: " + tree.sym.owner + "." + tree.sym);
        specs.putSpecs(tree.sym,new JmlSpecs.FieldSpecs(tree.mods)); // This specs only has modifiers - field spec clauses are added later (FIXME - where? why not here?)
        if (sym.kind == Kinds.VAR && sym.owner.kind == TYP && (sym.owner.flags_field & INTERFACE) != 0
                && utils.isJML(tree.mods)) {
            // In the case of a JML ghost variable that is a field of an interface, the default is static and not final
            // (unless explicitly specified final)
            // FIXME _ the following is not robust because annotations are not attributed yet - test these as well
            boolean isInstance = JmlAttr.instance(context).findMod(tree.mods,JmlToken.INSTANCE) != null;
            //boolean isGhost = JmlAttr.instance(context).findMod(tree.mods,JmlToken.GHOST) != null;
            //boolean isModel = JmlAttr.instance(context).findMod(tree.mods,JmlToken.MODEL) != null;
            if (isInstance && !wasStatic) tree.sym.flags_field &= ~Flags.STATIC;  // FIXME - this duplicates JmlCheck
            if (!wasFinal) sym.flags_field &= ~FINAL; 
        }
    }
    
    

    protected JCAnnotation tokenToAnnotationAST(JmlToken jt) {
        Class<?> c = jt.annotationType;
        if (c == null) return null;
        // FIXME - this is also repeated code and rep[eated fixed strings
        JCExpression t = jmlF.Ident(names.fromString("org"));
        t = jmlF.Select(t, names.fromString("jmlspecs"));
        t = jmlF.Select(t, names.fromString("annotation"));
        t = jmlF.Select(t, names.fromString(c.getSimpleName()));
        JCAnnotation ann = jmlF.Annotation(t, List.<JCExpression>nil());
        return ann;
    }

//    // FIXME - actually, perhaps we do not need to make JmlMemberEnter
//    // a IJmlVIsitor, in which case we can do away with all of these 
//    // empty methods.  The reason is that when adding members for the java
//    // class we ignore all JML declarations - we only process those from the
//    // spec files.
//    
//    @Override
//    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr tree) {
//    }
//
//    @Override
//    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl tree) {
//    }
//
//    @Override
//    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents tree) {
//    }
//
//    @Override
//    public void visitJmlBinary(JmlBinary that) {
//    }
//
//    @Override
//    public void visitJmlFunction(JmlFunction that) {
//    }
//
//    @Override
//    public void visitJmlMethodClauseAssignable(JmlMethodClauseAssignable that) {
//    }
//
//    @Override
//    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {
//    }
//    
//    @Override
//    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
//    }
//
//    @Override
//    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
//    }
//
//    @Override
//    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
//    }
//
//    @Override
//    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
//    }
//
//    @Override
//    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
//    }
//
//    @Override
//    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
//    }
//
//    @Override
//    public void visitJmlSingleton(JmlSingleton that) {
//    }
//
//    @Override
//    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
//    }
//
//    @Override
//    public void visitJmlStatement(JmlStatement that) {
//    }
//
//    @Override
//    public void visitJmlStatementDecls(JmlStatementDecls that) {
//    }
//
//    @Override
//    public void visitJmlStatementExpr(JmlStatementExpr that) {
//    }
//
//    @Override
//    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
//        // TODO Auto-generated method stub
//        
//    }
//
//    @Override
//    public void visitJmlStoreRefField(JmlStoreRefField that) {
//        // TODO Auto-generated method stub
//        
//    }
//
//    @Override
//    public void visitJmlStoreRefIdent(JmlStoreRefIdent that) {
//        // TODO Auto-generated method stub
//        
//    }
//
//    @Override
//    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
//        // TODO Auto-generated method stub
//        
//    }
//    

//    // A sub-phase that "compiles" annotations in annotated types.
//    static protected class JmlTypeAnnotate extends JmlTreeScanner  {
//        private Env<AttrContext> env;
//        public JmlTypeAnnotate(Env<AttrContext> env) { this.env = env; }
//
//        private void enterTypeAnnotations(List<JCTypeAnnotation> annotations) {
//            Set<TypeSymbol> annotated = new HashSet<TypeSymbol>();
//            if (!skipAnnotations)
//                for (List<JCTypeAnnotation> al = annotations; al.nonEmpty(); al = al.tail) {
//                    JCTypeAnnotation a = al.head;
//                    Attribute.Compound c = annotate.enterAnnotation(a,
//                            syms.annotationType,
//                            env);
//                    if (c == null) continue;
//                    Attribute.TypeCompound tc = new Attribute.TypeCompound(c.type, c.values, a.annotation_position);
//                    a.attribute_field = tc;
//                    // Note: @Deprecated has no effect on local variables and parameters
//                    if (!annotated.add(a.type.tsym))
//                        log.error(a.pos, "duplicate.annotation");
//                }
//        }
//
//        // each class (including enclosed inner classes) should be visited
//        // separately through MemberEnter.complete(Symbol)
//        // this flag is used to prevent from visiting inner classes.
//        private boolean isEnclosingClass = false;
//        @Override
//        public void visitClassDef(final JCClassDecl tree) {
//            if (isEnclosingClass)
//                return;
//            isEnclosingClass = true;
//            scan(tree.mods);
//            // type parameter need to be visited with a separate env
//            // scan(tree.typarams);
//            scan(tree.extending);
//            scan(tree.implementing);
//            scan(tree.defs);
//        }
//
//        private void annotate(final JCTree tree, final List<JCTypeAnnotation> annotations) {
//            annotate.later(new Annotate.Annotator() {
//                public String toString() {
//                    return "annotate " + annotations + " onto " + tree;
//                }
//                public void enterAnnotation() {
//                    JavaFileObject prev = log.useSource(env.toplevel.sourcefile);
//                    try {
//                        enterTypeAnnotations(annotations);
//                    } finally {
//                        log.useSource(prev);
//                    }
//                }
//            });
//        }
//
//        @Override
//        public void visitAnnotatedType(final JCAnnotatedType tree) {
//            annotate(tree, tree.annotations);
//            super.visitAnnotatedType(tree);
//        }
//        @Override
//        public void visitTypeParameter(final JCTypeParameter tree) {
//            annotate(tree, tree.annotations);
//            super.visitTypeParameter(tree);
//        }
//        @Override
//        public void visitNewArray(final JCNewArray tree) {
//            annotate(tree, tree.annotations);
//            for (List<JCTypeAnnotation> dimAnnos : tree.dimAnnotations)
//                annotate(tree, dimAnnos);
//            super.visitNewArray(tree);
//        }
//        @Override
//        public void visitMethodDef(JCMethodDecl tree) {
//            annotate(tree, tree.receiverAnnotations);
//            super.visitMethodDef(tree);
//        }
//    }

}
