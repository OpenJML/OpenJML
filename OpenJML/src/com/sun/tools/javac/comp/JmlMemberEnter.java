package com.sun.tools.javac.comp;

import static com.sun.tools.javac.code.Flags.DEPRECATED;
import static com.sun.tools.javac.code.Flags.FINAL;
import static com.sun.tools.javac.code.Flags.HASINIT;
import static com.sun.tools.javac.code.Flags.INTERFACE;
import static com.sun.tools.javac.code.Kinds.PCK;
import static com.sun.tools.javac.code.Kinds.TYP;
import static com.sun.tools.javac.code.TypeTags.CLASS;

import java.util.Deque;
import java.util.HashSet;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.IJmlVisitor;
import org.jmlspecs.openjml.JmlOptionName;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.code.Scope.Entry;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.CompletionFailure;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
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
import com.sun.tools.javac.util.Position;

public class JmlMemberEnter extends MemberEnter { //implements IJmlVisitor {

    protected Context context;
    
    protected JmlEnter enter;
    protected JmlResolve resolve;
    protected Name.Table names;
    protected JmlTree.Maker jmlF;
    protected Symtab syms;
    
    Name org_jmlspecs_lang;
    
    public JmlMemberEnter(Context context) {
        super(context);
        this.context = context;
        this.resolve = (JmlResolve)JmlResolve.instance(context);
        this.enter = (JmlEnter)JmlEnter.instance(context);
        this.org_jmlspecs_lang = Name.Table.instance(context).fromString("org.jmlspecs.lang");
        this.names = Name.Table.instance(context);
        this.jmlF = (JmlTree.Maker)JmlTree.Maker.instance(context);
        this.syms = Symtab.instance(context);
    }

    public static void preRegister(final Context context) {
        context.put(memberEnterKey, new Context.Factory<MemberEnter>() {
            public MemberEnter make() {
                return new JmlMemberEnter(context);
            }
        });
    }
    
    int modeOfFileBeingChecked = 0;
    
    void finishClass(JCClassDecl tree, Env<AttrContext> env) {
        int prevMode = modeOfFileBeingChecked;
        modeOfFileBeingChecked = ((JmlCompilationUnit)env.toplevel).mode;
        if ((JmlCompilationUnit.isForBinary(modeOfFileBeingChecked)) && !JmlAttr.instance(context).isModel(tree.mods)) { 
            finishSpecClass((JmlClassDecl)tree,env); 
            modeOfFileBeingChecked = prevMode;
            return; 
        }
        if (Utils.jmldebug) System.out.println("FINISHING CLASS " + tree.sym.fullname);
        
        // First we do everything that Java does.  However, note that we ignore
        // ghost/model declarations in the AST (although we could implement
        // visit methods that would process them when super.finishClass walks 
        // the AST).  The reason is that the ghost/model methods in the AST of
        // the source file are not necessarily in, or at least all of, the specs
        // for that file - those are obtained from the refinement files.  If the
        // .java file is the only spec file, then everything in the AST does 
        // constitute the spec.  If the .java file is not in the refinement 
        // sequence at all, then the specs are ignored.  If the .java file is
        // only one of the files in the specification sequence, then the stuff
        // in the AST is only a subset of the specs.  So we ignore the AST and
        // accumulate everything relevant in the specs stored in JmlSpecs.
        
        super.finishClass(tree,env);
        // Now go through everything in the spec file.  Some of it
        // will be duplicates of the stuff in the java file.  Some of
        // it will be ghost/model declarations that need to be entered 
        // into the class's scope.

        JavaFileObject prevSource = null;
        try {
            JmlClassDecl jtree = (JmlClassDecl)tree;
            JmlClassDecl specsDecl = jtree.specsDecl;  // FIXME - where was this set - is there just one?
            if (specsDecl == null) {
                if (Utils.jmldebug) System.out.println("FINISHING CLASS - NO SPECS " + tree.sym.fullname);
                return;
            }
            if (Utils.jmldebug) System.out.println("FINISHING CLASS - JML PHASE " + tree.sym.fullname);
            JmlSpecs.TypeSpecs tsp = jtree.typeSpecs;
            if (tsp == null) {
                tsp = jtree.typeSpecs = new JmlSpecs.TypeSpecs();
                JmlSpecs.instance(context).putSpecs(jtree.sym,tsp);
            }
            tsp.modifiers = specsDecl.mods;
            tsp.decl = specsDecl;
            tsp.file = specsDecl.sourcefile;

            prevSource = Log.instance(context).useSource(specsDecl.sourcefile);
            checkTypeMatch(jtree,specsDecl);
            resolve.allowJML = true;
            JmlMethodSpecs savedMethodSpecs = null;
            JmlSpecs.FieldSpecs mostRecentFieldSpecs = null;
            JmlVariableDecl mostRecentVarDecl = null;
            for (JCTree t: specsDecl.defs) {
                if (!(t instanceof JmlTypeClauseIn || t instanceof JmlTypeClauseMaps)) {
                    mostRecentFieldSpecs = null;
                }
                if (t instanceof JmlVariableDecl) {
                    // make the match, check it, link it
                    JmlVariableDecl vardecl = (JmlVariableDecl)t;
                    JmlVariableDecl match = null;
                    for (JCTree jt: jtree.defs) {
                        if (jt instanceof JmlVariableDecl) {
                            if (((JmlVariableDecl)jt).name.equals(vardecl.name)) {
                                // matched
                                match = (JmlVariableDecl)jt;
                                if (match.specsDecl != null) {
                                    Log.instance(context).error(vardecl.pos(),"jml.duplicate.var.match",vardecl.name);
                                } else {
                                    match.specsDecl = vardecl;
                                    JmlSpecs.instance(context).putSpecs(match.sym,mostRecentFieldSpecs=new JmlSpecs.FieldSpecs(specsDecl.mods));
                                    mostRecentVarDecl = vardecl;
                                }
                            }
                        }
                    }
                    if (match == null) {
                        Log.instance(context).error(vardecl.pos(),"jml.no.var.match",vardecl.name);
                    } else {
                        checkFieldMatch(match,vardecl);
                    }
                } else if (t instanceof JmlMethodDecl) {
                    JmlMethodDecl match = matchMethod((JmlMethodDecl)t,jtree,env);
                    // make the match, check it, link it
                    if (match == null) {
                        // Error already issued in matchMethod
                        // Ignore any specs
                        savedMethodSpecs = null; // FIXME - do we really want to completely ignore this method and its specs - it won't get type checked for example
                    } else {
                        // FIXME - if a method matched against a superclass, we have to be careful
                        if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
                        savedMethodSpecs.decl = ((JmlMethodDecl)t);
                        match.specsDecl = (JmlMethodDecl)t;
                        match.methodSpecs = savedMethodSpecs;
                        JmlSpecs.instance(context).putSpecs(match.sym, match.methodSpecs);
                        savedMethodSpecs = null;
                    }
                } else if (t instanceof JmlMethodSpecs) {
                    savedMethodSpecs = (JmlMethodSpecs)t;
                } else if (t instanceof JmlTypeClauseIn || t instanceof JmlTypeClauseMaps) {
                    if (mostRecentFieldSpecs == null) {
                        Log.instance(context).error(t.pos(),"jml.misplaced.var.spec",((JmlTypeClause)t).token.internedName());
                    } else {
                        mostRecentFieldSpecs.list.append((JmlTypeClause)t);
                        if (t instanceof JmlTypeClauseIn) ((JmlTypeClauseIn)t).parentVar = mostRecentVarDecl;
                    }
                } else if (t instanceof JmlTypeClauseInitializer) {
                    if (((JmlTypeClauseInitializer)t).token == JmlToken.INITIALIZER) {
                        if (tsp.initializerSpec != null) {
                            Log.instance(context).error(t.pos,"jml.one.initializer.spec.only");
                        } else {
                            if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
                            ((JmlTypeClauseInitializer)t).specs = savedMethodSpecs;
                            tsp.initializerSpec = ((JmlTypeClauseInitializer)t);
                        }
                    } else {
                        if (tsp.staticInitializerSpec != null) {
                            Log.instance(context).error(t.pos,"jml.one.initializer.spec.only");
                        } else {
                            if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
                            ((JmlTypeClauseInitializer)t).specs = savedMethodSpecs;
                            tsp.staticInitializerSpec = ((JmlTypeClauseInitializer)t);
                        }
                    }
                    savedMethodSpecs = null;
                } else if (t instanceof JmlTypeClause) {
                    if (t instanceof JmlTypeClauseDecl) {
                        // These are JML declarations
                        JmlTypeClauseDecl cl = (JmlTypeClauseDecl)t;
                        JCTree tr = cl.decl;
                        // We have already entered any model classes
                        if (tr instanceof JmlVariableDecl) {
                            if (Utils.jmldebug) System.out.println("JML VAR ENTER FOR " + ((JmlVariableDecl)tr).name);
                            memberEnter(tr,env);
                            JmlSpecs.instance(context).putSpecs(((JmlVariableDecl)tr).sym,mostRecentFieldSpecs=new JmlSpecs.FieldSpecs(((JmlVariableDecl)tr).mods));
                        } else if (tr instanceof JmlMethodDecl) {
                            if (Utils.jmldebug) System.out.println("JML METH ENTER FOR " + ((JmlMethodDecl)tr).name);
                            memberEnter(tr,env);
                            JmlMethodDecl match = (JmlMethodDecl)tr;
                            if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
                            savedMethodSpecs.decl = match;
                            match.methodSpecs = savedMethodSpecs;
                            JmlSpecs.instance(context).putSpecs(match.sym, match.methodSpecs);
                            savedMethodSpecs = null;
                        }
                    }
                    // All JML declarations, invariants, etc. are put in tsp.clauses
                    tsp.clauses.append((JmlTypeClause)t);
                } else if (t instanceof JmlClassDecl) {
                    // skip this - classes were already handled in Enter/JmlEnter
                } else if (t instanceof JCTree.JCBlock){
                    if (savedMethodSpecs != null) JmlSpecs.instance(context).putSpecs((ClassSymbol)specsDecl.sym, (JCTree.JCBlock)t, savedMethodSpecs);
                    savedMethodSpecs = null;
                    if (specsDecl.sym == null) {
                        // Initializer blocks are not allowed in specs (but are in model classes)
                        log.error(t.pos(),"jml.initializer.block.allowed");
                    }
                } else {
                    System.out.println("  FOUND & NOT SUPPORTED " + t.getClass());  // FIXME
                }
                if (savedMethodSpecs != null && !(t instanceof JmlMethodSpecs)) {
                    Log.instance(context).error(savedMethodSpecs.pos(),"jml.misplaced.method.specs",specsDecl.name);
                    savedMethodSpecs = null;
                }
            }
            if (savedMethodSpecs != null) {
                Log.instance(context).error(savedMethodSpecs.pos(),"jml.misplaced.method.specs",specsDecl.name);
                savedMethodSpecs = null;
            }
                // FIXME = use a visitor to be more O-O ?
            // FIXME - unify this method with the near duplicate below
        } finally {
            addRacMethods(tree.sym,env);
            resolve.allowJML = false;
            Log.instance(context).useSource(prevSource);
            if (Utils.jmldebug) {
                System.out.println("FINISHING CLASS - COMPLETE " + tree.sym.fullname);
                System.out.println("   SCOPE IS " + tree.sym.members());
            }
            modeOfFileBeingChecked = prevMode;
        }
    }

    void finishSpecClass(JmlClassDecl specsDecl, Env<AttrContext> env) {
        if (Utils.jmldebug) System.out.println("FINISHING SPEC CLASS " + specsDecl.sym.fullname);
        // Now go through everything in the spec file.  Some of it
        // will be duplicates of the stuff in the java file.  Some of
        // it will be ghost/model declarations that need to be entered 
        // into the class's scope.  ALl class declarations are already matched
        // and/or entered.

        JavaFileObject prevSource = null;
        try {
            if (Utils.jmldebug) System.out.println("FINISHING SPEC CLASS - JML PHASE " + specsDecl.sym.fullname);
            JmlSpecs.TypeSpecs tsp = JmlSpecs.instance(context).get(specsDecl.sym);
            if (tsp == null) {
                tsp = new JmlSpecs.TypeSpecs();
                JmlSpecs.instance(context).putSpecs(specsDecl.sym,tsp);
            }
            tsp.decl = specsDecl;
            tsp.modifiers = specsDecl.mods;
            tsp.file = specsDecl.sourcefile;
            
            ClassSymbol csym = specsDecl.sym;


            prevSource = Log.instance(context).useSource(specsDecl.sourcefile);
            checkTypeMatch(csym,specsDecl);
            resolve.allowJML = true; // This allows JML identifiers to be matched when lookup occurs
            JmlMethodSpecs savedMethodSpecs = null;
            JmlSpecs.FieldSpecs mostRecentFieldSpecs = null;
            JmlVariableDecl mostRecentVarDecl = null;
            for (JCTree t: specsDecl.defs) {
                if (t instanceof JmlVariableDecl) {
                    // make the match, check it, link it
                    mostRecentFieldSpecs = null;
                    JmlVariableDecl vardecl = (JmlVariableDecl)t;
                    Symbol.VarSymbol match = null;
                    Entry e = csym.members().lookup(vardecl.name);
                    if (e.sym != null && e.sym.kind != Kinds.VAR && e.sym.owner == csym) {
                        e = e.next();
                    }
                    if (e.sym != null && e.sym.owner == csym) {
                        match = (Symbol.VarSymbol)e.sym;
                    }
                    if (match == null) {
                        Log.instance(context).error(vardecl.pos(),"jml.no.var.match",vardecl.name);
                    } else {
                        JmlSpecs.instance(context).putSpecs(match,mostRecentFieldSpecs=new JmlSpecs.FieldSpecs(vardecl.mods));
                        checkFieldMatch(match,vardecl);
                        mostRecentVarDecl = vardecl;
                    }
                } else if (t instanceof JmlMethodDecl) {
                    mostRecentFieldSpecs = null;
                    MethodSymbol match = matchMethod((JmlMethodDecl)t,csym);
                    // make the match, check it, link it
                    if (match == null) {
                        // Error already issued
                        // Ignore the declaration and its spec
                        savedMethodSpecs = null;
                    } else {
                        if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
                        savedMethodSpecs.decl = ((JmlMethodDecl)t);
                        ((JmlMethodDecl)t).methodSpecs = savedMethodSpecs;
                        if (match.owner == csym) {
                            JmlSpecs.instance(context).putSpecs(match, savedMethodSpecs);
                        }
                        savedMethodSpecs = null;
                    }
                } else if (t instanceof JmlMethodSpecs) {
                    mostRecentFieldSpecs = null;
                    savedMethodSpecs = (JmlMethodSpecs)t;
                } else if (t instanceof JmlTypeClauseIn || t instanceof JmlTypeClauseMaps) {
                    if (mostRecentFieldSpecs == null) {
                        Log.instance(context).error(t.pos(),"jml.misplaced.var.spec",((JmlTypeClause)t).token.internedName());
                    } else {
                        mostRecentFieldSpecs.list.append((JmlTypeClause)t);
                        if (t instanceof JmlTypeClauseIn) ((JmlTypeClauseIn)t).parentVar = mostRecentVarDecl;
                    }
                } else if (t instanceof JmlTypeClauseInitializer) {
                    mostRecentFieldSpecs = null;
                    if (((JmlTypeClauseInitializer)t).token == JmlToken.INITIALIZER) {
                        if (tsp.initializerSpec != null) {
                            Log.instance(context).error(t.pos,"jml.one.initializer.spec.only");
                        } else {
                            if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
                            ((JmlTypeClauseInitializer)t).specs = savedMethodSpecs;
                            tsp.initializerSpec = ((JmlTypeClauseInitializer)t);
                        }
                    } else {
                        if (tsp.staticInitializerSpec != null) {
                            Log.instance(context).error(t.pos,"jml.one.initializer.spec.only");
                        } else {
                            if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
                            ((JmlTypeClauseInitializer)t).specs = savedMethodSpecs;
                            tsp.staticInitializerSpec = ((JmlTypeClauseInitializer)t);
                        }
                    }
                    savedMethodSpecs = null;
                } else if (t instanceof JmlTypeClause) {
                    mostRecentFieldSpecs = null;
                    // These are JML declarations
                    if (t instanceof JmlTypeClauseDecl) {
                        JmlTypeClauseDecl cl = (JmlTypeClauseDecl)t;
                        JCTree tr = cl.decl;
                        // We have already entered any model classes
                        if (tr instanceof JmlVariableDecl) {
                            if (Utils.jmldebug) System.out.println("JML VAR ENTER FOR " + ((JmlVariableDecl)tr).name);
                            memberEnter(tr,env);
                            JmlSpecs.instance(context).putSpecs(((JmlVariableDecl)tr).sym,mostRecentFieldSpecs=new JmlSpecs.FieldSpecs(((JmlVariableDecl)tr).mods));
                        } else if (tr instanceof JmlMethodDecl) {
                            if (Utils.jmldebug) System.out.println("JML METH ENTER FOR " + ((JmlMethodDecl)tr).name);
                            memberEnter(tr,env);
                            JmlMethodDecl match = (JmlMethodDecl)tr;
                            if (savedMethodSpecs == null) savedMethodSpecs = new JmlMethodSpecs();
                            savedMethodSpecs.decl = match;
                            match.methodSpecs = savedMethodSpecs;
                            JmlSpecs.instance(context).putSpecs(match.sym, match.methodSpecs);
                            savedMethodSpecs = null;
                        }
                    }
                    {
                        tsp.clauses.append((JmlTypeClause)t);
                    }
                } else if (t instanceof JmlClassDecl) {
                    mostRecentFieldSpecs = null;
                    // skip this - classes were already handled in Enter/JmlEnter
                } else if (t instanceof JCTree.JCBlock){
                    mostRecentFieldSpecs = null;
                    if (savedMethodSpecs != null) JmlSpecs.instance(context).putSpecs((ClassSymbol)specsDecl.sym, (JCTree.JCBlock)t, savedMethodSpecs);
                    savedMethodSpecs = null;
                    // Initializer blocks are not allowed in specs (but are in model classes)
                    log.error(t.pos(),"jml.initializer.block.allowed");
                } else {
                    mostRecentFieldSpecs = null;
                    System.out.println("  FOUND & NOT SUPPORTED " + t.getClass());  // FIXME
                }
                if (savedMethodSpecs != null && !(t instanceof JmlMethodSpecs) && !(t instanceof JCTree.JCBlock)) {
                    Log.instance(context).error(savedMethodSpecs.pos(),"jml.misplaced.method.specs",specsDecl.name);
                    savedMethodSpecs = null;
                }
            }
            if (savedMethodSpecs != null) {
                Log.instance(context).error(savedMethodSpecs.pos(),"jml.misplaced.method.specs",specsDecl.name);
                savedMethodSpecs = null;
            }
                // FIXME - are method and field specs already where they belong?
                // FIXME = use a visitor to be more O-O ?
            // FIXME - unify this method with the near duplicate above
        } finally {
            addRacMethods(specsDecl.sym,env);
            resolve.allowJML = false;
            Log.instance(context).useSource(prevSource);
            if (Utils.jmldebug) {
                System.out.println("FINISHING SPEC CLASS - COMPLETE " + specsDecl.sym.fullname);
                System.out.println("   SCOPE IS " + specsDecl.sym.members());
            }
        }
    }
    
    public void addRacMethods(ClassSymbol sym, Env<AttrContext> env) {
        if (!JmlOptionName.isOption(context,JmlOptionName.RAC)) return;
        JmlSpecs.TypeSpecs tsp = JmlSpecs.instance(context).get(sym);
        JCExpression vd = jmlF.Type(syms.voidType);
        JmlTree.JmlMethodDecl m = (JmlTree.JmlMethodDecl)jmlF.MethodDef(jmlF.Modifiers(Flags.PUBLIC|Flags.SYNTHETIC),names.fromString(JmlRac.invariantMethodString),vd,
                List.<JCTypeParameter>nil(),List.<JCVariableDecl>nil(),List.<JCExpression>nil(),jmlF.Block(0,List.<JCStatement>nil()), null);
        m.specsDecl = m;
        JmlTree.JmlMethodDecl ms = (JmlTree.JmlMethodDecl)jmlF.MethodDef(jmlF.Modifiers(Flags.PUBLIC|Flags.STATIC|Flags.SYNTHETIC),names.fromString(JmlRac.staticinvariantMethodString),vd,
                List.<JCTypeParameter>nil(),List.<JCVariableDecl>nil(),List.<JCExpression>nil(),jmlF.Block(0,List.<JCStatement>nil()), null);
        ms.specsDecl = ms;
        
        Utils.setJML(m.mods);
        Utils.setJML(ms.mods);
        JCAnnotation a = tokenToAnnotationAST(JmlToken.MODEL);
        // FIXME - should not rely on this, but use the annotations associated with the method symbol
        m.mods.annotations = m.mods.annotations.append(a);
        ms.mods.annotations = ms.mods.annotations.append(a);

        tsp.clauses.append(jmlF.JmlTypeClauseDecl(m));
        tsp.clauses.append(jmlF.JmlTypeClauseDecl(ms));
        tsp.checkInvariantDecl = m;
        tsp.checkStaticInvariantDecl = ms;
        memberEnter(m,env);
        memberEnter(ms,env);
        
        HashSet<Name> modelMethodNames = new HashSet<Name>();
        for (JmlTypeClause t : tsp.clauses) {
            if (!(t instanceof JmlTypeClauseDecl)) continue;
            JmlTypeClauseDecl td = (JmlTypeClauseDecl)t;
            if (!(td.decl instanceof JCVariableDecl)) continue;
            JCVariableDecl vdecl = (JCVariableDecl)td.decl;
            if (!JmlAttr.instance(context).isModel(vdecl.mods)) continue;  // FIXME -check for model on the symbol?
            long flags = Flags.PUBLIC | Flags.SYNTHETIC; // FIXME - should this match the access mods of the target field? with spec_ factored in?
            if ((vdecl.mods.flags & Flags.STATIC) != 0) flags |= Flags.STATIC;
            
            modelMethodNames.add(vdecl.name);
            Name name = names.fromString("_JML$model$" + vdecl.name);
            JmlTree.JmlMethodDecl mr = (JmlTree.JmlMethodDecl)jmlF.MethodDef(jmlF.Modifiers(flags),name,vdecl.vartype,
                    List.<JCTypeParameter>nil(),List.<JCVariableDecl>nil(),List.<JCExpression>nil(),jmlF.Block(0,List.<JCStatement>nil()), null);
            mr.pos = vdecl.pos;
            memberEnter(mr,env);
            JmlTypeClauseDecl tcd = jmlF.JmlTypeClauseDecl(mr);
            tcd.pos = mr.pos;
            tcd.source = td.source;
            tcd.modifiers = mr.mods;
            tsp.modelFieldMethods.append(tcd);
            tsp.clauses.append(tcd);
        }
    }


    public void checkFieldMatch(JmlVariableDecl javaField, JmlVariableDecl specField) {
        if (javaField == specField) return;
        // Presume that we can't get here unless the names are the same
        // FIXME - attribAnnotations, compare annotations
        {
            // Check that modifiers are the same
            long javaFlags = javaField.mods.flags;
            long specFlags = specField.mods.flags;
            boolean isInterface = (javaFlags & Flags.INTERFACE) != 0;
            long diffs = (javaFlags ^ specFlags)&(isInterface? Flags.InterfaceVarFlags : Flags.VarFlags);
            if (diffs != 0) {
                Log.instance(context).error(specField.pos(),"jml.mismatched.field.modifiers", specField.name, javaField.sym.enclClass().getQualifiedName()+"."+javaField.name,Flags.toString(diffs));  // FIXME - test this
            }
        }
        {
            // check for no initializer
            if (specField.getInitializer() != null && specField != javaField) {
                Log.instance(context).error(specField.getInitializer().pos(),"jml.no.initializer.in.specs",javaField.sym.enclClass().getQualifiedName()+"."+javaField.name);
            }
        }
        {
            // check that types are the same
            //Attr.instance(context).attribType(specField.vartype, javaField.sym.enclClass());
            Attr.instance(context).attribType(specField.vartype, javaField.sym.enclClass());
            if (!Types.instance(context).isSameType(javaField.vartype.type,specField.vartype.type)) {
                Log.instance(context).error(specField.vartype.pos(),"jml.mismatched.field.types",specField.name,javaField.sym.enclClass().getQualifiedName()+"."+javaField.name,specField.vartype.type,javaField.vartype.type);
                // This seems like a serious error , can we continue - FIXME
            }
        }

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
        }
        {
            // check for no initializer
            if (specField.getInitializer() != null && !JmlCompilationUnit.isJava(modeOfFileBeingChecked)) {
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
        
        // If these are the same declaration we don't need to check 
        // that the spec decl matches the java decl
        if (javaDecl == specsClassDecl) return;

        // Check annotations
        
        {
            // Check that modifiers are the same
            long matchf = javaClassSym.flags();
            long specf = specsClassDecl.mods.flags;
            long diffs = (matchf ^ specf)&Flags.ClassFlags; // Includes whether both are class or both are interface
            if (diffs != 0) {
                boolean isInterface = (matchf & Flags.INTERFACE) != 0;
                boolean isEnum = (matchf & Flags.ENUM) != 0;
                if ((Flags.ABSTRACT & matchf & ~specf) != 0 && isInterface) diffs &= ~Flags.ABSTRACT; 
                if ((Flags.STATIC & matchf & ~specf) != 0 && isEnum) diffs &= ~Flags.STATIC; 
                if ((Flags.FINAL & matchf & ~specf) != 0 && isEnum) diffs &= ~Flags.FINAL; 
                if (diffs != 0) Log.instance(context).error(specsClassDecl.pos(),"jml.mismatched.modifiers", specsClassDecl.name, javaClassSym.fullname, Flags.toString(diffs));  // FIXME - test this
            }
            // FIXME - check that both are Enum; check that both are Annotation
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
    
    public void checkTypeMatch(ClassSymbol javaClassSym, JmlClassDecl specsClassDecl) {
        
        // Check annotations
        
        {
            // Check that modifiers are the same
            long matchf = javaClassSym.flags();
            long specf = specsClassDecl.mods.flags;
            long diffs = (matchf ^ specf)&Flags.ClassFlags; // Includes whether both are class or both are interface
            if (diffs != 0) {
                boolean isInterface = (matchf & Flags.INTERFACE) != 0;
                boolean isEnum = (matchf & Flags.ENUM) != 0;
                if ((Flags.ABSTRACT & matchf & ~specf) != 0 && isInterface) diffs &= ~Flags.ABSTRACT; 
                if ((Flags.STATIC & matchf & ~specf) != 0 && isEnum) diffs &= ~Flags.STATIC; 
                if ((Flags.FINAL & matchf & ~specf) != 0 && isEnum) diffs &= ~Flags.FINAL; 
                if (diffs != 0) Log.instance(context).error(specsClassDecl.pos(),"jml.mismatched.modifiers", specsClassDecl.name, javaClassSym.fullname, Flags.toString(diffs));  // FIXME - test this
            }
            // FIXME - check that both are Enum; check that both are Annotation
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
    
    public JmlMethodDecl matchMethod(JmlMethodDecl specMethod, JmlClassDecl javaClassDecl, Env<AttrContext> env) {
        //attribAnnotations(javaClass,method.mods); // FIXME

        Attr.instance(context).attribTypeVariables(specMethod.typarams, env);
        //Attr.instance(context).attribBounds(specMethod.typarams); //, Enter.instance(context).getEnv(javaClassDecl.sym));
        int n = specMethod.getParameters().size();
        for (int i=0; i<n; i++) {
            Attr.instance(context).attribType(specMethod.getParameters().get(i).vartype, Enter.instance(context).getEnv(javaClassDecl.sym));
        }
        JmlMethodDecl match = null;
        try {
            if (Utils.jmldebug) System.out.println("  CLASS " + javaClassDecl.name + " SPECS HAVE METHOD " + specMethod.name);
            loop: for (JCTree t : javaClassDecl.defs) {
                // FIXME - allow this to match inherited methods also?
                if (t instanceof JmlMethodDecl) {
                    JmlMethodDecl javaMethod = (JmlMethodDecl)t;
                    if (!javaMethod.name.equals(specMethod.name)) continue;
                    if (javaMethod.getParameters().size() != specMethod.getParameters().size()) continue;
                    if (javaMethod.getTypeParameters().size() != specMethod.getTypeParameters().size()) continue;
                    for (int i=0; i<n; i++) {
                        if (!Types.instance(context).isSameType(javaMethod.getParameters().get(i).vartype.type,specMethod.getParameters().get(i).vartype.type)) continue loop;
                    }
                    // FIXME - compare type parameters
                    match = javaMethod;
                }
            }
            //if (match == null && ...
                // Check for a match against Object methods
            if (match == null) {
                // Make a string of the signatures of the Java methods that we are comparing against
                // and that do not match, to make a nice error message
                StringBuilder sb = new StringBuilder();
                sb.append("\n    Signatures found:");
                int len = sb.length();
                for (JCTree t : javaClassDecl.defs) {
                    if (t instanceof JmlMethodDecl) {
                        JmlMethodDecl javaMethod = (JmlMethodDecl)t;
                        if (!javaMethod.name.equals(specMethod.name)) continue;
                        MethodSymbol m = javaMethod.sym;
                        sb.append("\n\t\t\t").append(m.toString());
                    }
                }
                if (len == sb.length()) sb.append("   <none>");
                Log.instance(context).error(specMethod.pos(),"jml.no.method.match",
                        javaClassDecl.sym.fullname + "." + specMethod.name,
                        sb.toString());
            } else {
                checkMethodMatch(match,specMethod);
                addAnnotations(match.sym,env,specMethod.mods);
            }
        } catch (Exception e) {
            System.out.println("METHOD EXCEOPTION " + e);
        }
        return match;
    }

    public MethodSymbol matchMethod(JmlMethodDecl specMethod, ClassSymbol javaClassSymbol) {
        //attribAnnotations(javaClass,method.mods); // FIXME
        // FIXME - set env properly for the following call?  Is it really attribBOunds?

        
        Scope enclScope = enter.enterScope(env);
        MethodSymbol m = new MethodSymbol(0, specMethod.name, null, javaClassSymbol);
        m.flags_field = specMethod.mods.flags;
        specMethod.sym = m;
        Env<AttrContext> localEnv = methodEnv(specMethod, env);
        Type t = specMethod.type = signature(specMethod.typarams, specMethod.params,
                specMethod.restype, specMethod.thrown,
                localEnv);
        
        
        //Attr.instance(context).attribTypeVariables(specMethod.typarams, env);
        //Attr.instance(context).attribBounds(specMethod.typarams); //, Enter.instance(context).getEnv(javaClassDecl.sym));
        int n = specMethod.getParameters().size();
//        for (int i=0; i<n; i++) {
//            // FIXME - should the following use getEnv, getClassEnv? should it use the env of the javaClassSymbol or the spec decl?
//            Attr.instance(context).attribType(specMethod.getParameters().get(i).vartype, Enter.instance(context).getEnv(javaClassSymbol));
//        }
        boolean hasTypeParameters = specMethod.getTypeParameters().size() != 0;
        MethodSymbol match = null;
        try {
            if (Utils.jmldebug) System.out.println("  CLASS " + javaClassSymbol.name + " SPECS HAVE METHOD " + specMethod.name);
            Entry e = javaClassSymbol.members().lookup(specMethod.name);
            loop: while (true) {
                //if (e.sym != null && e.sym.kind != Kinds.MTH && e.sym.owner == javaClassSymbol) e = e.next();
                //if (!(e.sym != null && e.sym.owner == javaClassSymbol)) break;
                // Allow to match inherited methods
                if (e.sym != null && e.sym.kind != Kinds.MTH) e = e.next();
                if (e.sym == null) break;
                MethodSymbol javaMethod = (Symbol.MethodSymbol)e.sym;
                if (javaMethod.getParameters().size() != specMethod.getParameters().size()) { e = e.next(); continue; }
                if (javaMethod.getTypeParameters().size() != specMethod.getTypeParameters().size()) { e = e.next(); continue; }
                if (!hasTypeParameters) for (int i=0; i<n; i++) {  // FIXME - need to do actual matching for parameters with types
                    if (!Types.instance(context).isSameType(javaMethod.getParameters().get(i).type,specMethod.getParameters().get(i).vartype.type)) { e = e.next(); continue loop; }
                }
                match = javaMethod;
                break;
            }
            if (match == null && javaClassSymbol.isInterface()) {
                // Check for a match against Object methods
                e = Symtab.instance(context).objectType.tsym.members().lookup(specMethod.name);
                loop: while (true) {
                    //if (e.sym != null && e.sym.kind != Kinds.MTH && e.sym.owner == javaClassSymbol) e = e.next();
                    //if (!(e.sym != null && e.sym.owner == javaClassSymbol)) break;
                    // Allow to match inherited methods
                    if (e.sym != null && e.sym.kind != Kinds.MTH) e = e.next();
                    if (e.sym == null) break;
                    MethodSymbol javaMethod = (Symbol.MethodSymbol)e.sym;
                    if (javaMethod.getParameters().size() != specMethod.getParameters().size()) { e = e.next(); continue; }
                    if (javaMethod.getTypeParameters().size() != specMethod.getTypeParameters().size()) { e = e.next(); continue; }
                    // FIXME - need to check that type parameters have the same names and put them in scope so that we can test whether the
                    // parameters have the same type; also check the bounds
                    for (int i=0; i<n; i++) {
                        if (!Types.instance(context).isSameType(javaMethod.getParameters().get(i).type,specMethod.getParameters().get(i).vartype.type)) { e = e.next(); continue loop; }
                    }
                    match = javaMethod;
                    break;
                }
            }

            if (match == null) {
                // Make a string of the signatures of the Java methods that we are comparing against
                // and that do not match, to make a nice error message
                StringBuilder sb = new StringBuilder();
                sb.append("\n    Signatures found:");
                int len = sb.length();
                e = javaClassSymbol.members().lookup(specMethod.name);
                loop: while (sb.length() < 500) {
                    //if (e.sym != null && e.sym.kind != Kinds.MTH && e.sym.owner == javaClassSymbol) e = e.next();
                    //if (!(e.sym != null && e.sym.owner == javaClassSymbol)) break;
                    // Allow to match inherited methods
                    if (e.sym != null && e.sym.kind != Kinds.MTH) e = e.next();
                    if (e.sym == null) break;
                    MethodSymbol javaMethod = (Symbol.MethodSymbol)e.sym;
                    sb.append("\n\t\t\t").append(javaMethod.toString());
                    e = e.next();
                }
                if (sb.length() >= 500) sb.append(" .....");
                if (len == sb.length()) sb.append("   <none>");
                Log.instance(context).error(specMethod.pos(),"jml.no.method.match",
                        javaClassSymbol.fullname + "." + specMethod.name,
                        sb.toString());
            } else {
                checkMethodMatch(match,specMethod);
                addAnnotations(match,localEnv,specMethod.mods);
            }
        } catch (Exception e) {
            System.out.println("METHOD EXCEOPTION " + e);
        }
        return match;
    }

    public void checkMethodMatch(JmlMethodDecl match, JmlMethodDecl specMethodDecl) {
        if (match == specMethodDecl) return;
        {
            boolean isInterface = match.sym.enclClass().isInterface();
            // Check that modifiers are the same
            long matchf = match.mods.flags;
            long specf = specMethodDecl.mods.flags;
            matchf &= ~(~specf & Flags.SYNCHRONIZED); // Ignore synchronized modifiers on implementation
            long diffs = (matchf ^ specf)&Flags.MethodFlags;
            if (diffs != 0) {
                if ((Flags.NATIVE & matchf & ~specf)!= 0) diffs &= ~Flags.NATIVE;
                if (isInterface) diffs &= ~Flags.PUBLIC & ~Flags.ABSTRACT;
                if (diffs != 0) Log.instance(context).error(specMethodDecl.pos(),"jml.mismatched.method.modifiers", specMethodDecl.name, match.sym.toString(), Flags.toString(diffs));  // FIXME - test thi
            }
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
            // Check that the specification method has no body if it is not a .java file
            if (specMethodDecl.body != null && match != specMethodDecl) {
                Log.instance(context).error(specMethodDecl.body.pos(),"jml.no.body.allowed",match.sym.enclClass().fullname + "." + match.sym.toString());
            }
            
            // Check that the return types are the same
            if (specMethodDecl.restype != null) { // not a constructor
                if (specMethodDecl.restype.type == null) Attr.instance(context).attribType(specMethodDecl.restype, match.sym.enclClass());
                if (!Types.instance(context).isSameType(match.restype.type,specMethodDecl.restype.type)) {
                    Log.instance(context).error(specMethodDecl.restype.pos(),"jml.mismatched.return.type",
                            match.sym.enclClass().fullname + "." + match.sym.toString(),
                            specMethodDecl.restype.type,match.restype.type);
                }
            }
            
            // FIXME - check that JML annotations match
        }
    }

    public void checkMethodMatch(MethodSymbol match, JmlMethodDecl specMethodDecl) {
        {
            boolean isInterface = match.enclClass().isInterface();
            // Check that modifiers are the same
            long matchf = match.flags();
            long specf = specMethodDecl.mods.flags;
            matchf &= ~(~specf & Flags.SYNCHRONIZED); // Ignore synchronized modifiers on implementation
            long diffs = (matchf ^ specf)&Flags.MethodFlags;
            if (diffs != 0) {
                if ((Flags.NATIVE & matchf & ~specf)!= 0) diffs &= ~Flags.NATIVE;
                if (isInterface) diffs &= ~Flags.PUBLIC & ~Flags.ABSTRACT;
                if (diffs != 0) Log.instance(context).error(specMethodDecl.pos(),"jml.mismatched.method.modifiers", specMethodDecl.name, match.toString(), Flags.toString(diffs));  // FIXME - test thi
            }
            
            // Check that parameter names are the same (a JML requirement to avoid having to rename within specs)
            if (JmlCompilationUnit.isForSource(modeOfFileBeingChecked)) {
                for (int i = 0; i<match.getParameters().size(); i++) {
                    Symbol.VarSymbol javasym = match.getParameters().get(i);
                    JCTree.JCVariableDecl vv = specMethodDecl.params.get(i);
                    if (!javasym.name.equals(vv.name)) {
                        Log.instance(context).error(vv.pos(),"jml.mismatched.param.names",i,
                                match.enclClass().fullname + "." + match.toString(),
                                vv.name, javasym.name);
                    }
                }
            }

            // Check that the specification method has no body if it is not a .java file
            if (specMethodDecl.body != null && !JmlCompilationUnit.isJava(modeOfFileBeingChecked)) {
                Log.instance(context).error(specMethodDecl.body.pos(),"jml.no.body.allowed",match.enclClass().fullname + "." + match.toString());
            }
            
            // Check that the return types are the same
            boolean hasTypeParameters = specMethodDecl.getTypeParameters().size() != 0;  // FIXME - figure out how to do proper type matching 
            if (!hasTypeParameters && specMethodDecl.restype != null) { // not a constructor
                if (specMethodDecl.restype.type == null) Attr.instance(context).attribType(specMethodDecl.restype, match.enclClass());
                if (!Types.instance(context).isSameType(match.getReturnType(),specMethodDecl.restype.type)) {
                    Log.instance(context).error(specMethodDecl.restype.pos(),"jml.mismatched.return.type",
                            match.enclClass().fullname + "." + match.toString(),
                            specMethodDecl.restype.type,match.getReturnType());
                }
            }
            // FIXME - what about covariant return types ?????
            
            // FIXME - check that JML annotations are ok
        }
    }
    
    public void addAnnotations(Symbol sym, Env<AttrContext> env, JCTree.JCModifiers mods) {
        if (env == null) {
            System.out.println("NULL ENV " + sym);
        }
        annotateLaterConditional(mods.annotations, env, sym);
//        for (JCAnnotation a: mods.annotations) {
//            if (sym.attribute(a.type.tsym) == null) {
//                
//            }
//        }
    }

    public void completeBinaryTodo() {
        Deque<Env<AttrContext>> todo = ((JmlEnter)JmlEnter.instance(context)).binaryMemberTodo;
        Env<AttrContext> env;
        while ((env = todo.pollFirst()) != null) {
            if (Utils.jmldebug) System.out.println("DOING BINARY TODO " + 
                    (env.toplevel.sourcefile));
            
            completeSpecCUForBinary(env);
        }
    }
    
    // We have to do the equivalent of complete, except that the Java class is
    // already completed and all we want to do is the spec part.  Note that 
    // super.complete is for class symbols
    public void completeSpecCUForBinary(Env<AttrContext> specEnv) {
        Env<AttrContext> prevEnv = env;
        env = specEnv;
        JavaFileObject prev = Log.instance(context).useSource(specEnv.toplevel.sourcefile);
        int prevMode = modeOfFileBeingChecked;
        modeOfFileBeingChecked = ((JmlCompilationUnit)specEnv.toplevel).mode;

        specEnv.tree.accept(this); // process imports into current env
        for (JCTree dd: ((JmlCompilationUnit)specEnv.tree).defs) {
            // There are also import declarations in defs
            if (dd instanceof JmlClassDecl) {
                env = enter.typeEnvs.get(((JmlClassDecl)dd).sym);
                JmlClassDecl d = (JmlClassDecl)dd;
                completeSpecClassForBinary(d);
            }
        }
        // Model declarations will already have been processed as regular source classes
        
        // We need to put the compilation unit on the todo list for attribution
        // WAS: Todo.instance(context).append(enter.typeEnvs.get(((JmlCompilationUnit)env.tree).packge));
        Todo.instance(context).append(specEnv);
        env = prevEnv;
        Log.instance(context).useSource(prev);
        modeOfFileBeingChecked = prevMode;
    }
    
    public void completeSpecClassForBinary(JmlClassDecl d) {
            // FIXME - super.complete(), which we are emulating here sets baseEnv = baseEnv(d,env)
            // but that causes a problem since env.outer is null.  The following code works for
            // now but needs to be tested for nested classes and where the annotation is declared
            // in the same class file, perhaps nested.  ALso, need to see what else needs proper setting
            // up in this env created from a spec file instead of a source file.
        
        if (d.sym == null) return; // FIXME - why would this happen?
        if (d.mods.annotations.nonEmpty() && d.mods.annotations.head.annotationType.type == null) { // Check if already attributed
            Env<AttrContext> baseEnv = env; // FIXME  baseEnv(d, env);
            JmlAttr.instance(context).attribAnnotationTypes(d.mods.annotations, baseEnv);
            if (hasDeprecatedAnnotation(d.mods.annotations))
                d.sym.flags_field |= DEPRECATED;
            annotateLaterConditional(d.mods.annotations, baseEnv, d.sym);
        }
        finishClass(d,enter.typeEnvs.get(d.sym));
    }
    
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
//                    if (s.attributes_field != null &&
//                            s.attributes_field.nonEmpty() &&
//                            annotations.nonEmpty())
//                        log.error(annotations.head.pos,
//                                "already.annotated",
//                                Resolve.kindName(s), s);
                    enterAnnotations(annotations, localEnv, s);
                } finally {
                    log.useSource(prev);
                }
            }
        });
    }

    
    // duplicated from MemberEnter because it is private
    private boolean hasDeprecatedAnnotation(List<JCAnnotation> annotations) {
        Type dt = Symtab.instance(context).deprecatedType;
        for (List<JCAnnotation> al = annotations; al.nonEmpty(); al = al.tail) {
            JCAnnotation a = al.head;
            if (a.annotationType.type == dt && a.args.isEmpty())
                return true;
        }
        return false;
    }
    
    @Override
    public void visitTopLevel(JCTree.JCCompilationUnit tree) {
        super.visitTopLevel(tree);
        // Import-on-demand org.jmlspecs.lang.
        importAll(tree.pos, ClassReader.instance(context).enterPackage(org_jmlspecs_lang), env);
    }
    
    @Override 
    public void visitMethodDef(JCMethodDecl tree) {
        long flags = tree.mods.flags;
        boolean removedStatic = false;
        if (Utils.isJML(flags) && 
            (flags & Flags.STATIC) != 0) { // FIXME _ and in an interface?
                removedStatic = true;
                tree.mods.flags &= ~Flags.STATIC;
        }
        
        super.visitMethodDef(tree);
        if (removedStatic) {
            tree.sym.flags_field |= Flags.STATIC;
            tree.mods.flags |= Flags.STATIC;
        }
        
        // model methods in an interface are not implicitly abstract
        if (Utils.isJML(flags) && (tree.sym.owner.flags_field & INTERFACE) != 0
                && (flags&Flags.ABSTRACT) == 0) {
            tree.sym.flags_field &= ~Flags.ABSTRACT;
            tree.mods.flags &= ~Flags.ABSTRACT;
        }
    }
        
    // Duplicated from MemberEnter because it is declared private
    protected void importAll(int pos,
            final TypeSymbol tsym,
            Env<AttrContext> env) {
//      Check that packages imported from exist (JLS ???).
        if (tsym.kind == PCK && tsym.members().elems == null && !tsym.exists()) {
//          If we can't find java.lang, exit immediately.
            if (((PackageSymbol)tsym).fullname.equals(Name.Table.instance(context).java_lang)) {
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
     * done the same for super.  
     */
    @Override
    public void complete(Symbol sym) throws CompletionFailure {
        //System.out.println("completing " + sym);
        super.complete(sym);
        // If this is a class, enter symbols for this and super into
        // current scope.
        ClassSymbol c = (ClassSymbol)sym;
        ClassType ct = (ClassType)c.type;
        Env<AttrContext> env = enter.typeEnvs.get(c);
        if ((c.flags_field & INTERFACE) == INTERFACE) {
            VarSymbol thisSym =
                new VarSymbol(FINAL | HASINIT, Name.Table.instance(context)._this, c.type, c);
            thisSym.pos = Position.FIRSTPOS;
            env.info.scope.enter(thisSym);
//            if (ct.supertype_field.tag == CLASS) {
//                VarSymbol superSym =
//                    new VarSymbol(FINAL | HASINIT, names._super,
//                                  ct.supertype_field, c);
//                superSym.pos = Position.FIRSTPOS;
//                env.info.scope.enter(superSym);
//            }
        }
        //System.out.println("   completed " + sym);
    }
    
    @Override
    public void visitVarDef(JCVariableDecl tree) {
        long flags = tree.mods.flags;
        super.visitVarDef(tree);
        Symbol sym = tree.sym;
        if (sym.kind == Kinds.VAR && sym.owner.kind == TYP && (sym.owner.flags_field & INTERFACE) != 0
                && Utils.isJML(tree.mods)) {
            // In the case of a JML variable that is a field of an interface, the default is not static and not final
            // (unless explicitly specified final)
            // FIXME _ the following is not robust because annotations are not attributed yet
            boolean isInstance = JmlAttr.instance(context).findMod(tree.mods,JmlToken.INSTANCE) != null;
            if (isInstance) tree.sym.flags_field &= ~Flags.STATIC;
            if (isInstance && (flags&FINAL) == 0) sym.flags_field &= ~FINAL; 
        }
        
    }

    protected JCAnnotation tokenToAnnotationAST(JmlToken jt) {
        Class<?> c = jt.annotationType;
        if (c == null) return null;
        JCExpression t = jmlF.Ident(names.fromString("org"));
        t = jmlF.Select(t, names.fromString("jmlspecs"));
        t = jmlF.Select(t, names.fromString("annotations"));
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
//    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly that) {
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

}
