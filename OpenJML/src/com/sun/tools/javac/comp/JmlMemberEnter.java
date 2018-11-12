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
import static com.sun.tools.javac.code.Kinds.PCK;
import static com.sun.tools.javac.code.Kinds.TYP;

import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import javax.tools.JavaFileObject;
import javax.tools.JavaFileObject.Kind;

import org.eclipse.jdt.annotation.Nullable;
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

import com.sun.tools.javac.code.Attribute.Compound;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Lint;
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
import com.sun.tools.javac.code.Types;
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
        this.enter = (JmlEnter)JmlEnter.instance(context);
        this.names = Names.instance(context);
        this.org_jmlspecs_lang = names.fromString(Strings.jmlSpecsPackage);
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
                importAll(tree.pos, reader.enterPackage(names.fromString(Strings.jmlSpecsPackage)), specenv);
            }
        }
    }

    
    public int modeOfFileBeingChecked = 0;
    
    protected JmlClassDecl currentClass = null;
    
    @Override
    protected void finishClass(JCClassDecl tree, Env<AttrContext> env) {
        PrintWriter noticeWriter = log.getWriter(WriterKind.NOTICE);
        JmlClassDecl jtree = (JmlClassDecl)tree;
        JavaFileObject prevSource = log.useSource(jtree.source());;
        JmlClassDecl prevClass = currentClass;
        currentClass = (JmlClassDecl)tree;
        int prevMode = modeOfFileBeingChecked;  // FIXME _ suspect this is not accurate
        int nowmode = modeOfFileBeingChecked = ((JmlCompilationUnit)env.toplevel).mode;
        boolean prevAllowJML = resolve.allowJML();
        if (jtree.isJML()) resolve.setAllowJML(true);
        
        boolean isSpecForBinary = jtree.toplevel != null && jtree.toplevel.mode == JmlCompilationUnit.SPEC_FOR_BINARY;
        
        // Adjust the members of jtree - if there is a separate specs file, then remove any JML declarations in the Java file and 
        // replace them with JML declaratinos from the specs file
        
        boolean prevChk = ((JmlCheck)chk).noDuplicateWarn;
        boolean prevEntering = noEntering;
        if (!isSpecForBinary) {
            ListBuffer<JCTree> defs = new ListBuffer<>();
            if (jtree.specsDecl != jtree) {
                for (JCTree t: jtree.defs) {
                    if (t instanceof JmlMethodDecl) { 
                        if (!utils.isJML(((JmlMethodDecl)t).mods)) defs.add(t);
                        // else omit it
                    } else if (t instanceof JmlVariableDecl) {
                        if (!utils.isJML(((JmlVariableDecl)t).mods)) defs.add(t);
                        // else omit it
                    } else if (t instanceof JmlClassDecl) {
                        defs.add(t);
                    } else if (t instanceof JmlTypeClause) {
                        // omit
                    } else {
                        defs.add(t);
                    }
                }
                if (jtree.specsDecl != null) for (JCTree t: jtree.specsDecl.defs) {
                    if (t instanceof JmlMethodDecl) { 
                        if (utils.isJML(((JmlMethodDecl)t).mods)) { defs.add(t);  }
                    } else if (t instanceof JmlVariableDecl) {
                        if (utils.isJML(((JmlVariableDecl)t).mods)) { defs.add(t);  }
                    }
                }
                jtree.defs = defs.toList();
                dojml = true;
                JmlCheck.instance(context).noDuplicateWarn = false;
                ListBuffer<JCTree> remove = null;
                for (JCTree t: jtree.defs) {
                    if (t instanceof JmlSource) log.useSource(((JmlSource)t).source());
                    memberEnter(t,env); // FIXME - do something special for enums
                    if (t instanceof JCVariableDecl && ((JCVariableDecl)t).sym == null) {
                        if (remove == null) remove = new ListBuffer<>();
                        remove.add(t);
                    }
                    if (t instanceof JCMethodDecl && ((JCMethodDecl)t).sym == null) {
                        if (remove == null) remove = new ListBuffer<>();
                        remove.add(t);
                    }
                }
                if (remove != null) {
                    for (JCTree t: remove) {
                        jtree.defs = Utils.remove(jtree.defs, t);
                        if (jtree.specsDecl !=null) jtree.specsDecl.defs = Utils.remove(jtree.specsDecl.defs, t);
                    }
                }
////                boolean prevChk = ((JmlCheck)chk).noDuplicateWarn;
////                if (isSpecForBinary) ((JmlCheck)chk).noDuplicateWarn = false;
////                if (isSpecForBinary) dojml = true;
////                super.finishClass(tree, env);
////                if (isSpecForBinary) dojml = false;
////                if (isSpecForBinary) ((JmlCheck)chk).noDuplicateWarn = prevChk;
//                }
            } else {
                super.finishClass(jtree, env);
            }
            // Now create symbols for all of the Java and JML methods and fields
            // This operation will report any duplicates

        }
        
        if (isSpecForBinary) {
            jtree.specsDecl = jtree;
            // Here we add the JML declarations to the class
            log.useSource(jtree.source());
            JCTree first = jtree.defs.head;
            if (first != null) {
                if (first instanceof JmlMethodDecl) {
                    if ((((JmlMethodDecl)first).mods.flags & Flags.GENERATEDCONSTR) != 0) {
                        jtree.defs = Utils.remove(jtree.defs,first);
                    }
                }
            }
            for (JCTree t: jtree.defs) {
                boolean jml = false;
                boolean skip = false;
                if (t instanceof JmlMethodDecl) { 
                    if (utils.isJML(((JmlMethodDecl)t).mods)) jml = true;
                    // else omit it
                } else if (t instanceof JmlVariableDecl) {
                    if (utils.isJML(((JmlVariableDecl)t).mods)) jml = true;
                    // else omit it
                } else if (t instanceof JmlClassDecl) {
                    if (utils.isJML(((JmlClassDecl)t).mods)) jml = true;
                } else {
                    skip = true;
                }
                
                // Now create symbols for the JML methods and fields
                // We need to call memberEnter on Java declarations in the specs file to be
                // sure that method types and annotations are processed. However they will
                // then be reported as duplicates, so we turn off duplicate warnings
                // FIXME - however, then erroneous unmatched java declarations will be added to the class and silently accepted.
                
                if (!skip) {
                    JmlCheck jmlcheck = JmlCheck.instance(context);
                    boolean pre = jmlcheck.noDuplicateWarn;
                    jmlcheck.noDuplicateWarn = !jml;
                    noEntering = !jml && !utils.isJML(jtree); // FIXME - does this really need to be recursive?
                    memberEnter(t,env); // FIXME - do something special for enums
                    jmlcheck.noDuplicateWarn = pre;
                }
            }
        }
        noEntering = prevEntering;
        JmlCheck.instance(context).noDuplicateWarn = prevChk;
        

        if (utils.isJML(tree.mods)) resolve.setAllowJML(prevAllowJML);
        
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
            JmlClassDecl specsDecl = jtree.specsDecl;
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

            resolve.setAllowJML(true);
            
            
            // At this point, all java and spec members are entered
            // We still need to connect specs of fields and methods with their Java counterparts

            // FIXME - what about blocks

            // First for Java fields and methods
            
            matchStuff(jtree, jtree.sym, env, specsDecl);
            
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
                        annotateLater(tree.mods.annotations, methodEnv((JmlMethodDecl)t, env), m.sym, tree.pos());
                    } else {
                        ms = new MethodSpecs(m.specsDecl);
                    }
                    m.methodSpecsCombined = ms;
                    JmlSpecs.instance(context).putSpecs(m.sym, ms);
                }
            }
            
            // FIXME = use a visitor to be more O-O ?
            // FIXME - unify this method with the near duplicate below

            checkFinalTypeSpecs(specs.get(csym));

        } finally {
            inSpecFile = prevInSpecFile;
            inModelTypeDeclaration = prevInModel;
            addRacMethods(tree.sym,env);
            resolve.setAllowJML(prevAllowJML);
            log.useSource(prevSource);
            if (utils.jmlverbose >= Utils.JMLDEBUG) {
                noticeWriter.println("FINISHING CLASS - COMPLETE " + tree.sym.fullname);
                noticeWriter.println("   SCOPE IS " + tree.sym.members());
            }
            modeOfFileBeingChecked = prevMode;
            currentClass = prevClass;
        }
    }
    
    protected boolean noEntering = false;
    
    /** Returns true if there is a duplicate, whether or not it was warned about */
    protected boolean visitMethodDefHelper(JCMethodDecl tree, MethodSymbol m, Scope enclScope) {
        boolean was = ((JmlCheck)chk).noDuplicateWarn;
        if (m.isConstructor() && (m.flags() & Utils.JMLBIT) != 0 && m.params().isEmpty()) {
            ((JmlCheck)chk).noDuplicateWarn = true;
        }
        if (chk.checkUnique(tree.pos(), m, enclScope)) {
            if (!noEntering) {
                if (tree.body == null && m.owner.isInterface() && utils.isJML(m.flags())) {
                    m.flags_field |= (Flags.ABSTRACT | Utils.JMLADDED);
                    m.enclClass().flags_field |= Utils.JMLADDED;
                }
                enclScope.enter(m);
            }
            ((JmlCheck)chk).noDuplicateWarn = was;
            return true;
        } else {
            if (!((JmlCheck)chk).noDuplicateWarn) tree.sym = null;  // FIXME - this needs some testing
            ((JmlCheck)chk).noDuplicateWarn = was;
            return false;
        }
    }

    // FIXME _ not currently used
    public void checkForGhostModel(JCModifiers mods, JavaFileObject source, DiagnosticPosition pos) {
        JmlAnnotation a = utils.findMod(mods, JmlTokenKind.MODEL);
        if (a == null) a = utils.findMod(mods, JmlTokenKind.GHOST);
        if (!utils.isJML(mods)) {
            if (a != null) utils.error(source, pos, "jml.ghost.model.on.java");
        } else {
            if (a == null) utils.error(source, pos , "jml.missing.ghost.model");
        }
    }  
    
    protected List<JCTree> matchStuff(@Nullable JmlClassDecl jtree, ClassSymbol csym, Env<AttrContext> env, JmlClassDecl specsDecl) {
        Map<Symbol,JCTree> matches = new HashMap<Symbol,JCTree>();
        ListBuffer<JCTree> newlist = new ListBuffer<>();
        ListBuffer<JCTree> toadd = new ListBuffer<>();
        ListBuffer<JCTree> toremove = new ListBuffer<>();
        Env<AttrContext> prevEnv = this.env;
        this.env = env;

        for (JCTree specsMemberDecl: specsDecl.defs) {
            if (specsMemberDecl instanceof JmlVariableDecl) {
                JmlVariableDecl specsVarDecl = (JmlVariableDecl)specsMemberDecl;
                boolean ok = matchAndSetFieldSpecs(jtree, csym, specsVarDecl, matches, jtree == specsDecl);
                if (ok) {
                    newlist.add(specsVarDecl); // FIXME - are we actually using newlist? should we?
                } else {
                    toremove.add(specsVarDecl); 
                }
            } else if (specsMemberDecl instanceof JmlMethodDecl) {
                JmlMethodDecl specsMethodDecl = (JmlMethodDecl)specsMemberDecl;
                boolean ok = matchAndSetMethodSpecs(jtree, csym, specsMethodDecl, env, matches, jtree == specsDecl);
                if (!ok) {
                    toremove.add(specsMethodDecl); 
                }
            } else {
//                newlist.add(specsMemberDecl);
            }
        }
        // The following is somewhat inefficient, but it is only called when there are errors
        for (JCTree t: toremove.toList()) {
            jtree.defs = Utils.remove(jtree.defs, t);
        }

        this.env = prevEnv;
        matches.clear();
        return toadd.toList();
    }

    /** Finds a Java declaration matching the given specsVarDecl in the given class.
     * If javaDecl == null, then this is a match of specs to the members of a binary class symbol.
     * If javaDec != null, then it is the Java class declaration
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
//        if (specsVarDecl.name.toString().equals("configurationSizes")) Utils.stop();
        Name id = specsVarDecl.name;
        VarSymbol matchSym = null;
        if (true || !sameTree) {
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
        if (specsVarDecl.sym == null && matchSym != null && matchSym.pos == Position.NOPOS) {
            matchSym.pos = specsVarDecl.pos;
        }
        
        // matchsym == null ==> no match; otherwise matchSym is the matching symbol
        
        if (matchSym == null) {
            if (!utils.isJML(specsVarDecl.mods)) {
                // We are going to discard this declaration because of the error, so we do extra checking
                JmlAnnotation a = ((JmlAttr)attr).findMod(specsVarDecl.mods,JmlTokenKind.GHOST);
                if (a == null) a = ((JmlAttr)attr).findMod(specsVarDecl.mods,JmlTokenKind.MODEL);
                if (a != null) {
                    utils.error(specsVarDecl.sourcefile, a.pos(),"jml.ghost.model.on.java",specsVarDecl.name);
                }
                // Non-matching java declaration - an error
                // FIXME - the check on the owner should really be recursive
                if (!utils.isJML(csym.flags())) utils.error(specsVarDecl.sourcefile, specsVarDecl.pos(),"jml.no.var.match",specsVarDecl.name);
                return false;
            } else {
                // Non-matching JML declaration
                if (javaDecl != null) utils.error(specsVarDecl.sourcefile, specsVarDecl.pos(),"jml.internal","A JML declaration should have been matched, but was not");
                return javaDecl == null;
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
            // duplicate already reported if the specs declaration is JML declaration
            if (!utils.isJML(specsVarDecl.mods) && !sameTree) {
                utils.errorAndAssociatedDeclaration(specsVarDecl.sourcefile, specsVarDecl.pos, ((JmlVariableDecl)prevMatch).sourcefile, prevMatch.pos,"jml.duplicate.var.match",specsVarDecl.name);
            }
            return false;
        }

        {
            // New match - save it; also set the specs database
            matchesSoFar.put(matchSym,  specsVarDecl);
            JmlSpecs.FieldSpecs fieldSpecs = specsVarDecl.fieldSpecs;
            if (fieldSpecs != null) JmlSpecs.instance(context).putSpecs(matchSym,fieldSpecs);
            else {
                fieldSpecs = new JmlSpecs.FieldSpecs(specsVarDecl);   // FIXME - what about lists of in clauses
                specsVarDecl.fieldSpecs = fieldSpecs;
                specs.putSpecs(matchSym,  fieldSpecs);
            }
            specsVarDecl.sym = matchSym;
            specsVarDecl.type = matchSym.type;
            if (!sameTree) {
                // Copied from MemberEnter.visitVarDef
                Env<AttrContext> localEnv = env;
                if (visitVarDefIsStatic(specsVarDecl,env)) {
                    localEnv = env.dup(specsVarDecl, env.info.dup());
                    localEnv.info.staticLevel++;
                }
                annotateLater(specsVarDecl.mods.annotations, localEnv, matchSym, specsVarDecl.pos());
                typeAnnotate(specsVarDecl.vartype, env, matchSym, specsVarDecl.pos());
            }
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
        if (javaMatch != specsVarDecl) { // Check the match only if it is not a duplicate
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

        MethodSymbol matchSym = false ? specsMethodDecl.sym : matchMethod(specsMethodDecl,csym,env,false);
        if (matchSym != null && matchSym.owner != csym) {
            log.warning("jml.message", "Unexpected location (ASD): " + csym);
            matchSym = specsMethodDecl.sym;
        }
        
        // matchsym == null ==> no match or duplicate; otherwise matchSym is the matching symbol
        
        if (matchSym == null) {
            
            // DO we need to do any cross-linking? and in field specs?
//            combinedSpecs.cases.decl = specsMethodDecl;
//            specsMethodDecl.methodSpecsCombined = combinedSpecs;

            JmlAnnotation a = ((JmlAttr)attr).findMod(specsMethodDecl.mods,JmlTokenKind.GHOST);
            if (a == null) a = ((JmlAttr)attr).findMod(specsMethodDecl.mods,JmlTokenKind.MODEL);
            boolean classIsModel = ((JmlAttr)attr).isModel(javaDecl.getModifiers()); // FIXME - should really be recursive
            if (!utils.isJML(specsMethodDecl.mods)) {
                // Method is not (directly) in a JML declaration. So it should not have ghost or model annotations
                // We are going to discard this declaration because of the error, so we do extra checking
                if (a != null) {
                    utils.error(specsMethodDecl.sourcefile, a.pos(),"jml.ghost.model.on.java",specsMethodDecl.name);
                }
                // Non-matching java declaration - an error
                if (!classIsModel) {
                    utils.error(specsMethodDecl.sourcefile, specsMethodDecl.pos(),"jml.no.method.match",
                            csym.flatName() + "." + specsMethodDecl.sym);
                }
                return false;
            } else {
                // Non-matching ghost or model declaration; this is OK - there is no symbol yet
                // This should have a model or ghost declaration - that is checked in JmlAttr
                return true;
            }
        }

        // The matches map holds any previous matches found - all to specification declarations
        JCTree prevMatch = matchesSoFar.get(matchSym);
        if ((matchSym.flags() & Flags.GENERATEDCONSTR) != 0 && prevMatch instanceof JmlMethodDecl && utils.findMod(((JmlMethodDecl)prevMatch).mods, JmlTokenKind.MODEL) == null)  prevMatch = null;
        if (prevMatch != null) {
            // DO extra checking since we are discarding this declaration because it is already matched
            if (!utils.isJML(specsMethodDecl.mods)) {
                JmlAnnotation a = ((JmlAttr)attr).findMod(specsMethodDecl.mods,JmlTokenKind.GHOST);
                if (a == null) a = ((JmlAttr)attr).findMod(specsMethodDecl.mods,JmlTokenKind.MODEL);
                if (a != null) {
                    utils.error(specsMethodDecl.sourcefile, a.pos(),"jml.ghost.model.on.java",specsMethodDecl.name);
                }
            }
            // Previous match - give error - duplicate already reported if the specsMethodDecl is JML
            if (!utils.isJML(specsMethodDecl.mods) && !sameTree) {
                utils.errorAndAssociatedDeclaration(specsMethodDecl.sourcefile, specsMethodDecl.pos, ((JmlMethodDecl)prevMatch).sourcefile, prevMatch.pos,"jml.duplicate.method.match",specsMethodDecl.sym.toString(), csym.flatName());
            }
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
                
            } else if (javaMatch != specsMethodDecl) {
                javaMatch = null;
                log.error("jml.internal", "Unexpected duplicate Java method declaration, without a matching symbol: " + matchSym);
            }
        }

        { // Check the match only if it is not a duplicate
            checkMethodMatch(javaMatch,matchSym,specsMethodDecl,csym);
            addAnnotations(matchSym,env,specsMethodDecl.mods);
        }


        return true;
    }

    
    public void checkFinalTypeSpecs(JmlSpecs.TypeSpecs tspecs) {
        for (JmlTypeClause tc: tspecs.clauses) {
            if (tc instanceof JmlTypeClauseInitializer) {
            }
        }
    }
    
    public void addInitializerBlocks(ClassSymbol sym, Env<AttrContext> env) {
        JmlClassDecl classDecl = (JmlClassDecl)env.tree;
        
        JCTree.JCBlock block = jmlF.Block(Flags.SYNTHETIC, List.<JCStatement>nil());
        classDecl.defs = classDecl.defs.append(block);
        classDecl.initializerBlock = block;
    
        block = jmlF.Block(Flags.STATIC|Flags.SYNTHETIC, List.<JCStatement>nil());
        classDecl.defs = classDecl.defs.append(block);
        classDecl.staticInitializerBlock = block;
    
    }

    public void addRacMethods(ClassSymbol sym, Env<AttrContext> env) {
        if (!utils.rac) return;
        // We can't add methods to a binary class, can we?
        if (((JmlCompilationUnit)env.toplevel).mode == JmlCompilationUnit.SPEC_FOR_BINARY) return;
        
        if (sym.isAnonymous()) return;
        if (sym.isInterface()) return;  // FIXME - deal with interfaces.  ALso, no methods added to annotations
        JmlSpecs.TypeSpecs tsp = JmlSpecs.instance(context).get(sym);
        JCExpression vd = jmlF.Type(syms.voidType);
        JmlClassDecl jtree = (JmlClassDecl)env.tree;
        JmlClassDecl specstree = jtree.toplevel.mode == JmlCompilationUnit.SPEC_FOR_BINARY ? jtree : jtree.specsDecl;
            
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
        // Inner (non-static) classes may not have static members
        long staticFlag = Flags.STATIC;
        if (sym.getEnclosingElement() instanceof ClassSymbol && !sym.isStatic()) staticFlag = 0;
        JmlTree.JmlMethodDecl ms = jmlF.MethodDef(
                jmlF.Modifiers(Flags.PUBLIC|staticFlag|Flags.SYNTHETIC),
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
        
        ListBuffer<JCTree> newdefs = new ListBuffer<>();
        newdefs.add(m);
        newdefs.add(ms);
                
        // We can't use the annotations on the symbol because the annotations are not 
        // necessarily completed. We could force it, but in the interest of least disruption
        // of the OpenJDK processing, we just use the AST instead.
        JmlAttr attr = JmlAttr.instance(context);
        Map<Name,JmlVariableDecl> modelMethodNames = new HashMap<>();
        Symbol modelSym = attr.tokenToAnnotationSymbol.get(JmlTokenKind.MODEL);
        if (specstree != null) for (JCTree decl: specstree.defs) {  // FIXME - should specstree ever be null
            if (decl instanceof JmlMethodDecl) {
                if (!utils.rac) continue;
                JmlMethodDecl md = (JmlMethodDecl)decl;
                if (!md.isJML() || md.body != null) continue;
                boolean isModel = utils.findMod(md.mods,JmlTokenKind.MODEL)!= null;
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
            JCTree.JCThrow throwStatement = jmlF.Throw(jmlF.NewClass(null, List.<JCExpression>nil(), utils.nametree(decl.pos,Strings.jmlSpecsPackage + ".NoModelFieldMethod"), List.<JCExpression>nil(), null));
            
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
        for (JCTree md: nd) {  setDefaultCombinedMethodSpecs((JmlMethodDecl)md); }


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
        int endpos = modelVarDecl.getEndPosition(log.getSource(modelVarDecl.sourcefile).getEndPosTable());
        mr.mods.annotations = List.<JCAnnotation>of(utils.tokenToAnnotationAST(JmlTokenKind.MODEL,modelVarDecl.pos,endpos),
                                                    utils.tokenToAnnotationAST(JmlTokenKind.PURE,modelVarDecl.pos,endpos)
                );
        JmlSpecs.FieldSpecs fspecs = specs.getSpecs(modelVarDecl.sym);
        JmlTypeClauseDecl tcd = jmlF.JmlTypeClauseDecl(mr);
        tcd.pos = mr.pos;
        tcd.source = fspecs.source();
        tcd.modifiers = mr.mods;
        tsp.modelFieldMethods.append(tcd);
        tsp.decls.append(tcd);
        return mr;
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

    /** Checks that the jml annotations match Java annotations for annotations not in org.jmlspecs.annotation
     * and are a superset of the Java annotations for annotations in org.jmlspecs.annotation) */
    // MUST HAVE log.useSource set to specs file!
    protected void checkSameAnnotations(Symbol sym, JCModifiers specsmods, JavaFileObject javaSource) {
        // FIXME - check for null in annotations?
        if (sym.isAnonymous()) return;
        boolean saved1 = JmlPretty.useFullAnnotationTypeName, saved2 = JmlPretty.useJmlModifier;
        JmlPretty.useFullAnnotationTypeName = JmlPretty.useJmlModifier = false;
        PackageSymbol p = ((JmlAttr)attr).annotationPackageSymbol;
        for (Compound a  : sym.getAnnotationMirrors()) {
            if (a.type.tsym.owner.equals(p)) {
                if (utils.findMod(specsmods,a.type.tsym) == null) {
                    JavaFileObject prev = log.useSource(javaSource);
                    log.error(specsmods.pos,"jml.java.annotation.superseded",a);
                    log.useSource(prev);
                }
            } else {
                if (utils.findMod(specsmods,a.type.tsym) == null && !a.toString().startsWith("@sun")) {
                    log.error(specsmods.pos,"jml.missing.annotation",a);
                }
            }
        }
        JmlPretty.useFullAnnotationTypeName = saved1; JmlPretty.useJmlModifier = saved2;
    }

    /** Checks that the jml annotations are a superset of the Java annotations (for annotations in org.jmlspecs.annotation) */
    // MUST HAVE log.useSource set to specs file!
    protected void checkSameAnnotations(JCModifiers javaMods, JCModifiers specsmods, JavaFileObject javaSource) { // FIXME - don't need last argument
        PackageSymbol p = ((JmlAttr)attr).annotationPackageSymbol;
        boolean saved1 = JmlPretty.useFullAnnotationTypeName, saved2 = JmlPretty.useJmlModifier;
        JmlPretty.useFullAnnotationTypeName = JmlPretty.useJmlModifier = false;
        for (JCAnnotation a: javaMods.getAnnotations()) {
            if (a.type.tsym.owner.equals(p)) {
                if (utils.findMod(specsmods,a.type.tsym) == null) {
                    JavaFileObject prev = log.useSource(((JmlTree.JmlAnnotation)a).sourcefile);
                    log.error(specsmods.pos,"jml.java.annotation.superseded",a);
                    log.useSource(prev);
                }
            } else {
                if (utils.findMod(specsmods,a.type.tsym) == null && !a.toString().startsWith("@sun")) {
                    log.error(specsmods.pos,"jml.missing.annotation",a);
                }
            }
        }
        JmlPretty.useFullAnnotationTypeName = saved1; JmlPretty.useJmlModifier = saved2;
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
                !utils.isJML(specField.mods) && !specField.sym.owner.isEnum()) {
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
            checkSameAnnotations(javaDecl.mods,specsClassDecl.mods,javaDecl.source());
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
            checkSameAnnotations(javaClassSym,specsClassDecl.mods,prev); // FIXME - is prev the java source?
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
            if (localEnv != null) localEnv.info.scope.owner = match;
            for (List<JCVariableDecl> l = tree.params; l.nonEmpty(); l = l.tail) {
                JCVariableDecl param = l.head;
                param.sym.owner = match;
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

            // FIXME - we do need to exclude some anonymous classes,  but all of them?
            if (!javaClassSymbol.isAnonymous()) checkSameAnnotations(match,specMethodDecl.mods,prev); // FIXME - is prev really the file object for Java
            Iterator<JCVariableDecl> jmliter = specMethodDecl.params.iterator();
            Iterator<Symbol.VarSymbol> javaiter = match.getParameters().iterator();
            while (javaiter.hasNext() && jmliter.hasNext()) {
                Symbol.VarSymbol javaparam = javaiter.next();
                JmlVariableDecl jmlparam = (JmlVariableDecl)jmliter.next();
                checkSameAnnotations(javaparam,jmlparam.mods,prev); // FIXME - is prev really the file object for Java
            }



            // Check that the return types are the same
            if (specMethodDecl.restype != null) { // not a constructor
                if (specMethodDecl.restype.type == null) Attr.instance(context).attribType(specMethodDecl.restype, match.enclClass());
//                if (match.name.toString().equals("defaultEmpty")) {
//                    log.noticeWriter.println(match.name);
//                }
                Type javaReturnType = match.type.getReturnType();
                Type specReturnType = specMethodDecl.restype.type;
                if (!Types.instance(context).isSameType(javaReturnType,specReturnType)) {
                    // FIXME - when the result type is parameterized in a static method, the java and spec declarations
                    // end up with different types for the parameter.  Is this also true for the regular parameters?  
                    // FIXME - avoud the probloem for now.
                    if (!(specReturnType instanceof Type.TypeVar) && specReturnType.getTypeArguments().isEmpty()
                            && (!(specReturnType instanceof Type.ArrayType) || !(((Type.ArrayType)specReturnType).elemtype instanceof Type.TypeVar)) )
                        log.error(specMethodDecl.restype.pos(),"jml.mismatched.return.type",
                                match.enclClass().fullname + "." + match.toString(),
                                specReturnType, javaReturnType);
                }
            }

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

    
    VarSymbol findVarMatch(ClassSymbol csym, Name name) {
        Scope.Entry e = csym.members().lookup(name);  // FIXME - can have variables and methods with the same name
        while (e.sym != null && !(e.sym instanceof VarSymbol)) {
            e = e.next();
        }
        return (VarSymbol)e.sym;
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
                    if (!(s.hasAnnotations() &&
                        annotations.nonEmpty())) 
                        actualEnterAnnotations(annotations, localEnv, s);
//                    else if (!(annotations.head.type instanceof Type.ErrorType) )
//                        log.error(annotations.head.pos,
//                                  "already.annotated",
//                                  kindName(s), s);
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
            boolean isSpecForBinary = modeOfFileBeingChecked == JmlCompilationUnit.SPEC_FOR_BINARY;
            boolean isSpecFile = currentMethod.sourcefile == null || currentMethod.sourcefile.getKind() != JavaFileObject.Kind.SOURCE;
//            boolean isClassModel = ((JmlAttr)attr).isModel(env.enclClass.mods);
            if (isSpecFile && tree.sym != null) return; //Sometimes this is called when the method already is entered
            if (isJMLMethod) resolve.setAllowJML(true);
            super.visitMethodDef(tree);
//            if (!isSpecFile) super.visitMethodDef(tree);
//            if (isSpecFile) visitMethodDefBinary(tree);
        } finally {
            if (isJMLMethod) resolve.setAllowJML(prevAllowJml);
            currentMethod = prevMethod;
        }
        
    }

    
    public void visitMethodDef(JmlMethodDecl tree, ClassSymbol owner) {
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
        boolean prevCheck = ((JmlCheck)chk).noDuplicateWarn;
        ((JmlCheck)chk).noDuplicateWarn = true;
        if (chk.checkUnique(tree.pos(), m, enclScope)) {
            // Not a duplicate - OK if the declaration is JML - if not, then ignore it
            if (!utils.isJML(m.flags())) {
                // This is an error, but it is reported later
                //utils.error(((JmlMethodDecl)tree).sourcefile, tree, "jml.no.method.match", enclScope.owner.flatName() + "." + m);
            } else {
                enclScope.enter(m);
            }
        } else {
            // A duplicate - OK if the declaration is not JML
            if (utils.isJML(m.flags())) {
                // FIXME
            }
        }
        ((JmlCheck)chk).noDuplicateWarn = prevCheck;

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
        
        JmlResolve jresolve = JmlResolve.instance(context);
        boolean prevAllowJML = jresolve.setAllowJML(utils.isJML(sym.flags()));
        try {
            Env<AttrContext> env = enter.typeEnvs.get(sym.type.tsym);
            if (env == null) {
                log.error("jml.internal","JmlMemberEnter.complete called with a null env, presumably from a binary class, which should not be the argument of this complete call: " + sym);
                return;
            }
            super.complete(sym); // FIXME - not sure this should be called for binary classes
            // If this is a specification file then remove any automatically generated constructor
            if (env.tree instanceof JmlClassDecl) {
                JmlClassDecl jmltree = (JmlClassDecl)env.tree;
                if (jmltree.toplevel != null && jmltree.toplevel.mode == JmlCompilationUnit.SPEC_FOR_BINARY && !utils.isJML(jmltree)) {
                    if (jmltree.defs.head instanceof JmlMethodDecl) {
                        JmlMethodDecl md = (JmlMethodDecl)jmltree.defs.head;
                        if ((md.getModifiers().flags & Flags.GENERATEDCONSTR) != 0) {
                            jmltree.defs = jmltree.defs.tail;
                        }
                    }
                }
            }
            
            // FIXME - this might already be done?
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
            jresolve.setAllowJML(prevAllowJML);
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
        boolean isReplacementType = ((JmlVariableDecl)tree).jmltype;
        
        if (utils.isJML(tree.mods) || isReplacementType) resolve.setAllowJML(true);
        
//        boolean prevChk = ((JmlCheck)chk).noDuplicateWarn;
//        ((JmlCheck)chk).noDuplicateWarn = false;
        JavaFileObject prevSource = log.useSource( ((JmlVariableDecl)tree).source());
        super.visitVarDef(tree);
        log.useSource(prevSource);
//        ((JmlCheck)chk).noDuplicateWarn = prevChk;
        if (utils.isJML(tree.mods)) resolve.setAllowJML(prev);
        if (tree.sym == null) {
            // A duplicate
            return;
        }
        Symbol sym = tree.sym;
        if (specs.getSpecs(tree.sym) != null) log.warning("jml.internal","Expected null field specs here: " + tree.sym.owner + "." + tree.sym);
        JmlVariableDecl jtree = (JmlVariableDecl)tree;
        
        // FIXME - the following duplicates setting the specs with matchAndSetFieldSpecs - but if there is a source file, this comes first
        JmlSpecs.FieldSpecs fspecs = jtree.fieldSpecs;
        if (fspecs == null) fspecs = new JmlSpecs.FieldSpecs(jtree); // Does not include any in or maps clauses
        jtree.fieldSpecsCombined = fspecs; 
        specs.putSpecs(tree.sym,fspecs);
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
    
    protected void visitFieldDefHelper(JCVariableDecl tree, VarSymbol v, Scope enclScope) {
        if (chk.checkUnique(tree.pos(), v, enclScope)) {
            chk.checkTransparentVar(tree.pos(), v, enclScope);
            if (!noEntering) enclScope.enter(v);
        } else {
            tree.sym = null; // An indication that the field is a duplicate and should be removed/ignored
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
        specs.putSpecs(specstree.sym,new JmlSpecs.FieldSpecs(specstree)); // This specs only has modifiers - field spec clauses are added later (FIXME - where? why not here?)

        if (vsym.kind == Kinds.VAR && vsym.owner.kind == TYP && (vsym.owner.flags_field & INTERFACE) != 0
                && isJML) {
            // In the case of a JML ghost variable that is a field of an interface, the default is static and not final
            // (unless explicitly specified final)
            // FIXME _ the following is not robust because annotations are not attributed yet - test these as well
            boolean isInstance = utils.findMod(specstree.mods,JmlTokenKind.INSTANCE) != null;
            if (isInstance && !wasStatic) specstree.sym.flags_field &= ~Flags.STATIC;  // FIXME - this duplicates JmlCheck
            if (!wasFinal) vsym.flags_field &= ~FINAL; 
        }
        
        
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


    @Override
    protected void importHelper(JCCompilationUnit tree) {
        // Import-on-demand java.lang.
        importAll(tree.pos, reader.enterPackage(names.java_lang), env);
        importAll(tree.pos, reader.enterPackage(names.fromString(Strings.jmlSpecsPackage)), env);

        // Process all import clauses.
        memberEnter(tree.defs, env);
    }
    
    @Override
    protected void importAll(int pos,
            final TypeSymbol tsym,
            Env<AttrContext> env) {
        if (tsym.kind == PCK && tsym.members().elems == null && !tsym.exists()) {
            // If we can't find org.jmlspecs.lang, exit immediately.
            if (((PackageSymbol)tsym).fullname.toString().equals(Strings.jmlSpecsPackage)) {
                JCDiagnostic msg = diags.fragment("fatal.err.no." + Strings.jmlSpecsPackage);
                throw new FatalError(msg);
            }
        }
        super.importAll(pos, tsym, env);
    }


}
