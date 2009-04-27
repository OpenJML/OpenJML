package com.sun.tools.javac.comp;

import static com.sun.tools.javac.code.Flags.ABSTRACT;
import static com.sun.tools.javac.code.Flags.BLOCK;
import static com.sun.tools.javac.code.Flags.INTERFACE;
import static com.sun.tools.javac.code.Flags.NATIVE;
import static com.sun.tools.javac.code.Flags.STATIC;
import static com.sun.tools.javac.code.Flags.UNATTRIBUTED;
import static com.sun.tools.javac.code.Kinds.TYP;
import static com.sun.tools.javac.code.Kinds.VAL;
import static com.sun.tools.javac.code.Kinds.VAR;
import static org.jmlspecs.openjml.JmlToken.*;

import java.util.EnumMap;
import java.util.EnumSet;
import java.util.Iterator;

import javax.lang.model.type.TypeKind;
import javax.tools.JavaFileObject;

import org.jmlspecs.annotations.NonNull;
import org.jmlspecs.openjml.IJmlVisitor;
import org.jmlspecs.openjml.JmlCompiler;
import org.jmlspecs.openjml.JmlInternalError;
import org.jmlspecs.openjml.JmlOptionName;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeTranslator;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Lint;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.CompletionFailure;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.OperatorSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

/**
 * This class is an extension of the Attr class; it adds visitors methods so
 * that as the Attr class walks the entire AST, attributing all nodes (that is
 * doing name lookup and type assignment), the JML parts of the source tree are
 * attributed and checked as well.
 * <P>
 * On input to this class all top-level types and all their members,
 * recursively, are already entered into the symbol table (but local classes and
 * declarations are not). Also, the types of all annotations and of member
 * fields and member methods (return type, arguments and type arguments) are
 * already attributed.
 * <P>
 * The class has the responsibility of attributing the rest of the AST (e.g.,
 * method bodies, field initializers, expressions within JML annotations, etc.).
 * It also checks that JML modifiers are used correctly.
 * 
 * @author David Cok
 */
/* Note on the visitor class: Each node visitor is responsible to 
 * do the following:
 * a) any attribution of its subtrees, by calling an appropriate
 * attrib... method (e.g., attribExpr or attribType),
 * b) checking that the types of those subtrees are correct,
 * c) determining the type of the node itself,
 * d) checking that against the value of pt.  If a check call is
 * used to do this, then tree.type is set for you.  If you do the
 * checking yourself, then you have to set tree.type directly.
 * The check call handles casting, widening etc. for you, and
 * e) set the value of result to the resulting type.
 * 
 * This design appears to involve a lot of extra work.  Instead of
 * having the attrib calls pass in an expected type, which is set as
 * a member of the Attr class, why not just check it upon return?
 * That would save the stacking that is necessary in attribTree.
 */
public class JmlAttr extends Attr implements IJmlVisitor {

    /** This is the compilation context for which this is the unique instance */
    protected Context context;
    
    /** Set from the options for user-requested verbosity */
    protected boolean verbose = false;
    
    /** Set at construction according to the -rac compiler option */
    protected boolean racOption = false;
    
    protected Name resultName;
    
    protected Name exceptionName;
    protected Name exceptionCatchName;
    protected Name postCheckName;
    protected Name signalsCheckName;
    
    ClassSymbol utilsClass;
    JCIdent utilsClassIdent;
    protected JmlSpecs specs;

    /** The Names table from the compilation context, initialized in the constructor */
    @NonNull protected Names names;
    
    /** The factory used to create AST nodes, initialized in the constructor */
    @NonNull protected JmlTree.Maker factory;

    //DiagnosticPosition make_pos;
    protected JCLiteral trueLit;
    protected JCLiteral falseLit;
    protected JCLiteral nullLit;
    protected JCLiteral zeroLit;
    public ClassSymbol modelAnnotationSymbol = null;
    public ClassSymbol pureAnnotationSymbol = null;
    public ClassSymbol nonnullbydefaultAnnotationSymbol = null;
    public ClassSymbol nullablebydefaultAnnotationSymbol = null;

    // Unfortunately we cannot increase the number of primitive
    // type tags without modifying the TypeInfo file.  These
    // type tags are out of range, so we cannot use the usual
    // initType call to initialize them.
    // FIXME - may need to revisit this for boxing and unboxing
    protected Type TYPE; // This is a synonym for java.lang.Class
    protected Type REAL;// = new Type(1001,null);
    protected Type BIGINT;// = new Type(1002,null);
    protected Type Lock;// = new Type(1003,null);
    protected Type LockSet;// = new Type(1004,null);
    protected Type JMLUtilsType;
    protected Type JMLValuesType;
    protected Type JMLIterType;
    protected Type JMLSetType;
    
    /** When true, we are visiting subtrees that allow only pure methods and
     * pure operations */
    boolean pureEnvironment = false;
    
    /** This flag controls whether JML definitions in a class body are attributed.
     * Recall that the actual specifications are pulled off into the TypeSpecs
     * and JmlMethodSpecs structures, so we should ignore the definitions left
     * in the defs list of the Class.  If we attribute them as part of the class
     * body we end up doing duplicate and sometimes inappropriate work.
     */
    boolean attribSpecs = false;
    
    /** Holds the env of the enclosing method for subtrees of a MethodDecl. */
    Env<AttrContext> enclosingMethodEnv = null;
    
    /** Set to true when we are within a JML declaration */
    boolean isInJmlDeclaration = false;
 
    /** This field stores the clause type when a clause is visited (before 
     * visiting its components), in order that various clause-type-dependent
     * semantic tests can be performed (e.g. \result can only be used in some
     * types of clauses).
     */
    protected JmlToken currentClauseType = null;
    
    /** Constructor of a JmlAttr tool for the given context
     * 
     * @param context the compilation context in which we are working
     */
    protected JmlAttr(Context context) {
        super(context);
        this.context = context;
        this.verbose = JmlOptionName.isOption(context,"-verbose") ||
                        JmlOptionName.isOption(context,JmlOptionName.JMLVERBOSE) ||
                        Utils.jmldebug;
        initNames(context);
        this.specs = JmlSpecs.instance(context);
        this.factory = (JmlTree.Maker)JmlTree.Maker.instance(context);
        this.names = Names.instance(context);

        // Caution, because of circular dependencies among constructors of the
        // various tools, it can happen that syms is not fully constructed at this
        // point and syms.classType will be null.
        TYPE = syms.classType;
        if (TYPE == null) {
            System.err.println("INTERNAL FAILURE: A circular dependency among constructors has caused a failure to correctly construct objects.  Please report this internal problem.");
            new Exception().printStackTrace(System.err);
            throw new JmlInternalError();
        }

        utilsClass = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.utils.Utils"));
        utilsClassIdent = make.Ident(names.fromString("org.jmlspecs.utils.Utils"));
        utilsClassIdent.type = utilsClass.type;
        utilsClassIdent.sym = utilsClassIdent.type.tsym;

        JMLSetType = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.lang.JMLSetType")).type;
        JMLValuesType = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.lang.JMLList")).type;
        JMLUtilsType = utilsClass.type;
        JMLIterType = ClassReader.instance(context).enterClass(names.fromString("java.util.Iterator")).type;
        REAL = syms.doubleType;
        BIGINT = syms.longType;
        Lock = syms.objectType;
        LockSet = JMLSetType;
        nullablebydefaultAnnotationSymbol = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.annotations.NullableByDefault"));
        nonnullbydefaultAnnotationSymbol = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.annotations.NonNullByDefault"));
        
        if (REAL.tsym == null) {
            //TYPE.tsym = new ClassSymbol(Flags.PUBLIC, names.fromString("TYPE"), TYPE, syms.rootPackage);  // Instead \TYPE is a complete synonym for java.lang.Class
//            REAL.tsym = new ClassSymbol(Flags.PUBLIC, names.fromString("real"), REAL, syms.rootPackage);
//            BIGINT.tsym = new ClassSymbol(Flags.PUBLIC, names.fromString("bigint"), BIGINT, syms.rootPackage);
//            Lock.tsym = new ClassSymbol(Flags.PUBLIC, names.fromString("Lock"), Lock, syms.rootPackage);
//            LockSet.tsym = new ClassSymbol(Flags.PUBLIC, names.fromString("LockSet"), LockSet, syms.rootPackage);
        }
        
        this.resultName = Names.instance(context).fromString("_JML$$$result");
        this.exceptionName = Names.instance(context).fromString("_JML$$$exception");
        this.exceptionCatchName = Names.instance(context).fromString("_JML$$$exceptionCatch");
        this.postCheckName = Names.instance(context).fromString("postCheck");
        this.signalsCheckName = Names.instance(context).fromString("signalsCheck");
        
        trueLit = makeLit(syms.booleanType,1);
        falseLit = makeLit(syms.booleanType,0);
        nullLit = makeLit(syms.botType,null);
        zeroLit = makeLit(syms.intType,0);

    }
 
    /** Registers a singleton factory for JmlAttr against the attrKey, so that there is
     * just one instance per context.
     * @param context the context in which to register the instance
     */
    public static void preRegister(final Context context) {
        context.put(Attr.attrKey, new Context.Factory<Attr>() {
            public Attr make() {
                return new JmlAttr(context); // Registers itself on construction
            }
        });
    }
    
    /** Returns the instance for the given context
     * 
     * @param context the context in which we are working
     * @return the non-null instance of JmlAttr for this context
     */
    public static JmlAttr instance(Context context) {
        Attr instance = context.get(attrKey); 
        if (instance == null)
            instance = new JmlAttr(context); // Registers itself in the super constructor
        return (JmlAttr)instance; // If the registered instance is only an Attr, something is catastrophically wrong
    }

    /** Overrides the super class call in order to perform JML checks on class
     * modifiers.  (Actually, the work was moved to attribClassBody since attribClass
     * gets called multiple times for a Class).
     * @param c The class to check
     * @throws CompletionFailure
     */
    @Override
    public void attribClass(ClassSymbol c) throws CompletionFailure {
        //System.out.println("REQUESTING ATTRIBUTION " + c);
        // FIXME - can we make the following more efficient - this gets called a lot for classes already attributed
        JmlSpecs.TypeSpecs classSpecs = specs.get(c);
        if (classSpecs == null) {
            ((JmlCompiler)JmlCompiler.instance(context)).loadSpecsForBinary(env,c);
            classSpecs = specs.get(c);
            if (classSpecs == null) {
                // loadSpecsForBinary should always result in a TypeSpecs for the
                // class symbol, even if it is empty
                log.warning("jml.internal.notsobad","loadSpecsForBinary failed for class " + c);
            } else if (classSpecs.decl == null) {
                // Class is loaded: it is a binary class and has no specs
                // We do not need to attribute it
                c.flags_field &= ~UNATTRIBUTED;
            } else {
                // If it is newly loaded and has specs
                // we make sure it is unattributed, so that we attribute all
                // the specs
                c.flags_field |= UNATTRIBUTED;
                // FIXME - check that we are not attributing more than once
            }
        }
        
        // The previous operations might have attributed the current class
        // if there was a cycle. So we test first whether the class is still
        // UNATTRIBUTED.
        if ((c.flags_field & UNATTRIBUTED) == 0) return;
        // We let the super class turn it off to avoid recursion

        if (verbose && c != syms.predefClass) {
            System.out.println("typechecking " + c);
        }
        
        // FIXME - this won't be correct if specs come from multiple files
        JavaFileObject prev = log.useSource(classSpecs.file);
        
        // We are doing this with pureEnvironment since calls can be nested -
        // we can enter a pure environment from either an impure or pure
        // environment and we need to restore it properly.  Also, when in a
        // pure environment we may need to attribute a class, not all of which
        // is pure.
        boolean prevPureEnvironment = pureEnvironment;
        pureEnvironment = false;  
        try {
            this.racOption = JmlOptionName.isOption(context,JmlOptionName.RAC);
            super.attribClass(c);
            Env<AttrContext> e = enter.getEnv(c);

            // Binary files with specs had entries put in the Env map so that the
            // specs had environments against which to be attributed.  However, the
            // presence of envs for non-.java files confuses later compiler phases,
            // and we no longer need that mapping since all the specs are now
            // attributed and entered into the JmlSpecs database.  Hence we remove
            // the entry.
            if (e != null) {  // SHould be non-null the first time, but subsequent calls will have e null and so we won't do duplicate checking
                // FIXME - RAC should take advantage of the same stuff as ESC
                if (!JmlOptionName.isOption(context,JmlOptionName.RAC)) new JmlTreeTranslator(context).translate(e.tree);
                if (!JmlCompilationUnit.isJava(((JmlCompilationUnit)e.toplevel).mode)) {
                    //attribClassBodySpecs(e,c,false,true);// Binary class - we still need to do all the body stuff
                    enter.typeEnvs.remove(c); // FIXME - do we need this?
                }
            }
        } finally {
            pureEnvironment = prevPureEnvironment;
            log.useSource(prev);
        }
        if (Utils.jmldebug) System.out.println("ATTRIBUTING-END " + c.fullname);
        if (verbose && c != syms.predefClass) {
            System.out.println("typechecked " + c);
        }
    }
    
    /** Overrides in order to attribute class specs appropriately. */
    @Override
    protected void attribClassBody(Env<AttrContext> env, ClassSymbol c) {
        boolean prevIsInJmlDeclaration = isInJmlDeclaration;
        isInJmlDeclaration = Utils.isJML(c.flags());
        if (Utils.jmldebug) System.out.println("ATTRIBUTING-BODY " + c.fullname + " " + (isInJmlDeclaration?"inJML":"notInJML") + " WAS " + (prevIsInJmlDeclaration?"inJML":"notInJML"));
        boolean prevAttribSpecs = attribSpecs;  // Class definitions might be nested
        JavaFileObject prev = log.useSource(((JmlCompilationUnit)env.toplevel).sourcefile);  // FIXME - no write for multiple source files
        boolean oldRelax = relax;
        try {
            // We have a bit of confusion because JML specs are in multiple
            // places.  The consolidated material is in the specifications
            // structures obtained from JmlSpecs.  However, anything that was
            // in the original Java source file may still be there (but that is
            // only part of it).  So we arrange to NOT attribute the JML material
            // that may be in the Java file; and we attribute all the specs
            // later in attribClassBodySpecs.

            // This field is looked at by all the visit... methods
            attribSpecs = false;
            relax = true;  // Turns off some bogus lack of overriding warnings
            super.attribClassBody(env,c);
            attribSpecs = true; // Now do all the specs
            attribClassBodySpecs(env,c,prevIsInJmlDeclaration,false);
        } finally {
            relax = oldRelax;
            attribSpecs = prevAttribSpecs;
            isInJmlDeclaration = prevIsInJmlDeclaration;
            log.useSource(prev);
            if (Utils.jmldebug) System.out.println("ATTRIBUTING-MODS " + c.fullname + " " + isInJmlDeclaration);
        }
        // Finally, check the class modifiers
        // FIXME - actually we need to get the modifiers from TypeSpecs
        //Env<AttrContext> e = enter.typeEnvs.get(c);
        // FIXME - really need to do the second line
        //checkClassMods(c.owner,(JmlClassDecl)e.tree,((JmlClassDecl)e.tree).mods);
    }
    
    public void attribClassBodySpecs(Env<AttrContext> env, ClassSymbol c, boolean prevIsInJmlDeclaration, boolean doJava) {
        JmlSpecs.TypeSpecs tspecs = JmlSpecs.instance(context).get(c);
        JavaFileObject prev = log.currentSourceFile();
        JmlToken prevClauseType = currentClauseType;
        if (tspecs != null && tspecs.decl != null) {
            Env<AttrContext> prevEnv = this.env;
            this.env = env;

            // modifiers? annotations?
            
            // clauses and declarations
            for (JmlTypeClause clause: tspecs.clauses) {
                currentClauseType = clause.token;
                clause.accept(this);
            }
            currentClauseType = null;
            
            // Do the specs for initialization blocks // FIXME - wouldn't this duplicate work done in tree-walking
            for (JCTree.JCBlock m: tspecs.blocks.keySet()) {
                m.accept(this);
            }
            
            // Do the JML initializer and static initializer specs
            currentClauseType = JmlToken.INITIALIZER;
            if (tspecs.initializerSpec != null) tspecs.initializerSpec.accept(this); // FIXME - need to set log
            currentClauseType = JmlToken.STATIC_INITIALIZER;
            if (tspecs.staticInitializerSpec != null) tspecs.staticInitializerSpec.accept(this); // FIXME - need to set log
            if (tspecs != null && tspecs.modifiers != null) { // FIXME - why would we have null modifiers?
                log.useSource(tspecs.file);
                attribAnnotationTypes(tspecs.modifiers.annotations,env);
                isInJmlDeclaration = prevIsInJmlDeclaration;
                checkClassMods(c.owner,tspecs.decl,tspecs.modifiers);
            }
            
            
            this.env = prevEnv;
        }
        currentClauseType = prevClauseType;
        log.useSource(prev);
    }
    
    /** This is overridden to attribute the specs for the method, 
     * if there are any.  The specs are walked at the
     * time the block that is the method body is walked so that the scope 
     * is right.
     */
    @Override
    public void visitBlock(JCBlock tree) {
        Env<AttrContext> prevEnclosingMethodEnv = enclosingMethodEnv;
        
        // FIXME - what about initializer blocks - they also need an old environment
        
        if (env.info.scope.owner.kind == TYP) {
           // FIXME - if we are in a spec source file that is not Java, we may not have one of these - error
            super.visitBlock(tree);
            JmlMethodSpecs sp = JmlSpecs.instance(context).getSpecs(env.enclClass.sym,tree);
            //if (attribSpecs && sp != null) {
            if (sp != null) {
                Env<AttrContext> localEnv =
                    env.dup(tree, env.info.dup(env.info.scope.dupUnshared()));
                localEnv.info.scope.owner =
                    new MethodSymbol(tree.flags | BLOCK, names.empty, null,
                                     env.info.scope.owner);
                if (isStatic(tree.flags)) localEnv.info.staticLevel++;
//                boolean prev = attribSpecs;
//                attribSpecs = true;
                attribStat(sp,localEnv);
//                attribSpecs = prev;
            }
        } else {
            // Method blocks
            
            boolean topMethodBodyBlock = env.enclMethod != null &&
                                            env.enclMethod.body == tree;
            if (topMethodBodyBlock) {
                AttrContext a = env.info.dupUnshared();
                enclosingMethodEnv = env.dup(env.tree,a);
            }
            super.visitBlock(tree);
            if (env.enclMethod != null &&
                    env.enclMethod.body == tree) {
                // Note: we cannot just cache the current value of env for use later.
                // This is because the envs are presumed to be nested and share their
                // symbol tables.  Access to scopes is presumed to be nested - in Java
                // a reference to an identifier is always resolved in the current scope first,
                // not in an enclosing scope.  However, JML has the \old operator which gives
                // access to the scope at method definition time from within other nestings.
                boolean prevAllowJML = ((JmlResolve)JmlResolve.instance(context)).allowJML;
                try {
                    ((JmlResolve)JmlResolve.instance(context)).allowJML = true;
                    JmlMethodSpecs sp = ((JmlMethodDecl)env.enclMethod).methodSpecs; //specs.getSpecs(env.enclMethod.sym);
//                  if (enclosingMethodEnv == null) {
                    // FIXME - This can happen for anonymous classes, so I expect that
                    // specs (or at least \old) in anonymous classes will cause disaster
//                  System.out.println("DISASTER-2 AWAITS: " + env.enclMethod.name);
//                  System.out.println(env.enclMethod);
//                  }
                    if (sp != null) sp.accept(this);
//                  if (enclosingMethodEnv == null) {
//                  System.out.println("DODGED-2: " + env.enclMethod.name);
                    deSugarMethodSpecs(((JmlMethodDecl)env.enclMethod),sp);

//                  }
                } finally {
                    ((JmlResolve)JmlResolve.instance(context)).allowJML = prevAllowJML;
                }
            }

        }
        enclosingMethodEnv = prevEnclosingMethodEnv;
    }
    
    public void visitUnary(JCUnary tree) {
        super.visitUnary(tree);
        if (pureEnvironment) {
            int op = tree.getTag();
            if (op == JCTree.PREINC || op == JCTree.POSTINC ||
                    op == JCTree.PREDEC || op == JCTree.POSTDEC)
                log.error(tree.pos,"jml.no.incdec.in.pure");
        }
    }

    public void visitAssign(JCAssign tree) {
        super.visitAssign(tree);
        if (pureEnvironment) {
            log.error(tree.pos,"jml.no.assign.in.pure");
        }
    }

    public void visitAssignop(JCAssignOp tree) {
        super.visitAssignop(tree);
        if (pureEnvironment) {
            log.error(tree.pos,"jml.no.assign.in.pure");
        }
    }

    
    public JmlToken[] allowedTypeModifiers = new JmlToken[]{
        PURE, MODEL, NULLABLE_BY_DEFAULT, NON_NULL_BY_DEFAULT, QUERY};

    public JmlToken[] allowedNestedTypeModifiers = new JmlToken[]{
        PURE, MODEL, SPEC_PUBLIC, SPEC_PROTECTED, NULLABLE_BY_DEFAULT, NON_NULL_BY_DEFAULT, QUERY}; // FIXME - is NULLABLE_BY_DEFAULT supppsoed to be allowed?

    public JmlToken[] allowedNestedModelTypeModifiers = new JmlToken[]{
        PURE, MODEL, QUERY};

    public JmlToken[] allowedLocalTypeModifiers = new JmlToken[]{
        PURE, MODEL, QUERY};

    /** Checks the JML modifiers so that only permitted combinations are present. */
    public void checkClassMods(Symbol owner, JmlClassDecl tree, JCModifiers mods) {
        boolean inJML = Utils.isJML(mods);
        JCAnnotation model = findMod(mods,JmlToken.MODEL);
        boolean isModel = model != null;
        if (mods == null) {
            // no annotations to check
        } else if (owner.kind == Kinds.PCK) {  // Top level type declaration
            allAllowed(mods.annotations,allowedTypeModifiers,"type declaration");
        } else if (owner.kind != Kinds.TYP) { // Local
            allAllowed(mods.annotations,allowedLocalTypeModifiers,"local type declaration");
        } else if (!isModel) { // Nested/inner type declaration
            allAllowed(mods.annotations,allowedNestedTypeModifiers,"nested type declaration");
        } else { // Nested model type declaration
            allAllowed(mods.annotations,allowedNestedModelTypeModifiers,"nested model type declaration");
        }
        if (isInJmlDeclaration && isModel) {
            log.error(tree.pos,"jml.no.nested.model.type");
        } else if (inJML && !isModel && !isInJmlDeclaration) {
            log.error(tree.pos,"jml.missing.model");
        } else if (!inJML && isModel) {
            log.error(tree.pos,"jml.ghost.model.on.java");
        } 

        if (!isModel) checkForConflict(mods,SPEC_PUBLIC,SPEC_PROTECTED);
        checkForConflict(mods,NON_NULL_BY_DEFAULT,NULLABLE_BY_DEFAULT);
        checkForConflict(mods,PURE,QUERY);
    }
    
    /** This is overridden in order to do correct checking of whether a method body is
     * present or not.
     */
    @Override 
    public void visitMethodDef(JCMethodDecl m) {
        // Setting relax to true keeps super.visitMethodDef from complaining
        // that a method declaration in a spec file does not have a body
        // FIXME - what else is relaxed?  We should do the check under the right conditions?
        if (m.sym == null) return; // Guards against specification method declarations that are not matched - FIXME
        boolean oldrelax = relax;
        relax = true;
        JavaFileObject prevSource = null;
        try {
            if (Utils.jmldebug) System.out.println("ATTRIBUTING METHOD " + env.enclClass.sym + " " + m.sym);
            JmlMethodDecl jmethod = (JmlMethodDecl)m;
            prevSource = log.useSource(jmethod.source());
            attribAnnotationTypes(m.mods.annotations,env); // This is needed at least for the spec files of binary classes
            for (JCAnnotation a : m.mods.annotations) a.type = a.annotationType.type;  // It seems we need this, but it seems this should happen while walking the tree - FIXME
            boolean prevRelax = relax;
            // FIXME - need a better test than this
            // Set relax to true if this method declaration is allowed to have no body
            // because it is a model declaration or it is in a specification file.
            boolean isJavaFile = jmethod.sourcefile.getName().endsWith(".java");
            boolean isJmlDecl = Utils.isJML(m.mods);
            relax = isJmlDecl || !isJavaFile;
            super.visitMethodDef(m);
            relax = prevRelax;
            if (jmethod.methodSpecs != null) { // FIXME - should we get the specs to check from JmlSpecs?
                if (m.body == null) checkMethodSpecsDirectly(jmethod);
                // If the body is null, the specs are checked in visitBlock
                //else deSugarMethodSpecs(jmethod,jmethod.methodSpecs);
            }
            if (isJavaFile && !isJmlDecl) {
                // Java methods in Java files must have a body (usually)
                if (m.body == null) {
                    ClassSymbol owner = env.enclClass.sym;
                    // Empty bodies are only allowed for
                    // abstract, native, or interface methods, or for methods
                    // in a retrofit signature class.
                    if ((owner.flags() & INTERFACE) == 0 &&
                        (m.mods.flags & (ABSTRACT | NATIVE)) == 0 &&
                        !oldrelax)
                        log.error(m.pos(), "missing.meth.body.or.decl.abstract");
                }
            } else if (m.body != null && !isJmlDecl && !isJavaFile && !isInJmlDeclaration && (m.mods.flags & (Flags.GENERATEDCONSTR|Flags.SYNTHETIC)) == 0) {
                // Java methods not in Java files may not have bodies (generated constructors do)
                //log.error(m.pos(),"jml.no.body.allowed",m.sym);
                // A warning is appropriate, but this is a duplicate.
                // A warning is already given in JmlMemberEnter.checkMethodMatch
            }
            checkMethodModifiers(jmethod);
        } finally {
            relax = oldrelax;
            if (prevSource != null) log.useSource(prevSource);
        }
    }
    
    /** The annotations allowed on non-model non-constructor methods */
    public final JmlToken[] allowedMethodAnnotations =
        new JmlToken[] {
        MODEL, PURE, NONNULL, NULLABLE, SPEC_PUBLIC, SPEC_PROTECTED, HELPER, EXTRACT, QUERY, SECRET 
    };
    
    /** The annotations allowed on non-model non-constructor methods */
    public final JmlToken[] allowedInterfaceMethodAnnotations =
        new JmlToken[] {
        MODEL, PURE, NONNULL, NULLABLE, SPEC_PUBLIC, SPEC_PROTECTED, HELPER, QUERY 
    };
    
    /** The annotations allowed on model non-constructor methods */
    public final JmlToken[] allowedModelMethodAnnotations =
        new JmlToken[] {
        MODEL, PURE, NONNULL, NULLABLE, HELPER, EXTRACT, QUERY, SECRET 
    };
    
    /** The annotations allowed on model non-constructor interface methods */
    public final JmlToken[] allowedInterfaceModelMethodAnnotations =
        new JmlToken[] {
        MODEL, PURE, NONNULL, NULLABLE, HELPER, QUERY, SECRET
    };
    
    /** The annotations allowed on non-model constructors */
    public final JmlToken[] allowedConstructorAnnotations =
        new JmlToken[] {
        MODEL, PURE, SPEC_PUBLIC, SPEC_PROTECTED, HELPER, EXTRACT 
    };
    
    /** The annotations allowed on model constructors */
    public final  JmlToken[] allowedModelConstructorAnnotations =
        new JmlToken[] {
        MODEL, PURE, HELPER, EXTRACT 
    };
    
    /** Does the various checks of method/constructor modifiers */
    public void checkMethodModifiers(JmlMethodDecl tree) {
        boolean inJML = Utils.isJML(tree.mods);
        boolean model = isModel(tree.mods);
        boolean syn = (tree.mods.flags & Flags.SYNTHETIC) != 0;
        if (isInJmlDeclaration && model && !syn) {
            log.error(tree.pos,"jml.no.nested.model.type");
        } else if (inJML && !model  && !isInJmlDeclaration) {
            log.error(tree.pos,"jml.missing.model");
        } else if (!inJML && model) {
            log.error(tree.pos,"jml.ghost.model.on.java");
        }
        if (tree.getReturnType() != null) {
            if (tree.sym.enclClass().isInterface()) {
                if (model) {
                    allAllowed(tree.mods.annotations,allowedInterfaceModelMethodAnnotations,"interface model method declaration");
                } else {
                    allAllowed(tree.mods.annotations,allowedInterfaceMethodAnnotations,"interface method declaration");
                }
            } else {
                if (model) {
                    allAllowed(tree.mods.annotations,allowedModelMethodAnnotations,"model method declaration");
                } else {
                    allAllowed(tree.mods.annotations,allowedMethodAnnotations,"method declaration");
                }
            }
            checkForConflict(tree.mods,NONNULL,NULLABLE);
            checkForConflict(tree.mods,PURE,QUERY);
        } else { // Constructor
            if (model) {
                allAllowed(tree.mods.annotations,allowedModelConstructorAnnotations,"model constructor declaration");
            } else {
                allAllowed(tree.mods.annotations,allowedConstructorAnnotations,"constructor declaration");
            }            
        }
        if (!model) {
            checkForConflict(tree.mods,SPEC_PUBLIC,SPEC_PROTECTED);
        }
    }
    
    public void checkMethodSpecsDirectly(JmlMethodDecl tree) {
        // Copying what is done in super.visitMethodDef to setup an environment
        // This is only done if the method body is null, otherwise, it is quicker
        // to check the method specs with the body
        
        MethodSymbol m = tree.sym;

        Lint lint = env.info.lint.augment(m.attributes_field, m.flags());
        Lint prevLint = chk.setLint(lint);
        try {

            // Create a new environment with local scope
            // for attributing the method.
            Env<AttrContext> localEnv = memberEnter.methodEnv(tree, env);

            localEnv.info.lint = lint;

            // Enter all type parameters into the local method scope.
            for (List<JCTypeParameter> l = tree.typarams; l.nonEmpty(); l = l.tail)
                localEnv.info.scope.enterIfAbsent(l.head.type.tsym);

            // Attribute all value parameters if needed and add them into the scope
            for (List<JCVariableDecl> l = tree.params; l.nonEmpty(); l = l.tail) {
                attribStat(l.head, localEnv);
            }

            {
                // Both method specs and specs in statements in the method body use enclosingMethodEnv to resolve \old and \pre
                // references against the environment present when the method is called.  For method specs this does not change since
                // there are no introduced declarations, but it is convenient to use the same variable anyway.
                // In this case we don't need to dup it because it does not change.
                enclosingMethodEnv = localEnv;
                // Note: we cannot just cache the current value of env for use later.
                // This is because the envs are presumed to be nested and share their
                // symbol tables.  Access to scopes is presumed to be nested - in Java
                // a reference to an identifier is always resolved in the current scope first,
                // not in an enclosing scope.  However, JML has the \old operator which gives
                // access to the scope at method definition time from within other nestings.
                boolean prevAllowJML = JmlResolve.setJML(context,true);
                Env<AttrContext> prevEnv = env;
                try {
                    env = localEnv;
                    JmlMethodSpecs sp = tree.methodSpecs; // OR specs.getSpecs(env.enclMethod.sym); if we don't have a tree - FIXME
                    if (sp != null) sp.accept(this);
                    deSugarMethodSpecs(tree,tree.methodSpecs);
                } finally {
                    env = prevEnv;
                    JmlResolve.setJML(context,prevAllowJML);
                }
                enclosingMethodEnv = null;
            }
            localEnv.info.scope.leave();
            result = tree.type = m.type;

        }
        finally {
            chk.setLint(prevLint);
        }
    }
    
    JCExpression makeBinary(int optag, JCExpression lhs, JCExpression rhs, int pos) {
        if (optag == JCTree.OR && lhs == falseLit) return rhs;
        if (optag == JCTree.AND && lhs == trueLit) return rhs;
        JCBinary tree = make.at(pos).Binary(optag, lhs, rhs);
        tree.operator = predefBinOp(optag, lhs.type);
//        tree.operator = rs.resolveBinaryOperator(
//                null, optag, env, lhs.type, rhs.type);
        tree.type = tree.operator.type.getReturnType();
        return tree;
    }
    
    JCIdent makeIdent(JCVariableDecl decl) {
        JCIdent id = make.Ident(decl.name);
        id.sym = decl.sym;
        id.type = decl.type;
        // id.pos = ??? FIXME
        return id;
    }
    
    // FIXME - is there a faster way to do this?
    protected Symbol predefBinOp(int op, Type type) {
//        for (Symbol sym : syms.predefClass.members().getElements()) {
//            if ((sym instanceof OperatorSymbol) && ((OperatorSymbol)sym).opcode == op
//                    && ((OperatorSymbol)sym).getParameters().head.type == type) return sym;
//        }
//        return null;
        Name n = TreeInfo.instance(context).operatorName(op);
        Scope.Entry e = syms.predefClass.members().lookup(n);
        while (e.sym != null) {
            if (e.sym instanceof MethodSymbol) {
                MethodSymbol msym = (MethodSymbol)e.sym;
                Type t = msym.getParameters().head.type;
                if (t == type || (!type.isPrimitive() && t == syms.objectType)) return e.sym;
            }
            e = e.next();
        }
        return null;
    }

    
    /** Does a custom desugaring of the method specs.  It adds in the type
     * restrictions (non_null) and purity, desugars lightweight and heavyweight
     * to behavior cases, adds in defaults, desugars signals_only and denests.
     * It does not merge multiple specification cases (so we can give better
     * error messages) and it does not pull in inherited specs.  So in the end 
     * the desugared specs consist of a set of specification cases, each of 
     * which consists of a series of clauses without nesting; there is no
     * combining of requires or other clauses and no insertion of preconditions
     * into the other clauses.
     * @param msym
     * @param methodSpecs
     */
    // FIXME - base this on symbol rather than decl, but first check when all
    // the modifiers are added into the symbol
    // FIXME - check everything for position information
    public void deSugarMethodSpecs(JmlMethodDecl decl, JmlMethodSpecs methodSpecs) {
        //System.out.println("DESUGARING " + decl.sym.owner + " " + decl.sym);
        if (methodSpecs == null || methodSpecs.decl == null) return;
        Env<AttrContext> prevEnv = env;
        env = enter.getEnv((ClassSymbol)decl.sym.owner);
        JCMethodDecl prevEnclMethod = env == null ? null : env.enclMethod;
        if (env != null) env.enclMethod = decl; // This is here to handle the situation when deSugarMethodSPecs
                // is called from JmlSpecs to provide on demand desugaring.  In that case we are not within
                // a tree hierarchy, so we have to set the enclosing method declaration directly.  If we were only
                // calling deSugarMethodSpecs during AST attribution, then we would not need to set env or adjust
                // env.enclMethod.
        // FIXME if (specs.decl != decl) System.out.println("UNEXPECTED MISMATCH " + decl.sym + " " + specs.decl.sym);
        JavaFileObject prevSource = log.useSource(methodSpecs.decl.sourcefile);
        try {
            JmlTree.Maker jmlF = (JmlTree.Maker)make;
            JCLiteral nulllit = make.Literal(TypeTags.BOT, null).setType(syms.objectType.constType(null));
            //boolean defaultNonnull = determineDefaultNullability();
            ListBuffer<JmlMethodClause> clauses = new ListBuffer<JmlMethodClause>();
            for (JCVariableDecl p : decl.params) {
                if (!p.type.isPrimitive()) {
                    boolean isNonnull = specs.isNonNull(p.sym,decl.sym.enclClass());
                    if (isNonnull) {
                        JCIdent id = makeIdent(p);
                        JCExpression e = makeBinary(JCTree.NE,id,nulllit,p.pos);
                        clauses.append(jmlF.JmlMethodClauseExpr(JmlToken.REQUIRES,e));
                    }
                }
            }
            JCAnnotation nonnullAnnotation = findMod(decl.mods,JmlToken.NONNULL);
            // restype is null for constructors, possibly void for methods
            if (decl.restype != null && decl.restype.type.tag != TypeTags.VOID && !decl.restype.type.isPrimitive()) {
                boolean isNonnull = specs.isNonNull(decl.sym,decl.sym.enclClass());
                if (isNonnull) {
                    JCExpression id = jmlF.JmlSingleton(JmlToken.BSRESULT);
                    id.type = decl.restype.type;
                    JCExpression e = makeBinary(JCTree.NE,id,nulllit,0);
                if (nonnullAnnotation != null) e.pos = nonnullAnnotation.getPreferredPosition();
                else e.pos = decl.getPreferredPosition();   // FIXME - fix the position of the non-null if using default
                id.pos = e.pos; // FIXME - start and end as well?
                currentClauseType = JmlToken.ENSURES;
                attribExpr(e,env);
                currentClauseType = null;
                clauses.append(jmlF.at(decl.pos).JmlMethodClauseExpr(JmlToken.ENSURES,e));
                }
            }
            if (desugaringPure = (findMod(decl.mods,JmlToken.PURE) != null)) {
                JmlMethodClause c = jmlF.JmlMethodClauseAssignable(JmlToken.ASSIGNABLE,
                        List.<JCTree>of(jmlF.JmlSingleton(JmlToken.BSNOTHING)));
                //attribStat(c,env);
                clauses.append(c);
            }
            if (methodSpecs == null) return;
            JmlMethodSpecs newspecs;
            if (!methodSpecs.cases.isEmpty()) {
                ListBuffer<JmlSpecificationCase> newcases = deNest(clauses,methodSpecs.cases,null,decl);
                newspecs = jmlF.at(methodSpecs.pos).JmlMethodSpecs(newcases.toList());
                if (!methodSpecs.impliesThatCases.isEmpty()) newspecs.impliesThatCases = deNest(clauses,methodSpecs.impliesThatCases,null,decl).toList();
                if (!methodSpecs.forExampleCases.isEmpty()) newspecs.forExampleCases = deNest(clauses,methodSpecs.forExampleCases,null,decl).toList();
            } else if (!clauses.isEmpty()) {
                JCModifiers mods = jmlF.at(decl.pos).Modifiers(decl.mods.flags & Flags.AccessFlags);
                JmlSpecificationCase c = jmlF.JmlSpecificationCase(mods,false,null,null,clauses.toList());
                newspecs = jmlF.JmlMethodSpecs(List.<JmlSpecificationCase>of(c));
            } else {
                newspecs = methodSpecs;
            }
            newspecs.decl = methodSpecs.decl;
            methodSpecs.deSugared = newspecs;
        } finally {
            if (env != null) env.enclMethod = prevEnclMethod;
            env = prevEnv;
            log.useSource(prevSource);
        }
    }
    
    
    boolean desugaringPure = false;
    
    // FIXME -could be optimized for situatinos where there is just one spec case and/or no clause groups
    // FIXME - this ignores anything after a clause group.  That is OK in strict JML.  DO we want it?  There is no warning.
    public ListBuffer<JmlSpecificationCase> deNest(ListBuffer<JmlMethodClause> prefix, List<JmlSpecificationCase> cases, /*@ nullable */JmlSpecificationCase parent, JmlMethodDecl decl) {
        ListBuffer<JmlSpecificationCase> newlist = new ListBuffer<JmlSpecificationCase>();
        if (cases.isEmpty()) {
            if (parent != null) newlist.append(((JmlTree.Maker)make).at(parent.pos).JmlSpecificationCase(parent.modifiers,parent.code,parent.token,parent.also,prefix.toList()));
            else {
                // ERROR
                System.out.println("INTERNAL ERROR!");
            }
        } else {
            for (JmlSpecificationCase c: cases) {
                if (parent == null) {
                    JmlTree.Maker jmlF = (JmlTree.Maker)make;
                    JmlToken t = c.token;
                    if (t == JmlToken.NORMAL_BEHAVIOR || t == JmlToken.NORMAL_EXAMPLE) {
                        prefix.append(jmlF.at(c.pos).JmlMethodClauseSignals(JmlToken.SIGNALS,null,falseLit));
                    } else if (t == JmlToken.EXCEPTIONAL_BEHAVIOR || t == JmlToken.EXCEPTIONAL_EXAMPLE) {
                        prefix.append(jmlF.at(c.pos).JmlMethodClauseExpr(JmlToken.ENSURES,falseLit));
                    }
                }
                ListBuffer<JmlMethodClause> pr = copy(prefix);
                newlist.appendList(deNestHelper(pr,c.clauses,parent==null?c:parent,decl));
            }
        }
        return newlist;
    }
    
    public ListBuffer<JmlMethodClause> copy(ListBuffer<JmlMethodClause> p) {
        ListBuffer<JmlMethodClause> copy = new ListBuffer<JmlMethodClause>();
        copy.appendList(p);
        return copy;
    }
    
    public ListBuffer<JmlSpecificationCase> deNestHelper(ListBuffer<JmlMethodClause> prefix, List<JmlMethodClause> clauses, JmlSpecificationCase parent, JmlMethodDecl decl) {
        for (JmlMethodClause m: clauses) {
            if (m instanceof JmlMethodClauseGroup) {
                return deNest(prefix,((JmlMethodClauseGroup)m).cases, parent,decl);
            }
            JmlToken t = m.token;
            if (t == JmlToken.ENSURES) {
                if (parent.token == JmlToken.EXCEPTIONAL_BEHAVIOR || parent.token == JmlToken.EXCEPTIONAL_EXAMPLE) {
                    log.error(m.pos,"jml.misplaced.clause","Ensures","exceptional");
                    continue;
                }
            } else if (t == JmlToken.SIGNALS) {
                if (parent.token == JmlToken.NORMAL_BEHAVIOR || parent.token == JmlToken.NORMAL_EXAMPLE) {
                    log.error(m.pos,"jml.misplaced.clause","Signals","normal");
                    continue;
                }
            } else if (t == JmlToken.SIGNALS_ONLY) {
                if (parent.token == JmlToken.NORMAL_BEHAVIOR || parent.token == JmlToken.NORMAL_EXAMPLE) {
                    log.error(m.pos,"jml.misplaced.clause","Signals_only","normal");
                    continue;
                }
                int count = 0;
                for (JmlMethodClause mc: prefix) {
                    if (mc.token == JmlToken.SIGNALS_ONLY) count++;
                }
                if (count > 0) {
                    log.error(m.pos,"jml.multiple.signalsonly");
                }
            } else if (desugaringPure && t == JmlToken.ASSIGNABLE) {
                JmlMethodClauseAssignable asg = (JmlMethodClauseAssignable)m;
                if (decl.sym.isConstructor()) {
                    // A pure constructor allows assigning to class member fields
                    // So if there is an assignable clause the elements of the clause
                    // may only be members of the class
                    for (JCTree tt: asg.list) {
                        if (tt instanceof JmlStoreRefKeyword) {
                            if (((JmlStoreRefKeyword)tt).token == JmlToken.BSNOTHING) {
                                // OK
                            } else {
                                // FIXME - also allow this.*  or super.* or super.<ident> ?
                                log.error(m.pos,"jml.misplaced.clause","Assignable","pure");
                                break;
                            }
//                        } else if (tt instanceof JmlSingleton) { // FIXME - don't think this is needed
//                                if (((JmlSingleton)tt).token == JmlToken.BSNOTHING) {
//                                    // OK
//                                } else {
//                                    // FIXME - also allow this.*  or super.* or super.<ident> ?
//                                    log.error(m.pos,"jml.misplaced.clause","Assignable","pure");
//                                    break;
//                                }
                        } else if (tt instanceof JCIdent) {
                            // Simple identifier - OK
                        } else {
                            // FIXME - also allow this.*  or super.* or super.<ident> ?
                            log.error(m.pos,"jml.misplaced.clause","Assignable","pure");
                            break;
                        }
                    }
                } else {
                    for (JCTree tt: asg.list) {
                        if (tt instanceof JmlStoreRefKeyword &&
                            ((JmlStoreRefKeyword)tt).token == JmlToken.BSNOTHING) {
                                // OK
                        } else {
                            // FIXME - also allow this.*  or super.* or super.<ident> ?
                            log.error(m.pos,"jml.misplaced.clause","Assignable","pure");
                            break;
                        }
                    }
                }
            }
            prefix.append(m);
        }
        ListBuffer<JmlSpecificationCase> newlist = new ListBuffer<JmlSpecificationCase>();
        JmlSpecificationCase sc = (((JmlTree.Maker)make).JmlSpecificationCase(parent,prefix.toList()));
        newlist.append(sc);
        return newlist;
    }
    
//    /** Determines the default nullability for the compilation unit
//     * @return true if the default is non_null, false if the default is nullable
//     */
//    public boolean determineDefaultNullability() {
//        return false;  // FIXME
//    }
    
    protected void adjustVarDef(JCVariableDecl tree, Env<AttrContext> localEnv) {
        if (!forallOldEnv) return;
        // Undo the super class
        if ((tree.mods.flags & STATIC) != 0 ||
                (env.enclClass.sym.flags() & INTERFACE) != 0)
                localEnv.info.staticLevel--;
        // FIXME - actually, any initializer in an interface needs adjustment - might be instance
        
        // Redo, just dependent on static
        // FIXME - actually depends on whether the containing method is static
        // FIXME - check whetehr all specs are properly checked for stastic/nonstatic use of fields and methods
        // including material inherited from interfaces where the defaults are different
        if ((localEnv.enclMethod.mods.flags & STATIC) != 0)
                localEnv.info.staticLevel++;
        
    }
    
    /** This is overridden in order to check the JML modifiers of the variable declaration */
    @Override
    public void visitVarDef(JCVariableDecl tree) {
        attribAnnotationTypes(tree.mods.annotations,env);  // FIXME - we should not need these two lines I think, but otherwise we get NPE faults on non_null field declarations
        for (JCAnnotation a: tree.mods.annotations) a.type = a.annotationType.type;
        super.visitVarDef(tree);
        if (tree instanceof JmlVariableDecl) checkVarMods((JmlVariableDecl)tree);
        // Anonymous classes construct synthetic members (constructors at least)
        // which are not JML nodes.
        FieldSpecs fspecs = specs.getSpecs(tree.sym);
        if (fspecs != null) for (JmlTypeClause spec:  fspecs.list) spec.accept(this);
    }
    
    // MAINTENANCE ISSUE - copied from super class
    @Override
    protected void checkInit(JCTree tree,   // DRC - changed from private to protected
            Env<AttrContext> env,
            VarSymbol v,
            boolean onlyWarning) {
//      System.err.println(v + " " + ((v.flags() & STATIC) != 0) + " " +
//      tree.pos + " " + v.pos + " " +
//      Resolve.isStatic(env));//DEBUG

//      A forward reference is diagnosed if the declaration position
//      of the variable is greater than the current tree position
//      and the tree and variable definition occur in the same class
//      definition.  Note that writes don't count as references.
//      This check applies only to class and instance
//      variables.  Local variables follow different scope rules,
//      and are subject to definite assignment checking.
        if (v.pos > tree.pos &&
                v.owner.kind == TYP &&
                canOwnInitializer(env.info.scope.owner) &&
                v.owner == env.info.scope.owner.enclClass() &&
                ((v.flags() & STATIC) != 0) == Resolve.isStatic(env) &&
                (env.tree.getTag() != JCTree.ASSIGN ||
                        TreeInfo.skipParens(((JCAssign) env.tree).lhs) != tree)) {

            if (!onlyWarning || isStaticEnumField(v)) {
                // DRC - changed the following line to avoid complaints about forward references from invariants
                if (currentClauseType == null || currentClauseType == JmlToken.JMLDECL) log.error(tree.pos(), "illegal.forward.ref");
            } else if (useBeforeDeclarationWarning) {
                log.warning(tree.pos(), "forward.ref", v);
            }
        }

        v.getConstValue(); // ensure initializer is evaluated

        checkEnumInitializer(tree, env, v);
    }

    
    public JmlToken[] allowedFieldModifiers = new JmlToken[] {
            SPEC_PUBLIC, SPEC_PROTECTED, MODEL, GHOST,
            NONNULL, NULLABLE, INSTANCE, MONITORED, SECRET
       };
       
    public JmlToken[] allowedGhostFieldModifiers = new JmlToken[] {
            GHOST, NONNULL, NULLABLE, INSTANCE, MONITORED, SECRET
       };
       
    public JmlToken[] allowedModelFieldModifiers = new JmlToken[] {
            MODEL, NONNULL, NULLABLE, INSTANCE, SECRET
       };
       
    public JmlToken[] allowedFormalParameterModifiers = new JmlToken[] {
            NONNULL, NULLABLE, READONLY, REP, PEER, SECRET
       };
       
    public JmlToken[] allowedLocalVarModifiers = new JmlToken[] {
            NONNULL, NULLABLE, GHOST, UNINITIALIZED, READONLY, REP, PEER, SECRET
       };
       
    public void checkVarMods(JmlVariableDecl tree) {
        boolean inJML = Utils.isJML(tree.mods);
        boolean ghost = isGhost(tree.mods);
        if (tree.sym.owner.kind == Kinds.TYP) {  // Field declarations
            boolean model = isModel(tree.mods);
            boolean modelOrGhost = model || ghost;
            if (ghost) {
                allAllowed(tree.mods.annotations, allowedGhostFieldModifiers, "ghost field declaration");
            } else if (model) {
                allAllowed(tree.mods.annotations, allowedModelFieldModifiers, "model field declaration");
            } else {
                allAllowed(tree.mods.annotations, allowedFieldModifiers, "field declaration");
            }
            if (isInJmlDeclaration && modelOrGhost) {
                if (ghost) log.error(tree.pos,"jml.no.nested.ghost.type");
                else       log.error(tree.pos,"jml.no.nested.model.type");
            } else if (inJML && !modelOrGhost  && !isInJmlDeclaration) {
                log.error(tree.pos,"jml.missing.ghost.model");
            } else if (!inJML && modelOrGhost) {
                log.error(tree.pos,"jml.ghost.model.on.java");
            } 
            if (!model) checkForConflict(tree.mods,SPEC_PUBLIC,SPEC_PROTECTED);
            JCTree.JCAnnotation a;
            a = Utils.findMod(tree.mods,tokenToAnnotationName.get(INSTANCE));
            if (a != null && isStatic(tree.mods)) {
                log.error(a.pos(),"jml.conflicting.modifiers","instance","static");
            }
            if (model && ((tree.mods.flags & Flags.FINAL)!=0)) {
                a = Utils.findMod(tree.mods,tokenToAnnotationName.get(MODEL));
                log.error(a.pos(),"jml.conflicting.modifiers","model","final");
            }
        } else if ((tree.mods.flags & Flags.PARAMETER) != 0) { // formal parameters
            allAllowed(tree.mods.annotations, allowedFormalParameterModifiers, "formal parameter");
        } else { // local declaration
            allAllowed(tree.mods.annotations, allowedLocalVarModifiers, "local variable declaration");
            if (inJML && !ghost  && !isInJmlDeclaration) {
                log.error(tree.pos,"jml.missing.ghost");
            } else if (!inJML && ghost) {
                log.error(tree.pos,"jml.ghost.on.java");
            } 
        }
        
        checkForConflict(tree.mods,NONNULL,NULLABLE);
        
        // FIXME
        // spec_public only if already protected, default or private
        // spec_protected only if already default or private

    }
    
    public void visitJmlGroupName(JmlGroupName tree) {
        result = attribExpr(tree.selection,env,Type.noType);
        Symbol sym = null;
        if (tree.selection.type.tag == TypeTags.ERROR) return;
        else if (tree.selection instanceof JCIdent) sym = ((JCIdent)tree.selection).sym;
        else if (tree.selection instanceof JCFieldAccess) sym = ((JCFieldAccess)tree.selection).sym;
        else if (tree.selection instanceof JCErroneous) return;
        if (sym == null) {
            log.error(tree.pos,"jml.internal","Unexpectedly did not find a resolution for this data group expression");
            return;
        }
        if (!isModel(sym)) {
            log.error(tree.pos,"jml.datagroup.must.be.model");
        }
        if (inVarDecl != null && sym.isStatic() && !inVarDecl.sym.isStatic()) {  // FIXME - isStatic is not correct for JML fields in interfaces - use isStatic(sym.flags()) ?
            log.error(tree.pos,"jml.instance.in.static.datagroup");
        }
    }
    
    JmlVariableDecl inVarDecl;
    
    public void visitJmlTypeClauseIn(JmlTypeClauseIn tree) {
        boolean prev = JmlResolve.setJML(context,true);
        boolean prevEnv = pureEnvironment;
        JmlToken prevClauseType = currentClauseType;
        currentClauseType = tree.token;
        pureEnvironment = true;
        inVarDecl = tree.parentVar;
        for (JmlGroupName n: tree.list) {
            n.accept(this);
        }
        inVarDecl = null;
        pureEnvironment = prevEnv;
        currentClauseType = prevClauseType;
        JmlResolve.setJML(context,prev);
    }

    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps tree) {
        boolean prev = JmlResolve.setJML(context,true);
        boolean prevEnv = pureEnvironment;
        JmlToken prevClauseType = currentClauseType;
        currentClauseType = tree.token;
        pureEnvironment = true;
        // Also check that the member reference field matches the declaration FIXME
        // FIXME - static environment?
        attribExpr(tree.expression,env,Type.noType);
        for (JmlGroupName n: tree.list) {
            n.accept(this);
        }
        pureEnvironment = prevEnv;
        currentClauseType = prevClauseType;
        JmlResolve.setJML(context,prev);
    }

    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr tree) {
        if (!attribSpecs) return;
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        JavaFileObject old = log.useSource(tree.source);
        boolean prevAllowJML = JmlResolve.setJML(context,true);
        try {
            // invariant, axiom, initially
            Env<AttrContext> localEnv = env;//envForClause(tree,env.enclClass.sym);
            if ((tree.modifiers.flags & STATIC) != 0) localEnv.info.staticLevel++;

            attribExpr(tree.expression, localEnv, syms.booleanType);
            if ((tree.modifiers.flags & STATIC) != 0) localEnv.info.staticLevel--;
            checkTypeClauseMods(tree,tree.modifiers,tree.token.internedName() + " clause",tree.token);

        } finally {
            JmlResolve.setJML(context,prevAllowJML);
            pureEnvironment = prev;
            log.useSource(old);
        }
    }
    
    JmlToken[] clauseAnnotations = new JmlToken[]{ INSTANCE };
    JmlToken[] noAnnotations = new JmlToken[]{  };

    public void checkTypeClauseMods(JCTree tree, JCModifiers mods,String where, JmlToken token) {
        long f = 0;
        if (token != JmlToken.AXIOM) f = Flags.AccessFlags | Flags.STATIC;
        long diff = Utils.hasOnly(mods,f);
        if (diff != 0) log.error(tree.pos,"jml.bad.mods",Flags.toString(diff));
        JCAnnotation a = Utils.findMod(mods,tokenToAnnotationName.get(INSTANCE));
        if (a != null && isStatic(mods) ) {
            log.error(a.pos(),"jml.conflicting.modifiers","instance","static");
        }
        attribAnnotationTypes(mods.annotations,env);
        allAllowed(mods.annotations,token == JmlToken.AXIOM?noAnnotations:clauseAnnotations,where);
        if (token != JmlToken.AXIOM) {
            Check.instance(context).checkDisjoint(tree.pos(),mods.flags,Flags.PUBLIC,Flags.PROTECTED|Flags.PRIVATE);
            Check.instance(context).checkDisjoint(tree.pos(),mods.flags,Flags.PROTECTED,Flags.PRIVATE);
        }
    }
    
    
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint tree) {
        if (!attribSpecs) return;
        JavaFileObject old = log.useSource(tree.source);
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        boolean prevAllowJML = JmlResolve.setJML(context,true);
        try {
            // constraint
            Env<AttrContext> localEnv = env; // envForClause(tree,env.enclClass.sym);
            if ((tree.modifiers.flags & STATIC) != 0) localEnv.info.staticLevel++;
            attribExpr(tree.expression, localEnv, syms.booleanType);
            if ((tree.modifiers.flags & STATIC) != 0) localEnv.info.staticLevel--;
            checkTypeClauseMods(tree,tree.modifiers,"constraint clause",tree.token);
            if (tree.sigs != null) for (JmlTree.JmlConstraintMethodSig sig: tree.sigs) {

                if (sig.argtypes == null) {
                    // FIXME - not implemented
                } else {
                    ListBuffer<Type> types = new ListBuffer<Type>();
                    for (JCExpression e: sig.argtypes) {
                        attribType(e,localEnv);
                        types.append(e.type);
                    }
                    Type t = new Type.MethodType(types.toList(),null,null,null);
                    Symbol s = null;
                    if (sig.expression instanceof JCIdent) {
                        Name n = ((JCIdent)sig.expression).name;
                        if (n.equals(localEnv.enclClass.sym.name)) {
                            log.error(sig.pos(),"jml.no.constructors.allowed");
                        } else {
                            s = rs.resolveMethod(sig.pos(), env, n, t.getParameterTypes(), t.getTypeArguments());
                        }
                    } else if (sig.expression instanceof JCFieldAccess) {
                        JCFieldAccess selector = (JCFieldAccess)sig.expression;
                        attribTree(selector.selected,localEnv,VAR|TYP,Type.noType);
                        if (selector.selected.type.tsym != localEnv.enclClass.sym) {
                            log.error(sig.pos(),"jml.incorrect.method.owner");
                        } else {
                            s = rs.resolveMethod(sig.pos(), env, ((JCFieldAccess)sig.expression).name, t.getParameterTypes(), t.getTypeArguments());
                        }
                    } else {
                        // FIXME - error
                    }
                    if (s != null && s.kind != Kinds.ERR){
                        if (s.owner != localEnv.enclClass.sym) {
                            log.error(sig.pos(),"jml.incorrect.method.owner");
                        }
                    }
                }
            }

            // FIXME - complete implementation
        } finally {
            JmlResolve.setJML(context,prevAllowJML);
            pureEnvironment = prev;
            log.useSource(old);
        }
    }
    
   
    
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl tree) {
        if (!attribSpecs) return;
        JavaFileObject old = log.useSource(tree.source);
        boolean prevAllowJML = JmlResolve.setJML(context,true);
        try {
            attribStat(tree.decl,env);
        } finally {
            JmlResolve.setJML(context,prevAllowJML);
            log.useSource(old);
        }
    }
    
    
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer tree) {
        if (!attribSpecs) return;
        JavaFileObject old = log.useSource(tree.source);
        boolean prevAllowJML = JmlResolve.setJML(context,true);
        try {
            
            Env<AttrContext> localEnv =
                env.dup(tree, env.info.dup(env.info.scope.dupUnshared()));
            localEnv.info.scope.owner =
                new MethodSymbol(Flags.PRIVATE | BLOCK, names.empty, null,
                                 env.info.scope.owner);
            if (tree.token == JmlToken.STATIC_INITIALIZER) localEnv.info.staticLevel++;
            attribStat(tree.specs,localEnv);
        } finally {
            JmlResolve.setJML(context,prevAllowJML);
            log.useSource(old);
        }
    }
    
    
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents tree) {
        if (!attribSpecs) return;
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        JavaFileObject old = log.useSource(tree.source);
        boolean prevAllowJML = JmlResolve.setJML(context,true);
        try {
            attribExpr(tree.ident,env,Type.noType);
            Symbol sym = null;
            if (tree.ident instanceof JCIdent) sym = ((JCIdent)tree.ident).sym;
            else if (tree.ident instanceof JCFieldAccess) sym = ((JCFieldAccess)tree.ident).sym;
            else {
                // FIXME - error - not implemented
            }
            
            Env<AttrContext> localEnv = env; //envForClause(tree,sym);
            if ((tree.modifiers.flags & STATIC) != 0) localEnv.info.staticLevel++;
            
            if (tree.suchThat) {
                attribExpr(tree.expression, localEnv, syms.booleanType);
            } else if (tree.ident.type.getKind() == TypeKind.ERROR) {
                // skip
            } else if (tree.ident.type.getKind() == TypeKind.NONE) {
                // ERROR - parser should not let us get here - FIXME
            } else {
                attribExpr(tree.expression, localEnv, tree.ident.type);
            }
            if ((tree.modifiers.flags & STATIC) != 0) localEnv.info.staticLevel--;

            checkTypeClauseMods(tree,tree.modifiers,"represents clause",tree.token);
            if (sym != null && !sym.type.isErroneous() && sym.type.tag != TypeTags.ERROR) {
                if ( isStatic(sym.flags()) != isStatic(tree.modifiers)) {
                    // Note: we cannot use sym.isStatic() in the line above because it
                    // replies true when the flag is not set, if we are in an 
                    // interface and not a method.  Model fields do not obey that rule.
                    log.error(tree.pos,"jml.represents.bad.static");
                    // Presume that the model field is correct and proceed
                    if (isStatic(sym.flags())) tree.modifiers.flags |= Flags.STATIC;
                    else tree.modifiers.flags &=  ~Flags.STATIC;
                }
                if (!isModel(sym)) {
                    log.error(tree.pos,"jml.represents.expected.model");
                }
                if (env.enclClass.sym != sym.owner && isStatic(sym.flags())) {
                    log.error(tree.pos,"jml.misplaced.static.represents");
                }
            }
            
            // FIXME - need to check that ident refers to a model field
        } finally {
            JmlResolve.setJML(context,prevAllowJML);
            pureEnvironment = prev;
            log.useSource(old);
        }
    }
    
    /** This creates a local environment (like the initEnv for a variable declaration
     * that can be used to type-check the expression of a JmlTypeClause.  It handles
     * static correctly.
     * @param tree
     * @return the new environment
     */
    public Env<AttrContext> envForClause(JmlTypeClause tree, Symbol owner) {
        Env<AttrContext> localEnv = env.dupto(new AttrContextEnv(tree, env.info.dup()));
        localEnv.info.scope = new Scope.DelegatedScope(env.info.scope);
        localEnv.info.scope.owner = owner;
        //localEnv.info.lint = lint; // FIXME - what about lint?
        if ((tree.modifiers.flags & STATIC) != 0) // ||(env.enclClass.sym.flags() & INTERFACE) != 0) // FIXME - what about interfaces
            localEnv.info.staticLevel++;
        return localEnv;
    }
    
    
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor tree) {
        if (!attribSpecs) return;
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        JavaFileObject old = log.useSource(tree.source);
        boolean prevAllowJML = JmlResolve.setJML(context,true);
        try {
            // FIXME - need to check that ident is in this class
            attribExpr(tree.identifier,env,Type.noType);
            for (JCExpression c: tree.list) {
                attribExpr(c,env,Type.noType);
            }
        } finally {
            JmlResolve.setJML(context,prevAllowJML);
            pureEnvironment = prev;
            log.useSource(old);
        }
    }
    
    
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional tree) {
        if (!attribSpecs) return;
        JavaFileObject old = log.useSource(tree.source);
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        boolean prevAllowJML = JmlResolve.setJML(context,true);
        try {
            attribExpr(tree.identifier,env,Type.noType);
            attribExpr(tree.expression, env, syms.booleanType);
                // FIXME - need to check that ident is in this class
            // FIXM E- need to put in static environment, if appropriate
        } finally {
            JmlResolve.setJML(context,prevAllowJML);
            pureEnvironment = prev;
            log.useSource(old);
        }
    }
    
    
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {
        for (JmlSpecificationCase c: tree.cases) {
            c.accept(this);
        }
    }
    
    boolean forallOldEnv = false;
    
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl tree) {
        JmlToken t = tree.token;
        for (JCTree.JCStatement stat: tree.stats) {
            if (stat instanceof JmlVariableDecl) {
                forallOldEnv = true;
                stat.accept(this);
                forallOldEnv = false;
                JCTree.JCExpression init = ((JmlVariableDecl)stat).init;
                if (t == JmlToken.FORALL) {
                    if (init != null) log.error(init.pos(),"jml.forall.no.init");
                } else {
                    if (init == null) log.error(((JmlVariableDecl)stat).pos,"jml.old.must.have.init");
                }
                JCModifiers mods = ((JmlVariableDecl)stat).mods;
                if (Utils.hasOnly(mods,0)!=0) log.error(tree.pos,"jml.no.java.mods.allowed","method specification declaration");
                // The annotations are already checked as part of the local variable declaration
                //allAllowed(mods.annotations, JmlToken.typeModifiers, "method specification declaration");
            } else {
                log.error(stat.pos(),"jml.internal.notsobad","Unexpected " + stat.getClass() + " object type in a JmlMethodClauseDecl list");
            }
        }
    }

    /** This is an implementation that does the type attribution for 
     * method specification clauses
     * @param tree the method specification clause being attributed
     */
    
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) {
        switch (tree.token) {
            case REQUIRES:
            case ENSURES:
            case DIVERGES:
            case WHEN:
                attribExpr(tree.expression, env, syms.booleanType);
                break;
                
            case ACCESSIBLE:
            case CALLABLE:
            case CAPTURES:
                // FIXME - implement these - they will likely move to another method because they don't take expressions
                if (JmlOptionName.isOption(context, JmlOptionName.SHOW_NOT_IMPLEMENTED)) log.warning(tree.pos,"jml.unimplemented.construct",tree.token.internedName(),"JmlAttr.visitJmlMethodClauseExpr");
                break;
                
            default:
                log.error(tree.pos,"jml.unknown.construct",tree.token.internedName(),"JmlAttr.visitJmlMethodClauseExpr");
                break;
        }
    }

    /** This is an implementation that does the type attribution for 
     * method specification clauses
     * @param tree the method specification clause being attributed
     */
    
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional tree) {
        if (tree.predicate != null) attribExpr(tree.predicate, env, syms.booleanType);
        switch (tree.token) {
            case DURATION:
            case WORKING_SPACE:
                attribExpr(tree.expression, env, syms.longType);
                break;
                
            case MEASURED_BY:
                attribExpr(tree.expression, env, syms.intType);
                break;
                
            default:
                log.error(tree.pos,"jml.unknown.construct",tree.token.internedName(),"JmlAttr.visitJmlMethodClauseConditional");
                break;
        }
    }
    

    /** This is an implementation that does the type attribution for 
     * a signals method specification clause
     * @param tree the method specification clause being attributed
     */
    
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals tree) {
        if (tree.vardef.name == null) {
            tree.vardef.name = names.fromString("jml$$syntheticExceptionID");
        }
        

        Env<AttrContext> localEnv =
            env.dup(tree, env.info.dup(env.info.scope.dupUnshared()));

        tree.vardef.vartype.type = attribTree(tree.vardef.vartype, localEnv, TYP, syms.exceptionType);
        attribTree(tree.vardef, localEnv, pkind, syms.exceptionType);


        //initEnv.info.lint = lint; // FIXME - do we need this? - it si for suppressing warnings as in @SuppressWarning
        attribExpr(tree.expression, localEnv, syms.booleanType);
    }
    
    /** This is an implementation that does the type attribution for 
     * a signals_only method specification clause
     * @param tree the method specification clause being attributed
     */
    
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly tree) {
        for (JCExpression e: tree.list) {
            e.type = attribTree(e, env, TYP, syms.exceptionType);
        }
        // FIXME - need to compare these to the exceptions in the method declaration
    }
    
    /** This is an implementation that does the type attribution for 
     * a assignable method specification clause
     * @param tree the method specification clause being attributed
     */
    
    public void visitJmlMethodClauseAssignable(JmlMethodClauseAssignable tree) {
        for (JCTree e: tree.list) {
            attribExpr(e, env, Type.noType);
        }
    }


    
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        for (JCTree t: that.list) {
            attribExpr(t,env,Type.noType);
        }
        result = check(that, syms.booleanType, VAL, pkind, pt);
    }

    /** The JML modifiers allowed for a specification case */
    JmlToken[] specCaseAllowed = new JmlToken[]{};
    
    /** This implements the visiting of a JmlSpecificationCase, initiating
     * a visit of each clause in the case, setting the currentClauseType field
     * before visiting each one.
     */
    
    public void visitJmlSpecificationCase(JmlSpecificationCase tree) {
        JavaFileObject old = log.useSource(tree.sourcefile);
        Env<AttrContext> localEnv = null;
        Env<AttrContext> prevEnv = env;
        JmlToken prevClauseType = currentClauseType; // Just in case there is recursion
        try {
            if (tree.modifiers != null) {
                attribAnnotationTypes(tree.modifiers.annotations,env);
                if (tree.token == null) {
                    if (!Utils.hasNone(tree.modifiers)) {
                        log.error(tree.pos(),"jml.no.mods.lightweight");
                    }
                } else {
                    long diffs = Utils.hasOnly(tree.modifiers,Flags.AccessFlags);
                    if (diffs != 0) log.error(tree.pos(),"jml.bad.mods.spec.case",Flags.toString(diffs));
                    Check.instance(context).checkDisjoint(tree.pos(),tree.modifiers.flags,Flags.PUBLIC,Flags.PROTECTED|Flags.PRIVATE);
                    Check.instance(context).checkDisjoint(tree.pos(),tree.modifiers.flags,Flags.PROTECTED,Flags.PRIVATE);

                    // "code" is parsed specifically and is not considered a modifier
                    allAllowed(tree.modifiers.annotations,specCaseAllowed,"specification case");
                }
            }
            if (tree.code && tree.token == null) {
                // Lightweight specs may not be labeled "code"
                log.error(tree.pos(),"jml.no.code.lightweight");
            }
            // Making this sort of local environment restricts the scope of new
            // declarations but does not allow a declaration to hide earlier
            // declarations.  Thus old and forall declarations may rename
            // class fields, but may not rename method parameters or earlier old
            // or forall declarations.
            localEnv = env.dup(tree, env.info.dup(env.info.scope.dup()));
            env = localEnv;

            for (JmlMethodClause c: tree.clauses) {
                currentClauseType = c.token;
                c.accept(this);
            }
            
        } finally {
            env = prevEnv;
            if (localEnv != null) localEnv.info.scope.leave();
            currentClauseType = prevClauseType;
            log.useSource(old);
        }
    }
    
    /** Visits a JmlMethodSpecs by visiting each of its JmlSpecificationCases */
    
    public void visitJmlMethodSpecs(JmlMethodSpecs tree) {
        // The following test just returns when a JmlMethodSpecs object is
        // encountered that is just a member of a type declaration and has not
        // yet been associated with a method.
        // FIXME - does this still happen?  The following test seems overly complicated
        if (!attribSpecs && currentClauseType == null && env.enclMethod == null) return; 
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        //System.out.println("JMLATTR for specs cases of " + tree.decl.sym.owner + " " + tree.decl.sym);
        for (JmlSpecificationCase c: tree.cases) {
            c.accept(this);
        }
        pureEnvironment = prev;
    }
    
    // These are the annotation types in which \pre and \old with a label can be used (e.g. assert)
    private EnumSet<JmlToken> preTokens = JmlToken.methodStatementTokens;
    
    // These are the annotation, method and type spec clause types in which \old without a label can be used
    private EnumSet<JmlToken> oldNoLabelTokens = JmlToken.methodStatementTokens;
    {
        oldNoLabelTokens = oldNoLabelTokens.clone();
        oldNoLabelTokens.addAll(EnumSet.of(ENSURES,SIGNALS,CONSTRAINT,DURATION,WORKING_SPACE));
    }

    public void visitJmlMethodInvocation(JmlMethodInvocation tree) {
        JmlToken token = tree.token;
        if (tree.typeargs != null && tree.typeargs.size() != 0) {
            // At present the parser cannot produce anything with typeargs, but just in case
            // one squeaks through by some means or another
            log.error(tree.typeargs.head.pos(),"jml.no.typeargs.for.fcn",token.internedName());
        }
        
        Env<AttrContext> localEnv = env.dup(tree, env.info.dup());
            // FIXME: We create localEnv because that is what the super call does,
            // but I'm not sure why it is needed - DRC
        Type t = null;
        int n;
        switch (token) {
            case BSOLD:
            case BSPRE:
                // The argument can be a JML spec-expression
                // Expect one argument, result type is the same type
                n = tree.args.size();
                if (!(n == 1 || (token == JmlToken.BSOLD && n == 2))) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),
                            token == BSPRE ? "1" : "1 or 2",n);
                }
                if (token == BSPRE) {
                    // pre
                    if (!preTokens.contains(currentClauseType)) {
                        log.error(tree.pos+1, "jml.misplaced.old", "\\pre token", currentClauseType.internedName());
                        t = syms.errType;
                    }
                } else if (n == 1) {
                    // old with no label
                    if (!oldNoLabelTokens.contains(currentClauseType)) {
                        log.error(tree.pos+1, "jml.misplaced.old", "\\old token with no label", currentClauseType.internedName());
                        t = syms.errType;
                    }
                } else {
                    // old with label
                    if (!preTokens.contains(currentClauseType)) {
                        log.error(tree.pos+1, "jml.misplaced.old", "\\old token with a label", currentClauseType.internedName());
                        t = syms.errType;
                    }
                }
                Name label = null;
                if (n == 2) {
                    JCTree tr = tree.args.get(1);
                    if (tr.getTag() != JCTree.IDENT) {
                        log.error(tr.pos(),"jml.bad.label");
                    } else {
                        label = ((JCTree.JCIdent)tr).getName();
                    }
                }
                if (n == 0 || t == syms.errType) {
                    t = syms.errType;
                } else if (env.enclMethod == null) { // FIXME - what about types declared within methods
                    // In an type clause
                    attribExpr(tree.args.get(0), localEnv, Type.noType);
                    attribTypes(tree.typeargs, localEnv);
                    t = tree.args.get(0).type;
                } else {
                    // in a method clause
                    Env<AttrContext> oldenv = enclosingMethodEnv;
                    if (enclosingMethodEnv == null) {
                        // Just a precaution
                        Log.instance(context).error("jml.internal","Unsupported context for pre-state reference (anonymous class? initializer block?).  Please report the program.");
                        oldenv = env;
                        //
                    }
                    attribExpr(tree.args.get(0), oldenv, Type.noType);
                    attribTypes(tree.typeargs, oldenv);
                    t = tree.args.get(0).type;
                }
                result = check(tree, t, VAL, pkind, pt);
                break;
                
            case BSMAX:
                // Expect one argument of type JMLSetType, result type Lock
                // FIXME - this should be one argument of type JMLObjectSet, result type is Object
                // The argument expression may contain JML constructs
                attribArgs(tree.args, localEnv);  // We can't send in Lock as the requested type because Types does not know what to do with it - FIXME: perhaps make a JmlTypes that can handle the new primitives
                attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                }
                if (n == 0) t = syms.errType;
                else {
                    if (!tree.args.get(0).type.equals(JMLSetType)) {  // FIXME - use isSameType or check?  what about errors?
                        log.error(tree.args.get(0).pos(),"jml.max.expects.lockset",JMLSetType,tree.args.get(0).type.toString());
                    }
                    t = Lock;
                }
                result = check(tree, t, VAL, pkind, pt);
                break;

            case BSTYPEOF :
                // Expect one argument of any type, result type \TYPE
                // The argument expression may contain JML constructs
                attribArgs(tree.args, localEnv);
                attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                }
                t = this.TYPE;
                result = check(tree, t, VAL, pkind, pt);
                break;

            case BSNOTMODIFIED :
                // Expect any number of arguments of any type, result type is boolean
                // Can be used where an \old is used
                // FIXME - JML wants this to be a store-ref list
                if (!oldNoLabelTokens.contains(currentClauseType)) {
                    log.error(tree.pos+1, "jml.misplaced.old", "\\not_modified token", currentClauseType.internedName());
                    t = syms.errType;
                }
                attribArgs(tree.args, localEnv);
                attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                t = syms.booleanType;
                result = check(tree, t, VAL, pkind, pt);
                break;

            case BSNOTASSIGNED :
            case BSONLYASSIGNED :
            case BSONLYACCESSED :
            case BSONLYCAPTURED :
                // Expect any number of arguments of store-refs; result type is boolean
                attribArgs(tree.args, localEnv);
                attribTypes(tree.typeargs, localEnv);
                t = syms.booleanType;
                result = check(tree, t, VAL, pkind, pt);
                break;

            case BSNONNULLELEMENTS :
                // The argument can be a JML spec-expression
                // Expect any number of arguments of any array type, result type is boolean
                // TODO: Jml may require just one argument
                attribArgs(tree.args, localEnv);
                attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                t = syms.booleanType;
//                if (n != 1) {
//                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
//                }
                // FIXME - check that arguments are array type
                result = check(tree, t, VAL, pkind, pt);
                break;

            case BSELEMTYPE :
                // Expect one argument of any array type, result type is \TYPE
                // The argument expression may contain JML constructs
                attribArgs(tree.args, localEnv);
                attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                }
                if (n > 0) {
                    //attribTree(tree.args.get(0), localEnv, pkind, syms.classType); // FIXME - THIS DOES not work either
                    if (!(tree.args.get(0).type.tsym == syms.classType.tsym)) {  // FIXME - syms.classType is a parameterized type which is not equal to the argumet (particularly coming from \\typeof - using tsym works, but we ought to figure this out
                        log.error(tree.args.get(0).pos(),"jml.elemtype.expects.classtype",tree.args.get(0).type.toString());
                    }
                }
                // FIXME - need to check that argument is an array type - see comment above
                t = this.TYPE;
                result = check(tree, t, VAL, pkind, pt);
                break;


            case BSISINITIALIZED :
                // The argument is a type that is a reference type; the result is boolean
                // The argument may contain JML constructs
                attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                }
                if (n > 0) {
                    JCExpression arg = tree.args.get(0);
                    attribTree(arg, localEnv, TYP, Type.noType);
                    if (arg.type.isPrimitive()) {
                        log.error(arg.pos(),"jml.ref.arg.required",token.internedName());
                    }
                }
                
                t = syms.booleanType;
                result = check(tree, t, VAL, pkind, pt);
                break;

            case BSTYPELC :
                // Takes one argument which is a type (not an expression); the result is of type \TYPE
                // The argument may contain JML constructs
                attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                }
                if (n > 0) {
                    attribTree(tree.args.get(0), localEnv, TYP, Type.noType);
                }
                t = this.TYPE;
                result = check(tree, t, VAL, pkind, pt);
                break;

            case BSFRESH :
                // The arguments can be JML spec-expressions
                // The arguments can be any reference type; the result is boolean
                attribArgs(tree.args, localEnv); 
                attribTypes(tree.typeargs, localEnv);
                for (int i=0; i<tree.args.size(); i++) {
                    JCExpression arg = tree.args.get(i);
                    if (arg.type.isPrimitive()) {
                        log.error(arg.pos(),"jml.ref.arg.required",token.internedName());
                    }
                }
                result = check(tree, syms.booleanType, VAL, pkind, pt);
                break;

            case BSREACH :
                // The argument can be a JML spec-expressions
                // Expects one argument of reference type; result is of type JMLObjectSet
                attribArgs(tree.args, localEnv);
                attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                } else {
                    JCExpression arg = tree.args.get(0);
                    if (arg.type.isPrimitive()) {
                        log.error(arg.pos(),"jml.ref.arg.required",token.internedName());
                    }
                }
                if (JmlOptionName.isOption(context, JmlOptionName.SHOW_NOT_IMPLEMENTED)) log.warning(tree.pos,"jml.unimplemented.construct",token.internedName(),"JmlAttr.visitApply");
                result = tree.type = syms.errType;  // FIXME - result type not implemented
                break;
                
            case BSINVARIANTFOR :
                // The argument can be a JML spec-expression
                // Expects one argument of reference type; result is of type boolean
                attribArgs(tree.args, localEnv);
                attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                } else {
                    JCExpression arg = tree.args.get(0);
                    if (arg.type.isPrimitive()) {
                        log.error(arg.pos(),"jml.ref.arg.required",token.internedName());
                    }
                }
                result = check(tree, syms.booleanType, VAL, pkind, pt);
                break;


            case BSDURATION :
            case BSWORKINGSPACE :
                // The argument must be a Java expression
                // Expects one argument that is an arbitrary expression; result is of type long
                // Note: The JML reference manual puts constraints on the form of the expression; those seem to be unneeded
                // Note also: the argument is not actually evaluated (but needs to be evaluatable), 
                //   thus it may only contain Java constructs  (FIXME - there is no check on that)
                attribArgs(tree.args, localEnv); 
                attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                }
                result = check(tree, syms.longType, VAL, pkind, pt);
                break;

            case BSSPACE :
                // The argument may be a JML spec-expression
                // Expects one argument of reference type; result is of type long
                attribArgs(tree.args, localEnv);
                attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                }
                // FIXME - there is no check that the argument is of reference type - can't this apply to primitives as well?
                result = check(tree, syms.longType, VAL, pkind, pt);
                break;

            case BSNOWARN:
            case BSNOWARNOP:
            case BSWARN:
            case BSWARNOP:
            case BSBIGINT_MATH:
            case BSSAFEMATH:
            case BSJAVAMATH:
                // Expects one expression argument of any type; result is of the same type
                // FIXME - does this allow any JML spec-expression?
                // FIXME - the JMLb rules will require some numeric type promotions
                attribArgs(tree.args, localEnv);
                attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                }
                if (n == 0) {
                    t = syms.errType;
                } else {
                    t = tree.args.get(0).type;
                }
                result = check(tree, t, VAL, pkind, pt);
                break;
                 
            case BSONLYCALLED: // FIXME - needs implementation
            default:
                log.error(tree.pos,"jml.unknown.construct",token.internedName(),"JmlAttr.visitApply");
                result = tree.type = syms.errType;
                break;
                
        }
    }
    
    /** This is overridden to check that if we are in a pure environment,
     * the method is declared pure.
     */
    @Override
    public void visitApply(JCTree.JCMethodInvocation tree) {
        // Otherwise this is just a Java method application
        super.visitApply(tree);
        if (pureEnvironment && tree.meth.type != null && tree.meth.type.tag != TypeTags.ERROR) {
            // Check that the method being called is pure
            JCExpression m = tree.meth;
            Symbol sym = (m instanceof JCIdent ? ((JCIdent)m).sym : m instanceof JCFieldAccess ? ((JCFieldAccess)m).sym : null);
            if (sym instanceof MethodSymbol) {
                MethodSymbol msym = (MethodSymbol)sym;
                JmlMethodSpecs sp = JmlSpecs.instance(context).getSpecs(msym);
                if (sp != null) {
                    boolean isPure = isPure(msym) || isPure(msym.enclClass());
                    if (!isPure && !JmlOptionName.isOption(context,JmlOptionName.NOPURITYCHECK)) {
                        log.warning(tree.pos,"jml.non.pure.method",msym);
                    }
                }
            } else {
                // We are expecting that the expression that is the method
                // receiver (tree.meth) is either a JCIdent or a JCFieldAccess
                // If it is something else we end up here.
                if (sym == null) log.error("jml.internal.notsobad","Unexpected parse tree node for a method call in JmlAttr.visitApply: " + m.getClass());
                else log.error("jml.internal.notsobad","Unexpected symbol type for method expression in JmlAttr.visitApply: ", sym.getClass());
            }
        }
    }

    /** This handles JML statements such as assert and assume and unreachable and hence_by. */
    public void visitJmlStatementExpr(JmlTree.JmlStatementExpr tree) {
        boolean prevAllowJML = JmlResolve.setJML(context,true);
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        JmlToken prevClauseType = currentClauseType;
        currentClauseType = tree.token;
        // unreachable statements have a null expression
        if (tree.expression != null) attribExpr(tree.expression,env,syms.booleanType);
        if (tree.optionalExpression != null) attribExpr(tree.optionalExpression,env,syms.stringType);
        currentClauseType = prevClauseType;
        pureEnvironment = prev;
        JmlResolve.setJML(context,prevAllowJML);
    }

    boolean savedSpecOK = false; // FIXME - never read
    
    public void attribLoopSpecs(List<JmlTree.JmlStatementLoop> loopSpecs, Env<AttrContext> loopEnv) {
        savedSpecOK = false;
        if (loopSpecs == null || loopSpecs.isEmpty()) return;
        boolean prevAllowJML = JmlResolve.setJML(context,true);
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        for (JmlTree.JmlStatementLoop tree: loopSpecs) {
            JmlToken prevClauseType = currentClauseType;
            currentClauseType = tree.token;
            if (tree.token == JmlToken.LOOP_INVARIANT) attribExpr(tree.expression,loopEnv,syms.booleanType);
            else attribExpr(tree.expression,loopEnv,syms.longType);  // FIXME - what type to use
            currentClauseType = prevClauseType;
        }
        pureEnvironment = prev;
        JmlResolve.setJML(context,prevAllowJML);
    }
    
    
    /** This handles JML statements that give method-type specs for method body statements. */
    public void visitJmlStatementSpec(JmlTree.JmlStatementSpec tree) {
        boolean prevAllowJML = JmlResolve.setJML(context,true);
        JmlToken prevClauseType = currentClauseType;
        currentClauseType = null;
        if (tree.statementSpecs != null) attribStat(tree.statementSpecs,env);
        currentClauseType = prevClauseType;
        JmlResolve.setJML(context,prevAllowJML);
    }
    
    /** This handles JML declarations (method and ghost fields, methods, types) */
    public void visitJmlStatementDecls(JmlTree.JmlStatementDecls tree) {
        boolean prevAllowJML = JmlResolve.setJML(context,true);
        JmlToken prevClauseType = currentClauseType;
        currentClauseType = tree.token;
        for (JCTree.JCStatement s : tree.list) {
            attribStat(s,env);
        }
        currentClauseType = prevClauseType;
        JmlResolve.setJML(context,prevAllowJML);
    }
    
    /** This handles JML statements such as set and debug */
    public void visitJmlStatement(JmlTree.JmlStatement tree) {  // FIXME - need to test appropriately for purity
        boolean prevAllowJML = JmlResolve.setJML(context,true);
        JmlToken prevClauseType = currentClauseType;
        currentClauseType = tree.token;
        attribStat(tree.statement,env);
        currentClauseType = prevClauseType;
        JmlResolve.setJML(context,prevAllowJML);
    }

    /** This handles JML primitive types */
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        result = that.token == JmlToken.BSTYPEUC ? TYPE :
            that.token == JmlToken.BSBIGINT ? BIGINT :
            that.token == JmlToken.BSREAL ? REAL :
                    syms.errType ;
        if (result == syms.errType) {
            log.error(that.pos,"jml.unknown.type.token",that.token.internedName(),"JmlAttr.visitJmlPrimitiveTypeTree");
        }
        that.type = result;
    }
    
    /** This set holds method clause types in which the \result token may appear */
    public EnumSet<JmlToken> resultClauses = EnumSet.of(ENSURES,DURATION,WORKING_SPACE);
    
    /** This handles expression constructs with no argument list such as \\result */
    public void visitJmlSingleton(JmlSingleton that) {
        JmlToken jt = that.token;
        Type t = syms.errType;
        switch (jt) {
               
            case BSLOCKSET:
                t = JMLSetType;
                break;
                
            case BSINDEX:
                t = syms.intType;
                if (foreachLoopStack.isEmpty()) {
                    log.error(that.pos,"jml.outofscope",jt.internedName());
                } else {
                    that.info = foreachLoopStack.get(0).indexDecl.sym;
                }
                break;
                
            case BSVALUES:
                t = JMLValuesType;
                if (foreachLoopStack.isEmpty()) {
                    log.error(that.pos,"jml.outofscope",jt.internedName());
                } else {
                    JCVariableDecl d = foreachLoopStack.get(0).valuesDecl;
                    if (d == null) {
                        log.error(that.pos,"jml.notforthisloop",jt.internedName());
                    } else {
                        that.info = d.sym;
                    }
                }
                break;
                
            case BSRESULT:
                if (!resultClauses.contains(currentClauseType)) {
                    // The +1 is to fool the error reporting mechanism into 
                    // allowing other error reports about the same token
                    log.error(that.pos+1, "jml.misplaced.result", currentClauseType.internedName());
                }
                JCTree.JCMethodDecl md = env.enclMethod;
                JCTree res = md.getReturnType();
                if (res == null || types.isSameType(res.type,syms.voidType)) {
                    log.error(that.pos+1, "jml.void.result");
                    t = syms.errType;
                } else {
                    t = res.type;
                }
                break;
                
            case BSSAME:
                if (currentClauseType != REQUIRES) {
                    log.error(that.pos,"jml.misplaced.same");
                }
                t = syms.booleanType;
                // Check that this is only used in a requires clause and not in conjunction with anything else - FIXME
                break;
                
            case BSNOTSPECIFIED:
                t = syms.errType;  // Use errType so it does not propagate error messages
                break;

            case BSNOTHING:
            case BSEVERYTHING:
                t = Type.noType;
                break;
                
            case INFORMAL_COMMENT:
                t = syms.booleanType;
                break;
                
            default:
                t = syms.errType;
                log.error(that.pos,"jml.unknown.type.token",that.token.internedName(),"JmlAttr.visitJmlSingleton");
                break;
        }
        result = check(that, t, VAL, pkind, pt);
    }
    
//    public void visitJmlFunction(JmlFunction that) {
//        // Actually, I don't think this gets called.  It would get called through
//        // visitApply.
//        result = that.type = Type.noType;
//    }
    
    public void visitJmlRefines(JmlRefines that) {
        // nothing to do
    }
    

    public void visitJmlImport(JmlImport that) {
        visitImport(that);
        // FIXME - ignoring model
    }
    

    public void visitJmlBinary(JmlBinary that) {  // FIXME - how do we handle unboxing, casting
        switch (that.op) {
            case EQUIVALENCE:
            case INEQUIVALENCE:
            case IMPLIES:
            case REVERSE_IMPLIES:
                attribExpr(that.lhs,env,syms.booleanType);
                attribExpr(that.rhs,env,syms.booleanType);
                result = syms.booleanType;
                break;
                
            case LOCK_LT:
            case LOCK_LE:
                attribExpr(that.lhs,env,syms.objectType);
                attribExpr(that.rhs,env,syms.objectType);
                result = syms.booleanType;
                break;
                
                
            case SUBTYPE_OF:
                // Note: the method of comparing types here ignores any type
                // arguments.  If we use isSameType, for example, then Class
                // and Class<Object> are different.  In this case, all we need 
                // to know is that the operands are some type of Class.
                // FIXME - what about subclasses of Class
                attribExpr(that.lhs,env,Type.noType);
                if (!that.lhs.type.equals(TYPE)) {
                    if (!that.lhs.type.tsym.equals(syms.classType.tsym)) {
                        log.error(that.lhs.pos(),"jml.subtype.arguments",that.lhs.type);
                    }
                }
                attribExpr(that.rhs,env,Type.noType);
                if (!that.rhs.type.equals(TYPE)) {
                    if (!that.rhs.type.tsym.equals(syms.classType.tsym)) {
                        log.error(that.rhs.pos(),"jml.subtype.arguments",that.rhs.type);
                    }
                }
                result = that.type = syms.booleanType;
                break;
                
            default:
                log.error(that.pos(),"jml.unknown.operator",that.op.internedName(),"JmlAttr");
                break;
        }
        result = check(that, result, VAL, pkind, pt);
    }
    
    // TODO - note that this is not limited to boolean
    public void visitJmlLblExpression(JmlLblExpression that) {
        attribExpr(that.expression, env, Type.noType);
        result = check(that, that.expression.type, VAL, pkind, pt);
    }
    
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
//        for (JCVariableDecl decl: that.decls) {
//            attribType(decl.getType(),env);
//            decl.type = decl.vartype.type;
//        }
        
        // Need to create a local environment with the new names
        Env<AttrContext> localEnv =
            env.dup(that, env.info.dup(env.info.scope.dup()));
        for (JCVariableDecl decl: that.decls) {
            memberEnter.memberEnter(decl, localEnv);
            decl.type = decl.vartype.type; // FIXME not sure this is needed
        }
//        Iterator<JCExpression> iter = that.localtypes.iterator();
//        for (Name n: that.names) {
//            // FIXME - need to associate a better position with each type
//            JCExpression localtype = iter.next();
//            JCVariableDecl result = JmlTree.Maker.instance(context).at(localtype.pos()).VarDef(JmlTree.Maker.instance(context).Modifiers(0), n, localtype, null);
//            memberEnter.memberEnter(result, localEnv);
//        }

        if (that.range != null) attribExpr(that.range, localEnv, syms.booleanType);
        Type resultType = syms.errType;
        switch (that.op) {
            case BSEXISTS:
            case BSFORALL:
                attribExpr(that.predicate, localEnv, syms.booleanType);
                resultType = syms.booleanType;
                break;
                
            case BSNUMOF:
                attribExpr(that.predicate, localEnv, syms.booleanType);
                resultType = syms.intType; // FIXME - int? long? bigint?
                break;
                
            case BSMAX:
            case BSMIN:
                attribExpr(that.predicate, localEnv, syms.longType); // FIXME - int? long? numeric? bigint? double?
                resultType = that.predicate.type;
                break;

            case BSSUM:
            case BSPRODUCT:
                attribExpr(that.predicate, localEnv, syms.longType); // FIXME - int? long? numeric? bigint? double?
                resultType = that.predicate.type;
                break;
                
            default:
                log.error(that.pos(),"jml.unknown.construct",that.op.internedName(),"JmlAttr.visitJmlQuantifiedExpr");
                break;
        }
        for (JCVariableDecl decl: that.decls) {
            JCModifiers mods = decl.getModifiers();
            if (Utils.hasOnly(mods,0)!=0) log.error(mods.pos,"jml.no.java.mods.allowed","quantified expression");
            attribAnnotationTypes(mods.annotations,env);
            allAllowed(mods.annotations, JmlToken.typeModifiers, "quantified expression");
        }
        result = check(that, resultType, VAL, pkind, pt);
        localEnv.info.scope.leave();
        return;
    }
    
    public void visitJmlSetComprehension(JmlSetComprehension that) {
        // that.type must be a subtype of JMLSetType                    FIXME - not checked
        // that.variable must be a declaration of a reference type
        // that.predicate must be boolean
        // that.predicate must have a special form                      FIXME - not checked
        // result has type that.type
        // Generics: perhaps JMLSetType should have a type argument.  
        //   If so, then in new T { TT i | ... }
        // T is a subtype of JMLSetType<? super TT>  (FIXME - is that right?)
        // T must be allowed to hold elements of type TT
        attribType(that.newtype,env);
        attribType(that.variable.vartype,env);
        attribAnnotationTypes(that.variable.mods.annotations,env);

        Env<AttrContext> localEnv =
            env.dup(that, env.info.dup(env.info.scope.dup()));
//        localEnv.info.scope.owner =
//            new MethodSymbol(BLOCK, names.empty, null,
//                             env.info.scope.owner);

//        attribStat(that.variable, localEnv);
        memberEnter.memberEnter(that.variable, localEnv);

//        attribStat(that.variable,env);
//        Env<AttrContext> localEnv = memberEnter.initEnv(that.variable,env);

//        Env<AttrContext> initEnv = memberEnter.initEnv(that.variable, env);
//        initEnv.info.lint = localEnv.info.lint;

        attribExpr(that.predicate,localEnv,syms.booleanType);
        
        JCModifiers mods = that.variable.mods;
        if (Utils.hasOnly(mods,0)!=0) log.error(that.pos,"jml.no.java.mods.allowed","set comprehension expression");
        allAllowed(mods.annotations, JmlToken.typeModifiers, "set comprehension expression");

        result = check(that, that.newtype.type, VAL, pkind, pt);
        localEnv.info.scope.leave();
    }
    
    @Override
    public void visitSelect(JCFieldAccess tree) {
        if (tree.name != null) super.visitSelect(tree);
        // This is a store-ref with a wild-card field
        else {
            super.visitSelect(tree);
            result = tree.type = Type.noType;
        }
    }
    

    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        if (that.lo != null) attribExpr(that.lo,env,syms.intType); // FIXME - int or long or bigint
        if (that.hi != null && that.hi != that.lo) attribExpr(that.hi,env,syms.intType); // FIXME - int or long or bigint
        Type t = attribExpr(that.expression,env,Type.noType);
        if (t.getKind() != TypeKind.ARRAY) {
            if (t.getKind() != TypeKind.ERROR) log.error(that.expression.pos(),"jml.not.an.array",t);
            t = syms.errType;
            result = check(that, t, VAL, pkind, pt);
        } else {
            t = ((ArrayType)t).getComponentType();
            result = check(that, t, VAL, pkind, pt);
        }
    }



    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        result = that.type = Type.noType;
        // FIXME - call check
    }
    
    @Override
    public void visitReturn(JCReturn that) {
//        if (addRac && that.expr != null) {
//            that.expr = make.Assign(make.Ident(resultName),that.expr);
//        }
        super.visitReturn(that);
    }
    
    
    /** This is a map from token to Name.  It has to be generated at runtime because
     * Names are dependent on the Context.  It is supposedly a very fast
     * (i.e. array) lookup.  The Names are the fully-qualified name of the type
     * of the annotation that represents the given modifier token.
     */
    public EnumMap<JmlToken,Name> tokenToAnnotationName = new EnumMap<JmlToken,Name>(JmlToken.class);
    
    /** A Name for the fully-qualified name of the package that the JML annotations are defined in. */
    public Name packageName;
    
    /** For the given context, initialized the value of packageName and the
     * content of the tokenToAnnotationName mapping; since Name objects are
     * involved and they are defined per context, this initialization must be
     * performed after a context is defined.
     * @param context the compilation context in which to do this initialization
     */
    public void initNames(Context context) {
        Names names = Names.instance(context);
        packageName = (Names.instance(context).fromString(Utils.jmlAnnotationPackage));
        for (JmlToken t: JmlToken.modifiers) {
            if (t.annotationType == null) {
                // No class for this token, but we won't complain
                // The result is to silently ignore the token (TODO)
            } else {
                String s = t.annotationType.getName();
                Name n = names.fromString(s);
                tokenToAnnotationName.put(t,n);
            }
        }
    }
    
    /** Checks that all of the JML annotations present in the first argument
     * are also present in the second argument, issuing error messages if they
     * are not.
     * @param annotations a list of annotations to check
     * @param allowed the set of allowed annotations
     * @param place a description of where the annotations came from, for error messages
     */
    public void allAllowed(List<JCTree.JCAnnotation> annotations, JmlToken[] allowed, String place) {
        outer: for (JCTree.JCAnnotation a: annotations) {
            for (JmlToken c: allowed) {
                if (a.annotationType.type.tsym.flatName().equals(tokenToAnnotationName.get(c))) continue outer; // Found it
            }
            // a is not is the list, but before we complain, check that it is
            // one of our annotations
            if (a.annotationType.type.tsym.packge().flatName().equals(packageName)) { // FIXME - flatname or fullname
                log.error(a.pos(),"jml.illegal.annotation",place);
            }
        }
    }
    
    /** This checks that the given modifier set does not have annotations for
     * both of a pair of mutually exclusive annotations; it prints an error
     * message if they are both present
     * @param mods the modifiers to check
     * @param ta the first JML token
     * @param tb the second JML token
     */
    public void checkForConflict(JCModifiers mods, JmlToken ta, JmlToken tb) {
        JCTree.JCAnnotation a,b;
        a = Utils.findMod(mods,tokenToAnnotationName.get(ta));
        b = Utils.findMod(mods,tokenToAnnotationName.get(tb));
        if (a != null && b != null) {
            log.error(b.pos(),"jml.conflicting.modifiers",ta.internedName(),tb.internedName());
        }
    }
    
    /** Finds the annotation in the modifiers corresponding to the given token
     * @param mods the modifiers to check
     * @param ta the token to look for
     * @return a reference to the annotation AST node, or null if not found
     */
    //@ nullable
    public JCAnnotation findMod(/*@nullable*/JCModifiers mods, JmlToken ta) {
        if (mods == null) return null;
        return Utils.findMod(mods,tokenToAnnotationName.get(ta));
    }
    
    /** Returns true if the given modifiers includes model
     * @param mods the modifiers to check
     * @return true if the model modifier is present, false if not
     */
    public boolean isModel(/*@nullable*/JCModifiers mods) {
        return findMod(mods,JmlToken.MODEL) != null;
    }
    
    public boolean isModel(Symbol symbol) {
        if (modelAnnotationSymbol == null) {
            modelAnnotationSymbol = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.annotations.Model"));
        }
        return symbol.attribute(modelAnnotationSymbol)!=null;

    }
    
    public boolean isPure(Symbol symbol) {
        if (pureAnnotationSymbol == null) {
            pureAnnotationSymbol = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.annotations.Pure"));
        }
        return symbol.attribute(pureAnnotationSymbol)!=null;

    }
    
    /** Returns true if the given modifiers includes ghost
     * @param mods the modifiers to check
     * @return true if the ghost modifier is present, false if not
     */
    public boolean isGhost(/*@nullable*/JCModifiers mods) {
        return findMod(mods,JmlToken.GHOST) != null;
    }
    
    public boolean isStatic(/*@nullable*/JCModifiers mods) {
        return (mods.flags & Flags.STATIC)!=0;
    }
    
    public boolean isStatic(long flags) {
        return (flags & Flags.STATIC)!=0;
    }
    
    public JCFieldAccess findUtilsMethod(String n) {
        Scope.Entry e = utilsClass.members().lookup(names.fromString("assertionFailure"));
        Symbol ms = e.sym;
        JCFieldAccess m = make.Select(utilsClassIdent,names.fromString("assertionFailure"));
        m.sym = ms;
        m.type = m.sym.type;
        return m;
    }
    
//    // FIXME - can we cache the && and || operators ?
//    /** Make an attributed binary expression.
//     *  @param optag    The operators tree tag.
//     *  @param lhs      The operator's left argument.
//     *  @param rhs      The operator's right argument.
//     */
//    JCBinary makeBinary(int optag, JCExpression lhs, JCExpression rhs) {
//        JCBinary tree = make.Binary(optag, lhs, rhs);
//        tree.operator = rs.resolveBinaryOperator(
//            make_pos, optag, env, lhs.type, rhs.type);
//        tree.type = tree.operator.type.getReturnType();
//        return tree;
//    }
//
//    // FIXME - can we cache the ! operator?
//    /** Make an attributed unary expression.
//     *  @param optag    The operators tree tag.
//     *  @param arg      The operator's argument.
//     */
//    JCUnary makeUnary(int optag, JCExpression arg) {
//        JCUnary tree = make.Unary(optag, arg);
//        tree.operator = rs.resolveUnaryOperator(
//            make_pos, optag, env, arg.type);
//        tree.type = tree.operator.type.getReturnType();
//        return tree;
//    }

    /** Make an attributed tree representing a literal. This will be an
     *  Ident node in the case of boolean literals, a Literal node in all
     *  other cases.
     *  @param type       The literal's type.
     *  @param value      The literal's value.
     */
    JCLiteral makeLit(Type type, Object value) {
        return make.Literal(type.tag, value).setType(type);
    }

   
    public JCStatement methodCallPre(String sp, JCExpression tree) {
        // org.jmlspecs.utils.Utils.assertionFailure();
        
        String s = sp + "precondition is false";
        JCExpression lit = makeLit(syms.stringType,s);
        JCFieldAccess m = findUtilsMethod("assertionFailure");
        JCExpression nulllit = makeLit(syms.botType, null);
        JCExpression c = make.Apply(null,m,List.<JCExpression>of(lit,nulllit));
        c.setType(Type.noType);
        return make.Exec(c);
    }
    
    public JCStatement methodCallPost(String sp, JCExpression tree) {
        // org.jmlspecs.utils.Utils.assertionFailure();
        
        String s = sp + "postcondition is false";
        JCExpression lit = make.Literal(s);
        JCFieldAccess m = findUtilsMethod("assertionFailure");
        JCExpression nulllit = makeLit(syms.botType, null);
        JCExpression c = make.Apply(null,m,List.<JCExpression>of(lit,nulllit));
        c.setType(Type.noType);
        return make.Exec(c);
    }
    
//    public JCStatement methodCall(JmlStatementExpr tree) {
//        // org.jmlspecs.utils.Utils.assertionFailure();
//        
//        JmlToken t = tree.token;
//        String s = t == JmlToken.ASSERT ? "assertion is false" : t == JmlToken.ASSUME ? "assumption is false" : "unreachable statement reached";
//        s = tree.source.getName() + ":" + tree.line + ": JML " + s;
//        JCExpression lit = make.Literal(s);
//        JCFieldAccess m = findUtilsMethod("assertionFailure");
//        JCExpression nulllit = makeLit(syms.botType, null);
//        JCExpression c = make.Apply(null,m,List.<JCExpression>of(lit,nulllit));
//        c.setType(Type.noType);
//        return make.Exec(c);
//    }
//    
//    public JCStatement methodCall(JmlStatementExpr tree, JCExpression translatedOptionalExpr) {
//        // org.jmlspecs.utils.Utils.assertionFailure();
//        
//        JmlToken t = tree.token;
//        String s = t == JmlToken.ASSERT ? "assertion is false" : t == JmlToken.ASSUME ? "assumption is false" : "unreachable statement reached";
//        s = tree.source.getName() + ":" + tree.line + ": JML " + s;
//        JCExpression lit = make.Literal(s);
//        JCFieldAccess m = findUtilsMethod("assertionFailure");
//        JCExpression c = make.Apply(null,m,List.<JCExpression>of(lit,translatedOptionalExpr));
//        c.setType(Type.noType);
//        return make.Exec(c);
//    }
    
    public String position(JavaFileObject source, int pos) {
        JavaFileObject pr = log.currentSourceFile();
        log.useSource(source);
        String s = source.getName() + ":" + log.currentSource().getLineNumber(pos) + ": JML ";
        log.useSource(pr);
        return s;
    }

    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        attribLoopSpecs(that.loopSpecs,env);
        super.visitDoLoop(that);
    }
    
    java.util.List<JmlEnhancedForLoop> foreachLoopStack = new java.util.LinkedList<JmlEnhancedForLoop>();

    protected JCVariableDecl makeVariableDecl(Name name, Type type, JCExpression init, int pos) {
        JmlTree.Maker factory = (JmlTree.Maker)JmlTree.Maker.instance(context);
        VarSymbol vsym = new VarSymbol(0, name, type, null);
        vsym.pos = pos;
        JCVariableDecl decl = factory.at(pos).VarDef(vsym,init);
        return decl;
    }

    protected JCLiteral makeIntLiteral(int value, int pos) {
        JmlTree.Maker factory = (JmlTree.Maker)JmlTree.Maker.instance(context);
        JCLiteral lit = factory.at(pos).Literal(TypeTags.INT,value);
        lit.type = syms.intType;
        return lit;
    }
    
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop tree) {
        foreachLoopStack.add(0,tree);
        try {
        // MAINTENANCE ISSUE: code duplicated mostly from the superclass
            Env<AttrContext> loopEnv =
                env.dup(env.tree, env.info.dup(env.info.scope.dup()));
            savedSpecOK = true;
            attribStat(tree.var, loopEnv);
            Type exprType = types.upperBound(attribExpr(tree.expr, loopEnv));
            chk.checkNonVoid(tree.pos(), exprType);
            Type elemtype = types.elemtype(exprType); // perhaps expr is an array?
            if (elemtype == null) {
                // or perhaps expr implements Iterable<T>?
                Type base = types.asSuper(exprType, syms.iterableType.tsym);
                if (base == null) {
                    log.error(tree.expr.pos(), "foreach.not.applicable.to.type");
                    elemtype = syms.errType;
                } else {
                    List<Type> iterableParams = base.allparams();
                    elemtype = iterableParams.isEmpty()
                        ? syms.objectType
                        : types.upperBound(iterableParams.head);
                }
            }
            chk.checkType(tree.expr.pos(), elemtype, tree.var.sym.type);
            loopEnv.tree = tree; // before, we were not in loop!

            trForeachLoop(tree,elemtype);
            
            attribLoopSpecs(tree.loopSpecs,loopEnv);
            // FIXME - should this be before or after the preceding statement
            
            PackageSymbol p = enclosingMethodEnv.enclClass.sym.packge();
            if (tree.implementation != null && !p.flatName().toString().equals("org.jmlspecs.utils")) {
                attribStat(tree.implementation, loopEnv);
            } else {
                tree.implementation = null;
                attribStat(tree.body, loopEnv);
            }
            loopEnv.info.scope.leave();
            result = null;
        } finally {
            foreachLoopStack.remove(0);
        }
    }
    
    public JCExpression autobox(JCExpression e, Type elemtype) {
        factory.at(e.pos);
        Type boxed = Types.instance(context).boxedClass(elemtype).type;
        Name valueof = names.fromString("valueOf");
        JCExpression s = factory.Select(factory.Type(boxed),valueof);
        s = factory.Apply(null,s,List.<JCExpression>of(e));
        return s;
    }
    
    public void trForeachLoop(JmlEnhancedForLoop tree, Type elemtype) {
        // Desugar the foreach loops in order to put in the JML auxiliary loop indices
        factory.at(tree.pos); // Sets the position until reset
        
        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
        ListBuffer<JCExpressionStatement> step = new ListBuffer<JCExpressionStatement>();

        Name name = names.fromString("$$index$"+tree.pos);
        tree.indexDecl = makeVariableDecl(name,syms.intType,zeroLit,tree.pos);
        tree.indexDecl.sym.owner = tree.var.sym.owner;

        factory.at(tree.pos+1);
        JCIdent ident = factory.Ident(tree.indexDecl.sym);        
        JCExpressionStatement st = factory.Exec(factory.Unary(JCTree.PREINC,ident));  // ++ $$index;
        st.type = syms.intType;
        stats.append(tree.indexDecl);
        step.append(st);
        factory.at(tree.pos);

        Type boxedElemType = elemtype;
        if (elemtype.isPrimitive()) {
            boxedElemType = Types.instance(context).boxedClass(elemtype).type;
        }
        {
            Name defempty = names.fromString("defaultEmpty");
            JCFieldAccess sel = factory.Select(factory.Type(JMLUtilsType),defempty);
            JCExpression e = factory.Apply(List.<JCExpression>of(factory.Type(boxedElemType)),sel,List.<JCExpression>nil()); // Utils.<boxedElemType>defaultEmpty()

            int p = tree.pos;
            name = names.fromString("$$values$"+p);
            ClassType ct = new ClassType(JMLValuesType.getEnclosingType(),List.<Type>of(boxedElemType),JMLValuesType.tsym);
            tree.valuesDecl = makeVariableDecl(name,ct,e,p);
            tree.valuesDecl.sym.owner = tree.var.sym.owner;
            stats.append(tree.valuesDecl);

            factory.at(tree.pos+2);
            Name add = names.fromString("add");
            sel = factory.Select(factory.Ident(tree.valuesDecl),add);
            JCExpression ev = factory.Ident(tree.var);
            if (tree.var.type.isPrimitive() && !boxedElemType.isPrimitive()) ev = autobox(ev,tree.var.type);
            JCMethodInvocation app = factory.Apply(null,sel,List.<JCExpression>of(ev));
            
            factory.at(tree.pos+3);
            JCAssign asgn = factory.Assign(factory.Ident(tree.valuesDecl),app);
            step.append(factory.Exec(asgn));
            
            factory.at(tree.pos);

        }
        
        stats.append(tree.var);
        
        JCExpression cond = null;
        
        ListBuffer<JCStatement> bodystats = new ListBuffer<JCStatement>();

        JCExpression newvalue;
        JmlStatementLoop inv = null;
        if (tree.expr.type.tag == TypeTags.ARRAY) {
            // Replace the foreach loop for (T t: a) body;
            // by
            // int $$index = 0;
            // JMLList $$values = Utils.<T'>defaultEmpty();
            // T t;
            // for (; $$index < a.length; $$index++, $$values.add(t') ) {
            //       check loop invariant
            //    t = a[$$index];
            //    body
            // }
            
            JCExpression arraylen = factory.Select(tree.expr,syms.lengthVar);
            cond = factory.Binary(JCTree.LT,ident,arraylen);

            newvalue = factory.Indexed(tree.expr,ident); // newvalue :: expr[$$index]
            if (elemtype.isPrimitive() && !tree.var.type.isPrimitive()) newvalue = autobox(newvalue,elemtype);
            
            JCExpression invexpr = factory.Binary(JCTree.AND,factory.Binary(JCTree.LE,zeroLit,ident),factory.Binary(JCTree.LE,ident,arraylen));
            inv = factory.JmlStatementLoop(JmlToken.LOOP_INVARIANT,invexpr);

            
        } else {
            // Replace the foreach loop for (T t: c) body;
            // by
            // int $$index = 0;
            // JMLList $$values = Utils.<T>defaultEmpty();
            // Iterator<T> it = c.iterator();
            // T t = null;
            // for (; it.hasNext(); $$index++, $$values.add(t)) {
            //    t = it.next();
            //    body
            // }
            
            name = names.fromString("$$iter$"+tree.pos);
            ClassType ct = new ClassType(JMLIterType.getEnclosingType(),List.<Type>of(elemtype),JMLIterType.tsym);
            tree.iterDecl = makeVariableDecl(name,ct,nullLit,tree.pos);
            tree.iterDecl.sym.owner = tree.var.sym.owner;
            stats.append(tree.iterDecl);
            
            Name hasNext = names.fromString("hasNext");
            JCFieldAccess sel = factory.Select(factory.Ident(tree.iterDecl),hasNext);
            cond = factory.Apply(null,sel,List.<JCExpression>nil()); // cond :: $$iter . hasNext()

            Name next = names.fromString("next");
            sel = factory.Select(factory.Ident(tree.iterDecl),next);
            newvalue = factory.Apply(null,sel,List.<JCExpression>nil());  // newvalue ::  $$iter . next()
        }
        
        bodystats.append(factory.Exec(factory.Assign(factory.Ident(tree.var),newvalue))); // t = newvalue;
        bodystats.append(tree.body);
        
        factory.at(tree.pos+1);
        Name sz = names.fromString("size");
        JCFieldAccess sel = factory.Select(factory.Ident(tree.valuesDecl),sz);
        JCExpression invexpr2 = factory.Apply(null,sel,List.<JCExpression>nil());  // invexpr2 ::  $$values . size()
        invexpr2 = factory.Binary(JCTree.AND,factory.Binary(JCTree.NE,nullLit,factory.Ident(tree.valuesDecl)),factory.Binary(JCTree.EQ,ident,invexpr2));
        JmlStatementLoop inv2 = factory.JmlStatementLoop(JmlToken.LOOP_INVARIANT,invexpr2);
        factory.at(tree.pos);
        
        JCBlock block = factory.Block(0,bodystats.toList());
        block.endpos = (tree.body instanceof JCBlock) ? ((JCBlock)tree.body).endpos : tree.body.pos;
        
        JCForLoop forstatement = factory.ForLoop(List.<JCStatement>nil(),cond,step.toList(),block);
        JmlForLoop jmlforstatement = factory.JmlForLoop(forstatement,tree.loopSpecs);
        {
            ListBuffer<JmlStatementLoop> list = new ListBuffer<JmlStatementLoop>();
            list.appendList(tree.loopSpecs);
            if (inv != null) list.append(inv);
            list.append(inv2);
            jmlforstatement.loopSpecs = list.toList();
        }
        stats.append(jmlforstatement);

        JCBlock blockk = factory.Block(0,stats.toList());
        blockk.endpos = block.endpos;
        tree.implementation = blockk;
        
//        tree.var = translate(tree.var);
//        tree.expr = translate(tree.expr);
//        tree.body = translate(tree.body);
//        result = tree;
    }

    // MAINTENANCE ISSUE: code duplicated mostly from the superclass

    public void visitJmlForLoop(JmlForLoop tree) {
        Env<AttrContext> loopEnv =
            env.dup(env.tree, env.info.dup(env.info.scope.dup()));
        savedSpecOK = true;
        attribStats(tree.init, loopEnv);
        if (tree.cond != null) attribExpr(tree.cond, loopEnv, syms.booleanType);
        loopEnv.tree = tree; // before, we were not in loop!

        attribLoopSpecs(tree.loopSpecs, loopEnv);
        // FIXME - should this be before or after the preceding statement

        attribStats(tree.step, loopEnv);
        attribStat(tree.body, loopEnv);
        loopEnv.info.scope.leave();
        result = null;
    }

    public void visitJmlWhileLoop(JmlWhileLoop that) {
        attribLoopSpecs(that.loopSpecs,env);
        super.visitWhileLoop(that);
    }

    public void visitJmlStatementLoop(JmlStatementLoop that) {
        attribExpr(that.expression,env);
    }

    public void visitJmlClassDecl(JmlClassDecl that) {
        visitClassDef(that);
        // the work of attributing the specs is done in JmlAttr.attribClass
        // through attribClassBodySpecs - FIXME - not right
    }

    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        visitTopLevel(that);
    }

    public void visitJmlMethodDecl(JmlMethodDecl that) {
        visitMethodDef(that);
    }

    public void visitJmlVariableDecl(JmlVariableDecl that) {
        visitVarDef(that);
    }

}
