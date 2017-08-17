/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.comp;

import static com.sun.tools.javac.code.Flags.ABSTRACT;
import static com.sun.tools.javac.code.Flags.BLOCK;
import static com.sun.tools.javac.code.Flags.INTERFACE;
import static com.sun.tools.javac.code.Flags.NATIVE;
import static com.sun.tools.javac.code.Flags.STATIC;
import static com.sun.tools.javac.code.Flags.STRICTFP;
import static com.sun.tools.javac.code.Flags.SYNTHETIC;
import static com.sun.tools.javac.code.Flags.UNATTRIBUTED;
import static com.sun.tools.javac.code.Kinds.MTH;
import static com.sun.tools.javac.code.Kinds.TYP;
import static com.sun.tools.javac.code.Kinds.VAL;
import static com.sun.tools.javac.code.Kinds.VAR;
import static com.sun.tools.javac.code.TypeTag.FORALL;
import static com.sun.tools.javac.code.TypeTag.METHOD;
import static com.sun.tools.javac.code.TypeTag.NONE;
import static com.sun.tools.javac.tree.JCTree.Tag.ASSIGN;
import static org.jmlspecs.openjml.JmlTokenKind.*;

import java.util.Collection;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import javax.lang.model.type.TypeKind;
import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlSpecs.MethodSpecs;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlAnnotation;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlBlock;
import org.jmlspecs.openjml.JmlTree.JmlChoose;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlDoWhileLoop;
import org.jmlspecs.openjml.JmlTree.JmlEnhancedForLoop;
import org.jmlspecs.openjml.JmlTree.JmlExpression;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlImport;
import org.jmlspecs.openjml.JmlTree.JmlLabeledStatement;
import org.jmlspecs.openjml.JmlTree.JmlLblExpression;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseCallable;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignals;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignalsOnly;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlMethodSig;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlModelProgramStatement;
import org.jmlspecs.openjml.JmlTree.JmlPrimitiveTypeTree;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlSetComprehension;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlStatementLoop;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefArrayRange;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefKeyword;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefListExpression;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConstraint;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseIn;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMaps;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMonitorsFor;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTree.JmlWhileLoop;

import com.sun.source.tree.IdentifierTree;
import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Attribute.Compound;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.CompletionFailure;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.comp.Attr.ResultInfo;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.ExpressionExtension;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.JmlTokenizer;
import com.sun.tools.javac.tree.EndPosTable;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;

import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Pair;
import com.sun.tools.javac.util.Position;

/**
 * This class is an extension of the Attr class; it adds visitors methods so
 * that as the Attr class walks the entire AST, attributing all nodes 
 * (i.e., doing name lookup and type assignment), the JML parts of the source tree are
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
 * e) set the value of result to the resulting type (if it is needed
 * by the containing expression).
 * 
 * This design appears to involve a lot of extra work.  Instead of
 * having the attrib calls pass in an expected type, which is set as
 * a member of the Attr class, why not just check it upon return?
 * That would save the stacking that is necessary in attribTree.
 */
public class JmlAttr extends Attr implements IJmlVisitor {

    /** This is the compilation context for which this is the unique instance */
    @NonNull final protected Context context;
    
    /** The Name version of resultVarString in the current context */
    @NonNull final public Name resultName;
    
    /** The Name version of exceptionVarString in the current context */
    @NonNull final public Name exceptionName;

    /** The fully-qualified name of the Utils class */
    // Use .class on the class name instead of a string so that an error happens if the class is renamed
    // This class is in the runtime library
    @NonNull final public static String utilsClassName = org.jmlspecs.utils.Utils.class.getCanonicalName();
    
    /** Cached value of the org.jmlspecs.utils.Utils class */
    @NonNull final protected ClassSymbol utilsClass;
    
    /** Cached identifier of the org.jmlspecs.utils.Utils class */
    @NonNull final protected JCIdent utilsClassIdent;
    
    /** Cached value of the JMLDataGroup class */
    @NonNull final protected ClassSymbol datagroupClass;
    
    /** The JmlSpecs instance for this context */
    @NonNull final protected JmlSpecs specs;
    
    /** The Utils instance for this context */
    @NonNull final protected Utils utils;

    /** The Types instance for this context */
    @NonNull final public JmlTypes jmltypes;

    /** The Names table from the compilation context, initialized in the constructor */
    @NonNull final protected Names names;
    
    /** The tool used to read binary classes */
    @NonNull final protected ClassReader classReader;
    
    /** The factory used to create AST nodes, initialized in the constructor */
    /*@ non_null */ final protected JmlTree.Maker factory;
    
    /** A JmlCompiler instance */
    @NonNull final protected JmlCompiler jmlcompiler;
    
    /** A JmlResolve instance */
    @NonNull final protected JmlResolve jmlresolve;
    
    /** An instance of the tree utility class */
    @NonNull final protected JmlTreeUtils treeutils;

    /** A Literal for a boolean true */
    @NonNull final protected JCLiteral trueLit;
    
    /** A Literal for a boolean false */
    @NonNull final protected JCLiteral falseLit;
    
    /** A Literal for a null constant */
    @NonNull final protected JCLiteral nullLit;
    
    /** A Literal for an int zero */
    @NonNull final protected JCLiteral zeroLit;
    
    /** Cached value of the @Model annotation symbol */
    public ClassSymbol modelAnnotationSymbol = null;
    /** Cached value of the @Pure annotation symbol */
    public ClassSymbol pureAnnotationSymbol = null;
    /** Cached value of the @NonNull annotation symbol */
    public ClassSymbol nonnullAnnotationSymbol = null;
    /** Cached value of the @Nullable annotation symbol */
    public ClassSymbol nullableAnnotationSymbol = null;
    /** Cached value of the @NonNullByDefault annotation symbol */
    public ClassSymbol nonnullbydefaultAnnotationSymbol = null;
    /** Cached value of the @NullableByDefault annotation symbol */
    public ClassSymbol nullablebydefaultAnnotationSymbol = null;

    // Unfortunately we cannot increase the number of primitive
    // type tags without modifying the TypeInfo file.  These
    // type tags are out of range, so we cannot use the usual
    // initType call to initialize them.
    // FIXME - may need to revisit this for boxing and unboxing
    final public Type Lock;// = new Type(1003,null);
    final public Type LockSet;// = new Type(1004,null);
    final public Type JMLValuesType;
    final public Type JMLIterType;
    final public Type JMLSetType;
    
    // The following fields are stacked as the environment changes as one
    // visits down the tree.
    
    /** When true, we are visiting subtrees that allow only pure methods and
     * pure operations */
    protected boolean pureEnvironment = false;
    
    /** Holds the env of the enclosing method for subtrees of a MethodDecl. */
    protected Env<AttrContext> enclosingMethodEnv = null;
    
    /** Holds the env of the enclosing class for subtrees of a ClassDecl. */
    protected Env<AttrContext> enclosingClassEnv = null;
    
    /** Set to true when we are within a JML declaration */
    protected boolean isInJmlDeclaration = false;
 
    /** This field stores the clause type when a clause is visited (before 
     * visiting its components), in order that various clause-type-dependent
     * semantic tests can be performed (e.g. \result can only be used in some
     * types of clauses).
     */
    protected JmlTokenKind currentClauseType = null;
    
    /**
     * Holds the visibility of JML construct that is currently being visited.
     * Values are 0=package, Flags.PUBLIC=public, Flags.PROTECTED=protected,
     *      Flags.PRIVATE=private, -1=not in JML
     */  // FIXME - isa this Java visibility or JML visibility?
    protected long jmlVisibility = -1;
    
    /** This value is valid within a Signals clause */
    protected Type currentExceptionType = null;
    
    /** Queued up classes to be attributed */
    protected java.util.List<ClassSymbol> todo = new LinkedList<ClassSymbol>();
    
    /** A counter that indicates a level of nesting of attribClass calls */
    protected int level = 0;
    
    /** Registers a singleton factory for JmlAttr against the attrKey, so that there is
     * just one instance per context.
     * @param context the context in which to register the instance
     */
    public static void preRegister(final Context context) {
        context.put(Attr.attrKey, new Context.Factory<Attr>() {
            public Attr make(Context context) {
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
    
    /** Constructor of a JmlAttr tool for the given context
     * 
     * @param context the compilation context in which we are working
     */
    protected JmlAttr(Context context) {
        super(context);
        this.context = context;
        this.utils = Utils.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.factory = JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.classReader = ClassReader.instance(context);
        this.jmltypes = JmlTypes.instance(context);
        this.classReader.init(syms);
        this.jmlcompiler = (JmlCompiler)JmlCompiler.instance(context);
        this.jmlresolve = (JmlResolve)rs;
        this.treeutils = JmlTreeUtils.instance(context);
        
        // Caution, because of circular dependencies among constructors of the
        // various tools, it can happen that syms is not fully constructed at this
        // point and syms.objectType will be null.
        if (syms.objectType == null) {
            System.err.println("INTERNAL FAILURE: A circular dependency among constructors has caused a failure to correctly construct objects.  Please report this internal problem.");
            // Stack trace is printed inside the constructor
            throw new JmlInternalError();
        }
        initAnnotationNames(context);

        utilsClass = createClass(utilsClassName);
        utilsClassIdent = ((JmlTree.Maker)make).Ident(utilsClassName);
        utilsClassIdent.type = utilsClass.type;
        utilsClassIdent.sym = utilsClassIdent.type.tsym;

        datagroupClass = createClass(Strings.jmlSpecsPackage + ".JMLDataGroup");
        JMLSetType = createClass(Strings.jmlSpecsPackage + ".JMLSetType").type;
        JMLValuesType = createClass(Strings.jmlSpecsPackage + ".JMLList").type;
        JMLIterType = createClass("java.util.Iterator").type;
        Lock = syms.objectType;
        LockSet = JMLSetType;
        nullablebydefaultAnnotationSymbol = createClass("org.jmlspecs.annotation.NullableByDefault"); // FIXME - use defined Strings
        nonnullbydefaultAnnotationSymbol = createClass("org.jmlspecs.annotation.NonNullByDefault");
        nonnullAnnotationSymbol = createClass("org.jmlspecs.annotation.NonNull");
        nullableAnnotationSymbol = createClass("org.jmlspecs.annotation.Nullable");
        pureAnnotationSymbol = createClass("org.jmlspecs.annotation.Pure");
        modelAnnotationSymbol = createClass("org.jmlspecs.annotation.Model");

        this.resultName = names.fromString(Strings.resultVarString);
        this.exceptionName = names.fromString(Strings.exceptionVarString);
        
        trueLit = makeLit(syms.booleanType,1);
        falseLit = makeLit(syms.booleanType,0);
        nullLit = makeLit(syms.botType,null);
        zeroLit = makeLit(syms.intType,0);

    }
 
    /** Returns (creating if necessary) a class symbol for a given fully-qualified name */
    public ClassSymbol createClass(String fqName) {
        return classReader.enterClass(names.fromString(fqName));
    }
 
    /** Overrides the super class call in order to perform JML checks on class
     * modifiers.  (Actually, the work was moved to attribClassBody since attribClass
     * gets called multiple times for a Class).
     * @param c The class to check
     * @throws CompletionFailure
     */
    @Override
    public void attribClass(ClassSymbol c) throws CompletionFailure {
    	if (c.type instanceof Type.IntersectionClassType) {
    		// FIXME - what should we do in this case?
    		super.attribClass(c);
    		return;
    	}
        boolean isUnattributed =  (c.flags_field & UNATTRIBUTED) != 0;
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("Attributing-requested " + c + " specs="+(specs.get(c)!=null) + " env="+(enter.getEnv(c)!=null));
        
        // FIXME - can we make the following more efficient - this gets called a lot for classes already attributed
        /*@Nullable*/ JmlSpecs.TypeSpecs classSpecs = specs.get(c);  // Get null if there are none yet
        if (classSpecs == null) {
            jmlcompiler.loadSpecsForBinary(env,c);
            classSpecs = specs.get(c);
            if (classSpecs == null) {
                // loadSpecsForBinary should always result in a TypeSpecs for the
                // class symbol, even if the TypeSpecs is empty
                log.warning("jml.internal.notsobad","loadSpecsForBinary failed for class " + c);
                c.complete(); // At least complete it
            } 
        }

        if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("Attributing specs for " + c + " " + level);
        level++;
        if (c != syms.predefClass) {
            if (utils.jmlverbose >= Utils.JMLVERBOSE) context.get(Main.IProgressListener.class).report(0,2,"typechecking " + c);
        }

        // classSpecs.file is only useful for the modifiers/annotations
        // the specs themselves might come from any specification file
        JavaFileObject prev = classSpecs == null ? null : log.useSource(classSpecs.file);

        // We track pureEnvironment since calls can be nested -
        // we can enter a pure environment from either an impure or pure
        // environment and we need to restore it properly.  Also, when in a
        // pure environment we may need to attribute a class, not all of which
        // is pure.
        boolean prevPureEnvironment = pureEnvironment;
        pureEnvironment = false;  
        try {
            Env<AttrContext> eee = typeEnvs.get(c);
            if (eee != null) { // FIXME - is null an error? is null for annotations like SpecPublic, for example, but no attribution is needed either, since there are no spec files.
                JavaFileObject prevv = log.useSource(eee.toplevel.sourcefile);
                try {
                    super.attribClass(c); // No need to attribute the class itself if it was binary
                    attribFieldSpecs(eee,c);
                } finally {
                    log.useSource(prevv);
                }
            }
            if (!isUnattributed) return;

            // FIXME - do we still need this?
            // Binary files with specs had entries put in the Env map so that the
            // specs had environments against which to be attributed.  However, the
            // presence of envs for non-.java files confuses later compiler phases,
            // and we no longer need that mapping since all the specs are now
            // attributed and entered into the JmlSpecs database.  Hence we remove
            // the entry.
            Env<AttrContext> e = enter.getEnv(c);
            if (e != null) {  // SHould be non-null the first time, but subsequent calls will have e null and so we won't do duplicate checking
                //                // FIXME - RAC should take advantage of the same stuff as ESC
                //                if (true || !JmlOptionName.isOption(context,JmlOptionName.RAC)) {
                //                    new JmlTranslator(context).translate(e.tree);
                //                }
                
                if (e.tree != null && e.tree instanceof JmlClassDecl) {
                    Symbol thissym = thisSym(e.tree.pos(),e);
                    if (thissym instanceof VarSymbol) ((JmlClassDecl)e.tree).thisSymbol = (VarSymbol)thissym;
//                    //((JmlClassDecl)e.tree).thisSymbol = (VarSymbol)rs.resolveSelf(e.tree.pos(),e,c,names._this);
//                    if (!((JmlClassDecl)e.tree).sym.isInterface() && c != syms.objectType.tsym) ((JmlClassDecl)e.tree).superSymbol = (VarSymbol)rs.resolveSelf(e.tree.pos(),e,c,names._super);
                }

                if (e.toplevel.sourcefile.getKind() != JavaFileObject.Kind.SOURCE) {
                    // If not a .java file
                    enter.typeEnvs.remove(c); // FIXME - after flow checking of model methods and classes for binary classes?
                }
            }

        } finally {
            pureEnvironment = prevPureEnvironment;
            if (prev != null) log.useSource(prev);
            level--;
            if (c != syms.predefClass) {
                if (utils.jmlverbose >= Utils.JMLVERBOSE) context.get(Main.IProgressListener.class).report(0,2,"typechecked " + c);
            }
            if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("Attributing-complete " + c.fullname + " " + level);
            if (level == 0) completeTodo();
        }
    }
    
    public void attribFieldSpecs(Env<AttrContext> env, ClassSymbol csym) {
        Env<AttrContext> prev = this.env;
        this.env = env;
        try {
            JmlClassDecl cdecl = (JmlClassDecl)env.tree;
            for (JCTree t: cdecl.defs) {
                if (t instanceof JCVariableDecl) {
                    JCVariableDecl vdecl = (JCVariableDecl)t;
                    if (vdecl.sym != null) {  // FIXME - WHY WOULD THIS SYM EVER BE NULL?
                        FieldSpecs fspecs = specs.getSpecs(vdecl.sym);
                        if (fspecs != null) {
                            for (JmlTypeClause spec:  fspecs.list) {
                                if (spec instanceof JmlTypeClauseIn) spec.accept(this);
                                if (spec instanceof JmlTypeClauseMaps) spec.accept(this);
                            }
                        }
                    }
                }
            }
        } finally {
            this.env = prev;
        }
    }
    
    /** Attribute all classes whose attribution was deferred (while in the middle of attributing another class) */
    public void completeTodo() {
        level++;
        while (!todo.isEmpty()) {
            ClassSymbol sym = todo.remove(0);
            if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("Retrieved for attribution " + sym + " " + todo.size());
            attribClass(sym);
        }
        level--;
    }
    
    /** Adds a class symbol to the list of classes to be attributed later */
    public void addTodo(ClassSymbol c) {
        if (!todo.contains(c)) {
            if (!utils.isTypeChecked(c)) todo.add(c);
            if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("Queueing for attribution " + result.tsym + " " + todo.size());
        }
    }
    
    /** Overrides in order to attribute class specs appropriately. */
    @Override
    protected void attribClassBody(Env<AttrContext> env, ClassSymbol c) {
        Env<AttrContext> prevClassEnv = enclosingClassEnv;
        enclosingClassEnv = env;

        // FIXME - for a binary class c, env.tree appears to be the tree of the specs
        // FIXME - why should we attribute the Java class body in the case of a binary class
        
        boolean prevIsInJmlDeclaration = isInJmlDeclaration;
        isInJmlDeclaration = isInJmlDeclaration || utils.isJML(c.flags());  // REMOVED implementationAllowed ||
        ((JmlCheck)chk).setInJml(isInJmlDeclaration);
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("ATTRIBUTING-BODY " + c.fullname + " " + (isInJmlDeclaration?"inJML":"notInJML") + " WAS " + (prevIsInJmlDeclaration?"inJML":"notInJML"));
//        JavaFileObject prev = log.useSource(((JmlClassDecl)env.enclClass).toplevel.sourcefile);  // FIXME - no write for multiple source files
        boolean oldRelax = relax;
        try {
            // If the class is binary only, then we have not yet attributed the super/extending/implementing classes in the source AST for the specifications
            
            JmlClassDecl cd = (JmlClassDecl)env.tree;
            {
                JCExpression e = cd.extending;
                if (e != null && e.type == null) attribType(e,env);
            }
            if (cd != null) for (JCExpression e: cd.implementing) {
                if (e.type == null) attribType(e,env);
            }
            
            
            // The JML specs to check are are in the TypeSpecs structure

            relax = true;  // Turns off some bogus lack of overriding warnings
            super.attribClassBody(env,c);
            attribClassBodySpecs(env,c,prevIsInJmlDeclaration);
        
        } finally {
            relax = oldRelax;
            isInJmlDeclaration = prevIsInJmlDeclaration;
            enclosingClassEnv = prevClassEnv;
            ((JmlCheck)chk).setInJml(isInJmlDeclaration);
//            log.useSource(prev);
        }
    }
    
    // FIXME - do not need this is we can avoid having invariants in the class body
    @Override
    public Type attribStat(JCTree tree, Env<AttrContext> env) {
        if (tree instanceof JmlTypeClause && relax) return null;
        return super.attribStat(tree,env);
    }

    
    /** Attributes the specs (in the TypeSpecs structure) for the given class
     * 
     * @param env the current class environment
     * @param c the current class
     * @param prevIsInJmlDeclaration true if we are in a non-model JML declaration  (FIXME - this needs better evaluation)
     */
    public void attribClassBodySpecs(Env<AttrContext> env, ClassSymbol c, boolean prevIsInJmlDeclaration) {
        JmlSpecs.TypeSpecs tspecs = JmlSpecs.instance(context).get(c);
        JmlClassDecl classDecl = (JmlClassDecl)env.tree;
        JavaFileObject prev = log.currentSourceFile();
        
//        if (c.flatName().toString().equals("java.lang.Throwable")) Utils.stop();
        
        // This is not recursive within a class, but we can call out to attribute 
        // another class while in the middle of a clause
        JmlTokenKind prevClauseType = currentClauseType;
        
        try {
            if (tspecs != null) {
                Env<AttrContext> prevEnv = this.env;
                this.env = env;

                // The modifiers and annotations are checked in checkClassMods
                // which is part of checking the class itself

                // clauses and declarations
                for (JmlTypeClause clause: tspecs.clauses) {
                    currentClauseType = clause.token;
                    clause.accept(this);
                }
                currentClauseType = null;

                // model types, which are not in clauses

//                for (JmlClassDecl mtype: tspecs.modelTypes) {
//                    mtype.accept(this);
//                }

                //            // Do the specs for JML initialization blocks // FIXME - test the need for this - for initializatino blocks and JML initializations
                //            for (JCTree.JCBlock m: tspecs.blocks.keySet()) {
                //                m.accept(this);
                //            }


                if (tspecs.modifiers != null) {
                    log.useSource(tspecs.file);
                    attribAnnotationTypes(tspecs.modifiers.annotations,env);
                    isInJmlDeclaration = prevIsInJmlDeclaration;
                    ((JmlCheck)chk).setInJml(isInJmlDeclaration);
                    if (tspecs.file != null) log.useSource(tspecs.file);
                    checkClassMods(c,classDecl,tspecs);
                } else {
//                    log.warning("jml.internal.notsobad","Unexpected lack of modifiers in class specs structure for " + c); // FIXME - testJML2
                }
                
                // Checking all the in and maps clauses is delayed until all the fields have been processed 

                for (JCTree t: classDecl.defs) {
                    if (t instanceof JmlVariableDecl) {
                        checkVarMods2((JmlVariableDecl)t);
                    }
                }

                this.env = prevEnv;
            } else if (c.type instanceof Type.IntersectionClassType){
            	// FIXME - what should really be done here
            } else {
                log.warning("jml.internal.notsobad","Unexpected lack of class specs structure for " + c);
            }
        } finally {
            currentClauseType = prevClauseType;
            log.useSource(prev);
        }
    }
    
    public Env<AttrContext> localEnv(Env<AttrContext> env, JCTree tree) {
        return env.dup(tree, env.info.dup(env.info.scope.dupUnshared()));
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
            JmlSpecs.MethodSpecs msp = JmlSpecs.instance(context).getSpecs(env.enclClass.sym,tree);
            //if (attribSpecs && sp != null) {
            if (msp != null) {
                JmlMethodSpecs sp = msp.cases;
                Env<AttrContext> localEnv = localEnv(env,tree);
                localEnv.info.scope.owner =
                    new MethodSymbol(tree.flags | BLOCK, names.empty, null,
                                     env.info.scope.owner);
                if (isStatic(tree.flags)) localEnv.info.staticLevel++;
                //boolean prev = attribSpecs;
                //attribSpecs = true;
                attribStat(sp,localEnv);
                //attribSpecs = prev;
            }
        } else {
            // Method blocks
            
            boolean topMethodBodyBlock = env.enclMethod != null &&
                                            env.enclMethod.body == tree;
            if (topMethodBodyBlock) {
                // Scope is not duplicated
                enclosingMethodEnv = env.dup(env.tree,env.info.dupUnshared());
            }
            super.visitBlock(tree);
            //if (!isStatic(env.enclMethod.mods.flags)) {
            if (env.info.staticLevel == 0 && topMethodBodyBlock) {
                ((JmlMethodDecl)env.enclMethod)._this = (VarSymbol)thisSym(tree.pos(),enclosingMethodEnv);
            }
            
            if (env.enclMethod != null &&
                    env.enclMethod.body == tree) {
                // Note: we cannot just cache the current value of env for use later.
                // This is because the envs are presumed to be nested and share their
                // symbol tables.  Access to scopes is presumed to be nested - in Java
                // a reference to an identifier is always resolved in the current scope first,
                // not in an enclosing scope.  However, JML has the \old operator which gives
                // access to the scope at method definition time from within other nestings.
                boolean prevAllowJML = jmlresolve.setAllowJML(true);
                try {
                    JmlSpecs.MethodSpecs sp = ((JmlMethodDecl)env.enclMethod).methodSpecsCombined; //specs.getSpecs(env.enclMethod.sym);
                    currentSecretContext = sp.secretDatagroup;
                    currentQueryContext = null;
//                  if (enclosingMethodEnv == null) {
                    // FIXME - This can happen for anonymous classes, so I expect that
                    // specs (or at least \old) in anonymous classes will cause disaster
//                  log.getWriter(WriterKind.NOTICE).println("DISASTER-2 AWAITS: " + env.enclMethod.name);
//                  log.getWriter(WriterKind.NOTICE).println(env.enclMethod);
//                  }
                    if (sp != null && sp.cases != null) sp.cases.accept(this);
//                  if (enclosingMethodEnv == null) {
//                  log.getWriter(WriterKind.NOTICE).println("DODGED-2: " + env.enclMethod.name);
                    deSugarMethodSpecs(((JmlMethodDecl)env.enclMethod),sp);

//                  }
                } finally {
                    jmlresolve.setAllowJML(prevAllowJML);
                }
            }

        }
        enclosingMethodEnv = prevEnclosingMethodEnv;
    }
    
    @Override
    public void visitUnary(JCUnary tree) {
        super.visitUnary(tree);
        if (pureEnvironment) {
            // FIXME - this and the next two happen in pure model methods - should probably treat them as pure methods and not pureEnvironments
            if (tree.arg instanceof JCIdent && ((JCIdent)tree.arg).sym.owner.kind == Kinds.MTH) return;
            JCTree.Tag op = tree.getTag();
            if (op == JCTree.Tag.PREINC || op == JCTree.Tag.POSTINC ||
                    op == JCTree.Tag.PREDEC || op == JCTree.Tag.POSTDEC)
                log.error(tree.pos,"jml.no.incdec.in.pure");
        }
    }

    @Override
    public void visitAssign(JCAssign tree) {
        super.visitAssign(tree);
        if (pureEnvironment) {
            // The following checks that the assignment is local (the symbol being assigned is owned by the method)
            if (tree.lhs instanceof JCIdent && ((JCIdent)tree.lhs).sym.owner.kind == Kinds.MTH) return;
            log.error(tree.pos,"jml.no.assign.in.pure");
        }
        if (currentSecretContext != null) checkWritable(tree.lhs);
    }

    @Override
    public void visitAssignop(JCAssignOp tree) {
        super.visitAssignop(tree);
        if (pureEnvironment) {
            // The following checks that the assignment is local (the symbol being assigned is owned by the method)
            if (tree.lhs instanceof JCIdent && ((JCIdent)tree.lhs).sym.owner.kind == Kinds.MTH) return;
            log.error(tree.pos,"jml.no.assign.in.pure");
        }
        if (currentSecretContext != null) checkWritable(tree.lhs);
    }
    
    protected void checkWritable(JCTree lhs) {
        Type saved = result;
        Symbol s = null;

        if (lhs instanceof JCArrayAccess) {  // FIXME - shuold this be while instead of if
            lhs = ((JCArrayAccess)lhs).indexed;
        }
        if (lhs instanceof JCIdent) {
            if ((s=((JCIdent)lhs).sym) instanceof VarSymbol) checkSecretWritable(lhs.pos(),(VarSymbol)s);
            // FIXME - else not writable?
        } else if (lhs instanceof JCFieldAccess) {
            if ((s=((JCFieldAccess)lhs).sym) instanceof VarSymbol) checkSecretWritable(lhs.pos(),(VarSymbol)s);
            // FIXME - else not writable?
        }
        if (s == null || (!(s instanceof VarSymbol) && !(lhs instanceof JmlSingleton))) {
            log.error(lhs.pos(),"jml.not.writable.in.secret");  // FIXME - see what relaxed rules we can support; rely on assignable?
        }
        
        result = saved;
    }

    
    public JmlTokenKind[] allowedTypeModifiers = new JmlTokenKind[]{
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        OPTIONS, PURE, MODEL, QUERY, SKIP_RAC, NULLABLE_BY_DEFAULT, NON_NULL_BY_DEFAULT, IMMUTABLE};

    public JmlTokenKind[] allowedNestedTypeModifiers = new JmlTokenKind[]{
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        OPTIONS, PURE, MODEL, QUERY, SPEC_PUBLIC, SPEC_PROTECTED, NULLABLE_BY_DEFAULT, NON_NULL_BY_DEFAULT, IMMUTABLE};

    public JmlTokenKind[] allowedNestedModelTypeModifiers = new JmlTokenKind[]{
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        OPTIONS, PURE, MODEL, QUERY, NULLABLE_BY_DEFAULT, NON_NULL_BY_DEFAULT, IMMUTABLE};

    public JmlTokenKind[] allowedLocalTypeModifiers = new JmlTokenKind[]{
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        OPTIONS, PURE, MODEL, QUERY, IMMUTABLE};

    /** Checks the JML modifiers so that only permitted combinations are present. */
    public void checkClassMods(ClassSymbol classSymbol, /*@ nullable */ JmlClassDecl javaDecl, TypeSpecs tspecs) {
        //System.out.println("Checking " + javaDecl.name + " in " + owner);
        checkTypeMatch(classSymbol, tspecs.decl);
        Symbol owner = classSymbol.owner;
        JCModifiers specsModifiers = tspecs.modifiers;
        JmlClassDecl specsDecl = tspecs.decl;

        boolean inJML = utils.isJML(specsModifiers);
        JCAnnotation model = findMod(specsModifiers,JmlTokenKind.MODEL);
        boolean isModel = model != null;
        if (specsModifiers == null) {
            // no annotations to check
        } else if (owner.kind == Kinds.PCK) {  // Top level type declaration
            allAllowed(specsModifiers.annotations,allowedTypeModifiers,"type declaration");
        } else if (owner.kind != Kinds.TYP) { // Local
            allAllowed(specsModifiers.annotations,allowedLocalTypeModifiers,"local type declaration");
        } else if (!isModel) { // Nested/inner type declaration
            allAllowed(specsModifiers.annotations,allowedNestedTypeModifiers,"nested type declaration");
        } else { // Nested model type declaration
            allAllowed(specsModifiers.annotations,allowedNestedModelTypeModifiers,"nested model type declaration");
        }
        if (isInJmlDeclaration && isModel) {
            log.error(specsDecl,"jml.no.nested.model.type");
        } else if (inJML && !isModel && !isInJmlDeclaration) {
            log.error(specsDecl,"jml.missing.model");
        } else if (!inJML && isModel) {
            log.error(specsDecl,"jml.ghost.model.on.java");
        } 

        if (!isModel) {
            checkForConflict(specsModifiers,SPEC_PUBLIC,SPEC_PROTECTED);
            checkForRedundantSpecMod(specsModifiers);
        }
        checkForConflict(specsModifiers,NON_NULL_BY_DEFAULT,NULLABLE_BY_DEFAULT);
        checkForConflict(specsModifiers,PURE,QUERY);
        {
         // FIXME - this attribution should be done in the Enter or MemberEnter phase?
            attribAnnotationTypes(specsModifiers.annotations,env); 
            JavaFileObject prev = log.useSource(tspecs.file);
            if (javaDecl != null) {
                checkSameAnnotations(javaDecl.mods,specsModifiers,"class",classSymbol.toString()); 
            } else {
                long flags = classSymbol.flags();
                JCModifiers m = factory.Modifiers(flags, null); // FIXME - should check annotations
                checkSameAnnotations(m,specsModifiers,"class",classSymbol.toString()); 
            }
            log.useSource(prev);
        }
    }
    
    //public void checkTypeMatch(JmlClassDecl javaDecl, JmlClassDecl specsClassDecl) {
        public void checkTypeMatch(ClassSymbol javaClassSym, JmlClassDecl specsClassDecl) {
        
        //ClassSymbol javaClassSym = javaDecl.sym;
        JmlSpecs.TypeSpecs combinedTypeSpecs = specs.get(javaClassSym);
        
        // If these are the same declaration we don't need to check 
        // that the spec decl matches the java decl
        //if (javaDecl == specsClassDecl) return;

        // Check annotations
        
        
        // Check that every specification class declaration (e.g. class decl in a .jml file) has
        // Java modifiers that match the modifiers in the Java soursce or class file.
        JmlClassDecl specsDecl = combinedTypeSpecs.refiningSpecDecls;
        if (specsDecl != null) {
            // FIXME - no way to skip the loop if the specsDecl is the javaDecl
            
            // Check that modifiers are the same
            long matchf = javaClassSym.flags();
            long specf = specsDecl.mods.flags;
            long diffs = (matchf ^ specf)&Flags.ClassFlags; // Includes whether both are class or both are interface
            if (diffs != 0) {
                boolean isInterface = (matchf & Flags.INTERFACE) != 0;
                boolean isEnum = (matchf & Flags.ENUM) != 0;
                if ((Flags.ABSTRACT & matchf & ~specf) != 0 && (isInterface||isEnum)) diffs &= ~Flags.ABSTRACT; // FIXME - why for enum?
                if ((Flags.STATIC & matchf & ~specf) != 0 && isEnum) diffs &= ~Flags.STATIC; 
                if ((Flags.FINAL & matchf & ~specf) != 0 && isEnum) diffs &= ~Flags.FINAL; 
                if ((Flags.FINAL & matchf & ~specf) != 0 && javaClassSym.name.isEmpty()) diffs &= ~Flags.FINAL; // Anonymous classes are implicitly final
                if (diffs != 0) {
                    //JavaFileObject prev = log.useSource(specsClassDecl.source());
                    Log.instance(context).error(specsDecl.pos(),"jml.mismatched.modifiers", specsClassDecl.name, javaClassSym.fullname, Flags.toString(diffs));  // FIXME - test this
                    //log.useSource(prev);
                }
                // FIXME - how can we tell where in which specs file the mismatched modifiers are
                // SHould probably check this in the combining step
            }
            // FIXME - this is needed, but it is using the environment from the java class, not the 
            // spec class, and so it is using the import statements in the .java file, not those in the .jml file
            attribAnnotationTypes(specsClassDecl.mods.annotations, Enter.instance(context).typeEnvs.get(javaClassSym));  // FIXME - this is done later; is it needed here?

            //checkSameAnnotations(javaDecl.mods,specsClassDecl.mods);
            // FIXME - check that both are Enum; check that both are Annotation
        }
        if (combinedTypeSpecs.file == null || combinedTypeSpecs.file.getKind() == JavaFileObject.Kind.SOURCE){
            // This is already checked in enterTypeParametersForBinary (for binary classes)
            List<Type> t = ((Type.ClassType)javaClassSym.type).getTypeArguments();
            if (specsClassDecl != null) { // FIXME
            List<JCTypeParameter> specTypes = specsClassDecl.typarams;
            if (t.size() != specTypes.size()) {
                Log.instance(context).error(specsClassDecl.pos(),"jml.mismatched.type.arguments",javaClassSym.fullname,javaClassSym.type.toString());
            }
            // FIXME - check that the names and bounds are the same
            }
        }
    }
    
        // FIXME - this should be done in MemberEnter, not here -- needed for JmlVariableDecl, checking class mods
    protected boolean checkSameAnnotations(JCModifiers javaMods, JCModifiers specMods, String kind, String name) {
        //if (javaMods == specMods) return true;
        boolean saved1 = JmlPretty.useFullAnnotationTypeName, saved2 = JmlPretty.useJmlModifier;
        JmlPretty.useFullAnnotationTypeName = JmlPretty.useJmlModifier = false;
        PackageSymbol p = annotationPackageSymbol;
        boolean r = false;
        for (JCAnnotation a: javaMods.getAnnotations()) {
            // if sourcefile is null, the annotation was inserted to make an implicit annotation explicit; we don't complain about those, as the default may be superseded by a different explicit annotation
            TypeSymbol tsym = a.annotationType.type.tsym;
            if (((JmlTree.JmlAnnotation)a).sourcefile != null && tsym.owner.equals(p) && utils.findMod(specMods,tsym) == null) {
                JavaFileObject prev = log.useSource(((JmlTree.JmlAnnotation)a).sourcefile);
                log.warning(a.pos,"jml.java.annotation.superseded",kind,name,a); 
                log.useSource(prev);
                r = true;
            }
        }
        JmlPretty.useFullAnnotationTypeName = saved1; JmlPretty.useJmlModifier = saved2;
        return r;
    }


    
    VarSymbol currentSecretContext = null;
    VarSymbol currentQueryContext = null;
    
    boolean implementationAllowed = false;
    
    @Override
    protected boolean okAsEnum(Type clazztype) {
    	return !(isInJmlDeclaration && (clazztype.tsym.flags_field&Flags.ENUM) != 0);
    }

    @Override
    public void visitNewClass(JCNewClass tree) {
        boolean prev = implementationAllowed;
        boolean prevJml = isInJmlDeclaration;
        isInJmlDeclaration = true;  // FIXME - why is this true
        try {
            implementationAllowed= true;
            super.visitNewClass(tree);
            if (pureEnvironment) {
                Symbol sym = tree.constructor;
                MethodSymbol msym = null;
                if (sym instanceof MethodSymbol) msym = (MethodSymbol)sym;
                boolean isPure = msym == null || isPureMethod(msym);
                if (!isPure && JmlOption.isOption(context,JmlOption.PURITYCHECK)) {
                    log.warning(tree.pos,"jml.non.pure.method",utils.qualifiedMethodSig(msym));
                }
            }
            Type saved = result;
            TypeSymbol tsym = tree.clazz.type.tsym;
            if (tsym instanceof ClassSymbol) {
                isInJmlDeclaration = false;
                attribClass((ClassSymbol)tsym); // FIXME - perhaps this needs to be checked when specs are retrieved
            }
            result = saved;
        } finally {
            implementationAllowed = prev;
            isInJmlDeclaration = prevJml;
        }
    }
    
    @Override 
    public void visitReference(JCMemberReference that) {
        super.visitReference(that);
        if (that.sym == null) {
            for (Symbol s: that.expr.type.tsym.getEnclosedElements()) {
                if (s.name == that.name) {
                    that.sym = s;
                    that.type = s.type;
                    break;
                }
            }
        }
    }
    
    @Override
    protected boolean visitReferenceInJML() { 
        return currentClauseType != null;  // Returns true if in JML clause 
    }

    
    /** This is overridden in order to do correct checking of whether a method body is
     * present or not.
     */
    @Override 
    public void visitMethodDef(JCMethodDecl m) {
//        if (m.name.toString().equals("nonNullCheck") ){//&& m.sym.owner.toString().equals("java.lang.Object")) {
//            log.getWriter(WriterKind.NOTICE).println(m.sym.owner + ":" + m.sym);
//        }
        // Setting relax to true keeps super.visitMethodDef from complaining
        // that a method declaration in a spec file does not have a body
        // FIXME - what else is relaxed?  We should do the check under the right conditions?
        if (m.sym == null) return; // Guards against specification method declarations that are not matched - FIXME

        JmlMethodDecl jmethod = (JmlMethodDecl)m;
        Map<Name,Env<AttrContext>> prevLabelEnvs = labelEnvs;
        labelEnvs = new HashMap<Name,Env<AttrContext>>();


        boolean oldrelax = relax;
        relax = true;
        VarSymbol previousSecretContext = currentSecretContext;
        VarSymbol previousQueryContext = currentQueryContext;
        JavaFileObject prevSource = null;
        try {
            if (jmethod.methodSpecsCombined == null) {
                //log.getWriter(WriterKind.NOTICE).println("METHOD SPECS NOT COMBINED " + m.sym.owner + " " + m.sym);
                        // The following line does happen with anonymous classes implementing an interface, with no constructor given
                        // but what about FINISHING SPEC CLASS
                
                // FIXME: this also causes the Java file's specs to be used when the specs AST has been set to null
                jmethod.methodSpecsCombined = new JmlSpecs.MethodSpecs(jmethod); // BUG recovery?  FIXME - i think this happens with default constructors
                specs.putSpecs(m.sym,jmethod.methodSpecsCombined);
            }

            // Do this before we walk the method body
            determineQueryAndSecret(jmethod,jmethod.methodSpecsCombined);

            if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("ATTRIBUTING METHOD " + env.enclClass.sym + " " + m.sym);
            prevSource = log.useSource(jmethod.source());
            attribAnnotationTypes(m.mods.annotations,env); // This is needed at least for the spec files of binary classes
            annotate.flush();
            for (JCAnnotation a : m.mods.annotations) a.type = a.annotationType.type;  // It seems we need this, but it seems this should happen while walking the tree - FIXME
            
            JmlSpecs.MethodSpecs mspecs = specs.getSpecs(m.sym);
            if (mspecs != null) { // FIXME - is mspecs allowed to be null?
                currentSecretContext = mspecs.secretDatagroup;
                currentQueryContext = mspecs.queryDatagroup;
                if (currentQueryContext != null) currentSecretContext = currentQueryContext;
            }

            boolean prevRelax = relax;
            // FIXME - need a better test than this
            // Set relax to true if this method declaration is allowed to have no body
            // because it is a model declaration or it is in a specification file.
            boolean isJavaFile = jmethod.sourcefile != null && jmethod.sourcefile.getKind() == JavaFileObject.Kind.SOURCE;
            boolean isJmlDecl = utils.isJML(m.mods);
            relax = isJmlDecl || !isJavaFile;
            boolean prevAllowJML = jmlresolve.allowJML();
            if (isJmlDecl) prevAllowJML = jmlresolve.setAllowJML(true);
//            boolean prevChk = ((JmlCheck)chk).noDuplicateWarn;
//            ((JmlCheck)chk).noDuplicateWarn = false;
            super.visitMethodDef(m);
//            ((JmlCheck)chk).noDuplicateWarn = prevChk;
            if (isJmlDecl) jmlresolve.setAllowJML(prevAllowJML);
            relax = prevRelax;
            if (jmethod.methodSpecsCombined != null) { // FIXME - should we get the specs to check from JmlSpecs?
                if (m.body == null) {
                    currentSecretContext = mspecs.secretDatagroup;
                    currentQueryContext = null;
                    checkMethodSpecsDirectly(jmethod);
                }
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
            currentSecretContext = previousSecretContext;
            currentQueryContext = previousQueryContext;
            relax = oldrelax;
            if (prevSource != null) log.useSource(prevSource);
            labelEnvs.clear();
            labelEnvs = prevLabelEnvs;
        }
    }
    
    /** The annotations allowed on non-model non-constructor methods */
    public final JmlTokenKind[] allowedMethodAnnotations =
        new JmlTokenKind[] {
        MODEL, PURE, NONNULL, NULLABLE, OPTIONS, SPEC_PUBLIC, SPEC_PROTECTED, HELPER, EXTRACT, QUERY, SECRET, FUNCTION,
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        PEER, REP, READONLY, SKIP_ESC, SKIP_RAC, INLINE // FIXME - allowing these until the rules are really implemented

    };
    
    /** The annotations allowed on non-model non-constructor methods in interfaces */
    public final JmlTokenKind[] allowedInterfaceMethodAnnotations =
        new JmlTokenKind[] {
        MODEL, PURE, NONNULL, NULLABLE, OPTIONS, SPEC_PUBLIC, SPEC_PROTECTED, HELPER, QUERY, FUNCTION,
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        PEER, REP, READONLY // FIXME - allowing these until the rules are really implemented

    };
    
    /** The annotations allowed on model non-constructor methods */
    public final JmlTokenKind[] allowedModelMethodAnnotations =
        new JmlTokenKind[] {
        MODEL, PURE, NONNULL, NULLABLE, OPTIONS, HELPER, EXTRACT, QUERY, SECRET, FUNCTION,
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        PEER, REP, READONLY, SKIP_ESC, INLINE // FIXME - allowing these until the rules are really implemented

    };
    
    /** The annotations allowed on model non-constructor interface methods */
    public final JmlTokenKind[] allowedInterfaceModelMethodAnnotations =
        new JmlTokenKind[] {
        MODEL, PURE, NONNULL, NULLABLE, OPTIONS, HELPER, QUERY, SECRET, FUNCTION,
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        PEER, REP, READONLY // FIXME - allowing these until the rules are really implemented

    };
    
    /** The annotations allowed on non-model constructors */
    public final JmlTokenKind[] allowedConstructorAnnotations =
        new JmlTokenKind[] {
        MODEL, PURE, SPEC_PUBLIC, SPEC_PROTECTED, HELPER, EXTRACT,
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        PEER, REP, READONLY, OPTIONS, SKIP_ESC // FIXME - allowing these until the rules are really implemented

    };
    
    /** The annotations allowed on model constructors */
    public final  JmlTokenKind[] allowedModelConstructorAnnotations =
        new JmlTokenKind[] {
        MODEL, PURE, HELPER, EXTRACT ,
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        OPTIONS, PEER, REP, READONLY, INLINE // FIXME - allowing these until the rules are really implemented

    };
    
    /** Does the various checks of method/constructor modifiers */
    public void checkMethodModifiers(JmlMethodDecl javaMethodTree) {
        if ((javaMethodTree.sym.flags() & SYNTHETIC) != 0) return;
        JavaFileObject prev = log.currentSourceFile();
        try {
            JmlSpecs.MethodSpecs mspecs = specs.getSpecs(javaMethodTree.sym); //javaMethodTree.methodSpecsCombined;

            JCModifiers mods = mspecs.mods;
            boolean inJML = utils.isJML(mods);
            boolean classIsModel = isModel(javaMethodTree.sym.owner);
            boolean model = isModel(mods);
            boolean synthetic = mods != null && (mods.flags & Flags.SYNTHETIC) != 0;
            boolean anon = javaMethodTree.sym.owner.isAnonymous();
            boolean isConstructor = javaMethodTree.getReturnType() == null;
            if (classIsModel && model && !synthetic) {
                log.useSource(javaMethodTree.sourcefile);
                log.error(javaMethodTree.pos,"jml.no.nested.model.type");
            } else if (inJML && !model  && !isInJmlDeclaration) {
                if (!anon) {
                    log.useSource(javaMethodTree.sourcefile);
                    log.error(javaMethodTree.pos,"jml.missing.model");
                }
            } else if (!inJML && model) {
                log.useSource(javaMethodTree.sourcefile);
                log.error(javaMethodTree.pos,"jml.ghost.model.on.java");
            }
            
            // FIXME - this test is in the wrong place (NPE would happen above) and needs review inany case
            if (mods == null) mods = javaMethodTree.mods; // FIXME - this can happen for JML synthesized methods, such as are added for RAC - perhaps we should properly initialize the modifiers, but for now we just say they are OK

            // Check that any annotations are allowed and no conflicting pairs occur
            if (!isConstructor) {
                if (javaMethodTree.sym.enclClass().isInterface()) {
                    if (model) {
                        allAllowed(mods.annotations,allowedInterfaceModelMethodAnnotations,"interface model method declaration");
                    } else {
                        allAllowed(mods.annotations,allowedInterfaceMethodAnnotations,"interface method declaration");
                    }
                } else {
                    if (model) {
                        allAllowed(mods.annotations,allowedModelMethodAnnotations,"model method declaration");
                    } else {
                        allAllowed(mods.annotations,allowedMethodAnnotations,"method declaration");
                    }
                }
                checkForConflict(mods,NONNULL,NULLABLE);
                checkForConflict(mods,PURE,QUERY);
            } else { // Constructor
                if (model) {
                    allAllowed(mods.annotations,allowedModelConstructorAnnotations,"model constructor declaration");
                } else {
                    allAllowed(mods.annotations,allowedConstructorAnnotations,"constructor declaration");
                }            
            }
            
            // Check rules about Function
            JCAnnotation a=utils.findMod(mods,tokenToAnnotationSymbol.get(FUNCTION));
            if (a != null && !utils.isJMLStatic(javaMethodTree.sym)) {
                Symbol sym = javaMethodTree.sym.owner;
                if (sym instanceof ClassSymbol && !isImmutable((ClassSymbol)sym)) {
                    log.error(a.pos,"jml.function.must.have.immutable",javaMethodTree.name.toString());
                }
            }
            
            // Check rules about helper
            if ( (a=utils.findMod(mods,tokenToAnnotationSymbol.get(HELPER))) != null  &&
                    utils.findMod(mods,tokenToAnnotationSymbol.get(PURE)) == null  && 
                    (    (mods.flags & Flags.PRIVATE) == 0 
                    || utils.findMod(mods,tokenToAnnotationSymbol.get(SPEC_PUBLIC)) != null
                    || utils.findMod(mods,tokenToAnnotationSymbol.get(SPEC_PROTECTED)) != null
                            )
                    ) {
                log.useSource(((JmlTree.JmlAnnotation)a).sourcefile);
                log.error(a.pos,"jml.helper.must.be.private",javaMethodTree.name.toString());
            }
            if (!model) {
                checkForConflict(mods,SPEC_PUBLIC,SPEC_PROTECTED);
                checkForRedundantSpecMod(mods);
            }
            
            if ( (a=utils.findMod(mods,tokenToAnnotationSymbol.get(INLINE))) != null  &&
                    ((mods.flags & Flags.FINAL) == 0)  &&
                    !isConstructor
                    ) {
                log.useSource(((JmlTree.JmlAnnotation)a).sourcefile);
                log.warning(a.pos,"jml.inline.should.be.final",javaMethodTree.name.toString());
            }
        } finally {
            log.useSource(prev);
        }
    }
    
    protected void determineQueryAndSecret(JmlMethodDecl tree, JmlSpecs.MethodSpecs mspecs) {
        // Query

        // If no datagroup is named in a Query annotation, and the
        // default datagroup does not exist for the method, then a datagroup
        // is created for it.  However, if a datagroup is named in a Query annotation
        // then it is not created if it does not exist, even if it is the
        // name of the default datagroup.  The same rule applies to a 
        // Secret annotation for the method - but in some cases the Query
        // annotation will have created it, making for a bit of an anomaly.
        // TODO: clarify what the behavior should be and implement here and in the tests

        JCAnnotation query = findMod(tree.mods,JmlTokenKind.QUERY);
        VarSymbol queryDatagroup = null;
        if (query != null) {
            List<JCExpression> args = query.getArguments();
            Name datagroup = null;
            int pos = 0;
            if (args.isEmpty()) {
                // No argument - use the name of the method
                datagroup = tree.name;
                pos = query.pos;
            } else {
                datagroup = getAnnotationStringArg(query);
                pos = args.get(0).pos;
            }
            if (datagroup != null) {
                // Find the field with that name
                boolean prev = jmlresolve.setAllowJML(true);
                Symbol v = rs.findField(env,env.enclClass.type,datagroup,env.enclClass.sym);  // FIXME - test that this does not look outside the class and supertypes
                jmlresolve.setAllowJML(prev);
                if (v instanceof VarSymbol) {
                    //OK
                    queryDatagroup = (VarSymbol)v;
                    // Don't require datagroups to be model fields
                    //                  if (!isModel(v)) {
                    //                      // TODO - ideally would like this to point to the declaration of the VarSymbol - but it might not exist and we have to find it
                    //                      log.error(pos,"jml.datagroup.must.be.model");
                    //                  }
                } else if (args.size() == 0) {
                    // Create a default: public model secret JMLDataGroup
                    JmlTree.Maker maker = JmlTree.Maker.instance(context);
                    JCTree.JCModifiers nmods = maker.Modifiers(Flags.PUBLIC);
                    JCTree.JCAnnotation a = maker.Annotation(maker.Type(tokenToAnnotationSymbol.get(JmlTokenKind.MODEL).type),List.<JCExpression>nil());
                    JCTree.JCAnnotation aa = maker.Annotation(maker.Type(tokenToAnnotationSymbol.get(JmlTokenKind.SECRET).type),List.<JCExpression>nil());
                    nmods.annotations = List.<JCAnnotation>of(a,aa);
                    JCTree.JCExpression type = maker.Type(datagroupClass.type);
                    JCTree.JCVariableDecl vd = maker.VarDef(nmods,datagroup,type,null);
                    JmlMemberEnter.instance(context).memberEnter(vd,enclosingClassEnv);
                    JmlTree.JmlTypeClauseDecl td = maker.JmlTypeClauseDecl(vd);
                    utils.setJML(vd.mods);
                    vd.accept(this); // attribute it
                    queryDatagroup = vd.sym;
                    specs.getSpecs(enclosingClassEnv.enclClass.sym).clauses.append(td);
                } else {
                    log.error(pos,"jml.no.such.field",datagroup);
                }
            }
        }
        mspecs.queryDatagroup = queryDatagroup;
        // Secret
        JCAnnotation secret = findMod(tree.mods,JmlTokenKind.SECRET);
        VarSymbol secretDatagroup = null;
        if (secret != null) {
            List<JCExpression> args = secret.getArguments();
            int pos = 0;
            Name datagroup = null;
            if (args.size()!=1) {
                // No argument - error
                log.error(secret.pos(),"jml.secret.method.one.arg");
                datagroup = null;
            } else {
                // FIXME - what if the string is a qualified name?
                datagroup = getAnnotationStringArg(secret);
                pos = args.get(0).pos;
            }
            if (datagroup != null) {
                // Find the model field with that name
                boolean prev = jmlresolve.setAllowJML(true);
                Symbol v = rs.findField(env,env.enclClass.type,datagroup,env.enclClass.sym);
                jmlresolve.setAllowJML(prev);
                if (v instanceof VarSymbol) {
                    secretDatagroup = (VarSymbol)v;
                    //OK
                    //                  if (!isModel(v)) {
                    //                      // TODO - ideally would like this to point to the declaration of the VarSymbol - but it might not exist and we have to find it
                    //                      log.error(pos,"jml.datagroup.must.be.model");
                    //                  }
                } else {
                    log.error(pos,"jml.no.such.field",datagroup);
                }
            }
        }
        mspecs.secretDatagroup = secretDatagroup;
        if (queryDatagroup != null && queryDatagroup.equals(secretDatagroup)) {
            log.error(query.pos,"jml.not.both.query.and.secret");
        }    
    }
    
    public void checkMethodSpecsDirectly(JmlMethodDecl tree) {
        // Copying what is done in super.visitMethodDef to setup an environment
        // This is only done if the method body is null, otherwise, it is quicker
        // to check the method specs with the body
        
        boolean isInJml = ((JmlCheck)chk).setInJml(true);
        MethodSymbol m = tree.sym;

        Lint lint = env.info.lint.augment(m);
        Lint prevLint = chk.setLint(lint);
        MethodSymbol prevMethod = chk.setMethod(m);
        try {
            deferredLintHandler.flush(tree.pos());
            chk.checkDeprecatedAnnotation(tree.pos(), m);

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
                Env<AttrContext> prevEnv = enclosingMethodEnv;
                enclosingMethodEnv = localEnv;
                // Note: we cannot just cache the current value of env for use later.
                // This is because the envs are presumed to be nested and share their
                // symbol tables.  Access to scopes is presumed to be nested - in Java
                // a reference to an identifier is always resolved in the current scope first,
                // not in an enclosing scope.  However, JML has the \old operator which gives
                // access to the scope at method definition time from within other nestings.
                boolean prevAllowJML = jmlresolve.setAllowJML(true);
                Env<AttrContext> prevEnv2 = env;
                try {
                    env = localEnv;
                    JmlSpecs.MethodSpecs sp = tree.methodSpecsCombined; // OR specs.getSpecs(env.enclMethod.sym); if we don't have a tree - FIXME
                    if (sp != null) sp.cases.accept(this);
                    deSugarMethodSpecs(tree,tree.methodSpecsCombined);
                } finally {
                    env = prevEnv2;
                    jmlresolve.setAllowJML(prevAllowJML);
                    enclosingMethodEnv = prevEnv;
                }
            }
            localEnv.info.scope.leave();
            result = tree.type = m.type;

        }
        finally {
            ((JmlCheck)chk).setInJml(isInJml);
            chk.setLint(prevLint);
        }
    }
    
    /** Makes an attributed binary operation node
     * @param optag the kind of operation (e.g. JCTree.AND)
     * @param lhs the left-hand operand
     * @param rhs the right-hand operand
     * @param pos the soursce position of the node (e.g. of the operator)
     * @return the constructed node
     */
    protected JCExpression makeBinary(JCTree.Tag optag, JCExpression lhs, JCExpression rhs, int pos) {
        if (optag == JCTree.Tag.OR && lhs == falseLit) return rhs;
        if (optag == JCTree.Tag.AND && lhs == trueLit) return rhs;
        JCBinary tree = make.at(pos).Binary(optag, lhs, rhs);
        tree.operator = predefBinOp(optag, lhs.type);
        tree.type = tree.operator.type.getReturnType();
        return tree;
    }
    
    /** Makes an attributed JCIdent node
     * @param decl the declaration whose variable is being used in the Ident node
     * @param pos the source position at which to place the new node
     * @return the constructed node
     */
    protected JCIdent makeIdent(JCVariableDecl decl, int pos) {
        JCIdent id = make.at(pos).Ident(decl.name);
        id.sym = decl.sym;
        id.type = decl.type;
        return id;
    }

    /** Makes an attributed node representing a new variable declaration
     * such as a local declaration within the body of a method;
     * a new symbol is created, though not entered as a member in any scope;
     * the sourcefile (if it is a JmlVariableDecl) is not filled in;
     * @param name the name of the variable
     * @param type the type of the variable
     * @param init the (attributed) initialization expression or null
     * @param pos the preferred position indication
     * @return the AST node
     */
    protected JCVariableDecl makeVariableDecl(Name name, Type type, /*@Nullable*/ JCExpression init, int pos) {
        JmlTree.Maker factory = JmlTree.Maker.instance(context);
        VarSymbol vsym = new VarSymbol(0, name, type, null);
        vsym.pos = pos;
        JCVariableDecl decl = factory.at(pos).VarDef(vsym,init);
        return decl;
    }

    /** Make an attributed node representing a literal (no node position is set); 
     *  the value is an Integer for boolean (0=false, 1=true) or char types
     *  @param type       The literal's type.
     *  @param value      The literal's value (0/1 for boolean)
     */
    protected JCLiteral makeLit(Type type, Object value) {
        return make.Literal(type.getTag(), value).setType(type);
    }

    /** Make an attributed node representing an literal of type int
     * @param value the value of the literal
     * @param pos the equivalent source location for the node
     * @return the constructed node
     */
    protected JCLiteral makeIntLiteral(int value, int pos) {
        JmlTree.Maker factory = JmlTree.Maker.instance(context);
        JCLiteral lit = factory.at(pos).Literal(TypeTag.INT,value);
        lit.type = syms.intType;
        return lit;
    }
    

    // FIXME - is there a faster way to do this?
    /** Returns a Symbol (in the current compilation context) for the given operator
     * with the given (lhs) type
     * @param op the operator (e.g. JCTree.AND)
     * @param type the type of the lhs, for disambiguation
     * @return the method Symbol for the operation
     */
    protected Symbol predefBinOp(JCTree.Tag op, Type type) {
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
     * <BR>
     * A method specification can have
     * some preliminary clauses and then fork into multiple specification cases
     * or into the elements of a clause group.  We accumulate a prefix - a list
     * of clauses that are common to all subsequent specification cases. Then
     * we replicate the list and append the subsequent clauses to the appropriate
     * replicate. Note that the replication is shallow, so the replicates contain
     * equal object references to the common clauses.
     * @param decl the method declaration whose specs are being desugared
     * @param msp the method specs being desugared
     */
    // FIXME - base this on symbol rather than decl, but first check when all
    // the modifiers are added into the symbol
    // FIXME - check everything for position information
    public void deSugarMethodSpecs(JmlMethodDecl decl, JmlSpecs.MethodSpecs msp) {
        //log.getWriter(WriterKind.NOTICE).println("DESUGARING " + decl.sym.owner + " " + decl.sym + decl.toString());
        if (msp == null) return;
        JmlMethodSpecs methodSpecs = msp.cases;
        Env<AttrContext> prevEnv = env;
        
        Symbol owner = decl.sym.owner; 
        boolean specsCompletelyEmpty = methodSpecs.cases.isEmpty();
        
        env = enter.getEnv((ClassSymbol)decl.sym.owner);
        JCMethodDecl prevEnclMethod = env == null ? null : env.enclMethod;
        if (env != null) env.enclMethod = decl; // This is here to handle the situation when deSugarMethodSPecs
                // is called from JmlSpecs to provide on demand desugaring.  In that case we are not within
                // a tree hierarchy, so we have to set the enclosing method declaration directly.  If we were only
                // calling deSugarMethodSpecs during AST attribution, then we would not need to set env or adjust
                // env.enclMethod.
        if (env == null) env = enclosingMethodEnv;
        
        // DO a defensive check
        if (methodSpecs.decl != decl) {
            // FIXME this fails
            //log.error("jml.internal","UNEXPECTED MISMATCH when desugaring specs " + decl.sym + " " + methodSpecs.decl.sym);
        }
        
        
        JavaFileObject prevSource = log.useSource(decl.sourcefile);
        EndPosTable endPosTable = log.currentSource().getEndPosTable();

        try {
            JmlTree.Maker jmlMaker = (JmlTree.Maker)make;
            JCAnnotation pure = findMod(msp.mods,JmlTokenKind.PURE);
            if (pure == null) pure = findMod(msp.mods,JmlTokenKind.FUNCTION);
            desugaringPure = pure != null;
            if (!desugaringPure) {
                if (enclosingClassEnv != null) desugaringPure = (pure = findMod(enclosingClassEnv.enclClass.mods,JmlTokenKind.PURE)) != null;
            }

            if (specsCompletelyEmpty && !desugaringPure && !decl.sym.isConstructor()) {
                // If the local specs are completely empty, then the desugaring depends on what is inherited:
                // If the method at hand does not override anything, then we go on to add the default specs;
                // If the method at hand does override some parent methods, then we add no additional specs here
                if (utils.parents(decl.sym).size() > 1) { // The override list will always include the method itself
                    JmlMethodSpecs newspecs = jmlMaker.at(methodSpecs.pos).JmlMethodSpecs(List.<JmlTree.JmlSpecificationCase>nil());
                    newspecs.decl = methodSpecs.decl;
                    methodSpecs.deSugared = newspecs;
                    return;
                }
            }

            JCLiteral nulllit = make.Literal(TypeTag.BOT, null).setType(syms.objectType.constType(null));
            
            // A list in which to collect clauses
            ListBuffer<JmlMethodClause> clauses = new ListBuffer<JmlMethodClause>();

            // Add a precondition for each nonnull parameter
            for (JCVariableDecl p : decl.params) {
                if (p.type == null && p.sym != null) p.type = p.sym.type; // FIXME - A hack - why is p.type null - has the corresponding class not been Attributed?
                if (!p.type.isPrimitive()) {
                    JmlVariableDecl jp = (JmlVariableDecl)p;
                    boolean isNonnull = specs.isNonNull(jp); 
                    JCAnnotation nonnull = jp.specsDecl == null ? null : findMod(jp.specsDecl.mods,JmlTokenKind.NONNULL); // FIXME - this is not necessarily the correct position - could be in a .jml file
                    if (nonnull == null) nonnull = findMod(jp.mods,JmlTokenKind.NONNULL); // FIXME - this is not necessarily the correct position - could be in a .jml file
                    if (isNonnull) {
                        JCTree treeForPos = nonnull == null ? jp : nonnull;
                        int endPos = treeForPos.getEndPosition(endPosTable); 
                        JCIdent id = makeIdent(p,treeForPos.pos);
                        endPosTable.storeEnd(id, endPos);
                        JCExpression e = makeBinary(JCTree.Tag.NE,id,nulllit,treeForPos.pos);
                        endPosTable.storeEnd(e, endPos);
                        JmlMethodClauseExpr clause = jmlMaker.JmlMethodClauseExpr(JmlTokenKind.REQUIRES,e);
                        clause.pos = e.pos;
                        clause.sourcefile = decl.source(); // FIXME - should be set by where the nonnull annotation is
                        endPosTable.storeEnd(clause,endPos);
                        clauses.append(clause);
                    }
                }
            }
            
            // Add a nonnull postcondition on the return type
            JCAnnotation nonnullAnnotation = findMod(decl.mods,JmlTokenKind.NONNULL);
            int annotationPos = (nonnullAnnotation != null) ? nonnullAnnotation.getPreferredPosition() : decl.getPreferredPosition();
            int annotationEnd = (nonnullAnnotation != null) ? nonnullAnnotation.getEndPosition(endPosTable) : decl.getPreferredPosition()+1;
            // restype is null for constructors, possibly void for methods
            if (decl.restype != null && decl.restype.type.getTag() != TypeTag.VOID && !decl.restype.type.isPrimitive()) {
                boolean isNonnull = specs.isNonNull(decl.sym,decl.sym.enclClass());
                if (isNonnull) {
                    JCExpression id = jmlMaker.JmlSingleton(JmlTokenKind.BSRESULT);
                    id.type = decl.restype.type;
                    JCExpression e = makeBinary(JCTree.Tag.NE,id,nulllit,0);
                    id.pos = annotationPos;
                    e.pos = annotationPos;
                    endPosTable.storeEnd(e,annotationEnd);
                    endPosTable.storeEnd(id,annotationEnd);
                    JmlTokenKind prev = currentClauseType;
                    currentClauseType = JmlTokenKind.ENSURES;
                    attribExpr(e,env);
                    currentClauseType = prev;
                    JmlMethodClauseExpr cl = jmlMaker.at(annotationPos).JmlMethodClauseExpr(JmlTokenKind.ENSURES,e);
                    cl.sourcefile = decl.source();
                    endPosTable.storeEnd(cl,annotationEnd);
                    clauses.append(cl);
                }
            }
            
            // Add an assignable clause if the method is pure and has no assignable clause
            JmlMethodClause clp = null;
            if (desugaringPure) {
                if (decl.sym.isConstructor()) {
//                    JCIdent t = jmlMaker.Ident(names._this);
//                    t.type = decl.sym.owner.type;
//                    t.sym = decl.sym.owner;
//                    clp = jmlMaker.JmlMethodClauseStoreRef(JmlTokenKind.ASSIGNABLE,
//                            List.<JCExpression>of(jmlMaker.Select(t,(Name)null)));
                    clp = jmlMaker.JmlMethodClauseStoreRef(JmlTokenKind.ASSIGNABLE,
                            List.<JCExpression>of(jmlMaker.JmlStoreRefKeyword(JmlTokenKind.BSNOTHING)));
                    
                } else {
                    clp = jmlMaker.JmlMethodClauseStoreRef(JmlTokenKind.ASSIGNABLE,
                            List.<JCExpression>of(jmlMaker.JmlStoreRefKeyword(JmlTokenKind.BSNOTHING)));
                }
                if (pure != null) {
                    clp.pos = pure.pos;
                    endPosTable.storeEnd(clp,pure.getEndPosition(endPosTable));
                } else {
                    // This branch is defensive - should never happen
                    clp.pos = Position.NOPOS;
                    endPosTable.storeEnd(clp,Position.NOPOS);
                }
//                clauses.append(clp);
//                clp = null;
            }
            
            // We already have some implicit method spec clauses in 'clauses'
            // Desugar any specification cases
            JmlMethodSpecs newspecs;
            if (!methodSpecs.cases.isEmpty()) {
                ListBuffer<JmlSpecificationCase> allcases = new ListBuffer<JmlSpecificationCase>();
                ListBuffer<JmlSpecificationCase> allitcases = new ListBuffer<JmlSpecificationCase>();
                ListBuffer<JmlSpecificationCase> allfecases = new ListBuffer<JmlSpecificationCase>();
                for (JmlSpecificationCase c: methodSpecs.cases) {
                    ListBuffer<JmlMethodClause> cl = new ListBuffer<JmlMethodClause>();
                    cl.appendList(clauses);
                    JCModifiers mods = c.modifiers;
                    if (c.token == null) mods = decl.mods;
                    ListBuffer<JmlSpecificationCase> newcases = deNest(cl,List.<JmlSpecificationCase>of(c),null,decl,mods);
                    for (JmlSpecificationCase cs: newcases) {
                        // Note: a model program spec case has no clauses
                        if (cs.clauses != null) {
                            boolean hasAssignableClause = false;
                            boolean hasAccessibleClause = false;
                            for (JmlMethodClause clm: cs.clauses) {
                                if (clm.token == JmlTokenKind.ASSIGNABLE) { 
                                    hasAssignableClause = true; 
                                }
                                if (clm.token == JmlTokenKind.ACCESSIBLE) { 
                                    hasAccessibleClause = true; 
                                }
                            }
                            if (!hasAssignableClause && clp != null) {
                                cs.clauses = cs.clauses.append(clp);
                            }
                            if (!hasAccessibleClause) {
                                JmlMethodClause defaultClause;
                                if (decl.sym.isConstructor()) {
                                    JCIdent t = jmlMaker.Ident(names._this);
                                    t.type = decl.sym.owner.type;
                                    t.sym = decl.sym.owner;
                                    defaultClause = jmlMaker.JmlMethodClauseStoreRef(JmlTokenKind.ACCESSIBLE,
                                            List.<JCExpression>of(t,jmlMaker.Select(t,(Name)null)));
                                } else {
                                    defaultClause = jmlMaker.JmlMethodClauseStoreRef(JmlTokenKind.ACCESSIBLE,
                                            List.<JCExpression>of(jmlMaker.JmlStoreRefKeyword(JmlTokenKind.BSEVERYTHING)));
                                }
                                cs.clauses = cs.clauses.append(defaultClause);
                            }
                        }
                    }
                    allcases.appendList(newcases);
                }
                for (JmlSpecificationCase c: methodSpecs.impliesThatCases) {
                    ListBuffer<JmlMethodClause> cl = new ListBuffer<JmlMethodClause>();
                    cl.appendList(clauses);
                    JCModifiers mods = c.modifiers;
                    if (c.token == null) mods = decl.mods;
                    ListBuffer<JmlSpecificationCase> newcases = deNest(cl,List.<JmlSpecificationCase>of(c),null,decl,mods);
                    for (JmlSpecificationCase cs: newcases) {
                        // Note: a model program spec case has no clauses
                        if (cs.clauses != null) {
                            boolean hasAssignableClause = false;
                            boolean hasAccessibleClause = false;
                            for (JmlMethodClause clm: cs.clauses) {
                                if (clm.token == JmlTokenKind.ASSIGNABLE) { 
                                    hasAssignableClause = true; 
                                }
                                if (clm.token == JmlTokenKind.ACCESSIBLE) { 
                                    hasAccessibleClause = true; 
                                }
                            }
                            if (!hasAssignableClause && clp != null) {
                                cs.clauses = cs.clauses.append(clp);
                            }
                            if (!hasAccessibleClause) {
                                JmlMethodClause defaultClause;
                                if (decl.sym.isConstructor()) {
                                    JCIdent t = jmlMaker.Ident(names._this);
                                    t.type = decl.sym.owner.type;
                                    t.sym = decl.sym.owner;
                                    defaultClause = jmlMaker.JmlMethodClauseStoreRef(JmlTokenKind.ACCESSIBLE,
                                            List.<JCExpression>of(t,jmlMaker.Select(t,(Name)null)));
                                } else {
                                    defaultClause = jmlMaker.JmlMethodClauseStoreRef(JmlTokenKind.ACCESSIBLE,
                                            List.<JCExpression>of(jmlMaker.JmlStoreRefKeyword(JmlTokenKind.BSEVERYTHING)));
                                }
                                cs.clauses = cs.clauses.append(defaultClause);
                            }
                        }
                    }
                    allitcases.appendList(newcases);
                }
                for (JmlSpecificationCase c: methodSpecs.forExampleCases) {
                    ListBuffer<JmlMethodClause> cl = new ListBuffer<JmlMethodClause>();
                    cl.appendList(clauses);
                    JCModifiers mods = c.modifiers;
                    if (c.token == null) mods = decl.mods;
                    ListBuffer<JmlSpecificationCase> newcases = deNest(cl,List.<JmlSpecificationCase>of(c),null,decl,mods);
                    for (JmlSpecificationCase cs: newcases) {
                        // Note: a model program spec case has no clauses
                        if (cs.clauses != null) {
                            boolean hasAssignableClause = false;
                            boolean hasAccessibleClause = false;
                            for (JmlMethodClause clm: cs.clauses) {
                                if (clm.token == JmlTokenKind.ASSIGNABLE) { 
                                    hasAssignableClause = true; 
                                }
                                if (clm.token == JmlTokenKind.ACCESSIBLE) { 
                                    hasAccessibleClause = true; 
                                }
                            }
                            if (!hasAssignableClause && clp != null) {
                                cs.clauses = cs.clauses.append(clp);
                            }
                            if (!hasAccessibleClause) {
                                JmlMethodClause defaultClause;
                                if (decl.sym.isConstructor()) {
                                    JCIdent t = jmlMaker.Ident(names._this);
                                    t.type = decl.sym.owner.type;
                                    t.sym = decl.sym.owner;
                                    defaultClause = jmlMaker.JmlMethodClauseStoreRef(JmlTokenKind.ACCESSIBLE,
                                            List.<JCExpression>of(t,jmlMaker.Select(t,(Name)null)));
                                } else {
                                    defaultClause = jmlMaker.JmlMethodClauseStoreRef(JmlTokenKind.ACCESSIBLE,
                                            List.<JCExpression>of(jmlMaker.JmlStoreRefKeyword(JmlTokenKind.BSEVERYTHING)));
                                }
                                cs.clauses = cs.clauses.append(defaultClause);
                            }
                        }
                    }
                    allfecases.appendList(newcases);
                }
                newspecs = jmlMaker.at(methodSpecs.pos).JmlMethodSpecs(allcases.toList());
                newspecs.impliesThatCases = allitcases.toList();
                newspecs.forExampleCases = allfecases.toList();
            } else {
                if (clp != null) clauses.append(clp);
                if (!clauses.isEmpty()) {
                    JCModifiers mods = jmlMaker.at(decl.pos).Modifiers(decl.mods.flags & Flags.AccessFlags);
                    JmlSpecificationCase c = jmlMaker.JmlSpecificationCase(mods,false,null,null,clauses.toList());
                    newspecs = jmlMaker.JmlMethodSpecs(List.<JmlSpecificationCase>of(c));
                } else {
                    newspecs = methodSpecs;
                }
            }
            newspecs.decl = methodSpecs.decl;
            methodSpecs.deSugared = newspecs;
        } finally {
            if (env != null) env.enclMethod = prevEnclMethod;
            env = prevEnv;
            log.useSource(prevSource);
        }
    }
    
//    public void addDefaultClauses(List<JmlMethodClause> clauses) {
//        ListBuffer<JmlMethodClause> cl = new ListBuffer<JmlMethodClause>();
//        cl.appendList(clauses);
//        JCModifiers mods = c.modifiers;
//        if (c.token == null) mods = decl.mods;
//        ListBuffer<JmlSpecificationCase> newcases = deNest(cl,List.<JmlSpecificationCase>of(c),null,decl,mods);
//        for (JmlSpecificationCase cs: newcases) {
//            // Note: a model program spec case has no clauses
//            if (cs.clauses != null) {
//                boolean hasAssignableClause = false;
//                boolean hasAccessibleClause = false;
//                for (JmlMethodClause clm: cs.clauses) {
//                    if (clm.token == JmlTokenKind.ASSIGNABLE) { 
//                        hasAssignableClause = true; 
//                    }
//                    if (clm.token == JmlTokenKind.ACCESSIBLE) { 
//                        hasAccessibleClause = true; 
//                    }
//                }
//                if (!hasAssignableClause && clp != null) {
//                    cs.clauses = cs.clauses.append(clp);
//                }
//                if (!hasAccessibleClause) {
//                    JmlMethodClause defaultClause = jmlMaker.JmlMethodClauseStoreRef(JmlTokenKind.ACCESSIBLE,
//                             List.<JCExpression>of(jmlMaker.JmlStoreRefKeyword(JmlTokenKind.BSEVERYTHING)));
//                     cs.clauses = cs.clauses.append(defaultClause);
//                }
//            }
//        }
//
//    }
    
    
    boolean desugaringPure = false;
    
    // FIXME - this ignores anything after a clause group.  That is OK in strict JML.  DO we want it?  There is no warning.
    public ListBuffer<JmlSpecificationCase> deNest(ListBuffer<JmlMethodClause> prefix, List<JmlSpecificationCase> cases, /*@ nullable */JmlSpecificationCase parent, JmlMethodDecl decl, JCModifiers mods) {
        ListBuffer<JmlSpecificationCase> newlist = new ListBuffer<JmlSpecificationCase>();
        if (cases.isEmpty()) {
            if (parent != null) {
                addDefaultSignalsOnly(prefix,parent,decl);
                newlist.append(((JmlTree.Maker)make).at(parent.pos).JmlSpecificationCase(mods,parent.code,parent.token,parent.also,prefix.toList()));
            }
            else {
                // ERROR - not allowed to have an empty collection of specification cases
                // at the top level
                log.error("jml.internal","Unexpected empty set of specification cases at the top-level in JmlAttr");
            }
        } else if (cases.size() == 1) {
            // common case that just avoids copying the prefix
            JmlSpecificationCase c = cases.get(0);
            handleCase(parent, decl, newlist, c, prefix, mods);
        } else {
            for (JmlSpecificationCase cse: cases) {
                ListBuffer<JmlMethodClause> pr = copy(prefix);
                handleCase(parent, decl, newlist, cse, pr, mods);
            }
        }
        return newlist;
    }
    
    // FIXME - document; remove parent
    protected void addDefaultSignalsOnly(ListBuffer<JmlMethodClause> prefix, JmlSpecificationCase parent, JmlMethodDecl decl) {
        boolean anySOClause = false;
        for (JmlMethodClause cl: prefix) {
            if (cl.token == JmlTokenKind.SIGNALS_ONLY) anySOClause = true;
        }
        if (!anySOClause) {
            DiagnosticPosition p = decl.pos();
            if (decl.thrown != null && !decl.thrown.isEmpty()) p = decl.thrown.get(0).pos();
            ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
            if (decl.thrown != null) list.addAll(decl.thrown);
            list.add(factory.at(p).Type(syms.runtimeExceptionType));
            JmlMethodClauseSignalsOnly cl = (factory.at(p).JmlMethodClauseSignalsOnly(JmlTokenKind.SIGNALS_ONLY, list.toList()));
            cl.sourcefile = log.currentSourceFile();
            prefix.add(cl);
        }
    }

    /** Makes a copy of the list of clauses. 
     */
    public ListBuffer<JmlMethodClause> copy(ListBuffer<JmlMethodClause> p) {
        ListBuffer<JmlMethodClause> copy = new ListBuffer<JmlMethodClause>();
        copy.appendList(p);
        return copy;
    }
    
    protected void handleCase(JmlSpecificationCase parent, JmlMethodDecl decl,
            ListBuffer<JmlSpecificationCase> newlist, JmlSpecificationCase cse,
            ListBuffer<JmlMethodClause> pr, JCModifiers mods) {
        if (cse.token == JmlTokenKind.MODEL_PROGRAM) {
            newlist.append(cse);  // FIXME - check that model programs are only at the outer level
            return;
        }
        if (parent == null) {
            JmlTree.Maker jmlF = (JmlTree.Maker)make;
            JmlTokenKind t = cse.token;
            if (t == JmlTokenKind.NORMAL_BEHAVIOR || t == JmlTokenKind.NORMAL_EXAMPLE) {
                JmlMethodClauseSignals cl = jmlF.at(cse.pos).JmlMethodClauseSignals(JmlTokenKind.SIGNALS,null,falseLit);
                cl.sourcefile = cse.sourcefile;
                pr.append(cl);
            } else if (t == JmlTokenKind.EXCEPTIONAL_BEHAVIOR || t == JmlTokenKind.EXCEPTIONAL_EXAMPLE) {
                JmlMethodClauseExpr cl = jmlF.at(cse.pos).JmlMethodClauseExpr(JmlTokenKind.ENSURES,falseLit);
                cl.sourcefile = cse.sourcefile;
                pr.append(cl);
            }
        }
        newlist.appendList(deNestHelper(pr,cse.clauses,parent==null?cse:parent,decl,mods));
    }
    
    public ListBuffer<JmlSpecificationCase> deNestHelper(ListBuffer<JmlMethodClause> prefix, List<JmlMethodClause> clauses, JmlSpecificationCase parent, JmlMethodDecl decl, JCModifiers mods) {
        for (JmlMethodClause m: clauses) {
            if (m instanceof JmlMethodClauseGroup) {
                return deNest(prefix,((JmlMethodClauseGroup)m).cases, parent,decl, mods);
            }
            JmlTokenKind t = m.token;
            if (t == JmlTokenKind.ENSURES) {
                if (parent.token == JmlTokenKind.EXCEPTIONAL_BEHAVIOR || parent.token == JmlTokenKind.EXCEPTIONAL_EXAMPLE) {
                    log.error(m.pos,"jml.misplaced.clause","Ensures","exceptional");
                    continue;
                }
            } else if (t == JmlTokenKind.SIGNALS) {
                if (parent.token == JmlTokenKind.NORMAL_BEHAVIOR || parent.token == JmlTokenKind.NORMAL_EXAMPLE) {
                    log.error(m.pos,"jml.misplaced.clause","Signals","normal");
                    continue;
                }
            } else if (t == JmlTokenKind.SIGNALS_ONLY) {
                if (parent.token == JmlTokenKind.NORMAL_BEHAVIOR || parent.token == JmlTokenKind.NORMAL_EXAMPLE) {
                    log.error(m.pos,"jml.misplaced.clause","Signals_only","normal");
                    continue;
                }
                int count = 0;
                for (JmlMethodClause mc: prefix) {
                    if (mc.token == JmlTokenKind.SIGNALS_ONLY) count++;
                }
                if (count > 0) {
                    log.error(m.pos,"jml.multiple.signalsonly");
                }
            } else if (desugaringPure && t == JmlTokenKind.ASSIGNABLE) {
                JmlMethodClauseStoreRef asg = (JmlMethodClauseStoreRef)m;
                if (decl.sym.isConstructor()) {
                    // A pure constructor allows assigning to class member fields
                    // So if there is an assignable clause the elements of the clause
                    // may only be members of the class
                    for (JCTree tt: asg.list) {
                        if (tt instanceof JmlStoreRefKeyword) {
                            if (((JmlStoreRefKeyword)tt).token == JmlTokenKind.BSNOTHING) {
                                // OK
                            } else {
                                jmlerror(m,"jml.pure.constructor",tt);
                            }
                        } else if (tt instanceof JCIdent) {
                            // non-static Simple identifier is OK
                            // If the owner of the field is an interface, it
                            // is by default static. However, it might be a
                            // JML field marked as instance.
                            VarSymbol sym = (VarSymbol)((JCIdent)tt).sym;
                            if (utils.isJMLStatic(sym)) {
                                jmlerror(tt,"jml.pure.constructor",tt);
                            }
                        } else if (tt instanceof JCTree.JCFieldAccess) {
                            JCFieldAccess fa = (JCFieldAccess)tt;
                            boolean ok = false;
                            if (fa.selected instanceof JCIdent) {
                                Symbol sym = ((JCIdent)fa.selected).sym;
                                if (sym.name == names._this || sym.name == names._super) {
                                    Symbol fasym = fa.sym;
                                    if (fa.sym == null || !utils.isJMLStatic(fasym)) ok = true;
                                }
                            } 
                            if (!ok) jmlerror(tt,"jml.pure.constructor",tt);
                        } else {
                            // FIXME - also allow this.*  or super.* ?
                            jmlerror(tt,"jml.pure.constructor",tt);
                        }
                    }
                } else {
                    for (JCTree tt: asg.list) {
                        if (tt instanceof JmlStoreRefKeyword &&
                            ((JmlStoreRefKeyword)tt).token == JmlTokenKind.BSNOTHING) {
                                // OK
                        } else if (isFunction(decl.sym)) {
                            jmlerror(tt,"jml.function.method",tt);
                        } else {
                            jmlerror(tt,"jml.pure.method",tt);
                        }
                    }
                }
            }
            prefix.append(m);
        }
        addDefaultSignalsOnly(prefix,parent,decl);
        ListBuffer<JmlSpecificationCase> newlist = new ListBuffer<JmlSpecificationCase>();
        JmlSpecificationCase sc = (((JmlTree.Maker)make).JmlSpecificationCase(parent,prefix.toList()));
        sc.modifiers = mods;
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
        if ((localEnv.enclMethod.mods.flags & STATIC) != 0 ||
                (env.enclClass.sym.flags() & INTERFACE) != 0)
                localEnv.info.staticLevel++;
        
    }
    
//    /** This is overridden in order to check the JML modifiers of the variable declaration */
//    @Override
//    public void visitVarDef(JCVariableDecl tree) {
//        attribAnnotationTypes(tree.mods.annotations,env);  // FIXME - we should not need these two lines I think, but otherwise we get NPE faults on non_null field declarations
//        for (JCAnnotation a: tree.mods.annotations) a.type = a.annotationType.type;
//        super.visitVarDef(tree);
//        // Anonymous classes construct synthetic members (constructors at least)
//        // which are not JML nodes.
//        FieldSpecs fspecs = specs.getSpecs(tree.sym);
//        if (fspecs != null) {
//            boolean prev = jmlresolve.setAllowJML(true);
//            for (JmlTypeClause spec:  fspecs.list) spec.accept(this);
//            jmlresolve.setAllowJML(prev);
//        }
//
//        // These are checked later in visitJmlVariableDecl
////        // Check the mods after the specs, because the modifier checks depend on
////        // the specification clauses being attributed
////        if (tree instanceof JmlVariableDecl) {
////            checkVarMods((JmlVariableDecl)tree);
////        }
//    }
    
    // MAINTENANCE ISSUE - copied from super class
    @Override
    protected void checkInit(JCTree tree,
            Env<AttrContext> env,
            VarSymbol v,
            boolean onlyWarning) {

        if (env.tree instanceof JmlQuantifiedExpr) return;
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
        if ((env.info.enclVar == v || v.pos > tree.pos) &&
                v.owner.kind == TYP &&
                (env.tree.getTag() != null && enclosingInitEnv(env) != null) &&  // FIXME - this line used to be a check for canOwnInitializer, which was only used here and defined in Attr.java
                v.owner == env.info.scope.owner.enclClass() &&
                ((v.flags() & STATIC) != 0) == Resolve.isStatic(env) &&
                (!env.tree.hasTag(ASSIGN) ||
                        TreeInfo.skipParens(((JCAssign) env.tree).lhs) != tree)) {
            String suffix = (env.info.enclVar == v) ?
                    "self.ref" : "forward.ref";
            if (!onlyWarning || isStaticEnumField(v)) {
                // DRC - changed the following line to avoid complaints about forward references from invariants
                if (currentClauseType == null || currentClauseType == JmlTokenKind.JMLDECL) {
                    log.error(tree.pos(), "illegal.forward.ref");
                }
            } else if (useBeforeDeclarationWarning) {
                log.warning(tree.pos(), suffix, v);
            }
        }

        v.getConstValue(); // ensure initializer is evaluated

        checkEnumInitializer(tree, env, v);

    }

    
    public JmlTokenKind[] allowedFieldModifiers = new JmlTokenKind[] {
            SPEC_PUBLIC, SPEC_PROTECTED, MODEL, GHOST,
            NONNULL, NULLABLE, INSTANCE, MONITORED, SECRET,
            PEER, REP, READONLY // FIXME - allowing these until the rules are really implemented
       };
       
    public JmlTokenKind[] allowedGhostFieldModifiers = new JmlTokenKind[] {
            GHOST, NONNULL, NULLABLE, INSTANCE, MONITORED, SECRET,
            PEER, REP, READONLY // FIXME - allowing these until the rules are really implemented
       };
       
    public JmlTokenKind[] allowedModelFieldModifiers = new JmlTokenKind[] {
            MODEL, NONNULL, NULLABLE, INSTANCE, SECRET,
            PEER, REP, READONLY // FIXME - allowing these until the rules are really implemented
       };
       
    public JmlTokenKind[] allowedFormalParameterModifiers = new JmlTokenKind[] {
            NONNULL, NULLABLE, READONLY, REP, PEER, SECRET,
       };
       
    public JmlTokenKind[] allowedLocalVarModifiers = new JmlTokenKind[] {
            NONNULL, NULLABLE, GHOST, UNINITIALIZED, READONLY, REP, PEER, SECRET
       };
       
    public void checkVarMods(JmlVariableDecl tree) {
        if (tree.name == names.error || tree.type.isErroneous()) return;
        JCModifiers mods = tree.mods;
        String kind = (tree.mods.flags & Flags.PARAMETER) != 0 ? "parameter" : "field";
        if (tree.specsDecl != null) {
            JCModifiers jmlmods = tree.specsDecl.mods;
            attribAnnotationTypes(jmlmods.annotations,env);
//            for (JCAnnotation a: tree.mods.annotations) { // Iterating over annotations in .java file
//                JCAnnotation aa = utils.findMod(jmlmods, a.type.tsym); // CHeck if it is used in .jml file
//                if (aa == null) { // If not, report that it is ignored
//                    log.warning(a.pos(), "jml.java.annotation.superseded", kind , tree.name.toString(), a.toString());
//                }
//            }
            mods = tree.specsDecl.mods;
            log.useSource(tree.specsDecl.source());
        }
        boolean inJML = utils.isJML(mods);
        boolean ownerInJML = utils.isJML(tree.sym.owner.flags());
        boolean ghost = isGhost(mods);
        boolean model = isModel(mods);
        boolean modelOrGhost = model || ghost;
        if (tree.sym.owner.kind == Kinds.TYP) {  // Field declarations
            if (ghost) {
                allAllowed(mods.annotations, allowedGhostFieldModifiers, "ghost field declaration");
            } else if (model) {
                allAllowed(mods.annotations, allowedModelFieldModifiers, "model field declaration");
            } else {
                allAllowed(mods.annotations, allowedFieldModifiers, "field declaration");
            }
            if (!inJML && isInJmlDeclaration && modelOrGhost) {
                if (ghost) utils.error(tree.sourcefile,tree.pos,"jml.no.nested.ghost.type");
                else       utils.error(tree.sourcefile,tree.pos,"jml.no.nested.model.type");
            } else if (inJML && !modelOrGhost  && !isInJmlDeclaration) {
                utils.error(tree.sourcefile,tree,"jml.missing.ghost.model");
            } else if (!inJML && modelOrGhost) {
                utils.error(tree.sourcefile,tree.pos,"jml.ghost.model.on.java");
            } 
            JmlAnnotation a;
            if (!model) {
                checkForConflict(mods,SPEC_PUBLIC,SPEC_PROTECTED);
                checkForRedundantSpecMod(mods);
            }
            a = utils.findMod(mods,INSTANCE);
            if (a != null && isStatic(tree.mods)) {
                utils.error(a.sourcefile,a.pos(),"jml.conflicting.modifiers","instance","static");
            }
//            if (model && ((tree.mods.flags & Flags.FINAL)!=0)) {   // FIXME - WHy would model and final conflict
//                a = utils.findMod(tree.mods,MODEL);
//                utils.error(a.sourcefile,a.pos(),"jml.conflicting.modifiers","model","final");
//            }
            checkForConflict(mods,NONNULL,NULLABLE);
            if (tree.specsDecl != null) log.useSource(tree.source());
        } else if ((tree.mods.flags & Flags.PARAMETER) != 0) { // formal parameters
            JCModifiers pmods = tree.mods;
            if (tree.specsDecl != null) {
                JCModifiers jmlmods = tree.specsDecl.mods;
                attribAnnotationTypes(jmlmods.annotations,env);
                // Appropriate use of annotations is checked below.
//                for (JCAnnotation a: tree.mods.annotations) {
//                    JmlAnnotation aa = utils.findMod(jmlmods, a.type.tsym);
//                    if (aa == null) { // FIXME _ check on sourcefile
//                        JavaFileObject psource = log.useSource(tree.source());
//                        log.warning(a.pos(), "jml.java.annotation.superseded", "parameter", tree.name.toString(), a.toString());
//                        log.useSource(psource);
//                    }
//                }
                kind = "parameter";
                pmods = jmlmods;
            }
            if (tree.specsDecl != null) log.useSource(tree.specsDecl.source());
            allAllowed(pmods.annotations, allowedFormalParameterModifiers, "formal parameter");
            checkForConflict(pmods,NONNULL,NULLABLE);
            if (tree.specsDecl != null) log.useSource(tree.source());
            
        } else { // local declaration
            kind = "local variable declaration";
            allAllowed(tree.mods.annotations, allowedLocalVarModifiers, kind);
            if (inJML && !ghost  && !isInJmlDeclaration && !ownerInJML) {
                utils.error(tree.source(),tree.pos,"jml.missing.ghost");
            } else if (!inJML && ghost) {
                utils.error(tree.source(),tree.pos,"jml.ghost.on.java");
            } 
            checkForConflict(tree.mods,NONNULL,NULLABLE);
        }
        
        if (tree.specsDecl != null) {
            JavaFileObject prev = log.useSource(tree.specsDecl.source());
            checkSameAnnotations(tree.mods,tree.specsDecl.mods,kind,tree.name.toString());
            log.useSource(prev);
        }
             
        // Check that types match 
        if (tree.specsDecl != null) { // tree.specsDecl can be null if there is a parsing error
            JavaFileObject prev = log.useSource(tree.specsDecl.source());
            Type specType = attribType(tree.specsDecl.vartype,env);
            log.useSource(prev);
            if (specType != null) {
                if (!Types.instance(context).isSameType(tree.sym.type,specType)) {
                    if (specType.hasTag(TypeTag.TYPEVAR) && tree.sym.type.hasTag(TypeTag.TYPEVAR)) {
                        if (specType.tsym.name != tree.sym.type.tsym.name) {
                            utils.errorAndAssociatedDeclaration(tree.specsDecl.source(),tree.specsDecl.vartype.pos(),
                                tree.sourcefile, tree.pos(),
                                "jml.mismatched.field.types",tree.name,
                                tree.sym.enclClass().getQualifiedName()+"."+tree.sym.name,
                                specType.tsym,
                                tree.sym.type.tsym);
                        }
                        
                    } else if (!specType.toString().equals(tree.sym.type.toString())) {
                       utils.errorAndAssociatedDeclaration(tree.specsDecl.source(),tree.specsDecl.vartype.pos(),
                            tree.sourcefile, tree.pos(),
                            "jml.mismatched.field.types",tree.name,
                            tree.sym.enclClass().getQualifiedName()+"."+tree.sym.name,
                            specType,
                            tree.sym.type);
                    }
                }
            }
        }

    }
    
    /** This method checks specifications of field declarations that must be checked after all
     * fields have been initially processed, because they might have forward declarations.
     */
    public void checkVarMods2(JmlVariableDecl tree) {
        if (tree.name == names.error || tree.type.isErroneous()) return;
        JCModifiers mods = tree.mods;
        boolean inJML = utils.isJML(mods);
        boolean ownerInJML = utils.isJML(tree.sym.owner.flags());
        boolean ghost = isGhost(mods);
        boolean model = isModel(mods);
        boolean modelOrGhost = model || ghost;
        inVarDecl = tree;
        
        // Secret
        JmlAnnotation secret = findMod(mods,JmlTokenKind.SECRET);
        VarSymbol secretDatagroup = null;
        if (secret != null) {
            List<JCExpression> args = secret.getArguments();
            if (!args.isEmpty()) {
                utils.error(secret.sourcefile,args.get(0).pos,"jml.no.arg.for.field.secret");
            }
        }
        
        // Note that method parameters, which belong to Methods, have
        // null FieldSpecs
        if (tree.sym.owner.kind == Kinds.TYP) {
            // Check all datagroups that the field is in
            JmlSpecs.FieldSpecs fspecs = specs.getSpecs(tree.sym);
            long prevVisibility = jmlVisibility;
            JmlTokenKind prevClauseType = currentClauseType;
            if (fspecs != null) try {
                for (JmlTypeClause tc: fspecs.list) {
                    if (tc.token == JmlTokenKind.IN) {
                        JmlTypeClauseIn tcin = (JmlTypeClauseIn)tc;
                        currentClauseType = JmlTokenKind.IN;
                        jmlVisibility = tcin.parentVar.mods.flags & Flags.AccessFlags;
                        for (JmlGroupName g: tcin.list) {
                            attributeGroup(g);
                            if (g.sym == null) continue; // Happens if there was an error in finding g
                            if (hasAnnotation(g.sym,JmlTokenKind.SECRET) != (secret != null)) {
                                if (secret != null) {
                                    log.error(tcin.pos,"jml.secret.field.in.nonsecret.datagroup");
                                } else {
                                    log.error(tcin.pos,"jml.nonsecret.field.in.secret.datagroup");
                                }
                            }
                        }
                    }
                }
            } finally {
                jmlVisibility = prevVisibility;
                currentClauseType = prevClauseType;
                inVarDecl = null;
            }
            // Allow Java fields to be datagroups
//            if (secret != null && fspecs.list.isEmpty()) {
//                // Not in any datagroups
//                // Had better be model itself
//                if (!isModel(fspecs.mods)) {
//                    log.error(tree.pos,"jml.secret.field.model.or.in.secret.datagroup");
//                }
//            }
        }    
    }
    
//    // FIXME - this should be done in MemberEnter, not here
//    protected void checkSameAnnotations(Symbol sym, JCModifiers specsModifiers) {
//        for (Compound a  : sym.getAnnotationMirrors()) {
//            if (a.type.tsym.owner.equals(annotationPackageSymbol) && utils.findMod(specsModifiers,a.type.tsym) == null) {
//                log.error(specsModifiers.pos,"jml.missing.annotation",a);
//            }
//        }
//    }
    
    /** Overridden in order to be sure that the type specs are attributed. */
    public Type attribType(JCTree tree, Env<AttrContext> env) { // FIXME _ it seems this will automatically happen - why not?
        Type result = super.attribType(tree,env);
        if (result.getTag() != TypeTag.VOID && result.isErroneous() && 
                result.tsym instanceof ClassSymbol &&
                !result.isPrimitive()) {
            addTodo((ClassSymbol)result.tsym);
        }
        return result;
    }

    
    public void visitJmlGroupName(JmlGroupName tree) {
        Type saved = result = attribExpr(tree.selection,env,Type.noType);
        Symbol sym = null;
        if (tree.selection.type.getTag() == TypeTag.ERROR) return;
        else if (tree.selection instanceof JCIdent) sym = ((JCIdent)tree.selection).sym;
        else if (tree.selection instanceof JCFieldAccess) sym = ((JCFieldAccess)tree.selection).sym;
        else if (tree.selection instanceof JCErroneous) return;
        if (!(sym instanceof VarSymbol)) {
            // FIXME - does this happen?  emit errors
            sym = null;
        }
        tree.sym = (VarSymbol)sym;
        if (sym == null) {
            log.error(tree.pos,"jml.internal","Unexpectedly did not find a resolution for this data group expression");
            return;
        }
        if (!isModel(sym)) {
            log.error(tree.pos,"jml.datagroup.must.be.model.in.maps");
        }
        if (inVarDecl != null && utils.isJMLStatic(sym) && !utils.isJMLStatic(inVarDecl.sym)) {
            log.error(tree.pos,"jml.instance.in.static.datagroup");
        }
        result = saved;
    }
    
    JmlVariableDecl inVarDecl = null;
    
    public void visitJmlTypeClauseIn(JmlTypeClauseIn tree) {
        boolean prev = jmlresolve.setAllowJML(true);
        boolean prevEnv = pureEnvironment;
        JmlTokenKind prevClauseType = currentClauseType;
        JmlVariableDecl prevDecl = inVarDecl;
        currentClauseType = tree.token;
        pureEnvironment = true;
        inVarDecl = tree.parentVar;
        long prevVisibility = jmlVisibility;
        try {
            jmlVisibility = tree.parentVar.mods.flags & Flags.AccessFlags; // FIXME - don't thnk this is needed here
            if (checkForCircularity(inVarDecl.sym)) {
                log.error(inVarDecl.pos(),"jml.circular.datagroup.inclusion",inVarDecl.name);
            }
//            for (JmlGroupName n: tree.list) {
//                n.accept(this);
//                if (n.sym != null && n.sym != inVarDecl.sym && checkForCircularity(n.sym,inVarDecl.sym)) {
//                    log.error(inVarDecl.pos(),"jml.circular.datagroup.inclusion",inVarDecl.name);
//                    continue;
//                }
//            }
        } finally {
            jmlVisibility = prevVisibility;
            inVarDecl = prevDecl;
            pureEnvironment = prevEnv;
            currentClauseType = prevClauseType;
            jmlresolve.setAllowJML(prev);
            result = null;
        }
    }
    
    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps tree) {
        boolean prev = jmlresolve.setAllowJML(true);
        boolean prevEnv = pureEnvironment;
        JmlTokenKind prevClauseType = currentClauseType;
        currentClauseType = tree.token;
        pureEnvironment = true;
        long prevVisibility = jmlVisibility;
        // Also check that the member reference field matches the declaration FIXME
        // FIXME - static environment?
        // FIXME - check visibility
        try {
            // FIXME : jmlVisibility = tree.parentVar.mods.flags & Flags.AccessFlags;
            attribExpr(tree.expression,env,Type.noType);
            for (JmlGroupName n: tree.list) {
                n.accept(this);
            }
        } finally {
            jmlVisibility = prevVisibility;
            pureEnvironment = prevEnv;
            currentClauseType = prevClauseType;
            jmlresolve.setAllowJML(prev);
        }
    }

    public void annotate(final List<JCAnnotation> annotations,
            final Env<AttrContext> localEnv) {
        Set<TypeSymbol> annotated = new HashSet<TypeSymbol>();
        for (List<JCAnnotation> al = annotations; al.nonEmpty(); al = al.tail) {
            JCAnnotation a = al.head;
            Attribute.Compound c = annotate.enterAnnotation(a,
                                                            syms.annotationType,
                                                            env);
            if (c == null) continue;
            if (!annotated.add(a.type.tsym))
                log.error(a.pos, "duplicate.annotation");
        }
    }

    /** Attributes invariant, axiom, initially clauses */
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr tree) {
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        JavaFileObject old = log.useSource(tree.source);
        VarSymbol previousSecretContext = currentSecretContext;
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        boolean isStatic = tree.modifiers != null && isStatic(tree.modifiers);
        long prevVisibility = jmlVisibility;
        try {
            // invariant, axiom, initially
            Env<AttrContext> localEnv = env; // FIXME - here and in constraint, should we make a new local environment?
            //if (tree.token == JmlToken.AXIOM) isStatic = true; // FIXME - but have to sort out use of variables in axioms in general
            if (isStatic) localEnv.info.staticLevel++;

            if (tree.token == JmlTokenKind.INVARIANT) {
                jmlVisibility = -1;
                attribAnnotationTypes(tree.modifiers.annotations,env);
                annotate(tree.modifiers.annotations,env);
                JCAnnotation a = findMod(tree.modifiers,JmlTokenKind.SECRET);
                jmlVisibility = tree.modifiers.flags & Flags.AccessFlags;
                if (a != null) {
                    if (a.args.size() != 1) {
                        log.error(tree.pos(),"jml.secret.invariant.one.arg");
                    } else {
                        Name datagroup = getAnnotationStringArg(a);
                        if (datagroup != null) {
                            //Symbol v = rs.findField(env,env.enclClass.type,datagroup,env.enclClass.sym);
                            Symbol v = rs.resolveIdent(a.args.get(0).pos(),env,datagroup,VAR);
                            if (v instanceof VarSymbol) currentSecretContext = (VarSymbol)v;
                            else if (v instanceof PackageSymbol) {
                                log.error(a.args.get(0).pos(),"jml.annotation.arg.not.a.field",v.getQualifiedName());
                            }
                        }
                    }
                }
            }

            attribExpr(tree.expression, localEnv, syms.booleanType);
            if (isStatic) localEnv.info.staticLevel--;  // FIXME - move this to finally, but does not screw up the checks on the next line?
            checkTypeClauseMods(tree,tree.modifiers,tree.token.internedName() + " clause",tree.token);

        } finally {
            jmlVisibility = prevVisibility;
            currentSecretContext = previousSecretContext;
            jmlresolve.setAllowJML(prevAllowJML);
            pureEnvironment = prev;
            log.useSource(old);
        }
    }
    
    protected Name getAnnotationStringArg(JCAnnotation a) {
        // The expression is an assignment of a Literal string to an identifier
        // We only care about the literal string
        // FIXME - what if the string is a qualified name?
        JCExpression e = a.args.get(0);
        if (e instanceof JCAssign) {
            e = ((JCAssign)e).rhs;
        } 
        if (e instanceof JCLiteral) {
            JCLiteral lit = (JCLiteral)e;
            // Non-string cases will already have error messages
            if (lit.value instanceof String)
                    return names.fromString(lit.value.toString());
        }
        // So will non-literal cases
        return null;
    }
    
    protected VarSymbol getSecretSymbol(JCModifiers mods) {
        JCAnnotation secret = findMod(mods,JmlTokenKind.SECRET);
        if (secret == null) return null;
        if (secret.args.size() == 0) {
            log.error(secret.pos(),"jml.secret.requires.arg");
            return null;
        }
        Name n = getAnnotationStringArg(secret);
        boolean prev = jmlresolve.setAllowJML(true);
        Symbol sym = rs.resolveIdent(secret.args.get(0).pos(),env,n,VAR);
        jmlresolve.setAllowJML(prev);
        if (sym instanceof VarSymbol) return (VarSymbol)sym;
        log.error(secret.pos(),"jml.no.such.field",n.toString());
        return null;
    }
    
    protected VarSymbol getQuerySymbol(JCMethodInvocation tree, JCModifiers mods) {
        JCAnnotation query = findMod(mods,JmlTokenKind.QUERY);
        if (query == null) return null;
        List<JCExpression> args = query.getArguments();
        Name datagroup = null;
        DiagnosticPosition pos = tree.meth.pos();
        if (args.isEmpty()) {
            // No argument - use the name of the method
            if (tree.meth instanceof JCIdent) datagroup = ((JCIdent)tree.meth).name;
            else if (tree.meth instanceof JCFieldAccess) datagroup = ((JCFieldAccess)tree.meth).name;
            pos = query.pos();
        } else {
            datagroup = getAnnotationStringArg(query);
            pos = args.get(0).pos();
        }
        boolean prev = jmlresolve.setAllowJML(true);
        Symbol sym = rs.resolveIdent(pos,env,datagroup,VAR);
        jmlresolve.setAllowJML(prev);
        if (sym instanceof VarSymbol) return (VarSymbol)sym;
        log.error(pos,"jml.no.such.field",datagroup.toString());
        return null;
    }
    
    JmlTokenKind[] clauseAnnotations = new JmlTokenKind[]{ INSTANCE };
    JmlTokenKind[] invariantAnnotations = new JmlTokenKind[]{ SECRET, INSTANCE };
    JmlTokenKind[] noAnnotations = new JmlTokenKind[]{  };

    public void checkTypeClauseMods(JCTree tree, JCModifiers mods,String where, JmlTokenKind token) {
        long f = 0;
        if (token != JmlTokenKind.AXIOM) f = Flags.AccessFlags | Flags.STATIC | Flags.FINAL;
        long diff = utils.hasOnly(mods,f);
        if (diff != 0) log.error(tree.pos,"jml.bad.mods",Flags.toString(diff));
        JCAnnotation a = utils.findMod(mods,tokenToAnnotationSymbol.get(INSTANCE));
        if (a != null && isStatic(mods) ) {
            log.error(a.pos(),"jml.conflicting.modifiers","instance","static");
        }
        attribAnnotationTypes(mods.annotations,env);
        switch (token) {
            case AXIOM:
                allAllowed(mods.annotations,noAnnotations,where);
                break;
            case INVARIANT:
            case REPRESENTS:
                allAllowed(mods.annotations,invariantAnnotations,where);
                break;
            default:
                allAllowed(mods.annotations,clauseAnnotations,where);
                break;
        }
        if (token != JmlTokenKind.AXIOM) {
            Check.instance(context).checkDisjoint(tree.pos(),mods.flags,Flags.PUBLIC,Flags.PROTECTED|Flags.PRIVATE);
            Check.instance(context).checkDisjoint(tree.pos(),mods.flags,Flags.PROTECTED,Flags.PRIVATE);
        }
    }
    
    /** Attributes a constraint clause */
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint tree) {
        JavaFileObject old = log.useSource(tree.source);
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        long prevVisibility = jmlVisibility;
        try {
            // constraint
            boolean isStatic = (tree.modifiers.flags & STATIC) != 0;
            Env<AttrContext> localEnv = env;
            jmlVisibility = tree.modifiers.flags & Flags.AccessFlags;
            if (isStatic) localEnv.info.staticLevel++;
            ResultInfo prevResultInfo = resultInfo;
            resultInfo = new ResultInfo(VAL|TYP,Type.noType);
            attribExpr(tree.expression, localEnv, syms.booleanType);
            resultInfo = prevResultInfo;
            if (isStatic) localEnv.info.staticLevel--;
            checkTypeClauseMods(tree,tree.modifiers,"constraint clause",tree.token);
            if (tree.sigs != null) for (JmlTree.JmlMethodSig sig: tree.sigs) {
                if (sig.argtypes == null) {
                    // FIXME - not implemented
                } else {
                    sig.accept(this);
                    Symbol s = sig.methodSymbol;
                    if (s != null && s.isConstructor()
                            && !isStatic) {
                        log.error(sig.pos(),"jml.no.constructors.allowed");
                    }
                    if (s != null && s.kind != Kinds.ERR){
                        if (s.owner != localEnv.enclClass.sym) {
                            log.error(sig.pos(),"jml.incorrect.method.owner");
                        }
                    }

                }
            }
        } finally {
            jmlVisibility = prevVisibility;
            jmlresolve.setAllowJML(prevAllowJML);
            pureEnvironment = prev;
            log.useSource(old);
        }
    }
    
   
    /** Attributes a declaration within a JML annotation - that is, a
     * model method, model type, or ghost or model field
     */
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl tree) {
        JavaFileObject old = log.useSource(tree.source);
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        long prevVisibility = jmlVisibility;
        try {
            jmlVisibility = tree.modifiers.flags & Flags.AccessFlags;
            attribStat(tree.decl,env);
        } finally {
            jmlVisibility = prevVisibility;
            jmlresolve.setAllowJML(prevAllowJML);
            log.useSource(old);
        }
    }
    
    
    /** Attributes a initializer or static_initializer declaration */
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer tree) {
        JavaFileObject old = log.useSource(tree.source);
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        try {
            // FIXME - test declarations within specs
            Env<AttrContext> localEnv = localEnv(env,tree);
            localEnv.info.scope.owner =
                new MethodSymbol(Flags.PRIVATE | BLOCK, names.empty, null,
                                 env.info.scope.owner);
            if (tree.token == JmlTokenKind.STATIC_INITIALIZER) localEnv.info.staticLevel++;
            if (tree.specs != null) attribStat(tree.specs,localEnv);
        } finally {
            jmlresolve.setAllowJML(prevAllowJML);
            log.useSource(old);
        }
    }
    
    /** Attributes a represents clause */
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents tree) {
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        JavaFileObject old = log.useSource(tree.source);
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        VarSymbol prevSecret = currentSecretContext;
        long prevVisibility = jmlVisibility;
        try {
            //attribExpr(tree.ident,env,Type.noType);
            // Do this by hand to avoid issues with secret
            jmlVisibility = tree.modifiers.flags & Flags.AccessFlags;
            Symbol sym = null;
            if (tree.ident instanceof JCIdent) {
                JCIdent id = (JCIdent)tree.ident;
                ResultInfo prevResultInfo = resultInfo;
                resultInfo = new ResultInfo(VAL,Type.noType);
                super.visitIdent(id);
                resultInfo = prevResultInfo; // FIXME - in finally block
                sym = id.sym;
            }
            else if (tree.ident instanceof JCFieldAccess) {
                // FIXME - this needs fixing
                attribExpr(tree.ident,env,Type.noType);
                sym = ((JCFieldAccess)tree.ident).sym;
            }
            else {
                attribExpr(tree.ident,env,Type.noType);
                // FIXME - error - not implemented
            }
            
            // FIXME check that sym and represents are both secret or both not
            attribAnnotationTypes(tree.modifiers.annotations,env);
            annotate(tree.modifiers.annotations,env);
            JCAnnotation a = findMod(tree.modifiers,JmlTokenKind.SECRET);
            boolean representsIsSecret = a != null;
            if (a != null && a.args.size() != 0) {
                log.error(a.args.get(0).pos(),"jml.no.arg.for.secret.represents");
            }
            if (sym != null) {
                boolean symIsSecret = sym.attribute(tokenToAnnotationSymbol.get(JmlTokenKind.SECRET)) != null;
                if (symIsSecret != representsIsSecret) {
                    log.error(tree.pos(),"jml.represents.does.not.match.id.secret");
                }
            }
            
            if (representsIsSecret && sym instanceof VarSymbol) currentSecretContext = (VarSymbol)sym;
            
            Env<AttrContext> localEnv = env; //envForClause(tree,sym);
            if ((tree.modifiers.flags & STATIC) != 0) localEnv.info.staticLevel++;
            
            if (tree.suchThat) {
                attribExpr(tree.expression, localEnv, syms.booleanType);
            } else if (tree.ident.type == null) {
                // skip
            } else if (tree.ident.type.getKind() == TypeKind.ERROR) {
                // skip
            } else if (tree.ident.type.getKind() == TypeKind.NONE) {
                // ERROR - parser should not let us get here - FIXME
            } else {
                attribExpr(tree.expression, localEnv, tree.ident.type);
            }
            if ((tree.modifiers.flags & STATIC) != 0) localEnv.info.staticLevel--;

            checkTypeClauseMods(tree,tree.modifiers,"represents clause",tree.token);
            if (sym != null && !sym.type.isErroneous() && sym.type.getTag() != TypeTag.ERROR) {
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
            jmlVisibility = prevVisibility;
            jmlresolve.setAllowJML(prevAllowJML);
            pureEnvironment = prev;
            log.useSource(old);
            currentSecretContext = prevSecret;
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
    
    /** Attributes the monitors_for clause */
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor tree) {
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        JavaFileObject old = log.useSource(tree.source);
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        long prevVisibility = jmlVisibility;
        try {
            jmlVisibility = tree.modifiers.flags & Flags.AccessFlags;
            attribExpr(tree.identifier,env,Type.noType);

            Symbol sym = tree.identifier.sym;
            if (sym.owner != env.enclClass.sym) {
                log.error(tree.identifier.pos,"jml.ident.not.in.class",sym,sym.owner,env.enclClass.sym);
            } else {
                // FIXME - should this be done elsewhere?
                specs.getSpecs((VarSymbol)sym).list.append(tree);
            }
            
            // static does not matter here - the expressions in the
            // list do not need to be static just because the identifier is
            
            for (JCExpression c: tree.list) {
                attribExpr(c,env,Type.noType);
                if (c.type.isPrimitive()) {
                    log.error(c.pos,"jml.monitors.is.primitive");
                }
            }
        } finally {
            jmlVisibility = prevVisibility;
            jmlresolve.setAllowJML(prevAllowJML);
            pureEnvironment = prev;
            log.useSource(old);
        }
    }
    
    /** Attributes the readable-if and writable-if clauses */
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional tree) {
        JavaFileObject old = log.useSource(tree.source);
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        long prevVisibility = jmlVisibility;
        try {
            attribExpr(tree.identifier,env,Type.noType);
            
            Symbol sym = tree.identifier.sym;
            jmlVisibility = sym.flags() & Flags.AccessFlags;
            long clauseVisibility = tree.modifiers.flags & Flags.AccessFlags;
            if (clauseVisibility != 0 && clauseVisibility != jmlVisibility) {
                log.error(tree.identifier.pos,"jml.visibility.is.different",Flags.toString(clauseVisibility), Flags.toString(jmlVisibility));
            }
            
            if (sym.owner != env.enclClass.sym) {
                log.error(tree.identifier.pos,"jml.ident.not.in.class",sym,sym.owner,env.enclClass.sym);
            } else {
                // FIXME _ should this be done elsewhere
                VarSymbol vsym = (VarSymbol)sym;
                JmlSpecs.FieldSpecs fs = specs.getSpecs(vsym);
                //if (fs == null) specs.putSpecs(vsym,fs=new JmlSpecs.FieldSpecs(tree.sym.));
                fs.list.append(tree);
            }
            
            boolean isStatic = sym.isStatic();
            if (isStatic) // ||(env.enclClass.sym.flags() & INTERFACE) != 0) // FIXME - what about interfaces
                env.info.staticLevel++;
            attribExpr(tree.expression, env, syms.booleanType);
            if (isStatic) // ||(env.enclClass.sym.flags() & INTERFACE) != 0) // FIXME - what about interfaces
                env.info.staticLevel--;
        } finally {
            jmlVisibility = prevVisibility;
            jmlresolve.setAllowJML(prevAllowJML);
            pureEnvironment = prev;
            log.useSource(old);
        }
    }
    
    /** Attributes a method-clause group (the stuff within {| |} ) */
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {
        for (JmlSpecificationCase c: tree.cases) {
            c.accept(this);
        }
    }
    
    boolean forallOldEnv = false;
    
    /** Attributes for and old clauses within the specs of a method */
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl tree) {
        JmlTokenKind t = tree.token;
        for (JCTree.JCVariableDecl decl: tree.decls) {
            if (decl instanceof JmlVariableDecl) {
                int wasFlags = 0;
                if (env.enclMethod.sym.isStatic()) {
                    wasFlags = Flags.STATIC;  // old and forall decls are implicitly static for a static method
                    ((JmlVariableDecl)decl).mods.flags |= Flags.STATIC;  // old and forall decls are implicitly static for a static method
                }
                forallOldEnv = JmlCheck.instance(context).staticOldEnv;
                JmlCheck.instance(context).staticOldEnv = wasFlags != 0;
                try {
                    decl.accept(this);
                    if (decl.sym == null) {
                        if (toRemove == null) toRemove = new ListBuffer<>();
                        toRemove.add(tree);
                    }
                } finally {
                    JmlCheck.instance(context).staticOldEnv = forallOldEnv;
                    forallOldEnv = false;
                    if (env.enclMethod.sym.isStatic()) {
                        ((JmlVariableDecl)decl).mods.flags &= ~Flags.STATIC; 
                    }
                }
                JCTree.JCExpression init = ((JmlVariableDecl)decl).init;
                if (t == JmlTokenKind.FORALL) {
                    if (init != null) log.error(init.pos(),"jml.forall.no.init");
                } else {
                    if (init == null) log.error(((JmlVariableDecl)decl).pos,"jml.old.must.have.init");
                }
                JCModifiers mods = ((JmlVariableDecl)decl).mods;
                if (utils.hasOnly(mods,wasFlags)!=0) log.error(tree.pos,"jml.no.java.mods.allowed","method specification declaration");
                // The annotations are already checked as part of the local variable declaration
                //allAllowed(mods.annotations, JmlToken.typeModifiers, "method specification declaration");
            } else {
                log.error(decl.pos(),"jml.internal.notsobad","Unexpected " + decl.getClass() + " object type in a JmlMethodClauseDecl list");
            }
        }
    }
    
    // FIXME - test the name lookup with forall and old clauses
    
    protected Env<AttrContext> savedMethodClauseOutputEnv = null;

    /** This is an implementation that does the type attribution for 
     * method specification clauses
     * @param tree the method specification clause being attributed
     */
    
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) {
        savedMethodClauseOutputEnv = this.env;
        switch (tree.token) {
            case REQUIRES:
            case ENSURES:
            case DIVERGES:
            case WHEN:
            case RETURNS:
                attribExpr(tree.expression, env, syms.booleanType);
                break;
                
            case CONTINUES:
            case BREAKS:
                // FIXME - what about the label
                attribExpr(tree.expression, env, syms.booleanType);
                break;
            
            case CALLABLE:
                // FIXME - should be implemented somewhere else
                break;
                
            default:
                log.error(tree.pos,"jml.unknown.construct",tree.token.internedName(),"JmlAttr.visitJmlMethodClauseExpr");
                break;
        }
        savedMethodClauseOutputEnv = null;
    }
    
    public void visitJmlMethodClauseCallable(JmlMethodClauseCallable tree) {
        if (tree.methodSignatures != null) {
            for (JmlMethodSig sig : tree.methodSignatures) {
                visitJmlMethodSig(sig);
            }
        }
    }

    /** This is an implementation that does the type attribution for 
     * duration, working_space, measured_by clauses
     * (clauses that have an expression and an optional predicate)
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
    @Override
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals tree) {
        
        if (tree.vardef.name == null) {
            tree.vardef.name = names.fromString(Strings.syntheticExceptionID);
        }
        
        Env<AttrContext> localEnv = localEnv(env,tree);

        // FIXME - is this assignment needed? Why not elsewhere?
        tree.vardef.vartype.type = attribTree(tree.vardef.vartype, localEnv, new ResultInfo(TYP, syms.exceptionType));
        attribTree(tree.vardef, localEnv, new ResultInfo(VAR, syms.exceptionType));

        Type prev = currentExceptionType;
        currentExceptionType = tree.vardef.vartype.type;
        try {
            attribExpr(tree.expression, localEnv, syms.booleanType);
        } finally {
            currentExceptionType = prev;
        }
    }
    
    /** This is an implementation that does the type attribution for 
     * a signals_only method specification clause
     * @param tree the method specification clause being attributed
     */
    @Override
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly tree) {
        for (JCExpression e: tree.list) {
            e.type = attribTree(e, env, new ResultInfo(TYP, syms.exceptionType));
        }
        // FIXME - need to compare these to the exceptions in the method declaration
    }
    
    protected void checkIfLocal(JCTree e) {
        if (e instanceof JCIdent && ((JCIdent)e).sym.owner instanceof MethodSymbol) {
            log.error(e,"jml.no.formals.in.assignable",e.toString());
        }
    }
    
    /** This is an implementation that does the type attribution for 
     * assignable/accessible/captures method specification clauses
     * @param tree the method specification clause being attributed
     */
    @Override
    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef tree) {
        for (JCTree e: tree.list) {
            attribExpr(e, env, Type.noType);
            checkIfLocal(e);
        }
        // FIXME - check the result
    }

    // FIXME - need JmlAttr implementation for CALLABLE clauses
    
    @Override
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        for (JCTree t: that.list) {
            attribExpr(t,env,Type.noType);
        }
        if (!postClauses.contains(currentClauseType)) {
            log.error(that.pos+1, "jml.misplaced.token", that.token.internedName(), currentClauseType == null ? "jml declaration" : currentClauseType.internedName());
        }
        result = check(that, syms.booleanType, VAL, resultInfo);
    }

    /** The JML modifiers allowed for a specification case */
    JmlTokenKind[] specCaseAllowed = new JmlTokenKind[]{};
    
    ListBuffer<JmlMethodClause> toRemove = null;
    
    /** This implements the visiting of a JmlSpecificationCase, initiating
     * a visit of each clause in the case, setting the currentClauseType field
     * before visiting each one.
     */
    
    public void visitJmlSpecificationCase(JmlSpecificationCase tree) {
        JavaFileObject old = log.useSource(tree.sourcefile);
        Env<AttrContext> localEnv = null;
        Env<AttrContext> prevEnv = env;
        JmlTokenKind prevClauseType = currentClauseType; // Just in case there is recursion
        long prevVisibility = jmlVisibility;
        try {
            if (tree.modifiers != null) {
                attribAnnotationTypes(tree.modifiers.annotations,env);
                if (tree.token == null) {
                    if (!utils.hasNone(tree.modifiers)) {
                        log.error(tree.pos(),"jml.no.mods.lightweight");
                    }
                } else {
                    long diffs = utils.hasOnly(tree.modifiers,Flags.AccessFlags);
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
            if (enclosingMethodEnv != null) {   // FIXME - change these back to dup()?
                localEnv = localEnv(env,enclosingMethodEnv.tree);
            } else { // For initializer declarations with specs
                localEnv = localEnv(env,enclosingClassEnv.tree);
            }
            env = localEnv;

            if (tree.token == null) {
                if (enclosingMethodEnv != null)
                    jmlVisibility = enclosingMethodEnv.enclMethod.mods.flags & Flags.AccessFlags;
                else 
                    jmlVisibility = enclosingClassEnv.enclClass.mods.flags & Flags.AccessFlags; // FIXME - should this be the visibilty of the initializer block?
            } else {
                jmlVisibility = tree.modifiers == null ? 0 : (tree.modifiers.flags & Flags.AccessFlags);
            }
            
            if (tree.clauses != null) {
                toRemove = null;
                for (JmlMethodClause c: tree.clauses) {
                    currentClauseType = c.token;
                    c.accept(this);
                }
                if (toRemove != null) {
                    for (JmlMethodClause mc: toRemove) {
                        tree.clauses = Utils.remove(tree.clauses, mc);
                    }
                    toRemove = null;
                }
            }
            if (tree.block != null) {
                // model program
                boolean oldPure = pureEnvironment;
                pureEnvironment = false;
                try {
                    tree.block.accept(this);
                } finally {
                    pureEnvironment = oldPure;
                }
                
            } 
            
        } finally {
            env = prevEnv;
            jmlVisibility = prevVisibility;
            if (localEnv != null) localEnv.info.scope.leave();
            currentClauseType = prevClauseType;
            log.useSource(old);
        }
    }
    
    /** Visits a JmlMethodSpecs by visiting each of its JmlSpecificationCases */
    
    public void visitJmlMethodSpecs(JmlMethodSpecs tree) {
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        for (JmlSpecificationCase c: tree.cases) {
            // This check is put here rather than inside visitJmlSpecificationCase
            // so it is not checked for specification cases that are part of a 
            // refining statement
            if (c.modifiers != null && tree.decl != null) { // tree.decl is null for initializers and refining statements
                long methodMod = enclosingMethodEnv.enclMethod.mods.flags & Flags.AccessFlags;
                long caseMod = c.modifiers.flags & Flags.AccessFlags;
                if (methodMod == 0 && enclosingMethodEnv.enclClass.sym.isInterface()) methodMod = Flags.PUBLIC;
                if (methodMod != caseMod && c.token != null) {
                    if (caseMod == Flags.PUBLIC ||
                            methodMod == Flags.PRIVATE ||
                            (caseMod == Flags.PROTECTED && methodMod == 0)) {
                        DiagnosticPosition p = c.modifiers.pos();
                        if (p.getPreferredPosition() == Position.NOPOS) p = tree.pos();
                        if (!enclosingMethodEnv.enclMethod.name.toString().equals("clone")) {
                            JavaFileObject prevsource = log.useSource(c.source());
                            log.warning(p,"jml.no.point.to.more.visibility");
                            log.useSource(prevsource);
                        }
                    }
                }
            }

            c.accept(this);
        }
        pureEnvironment = prev;
    }
    
    // These are the annotation types in which \pre and \old with a label can be used (e.g. assert)
    private EnumSet<JmlTokenKind> preTokens = JmlTokenKind.methodStatementTokens;
    
    // These are the annotation, method and type spec clause types in which \old without a label can be used
    private EnumSet<JmlTokenKind> oldNoLabelTokens = JmlTokenKind.methodStatementTokens;
    {
        oldNoLabelTokens = oldNoLabelTokens.clone();
        oldNoLabelTokens.addAll(EnumSet.of(ENSURES,SIGNALS,CONSTRAINT,DURATION,WORKING_SPACE,JMLDECL)); // FIXME - double check JMLDECL
    }
    
    // FIXME - limit these to a method body
    Map<Name,Env<AttrContext>> labelEnvs = new HashMap<Name,Env<AttrContext>>();
    
    public void visitLabelled(JCLabeledStatement tree) {
        Env<AttrContext> labelenv = env.dup(tree,env.info.dupUnshared());
        labelEnvs.put(tree.label,labelenv);
        super.visitLabelled(tree);
    }
    
    protected Name currentEnvLabel = null;

    public void visitJmlMethodInvocation(JmlMethodInvocation tree) {
        JmlTokenKind token = tree.token;
        if (tree.typeargs != null && tree.typeargs.size() != 0) {
            // At present the parser cannot produce anything with typeargs, but just in case
            // one squeaks through by some means or another
            log.error(tree.typeargs.head.pos(),"jml.no.typeargs.for.fcn",token.internedName());
        }
        
//        Env<AttrContext> localEnv = env.dup(tree, env.info.dup( env.info.scope.dup()));
//        // This local environment is for good measure.  It is normally needed as
//        // a scope to hold type arguments.  But there are not any of those for
//        // these JML methods, so it should not technically be needed.
        Env<AttrContext> localEnv = env;
        ListBuffer<Type> argtypesBuf = new ListBuffer<Type>();
        boolean jmlstrict = JmlOption.isOption(context, JmlOption.STRICT);
        
        Type t = null;
        int n;
        switch (token) {
            case BSPAST:
            case BSOLD:
            case BSPRE:
                // The argument can be a JML spec-expression
                // Expect one argument, result type is the same type
                Name savedLabel = currentEnvLabel;
                n = tree.args.size();
                if (!(n == 1 || (token != JmlTokenKind.BSPRE && n == 2))) {
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
                    if (currentClauseType == null) {
                        // OK
                    } else if (!oldNoLabelTokens.contains(currentClauseType)) {
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
                    if (tr.getTag() != JCTree.Tag.IDENT) {
                        log.error(tr.pos(),"jml.bad.label");
                    } else {
                        label = ((JCTree.JCIdent)tr).getName();
                    }
                }
                
                // FIXME - is it possible for a variable to have a different type at a previous label?
                
                // label == empty ==> pre state; label == null ==> current state
                currentEnvLabel = label == null ? names.empty : label;
                if (n == 0 || t == syms.errType) {
                    t = syms.errType;
                } else if (env.enclMethod == null) { // FIXME - what about types declared within methods
                    // In an type clause
                    attribExpr(tree.args.get(0), localEnv, Type.noType);
                    attribTypes(tree.typeargs, localEnv);
                    t = tree.args.get(0).type;
                } else {
                    // in a method clause
                    Env<AttrContext> oldenv = savedMethodClauseOutputEnv;
                    if (oldenv == null) oldenv = enclosingMethodEnv;
                    if (label != null) {
                        Env<AttrContext> labelenv = labelEnvs.get(label);
                        if (labelenv == null) {
                            Log.instance(context).error(tree.args.get(1).pos(),"jml.unknown.label",label);
                        } else {
                            oldenv = labelenv;
                        }
                    }
                    if (enclosingMethodEnv == null) {
                        // Just a precaution
                        Log.instance(context).error("jml.internal","Unsupported context for pre-state reference (anonymous class? initializer block?).  Please report the program.");
                        oldenv = env;
                        //
                    }
                    
                    Env<AttrContext> qOldEnv = oldenv;
                    for (JmlQuantifiedExpr qexpr: quantifiedExprs) {

                        qOldEnv = envForExpr(qexpr,qOldEnv);
                        Scope enclScope = enter.enterScope(qOldEnv);

                        for (JCVariableDecl decl: qexpr.decls) {

                            // FIXME - do we need to do these checks?
//                            if (chk.checkUnique(tree.pos(), v, enclScope)) {
//                                chk.checkTransparentVar(tree.pos(), v, enclScope);
                                enclScope.enter(decl.sym);
//                            }
                        }
                    }
                    attribExpr(tree.args.get(0), qOldEnv, Type.noType);
                    attribTypes(tree.typeargs, qOldEnv);
                    t = tree.args.get(0).type;
                    Scope scope = qOldEnv.info.scope;
                    for (JmlQuantifiedExpr qexpr: quantifiedExprs) {
                        scope = scope.leave();
                    }
                }
                result = check(tree, t, VAL, resultInfo);
                currentEnvLabel = savedLabel;
                break;
                
            case BSMAX:
                // Expect one argument of type JMLSetType, result type Lock
                // FIXME - this should be one argument of type JMLObjectSet, result type is Object
                // The argument expression may contain JML constructs
                attribArgs(VAL, tree.args, localEnv, argtypesBuf);  // We can't send in Lock as the requested type because Types does not know what to do with it - FIXME: perhaps make a JmlTypes that can handle the new primitives
                //attribTypes(tree.typeargs, localEnv);
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
                result = check(tree, t, VAL, resultInfo);
                break;

            case BSTYPEOF :
                // Expect one argument of any type, result type \TYPE
                // The argument expression may contain JML constructs
                attribArgs(VAL, tree.args, localEnv, argtypesBuf);
                //attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                }
                t = jmltypes.TYPE;
                result = check(tree, t, VAL, resultInfo);
                break;

//            case BSNOTMODIFIED :
//                // Expect any number of arguments of any type, result type is boolean
//                // Can be used where an \old is used
//                // FIXME - JML wants this to be a store-ref list
//                if (!oldNoLabelTokens.contains(currentClauseType)) {
//                    log.error(tree.pos+1, "jml.misplaced.old", "\\not_modified token", currentClauseType.internedName());
//                    t = syms.errType;
//                }
//                attribArgs(tree.args, localEnv);
//                attribTypes(tree.typeargs, localEnv);
//                n = tree.args.size();
//                t = syms.booleanType;
//                result = check(tree, t, VAL, resultInfo);
//                break;

            case BSNONNULLELEMENTS :
                // The argument can be a JML spec-expression
                // Expect any number of arguments of any array type, result type is boolean
            {
                n = tree.args.size();
                if (n != 1 && jmlstrict) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                }

                for (JCExpression arg: tree.args) {
                    Type argtype = attribExpr(arg, localEnv);
                    if (!(argtype instanceof Type.ArrayType) && !argtype.isErroneous()) {
                        log.error(arg.pos(),"jml.arraytype.required",token.internedName(),argtype.toString(),arg.toString());
                    }
                }
                result = check(tree, syms.booleanType, VAL, resultInfo);
                break;
            }   
                
                
                


            case BSISINITIALIZED :
                // The argument is a type that is a reference type; the result is boolean
                // The argument may contain JML constructs
            {
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                }
                for (JCExpression arg: tree.args) {
                    Type argtype = attribExpr(arg, localEnv);
                    if (!argtype.isNullOrReference() && !argtype.isErroneous()) {
                        log.error(arg.pos(),"jml.ref.arg.required",token.internedName());
                    }
                }
                result = check(tree, syms.booleanType, VAL, resultInfo);
                break;
            }

            case BSTYPELC :
                // Takes one argument which is a type (not an expression); the result is of type \TYPE
                // The argument may contain JML constructs
                attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree,"jml.wrong.number.args",token.internedName(),1,n);
                }
                if (n > 0) {
                    JCExpression arg = tree.args.get(0);
                    attribTree(arg, localEnv, new ResultInfo(TYP, Type.noType));
                    if (!tree.javaType && arg.type.tsym.getTypeParameters().size() > 0 &&
                         !arg.type.isParameterized()) {
                        log.error(tree,"jml.invalid.erasedtype",JmlPretty.write(arg));
                    }
                    if (!tree.javaType) checkForWildcards(arg,arg);
                }
                t = jmltypes.TYPE;
                if (tree.javaType) t = syms.classType;
                Type saved = check(tree, t, VAL, resultInfo);
                addTodo(utilsClass);
                result = saved;
                break;

            case BSDISTINCT :
                // The result is boolean.
                // Case 1) All types are reference types
                // Case 2) Some or all are primitive - all must be convertible to
                // a common primitive type, including through unboxing
                attribArgs(VAL, tree.args, localEnv, argtypesBuf); 
                //attribTypes(tree.typeargs, localEnv);
                boolean anyPrimitive = false;
                Type maxPrimitiveType = null;
                for (JCExpression arg : tree.args) {
                    Type tt = arg.type;
                    if (tt.isErroneous()) continue;
                    if (tt.isPrimitive()) {
                        anyPrimitive = true;
                    }
                }
                if (anyPrimitive) for (JCExpression arg : tree.args) {
                    Type tt = arg.type;
                    if (tt.isErroneous()) { continue; }
                    if (!tt.isPrimitive()) tt = types.unboxedType(tt);
                    if (tt.getTag() == TypeTag.VOID) {
                        // FIXME -error
                    } else if (maxPrimitiveType == null) {
                        maxPrimitiveType = tt;
                    } else if (types.isConvertible(tt,maxPrimitiveType)) {
                        // OK
                    } else if (types.isConvertible(maxPrimitiveType, tt)) {
                        maxPrimitiveType = tt;
                    } else {
                        // FIXME - error
                    }
                }
                if (anyPrimitive) {
                    for (JCExpression arg : tree.args) {
                        Type tt = arg.type;
                        if (tt.isErroneous()) continue;
                        if (!tt.isPrimitive()) tt = types.unboxedType(tt);
                        if (!types.isConvertible(tt,maxPrimitiveType)) {
                            // FIXME - ERROR
                        }
                    }
                }
                result = check(tree, syms.booleanType, VAL, resultInfo);
                break;

            case BSFRESH :
                // The arguments can be JML spec-expressions
                // The arguments can be any reference type; the result is boolean
                attribArgs(VAL, tree.args, localEnv, argtypesBuf); 
                //attribTypes(tree.typeargs, localEnv);
                for (int i=0; i<tree.args.size(); i++) {
                    JCExpression arg = tree.args.get(i);
                    if (arg.type.isPrimitive()) {
                        log.error(arg.pos(),"jml.ref.arg.required",token.internedName());
                    }
                }
                if (!postClauses.contains(currentClauseType)) {
                    // The +1 is to fool the error reporting mechanism into 
                    // allowing other error reports about the same token
                    log.error(tree.pos+1, "jml.misplaced.token", token.internedName(), currentClauseType == null ? "jml declaration" : currentClauseType.internedName());
                }
                result = check(tree, syms.booleanType, VAL, resultInfo);
                break;

            case BSREACH :
                // The argument can be a JML spec-expressions
                // Expects one argument of reference type; result is of type JMLObjectSet
                attribArgs(VAL, tree.args, localEnv, argtypesBuf);
                //attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                } else {
                    JCExpression arg = tree.args.get(0);
                    if (arg.type.isPrimitive()) {
                        log.error(arg.pos(),"jml.ref.arg.required",token.internedName());
                    }
                }
                result = check(tree, JMLSetType, VAL, resultInfo);  // FXME - needs to be a settype of Object
                break;
                
            case BSINVARIANTFOR :
                // The argument can be a JML spec-expression
                // Expects one argument of reference type or a typename; result is of type boolean
            	
                n = tree.args.size();
                if (n != 1 && jmlstrict) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                }

                for (JCExpression arg: tree.args) {
                    attribTree(arg, localEnv, new ResultInfo(TYP|VAR, Infer.anyPoly));

                    if (arg.type.isPrimitive()) {
                        log.error(arg.pos(),"jml.ref.arg.required",token.internedName());
                    } else if (jmlstrict && treeutils.isATypeTree(arg)) {
                        log.error(arg.pos(),"jml.ref.arg.required",token.internedName());
                    }
                }
                result = check(tree, syms.booleanType, VAL, resultInfo);
                break;


            case BSDURATION :
            case BSWORKINGSPACE :
                // The argument must be a Java expression
                // Expects one argument that is an arbitrary expression; result is of type long
                // Note: The JML reference manual puts constraints on the form of the expression; those seem to be unneeded
                // Note also: the argument is not actually evaluated (but needs to be evaluatable), 
                //   thus it may only contain Java constructs  (FIXME - there is no check on that)
                attribArgs(VAL, tree.args, localEnv, argtypesBuf); 
                //attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                }
                result = check(tree, syms.longType, VAL, resultInfo);
                break;

            case BSSPACE :
                // The argument may be a JML spec-expression
                // Expects one argument of reference type; result is of type long
                attribArgs(VAL, tree.args, localEnv, argtypesBuf);
                //attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                }
                // FIXME - there is no check that the argument is of reference type - can't this apply to primitives as well?
                result = check(tree, syms.longType, VAL, resultInfo);
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
                attribArgs(VAL, tree.args, localEnv, argtypesBuf);
                //attribTypes(tree.typeargs, localEnv);
                n = tree.args.size();
                if (n != 1) {
                    log.error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
                }
                if (n == 0) {
                    t = syms.errType;
                } else {
                    t = tree.args.get(0).type;
                }
                result = check(tree, t, VAL, resultInfo);
                break;
                 
            default:
                ExpressionExtension ext = Extensions.instance(context).find(tree.pos,token,true);
                Type ttt = ext.typecheck(this,tree,localEnv);
                result = check(tree, ttt, VAL, resultInfo);
                break;

            case BSONLYCALLED: // FIXME - needs implementation
            case BSONLYASSIGNED: // FIXME - needs implementation
            case BSONLYACCESSED: // FIXME - needs implementation
            case BSONLYCAPTURED: // FIXME - needs implementation
            case BSNOTASSIGNED: // FIXME - needs implementation
            case BSNOTMODIFIED: // FIXME - needs implementation
                log.error(tree.pos,"jml.unknown.construct",token.internedName(),"JmlAttr.visitApply");
                result = tree.type = syms.errType;
                break;
                

                
        }
    }
    
    protected void checkForWildcards(JCExpression e, JCExpression arg) {
        if (e instanceof JCWildcard) {
            log.error(e,"jml.no.wildcards.in.type",JmlPretty.write(arg));
        }
        if (!(e instanceof JCTypeApply)) return;
        JCTypeApply t = (JCTypeApply)e;
        for (JCExpression ee: t.arguments) {
            checkForWildcards(ee,arg);
        }
    }
    
    /** This is overridden to check that if we are in a pure environment,
     * the method is declared pure.  Also to make sure any specs are attributed.
     */
    @Override
    public void visitApply(JCTree.JCMethodInvocation tree) {
        // Otherwise this is just a Java method application
        super.visitApply(tree);
        if (result.isErroneous()) return;
        Type savedResult = result;
        MethodSymbol msym = null;
        JCExpression m = tree.meth;
        Symbol sym = (m instanceof JCIdent ? ((JCIdent)m).sym : m instanceof JCFieldAccess ? ((JCFieldAccess)m).sym : null);
        if (sym instanceof MethodSymbol) msym = (MethodSymbol)sym;
        if (pureEnvironment && tree.meth.type != null && tree.meth.type.getTag() != TypeTag.ERROR) {
            // Check that the method being called is pure
            if (msym != null) {
                boolean isPure = isPureMethod(msym);
                if (!isPure && JmlOption.isOption(context,JmlOption.PURITYCHECK)) {
                    log.warning(tree.pos,"jml.non.pure.method",utils.qualifiedMethodSig(msym));
                }
                if (isPure && currentClauseType == JmlTokenKind.INVARIANT
                        && msym.owner == enclosingClassEnv.enclClass.sym
                        && !isHelper(msym)
                        && utils.rac) {
                    log.warning(tree.pos,"jml.possibly.recursive.invariant",msym);
                }
            } else {
                // We are expecting that the expression that is the method
                // receiver (tree.meth) is either a JCIdent or a JCFieldAccess
                // If it is something else we end up here.
                if (sym == null) log.error("jml.internal.notsobad","Unexpected parse tree node for a method call in JmlAttr.visitApply: " + m.getClass());
                else log.error("jml.internal.notsobad","Unexpected symbol type for method expression in JmlAttr.visitApply: ", sym.getClass());
            }
            // FIXME - could be a super or this call
        }
        if (msym != null) checkSecretCallable(tree,msym);
        result = savedResult;
    }

    /** This handles JML statements such as assert and assume and unreachable and hence_by. */
    public void visitJmlStatementExpr(JmlTree.JmlStatementExpr tree) {
        if (tree.token == JmlTokenKind.COMMENT) { result = null; return; }
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        JmlTokenKind prevClauseType = currentClauseType;
        currentClauseType = tree.token;
        // unreachable statements have a null expression
        if (tree.expression != null) attribExpr(tree.expression,env,syms.booleanType);
        if (tree.optionalExpression != null) attribExpr(tree.optionalExpression,env,Type.noType);
        currentClauseType = prevClauseType;
        pureEnvironment = prev;
        jmlresolve.setAllowJML(prevAllowJML);
        result = null; // No type returned
    }
    
    public void visitLetExpr(LetExpr tree) { 
        if (env.info.scope.owner.kind == TYP) {
            // Block is a static or instance initializer;
            // let the owner of the environment be a freshly
            // created BLOCK-method.
            Env<AttrContext> localEnv =
                env.dup(tree, env.info.dup(env.info.scope.dupUnshared()));
            localEnv.info.scope.owner =
                new MethodSymbol(BLOCK, names.empty, null, // FIXME - or'd other flags with BLOCK
                                 env.info.scope.owner);
            //if ((tree.mods.flags & STATIC) != 0) localEnv.info.staticLevel++;

            attribStats(tree.defs,localEnv);
            attribExpr(tree.expr,localEnv,Type.noType);
            Type resultType = tree.expr.type;
            if (resultType.constValue() != null) resultType = resultType.constType(null);
            result = check(tree, resultType, VAL, resultInfo);

        } else {
            // Create a new local environment with a local scope.
            Env<AttrContext> localEnv =
                env.dup(tree, env.info.dup(env.info.scope.dup()));

            attribStats(tree.defs,localEnv);
            attribExpr(tree.expr,localEnv,Type.noType);
            Type resultType = tree.expr.type;
            if (resultType.constValue() != null) resultType = resultType.constType(null);
            result = check(tree, resultType, VAL, resultInfo);

            localEnv.info.scope.leave();
        }
        
    }


    /** This handles JML statements such as assert and assume and unreachable and hence_by. */
    public void visitJmlStatementHavoc(JmlTree.JmlStatementHavoc tree) {
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        if (tree.storerefs != null) {
            for (JCTree e: tree.storerefs) {
                attribExpr(e, env, Type.noType);
            }
        }
        pureEnvironment = prev;
        jmlresolve.setAllowJML(prevAllowJML);
        result = null; // No type returned
    }

    boolean savedSpecOK = false; // FIXME - never read
    
    public void attribLoopSpecs(List<JmlTree.JmlStatementLoop> loopSpecs, Env<AttrContext> loopEnv) {
        savedSpecOK = false;
        if (loopSpecs == null || loopSpecs.isEmpty()) return;
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        boolean prev = pureEnvironment;
        pureEnvironment = true;
        for (JmlTree.JmlStatementLoop tree: loopSpecs) {
            JmlTokenKind prevClauseType = currentClauseType;
            currentClauseType = tree.token;
            if (tree.token == JmlTokenKind.LOOP_INVARIANT) {
                attribExpr(tree.expression,loopEnv,syms.booleanType);
            } else {
                attribExpr(tree.expression,loopEnv,syms.longType);  // FIXME - what type to use
            }
            currentClauseType = prevClauseType;
        }
        pureEnvironment = prev;
        jmlresolve.setAllowJML(prevAllowJML);
    }
    
    
    /** This handles JML statements that give method-type specs for method body statements. */
    public void visitJmlStatementSpec(JmlTree.JmlStatementSpec tree) {
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        JmlTokenKind prevClauseType = currentClauseType;
        currentClauseType = null;
        if (tree.statementSpecs != null) attribStat(tree.statementSpecs,env);
        currentClauseType = prevClauseType;
        jmlresolve.setAllowJML(prevAllowJML);
    }
    
    /** This handles JML declarations (method and ghost fields, methods, types) */
    public void visitJmlStatementDecls(JmlTree.JmlStatementDecls tree) {
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        JmlTokenKind prevClauseType = currentClauseType;
        currentClauseType = tree.token;
        for (JCTree.JCStatement s : tree.list) {
            attribStat(s,env);
        }
        currentClauseType = prevClauseType;
        jmlresolve.setAllowJML(prevAllowJML);
    }
    
    /** This handles JML statements such as set and debug */
    public void visitJmlStatement(JmlTree.JmlStatement tree) {  // FIXME - need to test appropriately for purity
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        JmlTokenKind prevClauseType = currentClauseType;
        currentClauseType = tree.token;
        if (tree.statement != null) attribStat(tree.statement,env);
        currentClauseType = prevClauseType;
        jmlresolve.setAllowJML(prevAllowJML);
    }

    /** This handles JML primitive types */
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        JmlType type = that.token == JmlTokenKind.BSTYPEUC ? jmltypes.TYPE :
            that.token == JmlTokenKind.BSBIGINT ? jmltypes.BIGINT :
            that.token == JmlTokenKind.BSREAL ? jmltypes.REAL :
                    null;
        if (type == null) {
            result = syms.errType;
            log.error(that.pos,"jml.unknown.type.token",that.token.internedName(),"JmlAttr.visitJmlPrimitiveTypeTree");
            return;
        }
        that.type = type;
        that.repType = jmltypes.repType(that.pos(), type);
        attribType(that.repType,env);
        result = type;
//        if (utils.rac) {
//            result = type.repType.type;
//            that.type = result;
//        }
    }
    
    /** This set holds method clause types in which the \result token may appear 
     * (and \not_assigned \only_assigned \only_captured \only_accessible \not_modified) */
    public EnumSet<JmlTokenKind> resultClauses = EnumSet.of(ENSURES,DURATION,WORKING_SPACE);
    
    /** This set holds method clause types in which the \exception token may appear  */
    public EnumSet<JmlTokenKind> exceptionClauses = EnumSet.of(SIGNALS);
    
    /** This set holds method clause types in which the these tokens may appear:
     *  \not_assigned \only_assigned \only_captured \only_accessible \not_modified */
    public EnumSet<JmlTokenKind> postClauses = EnumSet.of(ENSURES,SIGNALS,DURATION,WORKING_SPACE,ASSERT,ASSUME);

    /** This handles expression constructs with no argument list such as \\result */
    public void visitJmlSingleton(JmlSingleton that) {
        JmlTokenKind jt = that.token;
        Type t = syms.errType;
        switch (jt) {
               
            case BSLOCKSET:
                t = JMLSetType;
                break;
                
            case BSINDEX:
                t = syms.intType;
                if (loopStack.isEmpty()) {
                    log.error(that.pos,"jml.outofscope",jt.internedName());
                } else {
                    that.info = loopStack.get(0).sym;
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
                JCTree.JCMethodDecl md = enclosingMethodEnv.enclMethod;
                JCTree res = md.getReturnType();
                if (res == null || (!res.type.isErroneous() && types.isSameType(res.type,syms.voidType))) {
                    log.error(that.pos+1, "jml.void.result");
                    t = syms.errType;
                } else {
                    t = res.type;
                }
                if (currentEnvLabel != null) {
                    log.error(that.pos, "jml.no.result.in.old");
                }
                if (!resultClauses.contains(currentClauseType)) {
                    // The +1 is to fool the error reporting mechanism into 
                    // allowing other error reports about the same token
                    log.error(that.pos+1, "jml.misplaced.result", currentClauseType.internedName());
                    t = syms.errType;
                }
                break;
                
            case BSEXCEPTION:
                md = env.enclMethod;
                if (!exceptionClauses.contains(currentClauseType)) {
                    // The +1 is to fool the error reporting mechanism into 
                    // allowing other error reports about the same token
                    log.error(that.pos+1, "jml.misplaced.exception", currentClauseType.internedName());
                    t = syms.errType;
                } else {
                    t = currentExceptionType;
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
                ExpressionExtension ext = Extensions.instance(context).find(that.pos,jt,true);
                Type ttt = ext.typecheck(this,that,env);
                result = check(that, ttt, VAL, resultInfo);
                break;

//            default:
//                t = syms.errType;
//                log.error(that.pos,"jml.unknown.type.token",that.token.internedName(),"JmlAttr.visitJmlSingleton");
//                break;
        }
        result = check(that, t, VAL, resultInfo);
    }
    
//    public void visitJmlFunction(JmlFunction that) {
//        // Actually, I don't think this gets called.  It would get called through
//        // visitApply.
//        result = that.type = Type.noType;
//    }
    

    public void visitJmlImport(JmlImport that) {
        visitImport(that);
        // FIXME - ignoring model
    }
    
    public void visitJmlBlock(JmlBlock that) {
        visitBlock(that);
        if (that.cases != null) {
            boolean isStatic = (that.flags & Flags.STATIC) != 0;
            if (isStatic) env.info.staticLevel++;
            try {
                that.cases.accept(this);
            } finally {
                if (isStatic) env.info.staticLevel--;
            }
        }
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
                Type t = that.lhs.type;
                boolean errorAlready = false;
                if (t.isErroneous()) errorAlready = true;
                else if (!t.equals(jmltypes.TYPE)
                        && !t.tsym.equals(syms.classType.tsym)) {
                    errorAlready = true;
                    log.error(that.lhs.pos(),"jml.subtype.arguments",that.lhs.type);
                }
                attribExpr(that.rhs,env,Type.noType);
                Type tt = that.rhs.type;
                if (tt.isErroneous()) errorAlready = true;
                else if (!tt.equals(jmltypes.TYPE)
                        && !tt.tsym.equals(syms.classType.tsym)) {
                    errorAlready = true;
                    log.error(that.rhs.pos(),"jml.subtype.arguments",that.rhs.type);
                }
                if ((t == jmltypes.TYPE) != (tt == jmltypes.TYPE) && !errorAlready) {
                    log.error(that.rhs.pos(),"jml.subtype.arguments.same",that.rhs.type);
                }
                if (t != jmltypes.TYPE) that.op = JmlTokenKind.JSUBTYPE_OF; // Java subtyping
                
                result = syms.booleanType;
                break;
                
            default:
                log.error(that.pos(),"jml.unknown.operator",that.op.internedName(),"JmlAttr");
                break;
        }
        result = check(that, result, VAL, resultInfo);
    }
    
    /** 
     */
    public void visitJmlLabeledStatement(JmlLabeledStatement that) {
        visitLabelled(that);
    }
    
    /** Attributes a LBL expression.  Note that OpenJML allows an arbitrary
     * type LBL expression, e.g.  (\lbl A expr) .  This should report for the
     * label A the value of the expr, whatever its type.  For the standard
     * lblpos and lblneg expressions, the expr must be boolean.
     */
    public void visitJmlLblExpression(JmlLblExpression that) {
        if (!quantifiedExprs.isEmpty()) {
            // TODO _ COUld allow label expressions that do not contain quantified variables
            // FIXME - does not check set comprehension
            log.error(that.pos, "jml.lbl.in.quantified");
        }
        Type t = that.token == JmlTokenKind.BSLBLANY ? Type.noType : syms.booleanType;
        attribExpr(that.expression, env, t);
        Type resultType = that.expression.type;
        if (resultType.constValue() != null) resultType = resultType.constType(null);
        result = check(that, resultType, VAL, resultInfo);
    }
    
    /** This makes a new local environment that allows adding new declarations,
     * but can see out into the enclosing environment; you need to call leave()
     * when you leave this scope to get rid of new declarations.
     * An initEnv for example,
     * does not allow new declarations, and a raw new Scope or method env will not inherit 
     * the outer declarations.  This is used in particular by quantified
     * expressions and set comprehensions.
     * @param that the expression that occasions this new scope
     * @param env the current env
     * @return the new env
     */
    protected Env<AttrContext> envForExpr(JCTree tree,  Env<AttrContext> env) {
        Env<AttrContext> localEnv;
        // We can't use a delegated scope - they are used for variable initializers
        // and don;'t accept any new variable declarations.
        Scope sco = env.info.scope;
        while (sco instanceof Scope.DelegatedScope) sco = ((Scope.DelegatedScope)sco).next;

        long flags = 0L;
        if (sco.owner.kind != MTH) {
            // Block is a static or instance initializer;
            // let the owner of the environment be a freshly
            // created BLOCK-method.
            
            localEnv =
                env.dup(tree, env.info.dup(sco.dupUnshared()));
            localEnv.info.scope.owner =
                new MethodSymbol(flags | BLOCK, names.empty, null,
                                 sco.owner);
            if ((flags & STATIC) != 0) localEnv.info.staticLevel++;
        } else {
            // Create a new local environment with a local scope.
            localEnv =
                env.dup(tree, env.info.dup(sco.dup()));
            // For this kind of scope, you have to eventually call
            //             localEnv.info.scope.leave();
        }

//        // Previous
//        Scope sco = env.info.scope;
//        // DelegatedScopes are created for a variable initialization
//        while (sco instanceof Scope.DelegatedScope) sco = ((Scope.DelegatedScope)sco).next;
//        Scope sc = sco.dup(sco.owner);
//        //sc.next = env.info.scope; // FIXME-FIXES - should this go back in?
//        Env<AttrContext> localEnv = env.dup(that, env.info.dup(sc));
////        Env<AttrContext> localEnv = env.dup(that, env.info.dup(sc.dupUnshared()));
////        Env<AttrContext> localEnv =
////                env.dup(that, env.info.dup(env.info.scope.dupUnshared()));
        return localEnv;
    }
    
    protected java.util.List<JmlQuantifiedExpr> quantifiedExprs = new LinkedList<JmlQuantifiedExpr>();
    
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {

        Env<AttrContext> localEnv = envForExpr(that,env);
        
        boolean b = ((JmlMemberEnter)memberEnter).setInJml(true);
        for (JCVariableDecl decl: that.decls) {
            JCModifiers mods = decl.getModifiers();
            if (utils.hasOnly(mods,0)!=0) log.error(mods.pos,"jml.no.java.mods.allowed","quantified expression");
            attribAnnotationTypes(mods.annotations,env);
            allAllowed(mods.annotations, JmlTokenKind.typeModifiers, "quantified expression");
            utils.setExprLocal(mods);
//            if (utils.hasAny(mods,Flags.STATIC)) {
//                log.error(that.pos,
//                        "mod.not.allowed.here", asFlagSet(Flags.STATIC));
//            }
//            //if (Resolve.isStatic(env)) mods.flags |= Flags.STATIC;  // FIXME - this is needed for variables declared in quantified expressions in invariants - will need to ignore this when pretty printing?
            memberEnter.memberEnter(decl, localEnv);
            decl.type = decl.vartype.type; // FIXME not sure this is needed
        }
        ((JmlMemberEnter)memberEnter).setInJml(b);
        quantifiedExprs.add(that);
        
        try {
            
        if (that.range != null) attribExpr(that.range, localEnv, syms.booleanType);

        Type resultType = syms.errType;
        switch (that.op) {
            case BSEXISTS:
            case BSFORALL:
                attribExpr(that.value, localEnv, syms.booleanType);
                resultType = syms.booleanType;
                break;
                
            case BSNUMOF:
                attribExpr(that.value, localEnv, syms.booleanType);
                resultType = syms.intType; // FIXME - int? long? bigint?
                break;
                
            case BSMAX:
            case BSMIN:
                attribExpr(that.value, localEnv, Type.noType); // FIXME - int? long? numeric? bigint? double?
                resultType = that.value.type;
                break;

            case BSSUM:
            case BSPRODUCT:
                attribExpr(that.value, localEnv, syms.longType); // FIXME - int? long? numeric? bigint? double?
                resultType = that.value.type;
                break;
                
            default:
                log.error(that.pos(),"jml.unknown.construct",that.op.internedName(),"JmlAttr.visitJmlQuantifiedExpr");
                break;
        }
        result = check(that, resultType, VAL, resultInfo);
        
        if (utils.rac) {
            if (that.racexpr == null) createRacExpr(that,localEnv,resultType);
//            if (that.racexpr == null) {
//                System.out.println("NO QUANT");
//            }
        }
        } finally {
            quantifiedExprs.remove(quantifiedExprs.size()-1);
            localEnv.info.scope.leave();
        }
        return;
    }
    
    public boolean implementationAllowed() {
        return implementationAllowed;
    }

    
    public void createRacExpr(JmlQuantifiedExpr q, Env<AttrContext> localEnv, Type resultType) {
        /* The purpose of this method is to create a fully-qualified executable expression to use
         * in RAC. This is tricky. The primary JML quantified expression has already been attributed.
         * That declarations and the range and value expressions are reused in creating this RAC equivalent.
         * The problematic aspect is that one cannot attribute an expression twice and there is no check
         * to prevent re-attribution; re-attributing simple expressions causes no trouble, but the
         * reattribution logic can complain about, for example, duplicate declarations. Problems particularly
         * arise if the value subexpression of the quantified expression includes a a nested quantified
         * expression or method calls.
         * 
         * So we construct our RAC expression carefully distinguishing between new portions and already
         * attributed portions.
         * 
         * The general approach is to replace a quantified expression that returns a value of type TT with 
         * an expression of this template:
         *       new org.jmlspecs.utils.Utils.ValueTT() { 
         *              public TT value(Object args...) { ... expression ... }
         *       }.value( ... args ... )
         * The complicated aspect of this formula is that any subexpressions that do not depend on the 
         * quantification variables have to be passed in as arguments. Also we want any new declarations
         * to be attributed by the regular attribution mechanism. So the general approach is to construct
         * the new part of the final expression (including new declarations), attribute it, and then
         * piece in the subexpressions from the JML quantified statement that were already attributed.
         * This approach means that the initial, unattributed expression has some holes in it that need
         * filling in later.
         */
        JCStatement update = null;
        List<JCExpression> argslist = null;
        JCNewArray newarray = null;

        try {
            // If there is no range, we will not try to execute the expression
            if (q.range == null) {
                return; // FIXME - is this executable?
            }
            
            JmlTree.Maker F = factory;
            Type restype = q.type; // Result type of the expression

            // Attributed statements that return true or false
            JCReturn rettrue = F.Return(treeutils.trueLit); //F.Literal(TypeTag.BOOLEAN, 1).setType(syms.booleanType));
            JCReturn retfalse = F.Return(treeutils.falseLit); //F.Literal(TypeTag.BOOLEAN, 0).setType(syms.booleanType));
            
            // First assemble the portions that need attribution
            
            // FIXME - include bigint support, real?
            // Construct the fully qualified name of the class holding the methods we'll use
            JCExpression constructName = F.Ident(names.fromString("org"));
            constructName = F.Select(constructName, names.fromString("jmlspecs"));
            constructName = F.Select(constructName, names.fromString("utils"));
            constructName = F.Select(constructName, names.fromString("Utils"));
            TypeTag tag = restype.getTag();
            String s = tag == TypeTag.INT ? "ValueInt" :
                tag == TypeTag.BOOLEAN ? "ValueBool" :
                    tag == TypeTag.LONG ? "ValueLong" :
                        tag == TypeTag.DOUBLE ? "ValueDouble" : 
                            tag == TypeTag.FLOAT ? "ValueFloat" : 
                                tag == TypeTag.SHORT ? "ValueShort" : 
                                    tag == TypeTag.BYTE ? "ValueByte" : 
                                        tag == TypeTag.CHAR ? "ValueChar" : 
                                            "ValueInt";
            Name className = names.fromString(s);
            constructName = F.Select(constructName, className);
            // methodName is e.g., depending on the result type,  org.jmlspecs.utils.Utils.ValueBool
            
           
            JCVariableDecl initialDecl = null;
            JCVariableDecl valueDecl = null;
            JCVariableDecl firstDecl = null;
            ListBuffer<JCStatement> bodyStats = new ListBuffer<JCStatement>();

            if (q.op == JmlTokenKind.BSFORALL || q.op == JmlTokenKind.BSEXISTS) { 
            } else if (q.op == JmlTokenKind.BSNUMOF) {
                initialDecl = F.VarDef(F.Modifiers(0), names.fromString("_count$$$"), F.Type(restype), F.Literal(restype.getTag(),0).setType(syms.intType));
            } else if (q.op == JmlTokenKind.BSSUM) {
                initialDecl = F.VarDef(F.Modifiers(0), names.fromString("_sum$$$"), F.Type(restype), F.Literal(restype.getTag(),0).setType(syms.intType));
            } else if (q.op == JmlTokenKind.BSPRODUCT) {
                initialDecl = F.VarDef(F.Modifiers(0), names.fromString("_prod$$$"), F.Type(restype), F.Literal(restype.getTag(),1).setType(syms.intType));
            } else if (q.op == JmlTokenKind.BSMAX || q.op == JmlTokenKind.BSMIN) {
                firstDecl = F.VarDef(F.Modifiers(0), names.fromString("_first$$$"), F.TypeIdent(TypeTag.BOOLEAN), F.Literal(TypeTag.BOOLEAN,1).setType(syms.booleanType));
                initialDecl = F.VarDef(F.Modifiers(0), names.fromString(q.op == JmlTokenKind.BSMIN ? "_min$$$" : "_max$$$"), F.Type(restype), F.Literal(restype.getTag(),0).setType(restype));
                valueDecl = F.VarDef(F.Modifiers(0), names.fromString("_val$$$"), F.Type(restype), null);
            } else {
                return;
            }
            if (initialDecl != null) bodyStats.add(initialDecl);
            if (valueDecl != null) bodyStats.add(valueDecl);
            if (firstDecl != null) bodyStats.add(firstDecl);

            JCBlock body = null;
            
            // We create a declaration of 'args' and add it to bodyStats so it is attributed,
            // because we need an identifier that references the args declaration to sprinkle 
            // through the rewritten range and value expressions.
            
            Name argsname = names.fromString("args");
            JCVariableDecl argsdef = F.VarDef(F.Modifiers(Flags.FINAL),argsname,
                    F.TypeArray(F.Type(syms.objectType)),null);
            JCIdent argsID = F.Ident(argsdef.name);
            // argsdef is:  Object[] args = null;
            

            // We'd like to reuse the declarations that are actually within the JML quantifier
            // expression. They are already attributed. But they seem to be attributed within
            // a different environment. For example, if they are used, complaints occur that they
            // are not final. Perhaps this can be worked around, but for now we create a
            // parallel set of declarations. These will be attributed here and the ids are 
            // passed into the RACCopy.copy calls below, so that each identifier node is rewritten
            // to refer to the new declaration.
            
            Map<Symbol,JCVariableDecl> newdecls = new HashMap<Symbol,JCVariableDecl>();
            Map<Symbol,JCIdent> newids = new HashMap<Symbol,JCIdent>();
            for (JCVariableDecl v: q.decls) {
                JCVariableDecl newdecl = F.VarDef(F.Modifiers(0), v.name, v.vartype, null);
                JCIdent id = F.Ident(v.name);
                newdecls.put(v.sym,newdecl);
                newids.put(v.sym, id);
            }
            
            // We need to figure out the iterations that will occur within the body of the
            // RAC expression. That involves some manipulation of the 
            
            List<JCVariableDecl> decls = q.decls;
            ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
            JCExpression newvalue = JmlAttr.RACCopy.copy(q.value,context,decls,args,argsID,newids);
            JCExpression newrange = JmlAttr.RACCopy.copy(q.range,context,decls,args,argsID,newids);

            java.util.List<Bound> bounds = new java.util.LinkedList<Bound>();
            JCExpression innerexpr = determineRacBounds(decls,newrange,bounds);
            if (innerexpr == null) {
                return;
            }
            
            // Here we create declarations that will be needed. These are 
            // unattributed; they are attributed below, and then the attributed
            // declarations are used in the second phase of RAC expression construction.
            
            for (Bound bound: bounds) {
                JCExpression vartype = bound.decl.vartype;
                Name indexname = bound.decl.name;
                String var = indexname.toString();
                JCVariableDecl indexdef = newdecls.get(bound.decl.sym);
                if (bound.decl.type.getTag() == TypeTag.BOOLEAN) {
                    indexdef.init = F.Literal(syms.booleanType.getTag(),0);
                } else if (bound.decl.type.getTag() == TypeTag.CLASS) {
                    // nothing
                } else {
                    Name loname = names.fromString("$$$lo_" + var);
                    Name hiname = names.fromString("$$$hi_" + var);
                    bound.lodef = F.VarDef(F.Modifiers(0),loname,vartype,null);
                    bound.hidef = F.VarDef(F.Modifiers(0),hiname,vartype,null);
                    bodyStats.add(bound.lodef);
                    bodyStats.add(bound.hidef);
                    //indexdef = F.VarDef(F.Modifiers(0), indexname, vartype, F.Ident(loname));
                    indexdef.init = F.Ident(loname);
                }
//                indexdef.sym = bound.decl.sym;
//                indexdef.type = bound.decl.sym.type;
                bound.indexdef = indexdef;
                bodyStats.add(indexdef);
                
            }
            
            // Back to expressions that will need attributing.

            JCStatement retStandin = F.Return(F.Literal(restype.getTag(), 0));
            bodyStats.add(retStandin);
            
            JCMethodDecl methodDecl = F.MethodDef(
                    F.Modifiers(Flags.PUBLIC), 
                    names.fromString("value"),
                    F.Type(restype), // result type
                    List.<JCTypeParameter>nil(), // type parameters
                    List.<JCVariableDecl>of(argsdef), // parameters
                    List.<JCExpression>nil(), // thrown types
                    body=F.Block(0,bodyStats.toList()), // body - more to be added later
                    null); // default value
            utils.setJML(methodDecl.mods);
            methodDecl.mods.annotations = methodDecl.mods.annotations.append(utils.tokenToAnnotationAST(JmlTokenKind.PURE,0,0)); // FIXME- fix positions?
            // methodDecl is (RT is the result type): public RT value(Object[] args) { ... decls... }
            
            List<JCTree> defs = List.<JCTree>of(methodDecl);
            JmlClassDecl classDecl = (JmlClassDecl)F.AnonymousClassDef(F.Modifiers(0), defs) ;
            classDecl.specsDecl = classDecl;
            classDecl.typeSpecs = new JmlSpecs.TypeSpecs(classDecl);
            classDecl.toplevel = ((JmlClassDecl)enclosingClassEnv.enclClass).toplevel;
            JCNewClass anon = F.NewClass(null,List.<JCExpression>nil(),constructName,List.<JCExpression>nil(),classDecl); 
//            anon.constructor = new MethodSymbol(0, names.init, syms.unknownType, syms.noSymbol);
//            anon.constructorType = syms.unknownType;
            // anon is, e.g., depending on the result type: 
            //               new org.jmlspecs.utils.Utils.ValueBool() { public boolean value(Object[] args) { ... decls... } }

            
            ListBuffer<JCExpression> standinargs = new ListBuffer<JCExpression>(); //F.TypeCast(Type.(syms.objectType), F.Literal(syms.objectType.tag,null));
//            for (JCExpression ex: argslist) {
//                JCLiteral lit = F.Literal(ex.type.tag,0);
//                standinargs.add(lit);
//            }
            standinargs.add(F.Literal(TypeTag.INT,0));

            newarray = F.NewArray(F.Type(syms.objectType),List.<JCExpression>nil(),standinargs.toList()); 
            JCExpression call = F.Apply(List.<JCExpression>nil(),F.Select(anon,names.fromString("value")),List.<JCExpression>of(newarray)); 
            // call is, e.g., depending on the result type:
            //      new org.jmlspecs.utils.Utils.ValueBool() { public boolean value(Object[] args) {} }.value(null,null);
            // Need to fill in (a) the body of the method and (b) the araguments of the call

            q.racexpr = call;
            
            q.racexpr = treeutils.makeZeroEquivalentLit(q.pos, q.type);

            // Attribute the unattributed expression
            
            attribExpr(q.racexpr, localEnv, resultType); // This puts in the default constructor, which the check call does not
            //check(that.racexpr,resultType, VAL, resultInfo); // But this has the right environment

            // Now form the body of the expression from pieces that are already attributed.
            
            argslist = args.toList();
            
            // argsID is aliased with nodes inside newvalue and newrange, so the following
            // assignments effectively attribute those nodes
            argsID.type = argsdef.type;
            argsID.sym = argsdef.sym;
            
            // Determine core computation
            // forall:  if (range) if (!value) return false;
            // exists:  if (range) if (value) return true;
            // numof:   if (range) if (value) ++count;
            // sum:     if (range) sum += value;
            
            JCStatement retStat;
            JCExpression cond = newvalue;
            if (q.op == JmlTokenKind.BSFORALL || q.op == JmlTokenKind.BSEXISTS) { 
                if (q.op == JmlTokenKind.BSFORALL) {
                    cond = treeutils.makeNot(cond.pos, cond);
//                    cond = F.Unary(JCTree.NOT, cond).setType(syms.booleanType); 
//                    ((JCUnary)cond).operator = rs.resolveUnaryOperator(cond.pos(), JCTree.NOT, env, newvalue.type);
                }
                update = F.If(cond, q.op == JmlTokenKind.BSFORALL? retfalse : rettrue , null);
                retStat = q.op == JmlTokenKind.BSFORALL ? rettrue : retfalse;
            } else if (q.op == JmlTokenKind.BSNUMOF) {
                JCIdent id = F.Ident(initialDecl.name);
                id.setType(initialDecl.type);
                id.sym = initialDecl.sym;
                JCUnary op = (JCUnary)treeutils.makeUnary(id.pos, JCTree.Tag.PREINC, id);
//                JCUnary op = F.Unary(JCTree.PREINC, id);
//                op.setType(initialDecl.type);
//                op.operator = rs.resolveUnaryOperator(op.pos(),op.getTag(),env,op.arg.type);
                update = F.If(cond, F.Exec(op) , null);
                retStat = F.Return(id); // Is it OK to reuse the node?
            } else if (q.op == JmlTokenKind.BSSUM) {
                JCIdent id = F.Ident(initialDecl.name);
                id.setType(initialDecl.type);
                id.sym = initialDecl.sym;
                JCAssignOp asn = treeutils.makeAssignOp(Position.NOPOS, JCTree.Tag.PLUS_ASG, id, cond);
//                JCAssignOp asn = F.Assignop(JCTree.PLUS_ASG, id, cond);
//                asn.setType(initialDecl.type);
//                asn.operator = rs.resolveBinaryOperator(asn.pos(), asn.getTag() - JCTree.ASGOffset, env, asn.lhs.type, asn.rhs.type);
                update = F.Exec(asn);
                retStat = F.Return(id); // Is it OK to reuse the node?
            } else if (q.op == JmlTokenKind.BSPRODUCT) {
                JCIdent id = F.Ident(initialDecl.name);
                id.pos = Position.NOPOS;
                id.setType(initialDecl.type);
                id.sym = initialDecl.sym;
                JCAssignOp asn = treeutils.makeAssignOp(Position.NOPOS, JCTree.Tag.MUL_ASG, id, cond);
//                JCAssignOp asn = F.Assignop(JCTree.MUL_ASG, id, cond);
//                asn.setType(initialDecl.type);
//                asn.operator = rs.resolveBinaryOperator(asn.pos(), asn.getTag() - JCTree.ASGOffset, env, asn.lhs.type, asn.rhs.type);
                update = F.Exec(asn);
                retStat = F.Return(id);
            } else if (q.op == JmlTokenKind.BSMAX || q.op == JmlTokenKind.BSMIN) {
                JCIdent id = F.Ident(initialDecl.name);
                id.setType(initialDecl.type);
                id.sym = initialDecl.sym;
                JCIdent vid = F.Ident(valueDecl.name);
                vid.setType(valueDecl.type);
                vid.sym = valueDecl.sym;
                JCIdent fid = F.Ident(firstDecl.name);
                fid.setType(firstDecl.type);
                fid.sym = firstDecl.sym;
                JCBinary op1,op2;
                // FIXME - use treeutils here
                update = F.If((op1=F.Binary(
                                            JCTree.Tag.OR, 
                                            (op2=F.Binary(
                                                    ( q.op == JmlTokenKind.BSMIN ? JCTree.Tag.LT : JCTree.Tag.GT), 
                                                    F.Assign(vid, newvalue).setType(vid.type), 
                                                    id
                                                    )).setType(syms.booleanType), 
                                            fid
                                            )).setType(syms.booleanType)
                                   ,
                                   F.Block(0, 
                                           List.<JCStatement>of(
                                                   F.Exec(F.Assign(id, vid).setType(id.type)),
                                                   F.Exec(F.Assign(fid, F.Literal(TypeTag.BOOLEAN,0).setType(syms.booleanType)).setType(fid.type))
                                                   )
                                           ),
                                   null);
                op1.operator = treeutils.orSymbol;
                op2.operator = rs.resolveBinaryOperator(op2.pos(),op2.getTag(), env, op2.lhs.type, op2.rhs.type);
                retStat = F.Return(id);
            } else if (q.op == JmlTokenKind.BSMIN) {
                JCIdent id = F.Ident(initialDecl.name);
                id.setType(initialDecl.type);
                id.sym = initialDecl.sym;
                JCIdent vid = F.Ident(valueDecl.name);
                vid.setType(valueDecl.type);
                vid.sym = valueDecl.sym;
                JCIdent fid = F.Ident(firstDecl.name);
                fid.setType(firstDecl.type);
                fid.sym = firstDecl.sym;
                JCBinary op1,op2;
                // FIXME - use treeutils here
                update = F.If(
                        (op1=F.Binary(
                                JCTree.Tag.OR, 
                                (op2=F.Binary(
                                        JCTree.Tag.LT, 
                                        F.Assign(vid, newvalue).setType(vid.type), 
                                        id
                                        )).setType(syms.booleanType), 
                                fid
                                )).setType(syms.booleanType)
                        ,
                       F.Block(0, 
                               List.<JCStatement>of(
                                       F.Exec(F.Assign(id,vid).setType(id.type)),
                                       F.Exec(F.Assign(fid, F.Literal(TypeTag.BOOLEAN,0).setType(syms.booleanType).setType(fid.type)))
                                       )
                               ),
                       null);
                op1.operator = treeutils.orSymbol;
                op2.operator = rs.resolveBinaryOperator(op2.pos(),op2.getTag(), env, op2.lhs.type, op2.rhs.type);
                
                retStat = F.Return(id);
            } else {
                return;
            }


            JCStatement innerStatement = F.If(innerexpr, update, null);
            for (Bound bound: bounds) {
                JCVariableDecl indexdef = bound.indexdef;
                JCIdent indexid = newids.get(bound.decl.sym);
                indexid.sym = indexdef.sym;
                indexid.type = indexdef.type;
                Name indexname = indexdef.name;
                if (bound.decl.type.getTag() == TypeTag.BOOLEAN) {
                    JCIdent idx = F.at(Position.NOPOS).Ident(indexname);
                    idx.setType(indexdef.type);
                    idx.sym = indexdef.sym;
                    JCExpression neg = treeutils.makeNot(Position.NOPOS, idx);
                    JCAssign asgn = treeutils.makeAssign(Position.NOPOS, idx,neg);
                    JCStatement negate = F.at(Position.NOPOS).Exec(asgn);
                    JCDoWhileLoop dowhilestatement =
                        F.DoLoop(
                                F.Block(0,List.<JCStatement>of(innerStatement,negate)),
                                idx
                                );
                    innerStatement = F.Block(0,List.<JCStatement>of(indexdef,dowhilestatement));
                } else if (bound.decl.type.getTag() == TypeTag.CLASS) {
                    JCEnhancedForLoop foreach =
                        F.ForeachLoop(
                                indexdef,
                                bound.lo,
                                innerStatement);
                    innerStatement = foreach;
                    
                } else {
                    JCVariableDecl lodef = bound.lodef;
                    JCVariableDecl hidef = bound.hidef;
                    Name hiname = hidef.name;
                    lodef.init = bound.lo;
                    hidef.init = bound.hi;

                    JCIdent id = indexid;
                    JCExpression op = treeutils.makeUnary(Position.NOPOS,JCTree.Tag.PREINC, id);
                    JCStatement inc = F.Exec(op);

                    JCIdent hi = F.Ident(hiname);
                    hi.sym = hidef.sym;
                    hi.type = hidef.type;
                    
                    // FIXME - use treeutils
                    JCBinary bin = F.Binary(bound.hi_equal ? JCTree.Tag.LE : JCTree.Tag.LT, id, hi);
                    bin.operator = rs.resolveBinaryOperator(bin.pos(), bin.getTag(), env, id.type, hi.type);
                    bin.setType(syms.booleanType);
                    JCWhileLoop whilestatement =
                        F.WhileLoop(
                                bin,
                                F.Block(0,List.<JCStatement>of(innerStatement,inc)));
                    innerStatement = bound.lo_equal ?
                              F.Block(0,List.<JCStatement>of(lodef,hidef,indexdef,whilestatement))
                            : F.Block(0,List.<JCStatement>of(lodef,hidef,indexdef,inc,whilestatement));
                }
            }

            List<JCStatement> methodBody =
                    initialDecl == null ? List.<JCStatement>of(innerStatement,retStat) :
                        valueDecl == null ?   List.<JCStatement>of(initialDecl,innerStatement,retStat) :
                                  List.<JCStatement>of(firstDecl,initialDecl,valueDecl,innerStatement,retStat);

            // Fill in missing pieces
            body.stats = methodBody;
            newarray.elems = argslist;
            
        } catch (Exception e) {
            // If there is an exception, we just abort trying to produce a RAC expression
            q.racexpr = null;
        }
        return;

    }
    
    protected static class Bound {
        public JCVariableDecl decl;
        public JCExpression lo;
        public JCExpression hi;
        boolean lo_equal;
        boolean hi_equal;
        JCVariableDecl indexdef;
        /*@Nullable*/JCVariableDecl lodef;
        /*@Nullable*/JCVariableDecl hidef;
    }
    
    /** If appropriate bounds can be determined for all defined variables, the method returns the
     * remaining expression and fills in the Bound list (first element is innermost loop); if appropriate
     * bounds cannot be determined, the method returns null.
     */
    public JCExpression determineRacBounds(List<JCVariableDecl> decls, JCExpression range, java.util.List<Bound> bounds) {
        // Some current assumptions
        if (decls.length() != 1) return null; // FIXME - does only one declaration!!!!!!
        if (decls.head.type.getTag() == TypeTag.DOUBLE) return null;
        if (decls.head.type.getTag() == TypeTag.FLOAT) return null;
        
        if (decls.head.type.getTag() == TypeTag.BOOLEAN) {
            Bound b = new Bound();
            b.decl = decls.head;
            b.lo = null;
            b.hi = null;
            bounds.add(0,b);
            return range;
        } else if (decls.head.type.getTag() == TypeTag.CLASS) {
            if (range instanceof JCBinary && ((JCBinary)range).getTag() != JCTree.Tag.AND) return null;
            JCExpression check = 
                range instanceof JCBinary? ((JCBinary)range).lhs : range;
            if (!(check instanceof JCMethodInvocation)) return null;
            JCMethodInvocation mi = (JCMethodInvocation)check;
            if (!(mi.meth instanceof JCFieldAccess)) return null;
            JCFieldAccess fa = (JCFieldAccess)mi.meth;
            if (!fa.name.toString().equals("contains") && !fa.name.toString().equals("has")) return null;
            Bound b = new Bound();
            b.decl = decls.head;
            b.lo = fa.selected;
            // FIXME - should check whether fa.selected is Iterable
            b.hi = null;
            bounds.add(0,b);
            return check == range ? check : // FIXME - could be set to true 
                ((JCBinary)range).rhs;
        }


        try {
            // presume int
            JCBinary locomp = (JCBinary)((JCBinary)range).lhs;
            JCBinary hicomp = (JCBinary)((JCBinary)range).rhs;
            if (locomp.getTag() == JCTree.Tag.AND) {
                hicomp = (JCBinary)locomp.rhs;
                locomp = (JCBinary)locomp.lhs;
            } else if (hicomp.getTag() == JCTree.Tag.AND) {
                hicomp = (JCBinary)hicomp.lhs;
            }
            Bound b = new Bound();
            b.decl = decls.head;
            b.lo = locomp.lhs;
            b.hi = hicomp.rhs;
            b.lo_equal = locomp.getTag() == JCTree.Tag.LE;
            b.hi_equal = hicomp.getTag() == JCTree.Tag.LE;
            bounds.add(0,b);
        } catch (Exception e) {
            return null;
        }
        return range;
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

        Env<AttrContext> localEnv = envForExpr(that,env);
        JCModifiers mods = that.variable.mods;
        utils.setExprLocal(mods);

        memberEnter.memberEnter(that.variable, localEnv);
        attribExpr(that.predicate,localEnv,syms.booleanType);

        localEnv.info.scope.leave();
       
        if (utils.hasOnly(mods,0)!=0) log.error(that.pos,"jml.no.java.mods.allowed","set comprehension expression");
        allAllowed(mods.annotations, JmlTokenKind.typeModifiers, "set comprehension expression");

        result = check(that, that.newtype.type, VAL, resultInfo);
    }
    
    public String visibility(long f) {
        return f == 0? "package" : f==Flags.PUBLIC? "public" :f==Flags.PROTECTED? "protected" : "private";
    }
    
    @Override
    protected Type checkId(JCTree tree,
            Type site,
            Symbol sym,
            Env<AttrContext> env,
            ResultInfo resultInfo) {
            if (checkingSignature) return sym.type;
            return super.checkId(tree, site, sym, env, resultInfo);
    }

    
    @Override
    public void visitIdent(JCIdent tree) {
//        if (tree.name.toString().equals("TestJava")) org.jmlspecs.openjml.Utils.stop();
        long prevVisibility = jmlVisibility;
        JmlTokenKind prevClauseType = currentClauseType;
        try {
//            jmlVisibility = -1;
//            currentClauseType = null;
            // Visiting the ident itself in the super class should not need the
            // jmlVisibility. However, visiting the ident can trigger loading
            // and type-checking a whole new class - so we unset this field
            // in the mean time.
            super.visitIdent(tree);
        } finally {
            jmlVisibility = prevVisibility;
            currentClauseType = prevClauseType;
        }
        
        // The above call erroneously does not set tree.type for method identifiers
        // if the method failed to result, even though a symbol with an error
        // type is set, so we patch that here.  See also the comment at visitSelect.
        if (tree.type == null) tree.type = tree.sym.type;
        
        Type saved = result;
        if (!justAttribute && tree.sym instanceof VarSymbol) {
            checkSecretReadable(tree.pos(),(VarSymbol)tree.sym);
        }// Could also be a method call, and error, a package, a class...
        
        checkVisibility(tree, jmlVisibility, tree.sym);
        result = saved;
    }
    
    protected void checkVisibility(DiagnosticPosition pos, long jmlVisibility, Symbol sym) {
        if (jmlVisibility != -1) {
            long v = (sym.flags() & Flags.AccessFlags);
            if (sym instanceof ClassSymbol) {
                // FIXME - the code below crashes for class symbols. What should we do?
                // FIXME - we also get this case for annotations on a clause
            } else {
//                if (tree.sym.toString().equals("defaults")) {
//                    System.out.println("defaults");;
//                }
                JCModifiers mods = null;
                if (sym.owner != null && sym.owner.kind == TYP) {
                    if (sym.kind == VAR) {
                        VarSymbol vsym = (VarSymbol)sym;
                        FieldSpecs sp = specs.getSpecs(vsym);
                        if (sp != null) mods = sp.mods;
                    }
                    if (sym.kind == MTH) {
                        MethodSpecs sp = specs.getSpecs((MethodSymbol)sym);
                        if (sp != null) mods = sp.mods;
                    }
                }
                if (mods != null && findMod(mods,SPEC_PROTECTED) != null) {
                    v = Flags.PROTECTED;
                }
                if (mods != null && findMod(mods,SPEC_PUBLIC) != null) {
                    v = Flags.PUBLIC;
                }
            }
            if (currentClauseType == JmlTokenKind.INVARIANT || currentClauseType == JmlTokenKind.CONSTRAINT) {
                // An ident used in an invariant must have the same visibility as the invariant clause - no more, no less
                // Is the symbol more visible? OK if the symbol is not a modifiable variable
                if (jmlVisibility != v && moreOrEqualVisibleThan(v,jmlVisibility) 
                        && sym instanceof VarSymbol && !utils.isExprLocal(sym.flags()) && !special(v,sym)
                        && (sym.flags() & Flags.FINAL)==0 ) { 
                    log.error(pos, "jml.visibility", visibility(v), visibility(jmlVisibility), currentClauseType.internedName());
                }
                // Is the symbol less visible? not OK
                if (jmlVisibility != v && !moreOrEqualVisibleThan(v,jmlVisibility)
                        && !utils.isExprLocal(sym.flags()) && !special(v,sym)) { 
                    log.error(pos, "jml.visibility", visibility(v), visibility(jmlVisibility), currentClauseType.internedName());
                }
            } else if (currentClauseType == JmlTokenKind.REPRESENTS) {
                //log.error(tree.pos,"jml.internal","Case not handled in JmlAttr.visitIdent: " + currentClauseType.internedName());
                if (!moreOrEqualVisibleThan(v,jmlVisibility) && !special(v,sym)) {
                    log.error(pos, "jml.visibility", visibility(v), visibility(jmlVisibility), currentClauseType.internedName());
                }

            } else if (currentClauseType == JmlTokenKind.JMLDECL) {
                // FIXME - not sure what rules to apply to this case
            } else if (currentClauseType == JmlTokenKind.IN) {
                // In    V type x; //@ in y;
                // identifier y must be at least as visible as x (i.e., as V)
                if (!moreOrEqualVisibleThan(v,jmlVisibility)) {
                    log.error(pos, "jml.visibility", visibility(v), visibility(jmlVisibility), currentClauseType.internedName());
                }

            } else if (currentClauseType == JmlTokenKind.ENSURES || currentClauseType == JmlTokenKind.SIGNALS) {
                // An identifier mentioned in a clause must be at least as visible as the clause itself.
                if (!moreOrEqualVisibleThan(v,jmlVisibility) && !special(v,sym)) {
                    log.error(pos, "jml.visibility", visibility(v), visibility(jmlVisibility), currentClauseType.internedName());
                }
                
                if (currentEnvLabel != null && enclosingMethodEnv.enclMethod.sym.isConstructor()) {
                    if (!sym.isStatic()) log.error(pos,  "jml.no.old.in.constructor", sym);
                }

            } else  {
                // Default case
                // An identifier mentioned in a clause must be at least as visible as the clause itself.
                if (!moreOrEqualVisibleThan(v,jmlVisibility) && !special(v,sym)) {
                    log.error(pos, "jml.visibility", visibility(v), visibility(jmlVisibility), currentClauseType.internedName());
                }

            }
        }
        

    }
    
    // FIXME - not sure this is still needed
    boolean special(long v, Symbol sym) {
        if (sym instanceof TypeSymbol) return true;
        if (sym instanceof VarSymbol && sym.owner instanceof MethodSymbol) return true; // FIXME - not sure how to handle these various special names
        return sym.name.toString().equals("TYPE") || !(v != 0 || (!sym.name.equals(names._this) && !sym.name.equals(names._super)  && !sym.name.equals(names.length) && !sym.name.equals(names._class)));
    }
    
    final static int order[] = { 2, 4, 1, 0, 3}; // package, public, private, -, protected
    static boolean moreOrEqualVisibleThan(long v1, long v2) {
        return order[(int)v1] >= order[(int)v2];
    }
    
    @Override
    public void visitIndexed(JCArrayAccess tree) {
        super.visitIndexed(tree);
        Type saved = result;
        if (tree.indexed instanceof JCIdent && ((JCIdent)tree.indexed).sym instanceof VarSymbol) {
            checkSecretReadable(tree.pos(),(VarSymbol)((JCIdent)tree.indexed).sym);
        } else if (tree.indexed instanceof JCFieldAccess && ((JCFieldAccess)tree.indexed).sym instanceof VarSymbol) {
            checkSecretReadable(tree.pos(),(VarSymbol)((JCFieldAccess)tree.indexed).sym);
        }
        // FIXME - forbid everything else?
        result = saved;
    }
    
    protected void checkSecretCallable(JCMethodInvocation tree, MethodSymbol msym) {
        DiagnosticPosition pos = tree.meth.pos();
        if (tree.meth instanceof JCFieldAccess) {
            // FIXME - really want this from pos to endpos, not from startpos to endpos
            pos = ((JCFieldAccess)tree.meth).pos();
        }
        
        JmlSpecs.MethodSpecs mspecs = specs.getSpecs(msym);
        VarSymbol calledSecret = null;
        VarSymbol calledQuery = null;
        boolean calledPure = false;
        if (mspecs != null) {
            calledSecret = getSecretSymbol(mspecs.mods);
            calledQuery = getQuerySymbol(tree,mspecs.mods);
            calledPure = findMod(mspecs.mods,JmlTokenKind.PURE) != null;
        }
        
        if (currentQueryContext != null) {
            // query method - may call query methods for a contained datagroup
            //              - may call secret methods for a contained datagroup
            //              - may call open pure method
            if (calledSecret != null) {
                if (!isContainedInDatagroup(calledSecret,currentQueryContext)) {
                    log.error(pos,"jml.incorrect.datagroup");
                }
            }
            if (calledQuery != null) {
                if (!isContainedInDatagroup(calledQuery,currentQueryContext)) {
                    log.error(pos,"jml.incorrect.datagroup");
                }
            }
            if (calledSecret == null && calledQuery == null) {
                if (!calledPure) {
                    log.error(pos,"jml.incorrect.datagroup");
                }
            }
        }
        if (currentSecretContext != null && currentSecretContext != currentQueryContext) {
            if (calledSecret != null) {
                if (!isContainedInDatagroup(calledSecret,currentSecretContext)) {
                    log.error(pos,"jml.incorrect.datagroup");
                }
            }
            if (calledQuery != null) {
                if (!isContainedInDatagroup(calledQuery,currentSecretContext)) {
                    log.error(pos,"jml.incorrect.datagroup");
                }
            }
            if (calledSecret == null && calledQuery == null) {
                if (!calledPure) {
                    log.error(pos,"jml.incorrect.datagroup");
                }
            }        }
        if (currentQueryContext == null && currentSecretContext == null) {
            // open method - may call query methods, but no secret methods
            if (calledSecret != null) {
                log.error(pos,"jml.open.may.not.call.secret");
            }
        }
    }
    
    protected void checkSecretReadable(DiagnosticPosition pos, VarSymbol vsym) {
        // If the variable is local to the method, then secret/query rules do not apply
        if (vsym.owner instanceof MethodSymbol) return;

        JmlSpecs.FieldSpecs fspecs = specs.getSpecs(vsym);
        boolean identIsSecret = fspecs != null && findMod(fspecs.mods,JmlTokenKind.SECRET) != null;
        // Rules:
        // If method is open, then ident may not be secret
        // If method is query and we are in the method specs, then ident may not be secret
        // If method is query, then ident is open or is secret for the same datagroup
        // If method is secret, then ident is open or is secret for the same datagroup
        
        if (identIsSecret) {
            boolean prevAllow = ((JmlResolve)rs).setAllowJML(true);
            if (currentSecretContext != null && isContainedInDatagroup(vsym,currentSecretContext)) {
                // OK - we are in a secret context and the variable is in that context
            } else if (currentClauseType == JmlTokenKind.IN || currentClauseType == JmlTokenKind.MAPS) {
                // OK - this is the target of an in or maps clause - secrecy restrictions are checked there
            } else if (currentQueryContext != null && isContainedInDatagroup(vsym,currentQueryContext)) {
                // OK - we are in a query context and the variable in secret for that context
            } else if (currentSecretContext != null) {
                log.error(pos,"jml.not.in.secret.context",vsym.getQualifiedName(),currentSecretContext.getQualifiedName());
            } else {
                // in open context
                log.error(pos,"jml.no.secret.in.open.context",vsym.getQualifiedName());
            }
            ((JmlResolve)rs).setAllowJML(prevAllow);
        }
    }
    
    protected void checkSecretWritable(DiagnosticPosition pos, VarSymbol vsym) {
        // If the variable is local to the method, then secret/query rules do not apply
        if (vsym.owner instanceof MethodSymbol) return;

        JmlSpecs.FieldSpecs fspecs = specs.getSpecs(vsym);
        boolean identIsSecret = fspecs != null && findMod(fspecs.mods,JmlTokenKind.SECRET) != null;
        // Rules:
        // If method is open, then ident may not even be read
        // If method is query, then ident must be secret for the same datagroup
        // If method is secret, then ident must be secret for the same datagroup
        
        boolean prevAllow = ((JmlResolve)rs).setAllowJML(true);
        boolean error = false;
        if (currentSecretContext != null) {
            if (!identIsSecret || !isContainedInDatagroup(vsym,currentSecretContext)) {
                // ERROR - may not write a non-secret field in a secret context
                // ERROR - field is not in the correct secret context to be written
                log.error(pos,"jml.not.writable.in.secret.context",vsym.getQualifiedName(),currentSecretContext.getQualifiedName());
                error = true;
            }
        }
        if (currentQueryContext != null && !error) {
            if (!identIsSecret || !isContainedInDatagroup(vsym,currentQueryContext)) {
                // ERROR - may not write a non-secret field in a secret context
                // ERROR - field is not in the correct secret context to be written
                log.error(pos,"jml.not.writable.in.secret.context",vsym.getQualifiedName(),currentQueryContext.getQualifiedName());
            }
        }
        ((JmlResolve)rs).setAllowJML(prevAllow);
    }
    
    boolean justAttribute = false;
    
    protected void attributeGroup(JmlGroupName g) {
        // Note that this.env should be the class env of the environment in which the group name is being resolved
        if (g.sym == null) {
            // Possibly not yet resolved - perhaps a forward reference, or perhaps does not exist
            boolean prevj = justAttribute;
            justAttribute = true;
            boolean prev = JmlResolve.instance(context).allowJML();
            JmlResolve.instance(context).setAllowJML(true);
            try {
                g.accept(this);
            } finally {
                JmlResolve.instance(context).setAllowJML(prev);
                justAttribute = prevj;
            }
        }
    }
    
    // Returns true if contextSym is contained (transitively) in the varSym datagroup
    protected boolean isContainedInDatagroup(@Nullable VarSymbol varSym, @Nullable VarSymbol contextSym) {
        if (varSym == contextSym) return true;
        JmlSpecs.FieldSpecs fspecs = specs.getSpecs(varSym);
        for (JmlTypeClause t: fspecs.list) {
            if (t.token == JmlTokenKind.IN) {  // FIXME - relies on variable IN clauses being attributed before a method that uses them
                for (JmlGroupName g: ((JmlTypeClauseIn)t).list) {
                    attributeGroup(g);
                    if (varSym == g.sym) { // Explicitly listed in self - should this be allowed? (FIXME)
                        continue;
                    }
                    if (g.sym != null) { // try again - if still null, it is because the datagroup mentioned in the
                                // in clause is not resolvable - perhaps does not exist
                        boolean b = isContainedInDatagroup(g.sym,contextSym);
                        if (b) return true;
                    } else if (g.selection instanceof JCIdent && ((JCIdent)g.selection).name == contextSym.name) {
                        return true; // Not resolvable - return true to avoid additional errors later
                    } else {
                        return false; 
                    }
                }
            }
        }
        return false;
    }
    
    public boolean checkForCircularity(VarSymbol varsym) {
        Collection<VarSymbol> roots = new LinkedList<>();
        return checkForCircularity(varsym, roots);
    }
    
    public boolean checkForCircularity(VarSymbol varsym, Collection<VarSymbol> roots) {
        if (roots.contains(varsym)) return true;
        roots.add(varsym);
        JmlSpecs.FieldSpecs fspecs = specs.getSpecs(varsym);
        for (JmlTypeClause t: fspecs.list) {
            if (t.token == JmlTokenKind.IN) {
                for (JmlGroupName g: ((JmlTypeClauseIn)t).list) {
                    attributeGroup(g);
                    if (g.sym == null) {
                        continue;
                    }
                    if (g.sym == varsym) {
                        // FIXME - should we waran about listing oneslef in an IN clause?
                    } else if (checkForCircularity(g.sym,roots)) {
                        return true;
                    }
                }
            }
        }
        roots.remove(varsym);
        return false;
    }
    
    
    /** Attributes a member select expression (e.g. a.b); also makes sure
     * that the type of the selector (before the dot) will be attributed;
     * that makes sure that the specifications of members are properly
     * attributed when needed later in esc or rac.
     */
    @Override
    public void visitSelect(JCFieldAccess tree) {
//        if (tree.name != null && tree.name.toString().equals("class")) {
//            int i = 0;
//        }
        if (tree.name != null) {
//            if (!tree.toString().startsWith("java")  && !tree.toString().startsWith("org.")) {
//                if (tree.toString().endsWith(".buf")) Utils.stop();
//            }
            super.visitSelect(tree);
//            if (tree.sym instanceof ClassSymbol) ((JmlCompiler)JmlCompiler.instance(context)).loadSpecsForBinary(null,(ClassSymbol)tree.sym);
            // The super call does not always call check... (which assigns the
            // determined type to tree.type, particularly if an error occurs,
            // so we fill it in
            if (tree.type == null) tree.type = result;
        } else {
            // This is a store-ref with a wild-card field
            // FIXME - the following needs some review
            attribTree(tree.selected, env, new ResultInfo(TYP|VAR, Infer.anyPoly));
            result = tree.type = Type.noType;
        }
        Type saved = result;
        
        Symbol s = tree.selected.type.tsym;
        if (!(s instanceof PackageSymbol)) {
            ClassSymbol c = null;
            if (s instanceof ClassSymbol) c = (ClassSymbol)s;
            else  c = s.enclClass();
            if (c != null) addTodo(c);
        }
        
        if (tree.sym != null) checkVisibility(tree, jmlVisibility, tree.sym);

        // For selections that are fields with an enclosing class, we check whether it is readable
        // The check on the enclosing class omits fields such as .class
        if (tree.sym instanceof VarSymbol && tree.sym.enclClass() != null) {
            checkSecretReadable(tree.pos(),(VarSymbol)tree.sym);
        } // FIXME - what else could it be, besides an error?
//        if (tree.sym instanceof ClassSymbol) ((JmlCompiler)JmlCompiler.instance(context)).loadSpecsForBinary(env,(ClassSymbol)tree.sym);
        result = saved;
    }
    
    @Override
    public void visitTypeCast(JCTypeCast tree) {
        if (tree.clazz instanceof JmlPrimitiveTypeTree) {
            // FIXME - this needs to be expanded to include real and bigint and
            // arrays of such
            JmlTokenKind t = ((JmlPrimitiveTypeTree)tree.clazz).token;
            Type clazztype = attribType(tree.clazz, env);
            if (t == JmlTokenKind.BSTYPEUC) {
                chk.validate(tree.clazz, env);
                Type exprtype = attribExpr(tree.expr, env, Infer.anyPoly);
                // Only Class objects may be cast to TYPE
                // Compare tsym instead of just the thpe because the
                // exprtype is likely a Class<T> and syms.classType is a Class
                // or Class<?>
                if (exprtype.tsym == syms.classType.tsym) {
                    result = check(tree, clazztype, VAL, resultInfo);
                } else {
                    log.error(tree.expr.pos,"jml.only.class.cast.to.type",exprtype);
                    result = tree.type = jmltypes.TYPE;
                }
            } else {
                // For now do no checking // FIXME
                Type exprtype = attribExpr(tree.expr, env, Infer.anyPoly);
                result = tree.type = clazztype;
            }
        } else {
            super.visitTypeCast(tree);
        }
    }
    
    /** Attrbutes an array-element-range (a[1 .. 2]) store-ref expression */
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        if (that.lo != null) attribExpr(that.lo,env,syms.intType); // FIXME - int or long or bigint
        if (that.hi != null && that.hi != that.lo) attribExpr(that.hi,env,syms.intType); // FIXME - int or long or bigint
        Type t = attribExpr(that.expression,env,Type.noType);
        if (t.getKind() != TypeKind.ARRAY) {
            if (t.getKind() != TypeKind.ERROR) log.error(that.expression.pos(),"jml.not.an.array",t);
            t = syms.errType;
            result = check(that, t, VAL, resultInfo);
        } else {
            t = ((ArrayType)t).getComponentType();
            result = check(that, t, VAL, resultInfo);
        }
    }



    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        result = that.type = Type.noType;
        // FIXME - call check
    }
    
//    @Override
//    public void visitReturn(JCReturn that) {
////        if (addRac && that.expr != null) {
////            that.expr = make.Assign(make.Ident(resultName),that.expr);
////        }
//        super.visitReturn(that);
//    }
    
    
    /** This is a map from token to Name.  It has to be generated at runtime because
     * Names are dependent on the Context.  It is supposedly a very fast
     * (i.e. array) lookup.  The Names are the fully-qualified name of the type
     * of the annotation that represents the given modifier token.
     */
    public EnumMap<JmlTokenKind,Name> tokenToAnnotationName = new EnumMap<JmlTokenKind,Name>(JmlTokenKind.class);
    
    /** A map from token to ClassSymbol, valid for tokens that have annotation equivalents. */
    public EnumMap<JmlTokenKind,ClassSymbol> tokenToAnnotationSymbol = new EnumMap<JmlTokenKind,ClassSymbol>(JmlTokenKind.class);

    /** A Name for the fully-qualified name of the package that the JML annotations are defined in. */
    public Name annotationPackageName;
    
    /** A Name for the fully-qualified name of the package that the JML annotations are defined in. */
    public PackageSymbol annotationPackageSymbol;
    
    /** For the given context, initializes the value of packageName and the
     * content of the tokenToAnnotationName mapping; since Name objects are
     * involved and they are defined per context, this initialization must be
     * performed after a context is defined.
     * @param context the compilation context in which to do this initialization
     */
    public void initAnnotationNames(Context context) {
        Names names = Names.instance(context);
        annotationPackageName = names.fromString(Strings.jmlAnnotationPackage);
        for (JmlTokenKind t: JmlTokenKind.modifiers) {
            if (t.annotationType == null) {
                // No class for this token, but we won't complain
                // The result is to silently ignore the token (TODO)
            } else {
                String s = t.annotationType.getName();
                Name n = names.fromString(s);
                tokenToAnnotationName.put(t,n);
                ClassSymbol sym = ClassReader.instance(context).enterClass(n);
                tokenToAnnotationSymbol.put(t,sym);
            }
        }
        annotationPackageSymbol = tokenToAnnotationSymbol.get(JmlTokenKind.PURE).packge();
    }
    
    /** Checks that all of the JML annotations present in the first argument
     * are also present in the second argument, issuing error messages if they
     * are not.
     * @param annotations a list of annotations to check
     * @param allowed the set of allowed annotations
     * @param place a description of where the annotations came from, for error messages
     */
    public void allAllowed(List<JCTree.JCAnnotation> annotations, JmlTokenKind[] allowed, String place) {
        outer: for (JCTree.JCAnnotation a: annotations) {
            for (JmlTokenKind c: allowed) {
                if (a.annotationType.type.tsym.flatName().equals(tokenToAnnotationName.get(c))) continue outer; // Found it
            }
            // a is not in the list, but before we complain, check that it is
            // one of our annotations
            if (a.annotationType.type.tsym.packge().flatName().equals(annotationPackageName)) { // FIXME - change to comparing symbols instead of strings?
                JavaFileObject prev = log.useSource(((JmlTree.JmlAnnotation)a).sourcefile);
                log.error(a.pos,"jml.illegal.annotation",place);
                log.useSource(prev);
            }
        }
    }
    
    /** This checks that the given modifier set does not have annotations for
     * both of a pair of mutually exclusive annotations; it prints an error
     * message if they are both present; returns true if an error happened
     * @param mods the modifiers to check
     * @param ta the first JML token
     * @param tb the second JML token
     */
    public boolean checkForConflict(JCModifiers mods, JmlTokenKind ta, JmlTokenKind tb) {
        JCTree.JCAnnotation a,b;
        a = utils.findMod(mods,tokenToAnnotationSymbol.get(ta));
        b = utils.findMod(mods,tokenToAnnotationSymbol.get(tb));
        if (a != null && b != null) {
            JavaFileObject prev = log.useSource(((JmlTree.JmlAnnotation)b).sourcefile);
            log.error(b.pos(),"jml.conflicting.modifiers",ta.internedName(),tb.internedName());
            log.useSource(prev);
            return true;
        }
        return false;
    }
    
    public boolean checkForRedundantSpecMod(JCModifiers mods) {
        JCTree.JCAnnotation a;
        boolean result = false;
        if ((mods.flags & Flags.PROTECTED) != 0 &&
                (a=utils.findMod(mods,tokenToAnnotationSymbol.get(SPEC_PROTECTED))) != null ) {
            JavaFileObject prev = log.useSource(((JmlTree.JmlAnnotation)a).sourcefile);
            log.warning(a.pos(),"jml.redundant.visibility","protected","spec_protected");
            log.useSource(prev);
            result = true;
        }
        if ((mods.flags & Flags.PUBLIC) != 0 &&
                (a=utils.findMod(mods,tokenToAnnotationSymbol.get(SPEC_PROTECTED))) != null ) {
            JavaFileObject prev = log.useSource(((JmlTree.JmlAnnotation)a).sourcefile);
            log.warning(a.pos(),"jml.redundant.visibility","public","spec_protected");
            log.useSource(prev);
            result = true;
        }
        if ((mods.flags & Flags.PUBLIC) != 0 &&
                (a=utils.findMod(mods,tokenToAnnotationSymbol.get(SPEC_PUBLIC))) != null ) {
            JavaFileObject prev = log.useSource(((JmlTree.JmlAnnotation)a).sourcefile);
            log.warning(a.pos(),"jml.redundant.visibility","public","spec_public");
            log.useSource(prev);
            result = true;
        }
        return result;
    }
    
    /** Finds the annotation in the modifiers corresponding to the given token
     * @param mods the modifiers to check
     * @param ta the token to look for
     * @return a reference to the annotation AST node, or null if not found
     */
    //@ nullable
    public JmlAnnotation findMod(/*@nullable*/JCModifiers mods, JmlTokenKind ta) {
        if (mods == null) return null;
        return utils.findMod(mods,tokenToAnnotationSymbol.get(ta));
    }

    /** Returns true if the given symbol is specified as Helper or Function annotation */
    public boolean isNonNull(/*@ nullable */ JCModifiers mods) {
        if (mods != null) {
            List<JCAnnotation> list = mods.getAnnotations();
            if (list != null) for (JCAnnotation a: list) {
                if (a.annotationType.type.tsym == nonnullAnnotationSymbol) return true;
                if (a.annotationType.type.tsym == nullableAnnotationSymbol) return false;
            }
        }
        return false;  // FIXME - use default?
    }
    

    /** Returns true if the given modifiers includes model
     * @param mods the modifiers to check
     * @return true if the model modifier is present, false if not
     */
    public boolean isModel(/*@nullable*/JCModifiers mods) {
        return findMod(mods,JmlTokenKind.MODEL) != null;
    }
    
    /** Returns true if the given symbol has a given annotation 
     * @param symbol the symbol to check
     * @return true if the symbol has a given annotation, false otherwise
     */
    public boolean hasAnnotation(Symbol symbol, JmlTokenKind t) {
      return symbol.attribute(tokenToAnnotationSymbol.get(t)) != null;

  }
  
    /** Returns true if the given symbol has a given annotation 
     * @param symbol the symbol to check
     * @return true if the symbol has a given annotation, false otherwise
     */
    public Attribute.Compound findAnnotation(Symbol symbol, JmlTokenKind t) {
      return symbol.attribute(tokenToAnnotationSymbol.get(t));

  }
  
    /** Returns true if the given symbol has a model annotation 
     * @param symbol the symbol to check
     * @return true if the symbol has a model annotation, false otherwise
     */
    public boolean isModel(Symbol symbol) {
//      if (modelAnnotationSymbol == null) {
//          modelAnnotationSymbol = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.annotation.Model"));
//      }
      return symbol.attribute(tokenToAnnotationSymbol.get(JmlTokenKind.MODEL))!=null;

  }
  
//    /** Returns true if the given symbol has a pure annotation 
//     * @param symbol the symbol to check
//     * @return true if the symbol has a model annotation, false otherwise
//     */
//    public boolean isPureClass(ClassSymbol symbol) {
//        return specs.isPure(symbol);
////            TypeSpecs tspecs = specs.getSpecs(symbol);
////            if (tspecs == null) return false;
////            return findMod(tspecs.modifiers,PURE) != null;
//    }
    
    public boolean isPureMethod(MethodSymbol symbol) {
        for (MethodSymbol msym: Utils.instance(context).parents(symbol)) {
            MethodSpecs mspecs = specs.getSpecs(msym);
            if (mspecs == null) {
                // FIXME - A hack - the .jml file should have been read for org.jmlspecs.lang.JMLList
                if (msym.toString().equals("size()") && msym.owner.toString().equals(Strings.jmlSpecsPackage + ".JMLList")) return true;
                // FIXME - check when this happens - is it because we have not attributed the relevant class (and we should) or just because there are no specs
                continue;
            }
            boolean isPure = specs.isPure(symbol);
            if (isPure) return true;
        }
        return false;
    }
    
    /** Returns true if the given symbol has a pure annotation 
     * @param symbol the symbol to check
     * @return true if the symbol has a model annotation, false otherwise
     */
    public boolean isHelper(MethodSymbol symbol) {
        MethodSpecs mspecs = specs.getSpecs(symbol);
        if (mspecs == null) {
            // FIXME - check when this happens - is it because we have not attributed the relevant class (and we should) or just because there are no specs
            return false;
        }
        return findMod(mspecs.mods,JmlTokenKind.HELPER) != null || findMod(mspecs.mods,JmlTokenKind.FUNCTION) != null;
//
//        if (symbol.attributes_field == null) return false;  // FIXME - should have the attributes - this is necessary but why?
//        return symbol.attribute(tokenToAnnotationSymbol.get(JmlToken.HELPER))!=null;

    }
    
    public void addHelper(MethodSymbol symbol) {
        MethodSpecs mspecs = specs.getSpecs(symbol);
        if (mspecs == null) {
            // FIXME - check when this happens - is it because we have not attributed the relevant class (and we should) or just because there are no specs
            return ;
        }
        // FIXME - what if mspecs.mods is null
        Symbol ansym = tokenToAnnotationSymbol.get(JmlTokenKind.HELPER);
        Attribute.Compound a = new Attribute.Compound(ansym.type,List.<Pair<MethodSymbol,Attribute>>nil());
        JCAnnotation an = factory.Annotation(a);
        an.type = ansym.type;
        mspecs.mods.annotations = mspecs.mods.annotations.append(an);
        return;
    }
    
    public boolean isFunction(MethodSymbol symbol) {
        MethodSpecs mspecs = specs.getSpecs(symbol);
        if (mspecs == null) {
            // FIXME - check when this happens - is it because we have not attributed the relevant class (and we should) or just because there are no specs
            return false;
        }
        return findMod(mspecs.mods,JmlTokenKind.FUNCTION) != null;
    }
    
    public boolean isImmutable(ClassSymbol symbol) {
        TypeSpecs mspecs = specs.getSpecs(symbol);
        if (mspecs == null) {
            // FIXME - check when this happens - is it because we have not attributed the relevant class (and we should) or just because there are no specs
            return false;
        }
        return findMod(mspecs.modifiers,JmlTokenKind.IMMUTABLE) != null;
    }
    
    public JCAnnotation hasAnnotation(JmlVariableDecl decl, JmlTokenKind token) {
        if (decl.specsDecl != null) {
            return findMod(decl.specsDecl.mods, token);
        } else {
            return findMod(decl.mods, token);
        }
    }
    
    /** Returns true if the given modifiers/annotations includes ghost
     * @param mods the modifiers to check
     * @return true if the ghost modifier is present, false if not
     */
    public boolean isGhost(/*@nullable*/JCModifiers mods) {
        return findMod(mods,JmlTokenKind.GHOST) != null;
    }
    
    /** Returns true if the given modifiers/annotations includes static
     * @param mods the modifiers to check
     * @return true if the static modifier is present, false if not
     */
    public boolean isStatic(JCModifiers mods) {
        return (mods.flags & Flags.STATIC)!=0;
    }
    
    /** Returns true if the given flags includes static
     * @param flags the modifier flags to check
     * @return true if the static modifier is present, false if not
     */
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
    
    /** Returns a string combining the file name and line number, for RAC error messages
     * @param source the file containing the source location being referenced
     * @param pos the character position within the file [TODO - 0 or 1-based?]
     */
    public String position(JavaFileObject source, int pos) {
        JavaFileObject pr = log.currentSourceFile();
        log.useSource(source);
        String s = source.getName() + ":" + log.currentSource().getLineNumber(pos) + ": JML ";
        log.useSource(pr);
        return s;
    }
    
    protected int loopIndexCount = 0;

    /** Attributes the specs for a do-while loop */
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        loopStack.add(0,treeutils.makeIdent(that.pos, "loopIndex_" + (++loopIndexCount), syms.intType));
        attribLoopSpecs(that.loopSpecs,env);
        super.visitDoLoop(that);
        loopStack.remove(0);
    }
    
    java.util.List<JCIdent> loopStack = new java.util.LinkedList<JCIdent>();
    java.util.List<JmlEnhancedForLoop> foreachLoopStack = new java.util.LinkedList<JmlEnhancedForLoop>();

    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop tree) {
        loopStack.add(0,treeutils.makeIdent(tree.pos, "loopIndex_" + (++loopIndexCount), syms.intType));
        foreachLoopStack.add(0,tree);
        Env<AttrContext> loopEnv =
                env.dup(env.tree, env.info.dup(env.info.scope.dup()));
        try {
        // MAINTENANCE ISSUE: code duplicated mostly from the superclass
            //the Formal Parameter of a for-each loop is not in the scope when
            //attributing the for-each expression; we mimick this by attributing
            //the for-each expression first (against original scope).
            Type exprType = types.cvarUpperBound(attribExpr(tree.expr, loopEnv));
            attribStat(tree.var, loopEnv);
            chk.checkNonVoid(tree.pos(), exprType);
            Type elemtype = types.elemtype(exprType); // perhaps expr is an array?
            if (elemtype == null) {
                // or perhaps expr implements Iterable<T>?
                Type base = types.asSuper(exprType, syms.iterableType.tsym);
                if (base == null) {
                    log.error(tree.expr.pos(),
                            "foreach.not.applicable.to.type",
                            exprType,
                            diags.fragment("type.req.array.or.iterable"));
                    elemtype = types.createErrorType(exprType);
                } else {
                    List<Type> iterableParams = base.allparams();
                    elemtype = iterableParams.isEmpty()
                        ? syms.objectType
                        : types.wildUpperBound(iterableParams.head);
                }
            }
            chk.checkType(tree.expr.pos(), elemtype, tree.var.sym.type);
            loopEnv.tree = tree; // before, we were not in loop!
            trForeachLoop(tree,tree.var.sym.type); // DRC - added
            attribStat(tree.body, loopEnv);
            attribLoopSpecs(tree.loopSpecs,loopEnv); // DRC - added
            result = null;

//            Type exprType = types.cvarUpperBound(attribExpr(tree.expr, loopEnv));
//            savedSpecOK = true;
//            attribStat(tree.var, loopEnv);
//            chk.checkNonVoid(tree.pos(), exprType);
//            Type elemtype = types.elemtype(exprType); // perhaps expr is an array?
//            if (elemtype == null) {
//                // or perhaps expr implements Iterable<T>?
//                Type base = types.asSuper(exprType, syms.iterableType.tsym);
//                if (base == null) {
//                    log.error(tree.expr.pos(),
//                            "foreach.not.applicable.to.type",
//                            exprType,
//                            diags.fragment("type.req.array.or.iterable"));
//                    elemtype = types.createErrorType(exprType);
//                } else {
//                    List<Type> iterableParams = base.allparams();
//                    elemtype = iterableParams.isEmpty()
//                        ? syms.objectType
//                        : types.wildUpperBound(iterableParams.head);
//                }
//            }
//            chk.checkType(tree.expr.pos(), elemtype, tree.var.sym.type);
//            loopEnv.tree = tree; // before, we were not in loop!

            

        } finally {
            loopEnv.info.scope.leave();
            loopStack.remove(0);
            foreachLoopStack.remove(0);
        }
    }
    
    /** Returns an unattributed expression tree that boxes the given 
     * expression to the given type.  It is the caller's responsibility to
     * be sure that the type of the expression argument is consistent with the
     * given target type.
     * @param e the expression to box
     * @param boxedtype the target type
     * @return the boxed expression
     */
    public JCExpression autobox(JCExpression e, Type boxedtype) {
        factory.at(e.pos);
        //Type boxed = Types.instance(context).boxedClass(vartype).type;
        Name valueof = names.fromString("valueOf");
        JCExpression s = factory.Select(factory.Type(boxedtype),valueof);
        s = factory.Apply(null,s,List.<JCExpression>of(e));
        return s;
    }
    
    /** Returns an unattributed expression tree that unboxes the given 
     * expression to the given type.  It is the caller's responsibility to
     * be sure that the type of the expression argument is consistent with the
     * given target type.
     * @param e the expression to unbox
     * @param vartype the target unboxed type
     * @return the unboxed expression
     */
    public JCExpression autounbox(JCExpression e, Type vartype) {
        
        factory.at(e.pos);
        String name = null;
        switch (vartype.getKind()) {
            case BYTE: name = "byteValue"; break;
            case BOOLEAN: name = "booleanValue"; break;
            case INT: name = "intValue"; break;
            case SHORT: name = "shortValue"; break;
            case LONG: name = "longValue"; break;
            case CHAR: name = "charValue"; break;
            case FLOAT: name = "floatValue"; break;
            case DOUBLE: name = "doubleValue"; break;
            default:
                log.error(e.pos,"jml.invalid.unboxing",vartype);
                return factory.Erroneous();
        }
        
        Name value = names.fromString(name);
        JCFieldAccess s = factory.Select(e,value);
        s.type = vartype;  // FIXME - no sym set? or is this a method type?
        JCMethodInvocation ss = factory.Apply(null,s,List.<JCExpression>nil());
        ss.type = vartype; // FIXME - typeargs, varargselement ?
        return ss;
    }
    
    /** Translates an enhanced for loop into a traditional for loop so that
     * we have access to loop variables for use in invariants.
     * @param tree  the enhanced for loop
     * @param vartype the type of the loop variable
     */
        // Translating:  T elem : e
    public void trForeachLoop(JmlEnhancedForLoop tree, Type vartype) {
        // vartype is T ; boxedVarType is T' which is the boxed type (if necessary) of T
        
        // Desugar the foreach loops in order to put in the JML auxiliary loop indices
        factory.at(tree.pos); // Sets the position until reset
        
        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
        ListBuffer<JCExpressionStatement> step = new ListBuffer<JCExpressionStatement>();

        // tree.indexDecl:     int  $$index$nnn = 0
        Name name = names.fromString("$$index$"+tree.pos);
        tree.indexDecl = makeVariableDecl(name,syms.intType,zeroLit,tree.pos);
        tree.indexDecl.sym.owner = tree.var.sym.owner;

        factory.at(tree.pos+1);
        JCIdent ident = factory.Ident(tree.indexDecl.sym);        
        JCExpressionStatement st = factory.Exec(factory.Unary(JCTree.Tag.PREINC,ident));  // ++ $$index;
        st.type = syms.intType;
        stats.append(tree.indexDecl);   // stats gets    int  $$index$nnn = 0;
        step.append(st);                // step  gets    ++ $$index$nnn;
        factory.at(tree.pos);

        Type boxedVarType = vartype;
        if (vartype.isPrimitive()) {
            boxedVarType = Types.instance(context).boxedClass(vartype).type;
        }
        
        
        Type elemtype = null;
        if (tree.expr.type.getTag() == TypeTag.ARRAY) {
            elemtype = ((ArrayType)tree.expr.type).elemtype;
        } else {
            elemtype = vartype;  // FIXME - this should be the type returned by the iterator
        }
        

        {
            
            Name defempty = names.fromString("defaultEmpty");
            JCFieldAccess sel = factory.Select(factory.Type(utilsClass.type),defempty);
            JCExpression e = factory.Apply(List.<JCExpression>of(factory.Type(boxedVarType)),sel,List.<JCExpression>nil()); 
            // FIXME e.type = ?
            // e:    Utils.<T'>defaultEmpty()
            
            int p = tree.pos;
            name = names.fromString("$$values$"+p);
            ClassType ct = new ClassType(JMLValuesType.getEnclosingType(),List.<Type>of(boxedVarType),JMLValuesType.tsym);
            tree.valuesDecl = makeVariableDecl(name,ct,e,p);
            tree.valuesDecl.sym.owner = tree.var.sym.owner;
            // tree.valuesDecl :    JMLValuesType<T'> $$values$ppp = Utils.<T'>defaultEmpty();
            stats.append(tree.valuesDecl);
            
//            // Add postconditions of defaultEmpty by hand
//            // assume $$values$ppp != null;
//            // assume $$values$ppp.length == 0;
//            JCExpression nn = factory.at(p).Binary(JCTree.NE, factory.Ident(tree.valuesDecl), nullLit );
//            stats.append( factory.at(p).JmlExpressionStatement(JmlToken.ASSUME, Label.POSTCONDITION, nn));
//            nn = factory.at(p).Select(factory.Ident(tree.valuesDecl), names.fromString("size"));
//            nn = factory.at(p).Apply(null,nn,List.<JCExpression>nil());
//            nn = factory.at(p).Binary(JCTree.EQ, nn, zeroLit );
//            stats.append( factory.at(p).JmlExpressionStatement(JmlToken.ASSUME, Label.POSTCONDITION, nn));
            
            factory.at(tree.pos+2);
            Name add = names.fromString("add");
            sel = factory.Select(factory.Ident(tree.valuesDecl),add);  // $$values$ppp.add
            //sel.type = 
            JCExpression ev = factory.Ident(tree.var);   // elem
            if (vartype.isPrimitive()) ev = autobox(ev,boxedVarType);
            JCMethodInvocation app = factory.Apply(null,sel,List.<JCExpression>of(ev));  // $$values$ppp.add(autobox(ev)); [autoboxing only if necessary]
            //app.type = tree.valuesDecl.type; // FIXME _ check this
            //
            
            factory.at(tree.pos+3);
            JCAssign asgn = factory.Assign(factory.Ident(tree.valuesDecl),app);
            asgn.type = asgn.lhs.type;
            step.append(factory.Exec(asgn));
            
            factory.at(tree.pos);

        }
        
        stats.append(tree.var);
        
        JCExpression cond = null;
        
        ListBuffer<JCStatement> bodystats = new ListBuffer<JCStatement>();

        JCExpression newvalue;
        JmlStatementLoop inv = null;
        if (tree.expr.type.getTag() == TypeTag.ARRAY) {
            // Replace the foreach loop for (T t: a) body;
            // by
            // int $$index = 0;
            // final non_null JMLList $$values = Utils.<T'>defaultEmpty();
            // T t;
            // for (; $$index < a.length; $$index++, $$values.add(t') ) {
            //       check loop invariant
            //    t = a[$$index];
            //    body
            // }
            
            JCExpression arraylen = factory.Select(tree.expr,syms.lengthVar);
            cond = factory.Binary(JCTree.Tag.LT,ident,arraylen);
            cond.type = syms.booleanType;

            newvalue = factory.Indexed(tree.expr,ident); // newvalue :: expr[$$index]
            // FIXME newvalue.type = ???
            if (elemtype.isPrimitive() && !vartype.isPrimitive()) {
                newvalue = autobox(newvalue,vartype);
            } else if (!elemtype.isPrimitive() && vartype.isPrimitive()) {
                newvalue = autounbox(newvalue,vartype);
            }
            
            JCBinary invexpr = factory.Binary(JCTree.Tag.AND,factory.Binary(JCTree.Tag.LE,zeroLit,ident),factory.Binary(JCTree.Tag.LE,ident,arraylen));
            invexpr.type = invexpr.lhs.type = invexpr.rhs.type = syms.booleanType;
            inv = factory.JmlStatementLoop(JmlTokenKind.LOOP_INVARIANT,invexpr);

            
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
            ClassType ct = new ClassType(JMLIterType.getEnclosingType(),List.<Type>of(boxedVarType),JMLIterType.tsym);
            tree.iterDecl = makeVariableDecl(name,ct,nullLit,tree.pos);
            tree.iterDecl.sym.owner = tree.var.sym.owner;
            stats.append(tree.iterDecl);
            
            Name hasNext = names.fromString("hasNext");
            JCFieldAccess sel = factory.Select(factory.Ident(tree.iterDecl),hasNext);
            cond = factory.Apply(null,sel,List.<JCExpression>nil()); // cond :: $$iter . hasNext()
            cond.type = syms.booleanType;

            Name next = names.fromString("next");
            sel = factory.Select(factory.Ident(tree.iterDecl),next);
            newvalue = factory.Apply(null,sel,List.<JCExpression>nil());  // newvalue ::  $$iter . next()
            // FIXME - newvalue.type = ???
        }
        
        bodystats.append(factory.Exec(factory.Assign(factory.Ident(tree.var),newvalue))); // t = newvalue;
        // FIXME - assign types
        bodystats.append(tree.body);
        
        factory.at(tree.pos+1);
        Name sz = names.fromString("size");
        JCFieldAccess sel = factory.Select(factory.Ident(tree.valuesDecl),sz);
        // FIXME sel.type ??? invexpr2.type
        JCExpression invexpr2 = factory.Apply(null,sel,List.<JCExpression>nil());  // invexpr2 ::  $$values . size()
        JCBinary invexpr3 = factory.Binary(JCTree.Tag.AND,factory.Binary(JCTree.Tag.NE,nullLit,factory.Ident(tree.valuesDecl)),factory.Binary(JCTree.Tag.EQ,ident,invexpr2));
        invexpr3.type = invexpr3.lhs.type = invexpr3.rhs.type = syms.booleanType;
        JmlStatementLoop inv2 = factory.JmlStatementLoop(JmlTokenKind.LOOP_INVARIANT,invexpr3);
        
        factory.at(tree.pos);
        JCBlock block = factory.Block(0,bodystats.toList());
        block.endpos = (tree.body instanceof JCBlock) ? ((JCBlock)tree.body).endpos : tree.body.pos;
        
        JCForLoop forstatement = factory.ForLoop(List.<JCStatement>nil(),cond,step.toList(),block);
        JmlForLoop jmlforstatement = factory.JmlForLoop(forstatement,tree.loopSpecs);
        {
            ListBuffer<JmlStatementLoop> list = new ListBuffer<JmlStatementLoop>();
            list.append(inv2);
            if (inv != null) list.append(inv);
            if (tree.loopSpecs != null) list.appendList(tree.loopSpecs);
            jmlforstatement.loopSpecs = list.toList();
        }
        stats.append(jmlforstatement);

        JCBlock blockk = factory.Block(0,stats.toList());
        blockk.endpos = block.endpos;
        tree.implementation = blockk;
        tree.internalForLoop = jmlforstatement;
        
//        tree.var = translate(tree.var);
//        tree.expr = translate(tree.expr);
//        tree.body = translate(tree.body);
//        result = tree;
    }

    // MAINTENANCE ISSUE: code duplicated mostly from the superclass

    public void visitJmlForLoop(JmlForLoop tree) {
        loopStack.add(0,treeutils.makeIdent(tree.pos, "loopIndex_" + (++loopIndexCount), syms.intType));
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
        loopStack.remove(0);
    }

    public void visitJmlWhileLoop(JmlWhileLoop that) {
        loopStack.add(0,treeutils.makeIdent(that.pos, "loopIndex_" + (++loopIndexCount), syms.intType));
        attribLoopSpecs(that.loopSpecs,env);
        super.visitWhileLoop(that);
        loopStack.remove(0);
    }

    public void visitJmlStatementLoop(JmlStatementLoop that) {
        attribExpr(that.expression,env);
    }

    public void visitJmlChoose(JmlChoose that) {
        // FIXME - fill in
    }

    public void visitJmlClassDecl(JmlClassDecl that) {
        // Typically, classes are attributed by calls to attribClass and
        // then to attibClassBody and attribClassBodySpecs, but local
        // classes do end up here.
        that.toplevel = (JmlCompilationUnit)enclosingClassEnv.toplevel;

        if (that.specsDecl == null) {
            // A local class is its own specification , so we fill in the
            // specification information.  It might be nice to do this 
            // earlier and avoid this check, but there is no convenient place
            // during parsing, and the Enter/MemberEnter steps do not handle
            // local classes.
            // There is also the case of anonymous classes in expressions that
            // in class specs (e.g. invariants)
//            if (enclosingMethodEnv == null && !isInJmlDeclaration) {
//                // Warn for non-local classes
//                log.error("jml.internal.notsobad","A non-local class's specsDecl field was unexpectedly null in JmlAtt.visitJmlClassDecl: " + that.name);
//            }
            that.specsDecl = that;
            that.typeSpecs = new JmlSpecs.TypeSpecs(that);
        }
        

//        boolean prev = isInJmlDeclaration;
//        if (implementationAllowed) isInJmlDeclaration = true;
//        try {
            visitClassDef(that);
//        } finally {
//            isInJmlDeclaration = prev;
//        }
    }

    public void visitClassDef(JCClassDecl tree) {
        // The superclass calls classEnter if the env is owned by a VAR or MTH.
        // But JML has the case of an anonymous class that occurs in a class
        // specification (e.g. an invariant), or in a method clause (so it is
        // owned by the method)
        if ((env.info.scope.owner.kind & (VAR | MTH)) == 0 && tree.sym == null) {
            enter.classEnter(tree, env);
        }
        super.visitClassDef(tree);

    }
    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        visitTopLevel(that);
    }

    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        visitMethodDef(that);
    }
    
    public static class SpecialDiagnosticPosition extends com.sun.tools.javac.util.JCDiagnostic.SimpleDiagnosticPosition {
        String message;
        public SpecialDiagnosticPosition(String message) {
            super(-1);
            this.message = message;
        }
    }

    // FIXME - is this only ghost declarations
    // and don't the modifiers get checked twice - does the super.visitVarDef actually work?
    /** Attributes a variable declared within a JML spec - that is a ghost
     * variable declaration, along with checking any JML 
     * annotations and specifications of the declaration.  The super call
     * adds the declaration to the current scope.
     * @param that the AST node to attribute
     */
    @Override
    public void visitJmlVariableDecl(JmlVariableDecl that) {

        JavaFileObject prevSource = null;
        JmlTokenKind saved = currentClauseType;
        try {
            if (that.source() != null) prevSource = log.useSource(that.source());

            // If there is a .jml file containing the specifications, then just use those instead of the annotations in the
            // .java file. FIXME - really we should always be looking in the specs database, rather than modifying the ast
            JCModifiers originalMods = that.mods;
            JCModifiers newMods = originalMods;
            if (that.specsDecl != null) newMods = that.mods = that.specsDecl.mods;

            // FIXME - we should not need these two lines I think, but otherwise we get NPE faults on non_null field declarations
            attribAnnotationTypes(that.mods.annotations,env); annotate.flush(); 
            for (JCAnnotation a: that.mods.annotations) a.type = a.annotationType.type;

            boolean prev = false;
            boolean isReplacementType = that.jmltype;
            if (utils.isJML(that.mods) || isReplacementType) {
                prev = ((JmlResolve)rs).setAllowJML(true);
            }
            if (utils.isJML(that.mods)) currentClauseType = JmlTokenKind.JMLDECL; // FIXME - could be model, if it matters
            if (that.vartype.type == null) attribType(that.vartype,env);
            if (that.originalVartype != null && that.originalVartype.type == null) attribType(that.originalVartype,env);
//            if (that.name.toString().equals("objectState")) Utils.stop();
            ((JmlMemberEnter)memberEnter).dojml = true;
            visitVarDef(that);
            ((JmlMemberEnter)memberEnter).dojml = false;
            if (that.sym == null) return; // Duplicate to be removed 
            // Anonymous classes construct synthetic members (constructors at least)
            // which are not JML nodes.
            FieldSpecs fspecs = specs.getSpecs(that.sym);
            
            // We do the checking of in and maps clauses after all fields and methods have been attributed
            //if (fspecs != null) for (JmlTypeClause spec:  fspecs.list) spec.accept(this);

            if (!that.type.isPrimitive()) {
                JCAnnotation snullness;
                JmlTokenKind nullness = specs.defaultNullity(enclosingClassEnv.enclClass.sym);
                if ((snullness=utils.findMod(that.mods,nonnullAnnotationSymbol)) != null) { 
                    nullness = JmlTokenKind.NONNULL;
                } else if ((snullness=utils.findMod(that.mods,nullableAnnotationSymbol)) != null || skipDefaultNullity) {
                    nullness = JmlTokenKind.NULLABLE;
                } else {
                    Symbol s = (nullness == JmlTokenKind.NONNULL) ? nonnullAnnotationSymbol : nullableAnnotationSymbol;
                    Attribute.Compound a = new Attribute.Compound(s.type,List.<Pair<MethodSymbol,Attribute>>nil());
                    that.sym.appendAttributes(List.<Compound>of(a));
                    JCAnnotation an = factory.at(that).Annotation(a);  // FIXME - needs a position and a source - we should get the NonNullByDefault if possible
                    ((JmlTree.JmlAnnotation)an).sourcefile = that.sourcefile;
                    an.type = an.annotationType.type;
                    that.mods.annotations = that.mods.annotations.append(an);
                    snullness = an;
                }
                Symbol s = (nullness == JmlTokenKind.NONNULL) ? nonnullAnnotationSymbol : nullableAnnotationSymbol;
                if (that.sym.attribute(s) == null) {
                    Attribute.Compound a = new Attribute.Compound(s.type,List.<Pair<MethodSymbol,Attribute>>nil());
                    that.sym.appendAttributes(List.<Compound>of(a));
                }
            }
            //        if (newMods != originalMods) for (JCAnnotation a: originalMods.annotations) { a.type = attribType(a,env); }


            // Check the mods after the specs, because the modifier checks depend on
            // the specification clauses being attributed

            that.mods = originalMods; 
            if (!that.type.isErroneous()) checkVarMods(that);
            that.mods = newMods;
            if (utils.isJML(that.mods)) prev = ((JmlResolve)rs).setAllowJML(prev);

            //        if (that.specsDecl != null) {
            //            that.mods.annotations = that.specsDecl.mods.annotations;
            //        }
        } finally {
            if (prevSource != null) log.useSource(prevSource);
            currentClauseType = saved;
        }
    }
    
    boolean skipDefaultNullity = false;
    
    @Override
    public void visitLambda(final JCLambda that) {
        boolean saved = skipDefaultNullity;
        try {
            skipDefaultNullity = true;
            super.visitLambda(that);
        } finally {
            skipDefaultNullity = saved;
        }
    }

    
    // These are here mostly to make them visible to extensions

    /** This is here also to do some checking for missing implementations */
    @Override
    public Type attribExpr(JCTree tree, Env<AttrContext> env, Type pt) {
        Type type = super.attribExpr(tree,env,pt);
        return type;
    }
    
    public Symbol attribIdent(JCTree tree, JCCompilationUnit topLevel) {
        Symbol s = super.attribIdent(tree,topLevel);
        return s;
    }

    
    /** Attribute the arguments in a method call, returning a list of types;
     * the arguments themselves have their types recorded.
     */
    @Override   // FIXME _ why is this needed?
    public int attribArgs(int initialKind, List<JCExpression> trees, Env<AttrContext> env, ListBuffer<Type> argtypes) {
        return super.attribArgs(initialKind, trees, env, argtypes);
    }
    
    public int attribArgs(List<JCExpression> trees, Env<AttrContext> env, ListBuffer<Type> argtypes) {
        return super.attribArgs(Kinds.VAL, trees, env, argtypes);
    }
    
    /** Attribute the elements of a type argument list, returning a list of types;
     * the type arguments themselves have their types recorded.
     */
    @Override 
    public List<Type> attribTypes(List<JCExpression> trees, Env<AttrContext> env) {
        return super.attribTypes(trees,env);
    }

    boolean checkingSignature = false;
    
    public void visitJmlMethodSig(JmlMethodSig that) {
        Env<AttrContext> localEnv = env.dup(that.expression, env.info.dup());

        List<Type> argtypes = that.argtypes != null ? super.attribAnyTypes(that.argtypes, localEnv) : List.<Type>nil();
        List<Type> typeargtypes = List.<Type>nil(); // attribAnyTypes(that.typeargs, localEnv);// FIXME - need to handle template arguments

        Name methName = TreeInfo.name(that.expression);

        boolean isConstructorCall =
            methName == enclosingClassEnv.enclClass.sym.name;
        
        // ... and attribute the method using as a prototype a methodtype
        // whose formal argument types is exactly the list of actual
        // arguments (this will also set the method symbol).
        
        if (isConstructorCall) {
            // Adapted from Attr.visitApply // FIXME - may not be general enough
            Type clazztype = attribType(that.expression, env);
            ClassType site = new ClassType(clazztype.getEnclosingType(),
                    clazztype.tsym.type.getTypeArguments(),
                    clazztype.tsym);

            Env<AttrContext> diamondEnv = localEnv.dup(that);
            diamondEnv.info.selectSuper = false;
            diamondEnv.info.pendingResolutionPhase = null;

            //if the type of the instance creation expression is a class type
            //apply method resolution inference (JLS 15.12.2.7). The return type
            //of the resolved constructor will be a partially instantiated type
            Symbol constructor = rs.resolveDiamond(that.pos(),
                    diamondEnv,
                    site,
                    argtypes,
                    typeargtypes);
            that.methodSymbol = (MethodSymbol)constructor.baseSymbol();
            
        } else {
            // Adapted from Attr.visitMethodDef // FIXME - may not be general enough
            int kind = VAL; // FIXME - could also be POLY
            Type mpt = newMethodTemplate(Type.noType, argtypes, typeargtypes);
            localEnv.info.pendingResolutionPhase = null;
            boolean prev = checkingSignature;
            checkingSignature = true;
            Type mtype = attribTree(that.expression, localEnv, new ResultInfo(kind, mpt, chk.basicHandler));
            checkingSignature = prev;

            Symbol sym = null;
            if (that.expression instanceof JCFieldAccess) {
                sym = ((JCFieldAccess)that.expression).sym;
            } else { // JCIdent
                sym = ((JCIdent)that.expression).sym;
            }
            if (sym instanceof MethodSymbol) that.methodSymbol = (MethodSymbol)sym;
            else {
                // Constructor ?
                // FIXME
            }
        }
        
//        // FIXME - need a better check that the expression is a constructor
//        // This won't even work if the method has the class name as a suffix
//        Name name;
//        Type classType;
//        if (that.expression instanceof JCIdent) {
//            name = ((JCIdent)that.expression).name;
//            classType = env.enclClass.type;
//        } else {
//            JCFieldAccess fa = (JCFieldAccess)that.expression;
//            name = fa.name;
//            if (fa.selected instanceof JCIdent && ((JCIdent)fa.selected).name == names._this) {
//                attribExpr(fa.selected,localEnv);
//                classType = fa.selected.type;
//            } else {
//                attribExpr(fa.selected,localEnv);
//                classType = fa.selected.type;
//            }
//        }
//        if (name.toString().equals(env.enclClass.name.toString())) {
//            Symbol sym = jmlresolve.resolveConstructor(that.pos(),localEnv,
//                    env.enclClass.type,
//                    argtypes,
//                    typeargtypes);
//            that.methodSymbol = (MethodSymbol)sym;
//        } else {
//            Symbol sym = jmlresolve.resolveMethod(that.pos(), localEnv, name, argtypes, typeargtypes);
//            //Symbol sym = jmlresolve.findMethod(localEnv, classType, name, argtypes, typeargtypes,false,false,false);
//
//            // If there was an error attributing the JmlMethodSig, then sym
//            // will not be a MethodSymbol
////            if (!(sym instanceof MethodSymbol)) {
////                jmlerror(that,"internal.error","No method found with the given signature");
////            }
//            that.methodSymbol = sym instanceof MethodSymbol ? (MethodSymbol)sym : null;
//        }
    }

    public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
        // TODO Auto-generated method stub
        
    }
    
    public void jmlerror(int begin, int end, String key, Object... args) {
        log.error(new JmlTokenizer.DiagnosticPositionSE(begin,end-1),key,convertErrorArgs(args));
    }

    public void jmlerror(JCTree tree, String key, Object... args) {
        log.error(new JmlTokenizer.DiagnosticPositionSE(tree.pos,tree.getEndPosition(log.currentSource().getEndPosTable())),key,convertErrorArgs(args));
    }
    
    public Object[] convertErrorArgs(Object[] args) {
        Object[] out = new Object[args.length];
        for (int i=0; i<args.length; i++) {
            Object a = args[i];
            out[i] = a instanceof JCTree ? JmlPretty.write((JCTree)a) : a;
        }
        return args;
    }
    
    public static class RACCopy extends JmlTreeCopier {
        
        List<JCVariableDecl> decls;
        Names names = Names.instance(context);
        Symtab syms = Symtab.instance(context);
        ListBuffer<JCExpression> arguments;
        JCIdent argsID;
        
        Map<Symbol,JCIdent> newids;
        
        public RACCopy(Context context, List<JCVariableDecl> decls, ListBuffer<JCExpression> args, JCIdent argsID, Map<Symbol,JCIdent> newids) {
            super(context, JmlTree.Maker.instance(context));
            this.decls = decls;
            this.arguments = args;
            this.argsID = argsID;
            this.newids = newids;
        }
        
        public static JCExpression copy(JCExpression that, Context context, List<JCVariableDecl> decls, ListBuffer<JCExpression> args, JCIdent argsID, Map<Symbol,JCIdent> newids) {
            return new RACCopy(context,decls,args,argsID,newids).copy(that,(Void)null);
        }
        
        public <T extends JCTree> T copy(T tree, Void p) {
            if (tree == null) return null;
            if (!(tree instanceof JCIdent)) {

                if (tree instanceof JCExpression) {
                    JCExpression expr = (JCExpression)tree;
                    if (RACCheck.allInternal(expr,decls)) {
                        return tree;
                    }
                    if (RACCheck.allExternal(expr,decls)) {
                        if (expr.type.getTag() != TypeTag.METHOD) {
                            int n = arguments.size();
                            arguments.add(expr);
                            JCExpression lit = M.Literal(TypeTag.INT,n).setType(syms.intType);
                            JCExpression arg = M.Indexed(argsID,lit).setType(syms.objectType);
                            arg = M.TypeCast(M.Type(expr.type),arg).setType(expr.type);
                            return (T)arg;
                        }
                    }
                }
            }

            return (T) (tree.accept(this, p));
        }

        @Override
        public JCTree visitIdentifier(IdentifierTree node, Void p) {
            JCIdent expr = (JCIdent)node;
            if (!(expr.sym instanceof Symbol.VarSymbol)) { //Method and class symbols can be internal or external 
                return super.visitIdentifier(node,p);
            }
            
//            if (RACCheck.allInternal(expr,decls)) {
//                return expr;
//            }
            if (RACCheck.allExternal(expr,decls)) {
                int n = arguments.size();
                arguments.add(expr);
                JCExpression lit = M.Literal(TypeTag.INT,n).setType(syms.intType);
                JCExpression arg = M.Indexed(argsID,lit).setType(syms.objectType);
                arg = M.TypeCast(M.Type(expr.type),arg).setType(expr.type);  // M.Type sets its own type
                return arg;
            }
            
            Symbol n = expr.sym;
            JCIdent id = newids.get(n);
            if (id == null) {
                System.out.println("ERROR"); // FIXME
            }
            return id;

            // Include this for symmetry, but we acually should never get to this point
            // super.visitIdentifier(node,p);
        }
        
        @Override
        public JCTree visitJmlQuantifiedExpr(JmlQuantifiedExpr that, Void p) {
            return copy(that.racexpr);
//            List<JCVariableDecl> prevList = decls;
//            decls = decls.prependList(that.decls.toList());
//            try {
//                JCExpression newrange = copy(that.range);
//                JCExpression newvalue = copy(that.value);
//                return M.JmlQuantifiedExpr(that.op, that.decls, newrange, newvalue);
//            } finally {
//                decls = prevList;
//            }
        }

        
    }
    
    public static class RACCheck extends JmlTreeScanner {
        
        public static class RCheckEx extends RuntimeException {}
        
        boolean checkInternal;
        List<JCVariableDecl> decls;
        
        public RACCheck(List<JCVariableDecl> decls) {
            this.decls = decls;
        }
        
        public static boolean allInternal(JCExpression expr, List<JCVariableDecl> decls) {
            try {
                RACCheck s = new RACCheck(decls);
                s.checkInternal = true;
                expr.accept(s);
                return true;
            } catch (RCheckEx e) {
                return false;
            }
        }
        
        public static boolean allExternal(JCExpression expr, List<JCVariableDecl> decls) {
            try {
                RACCheck s = new RACCheck(decls);
                s.checkInternal = false;
                expr.accept(s);
                return true;
            } catch (RCheckEx e) {
                return false;
            }
        }
        
        @Override
        public void visitIdent(JCIdent that) {
            Symbol n = that.sym;
            if (!(n instanceof Symbol.VarSymbol)) return; //Method and class symbols can be internal or external 
            Iterator<JCVariableDecl> iter = decls.iterator();
            while (iter.hasNext()) {
                JCVariableDecl d = iter.next();
                if (d.sym.equals(n)) {
                    // identifier matches a quantifier declaration
                    // so it is definitely internal
                    //if (checkInternal) return;
                    throw new RCheckEx();
                }
            }
            // No matches found so the identifier is
            // definitely external
            if (checkInternal) throw new RCheckEx();
        }
        
        @Override
        public void visitJmlSingleton(JmlSingleton that) {
            if (that.token == JmlTokenKind.BSRESULT) {
                // external
                if (checkInternal) throw new RCheckEx();
            }
        }
        
        @Override
        public void visitJmlMethodInvocation(JmlMethodInvocation that) {
            if (that.token == JmlTokenKind.BSOLD || that.token == JmlTokenKind.BSPAST || that.token == JmlTokenKind.BSPRE) {
                // external
                if (checkInternal) throw new RCheckEx();
            }
        }
    }

    @Override
    protected boolean isBooleanOrNumeric(Env<AttrContext> env, JCExpression tree) {
        if (tree instanceof JmlExpression) {
            if (tree instanceof JmlQuantifiedExpr) return true; // At least for current quantifiers: forall, exists, sum, prod, num_of
            if (tree instanceof JmlSingleton) {
                JmlTokenKind kind = ((JmlSingleton)tree).token;
                if (kind == JmlTokenKind.INFORMAL_COMMENT) return true;
                if (kind == JmlTokenKind.BSRESULT) {
                    JCTree.JCMethodDecl md = enclosingMethodEnv.enclMethod;
                    JCTree res = md.getReturnType(); 
                    TypeTag t = res.type.getTag();
                    if (t == TypeTag.BOOLEAN || t == TypeTag.INT || t == TypeTag.LONG || t == TypeTag.SHORT || t == TypeTag.CHAR || t == TypeTag.BYTE) return true;
                    return false;
                }
            }
            jmlerror(tree,"jml.internal", "Unimplemented option in JmlAttr:isBooleanOrNumeric -- "  + tree.getClass());
            return false;
        }
        return super.isBooleanOrNumeric(env,tree);
    }

    public MethodSymbol makeInitializerMethodSymbol(long flags, Env<AttrContext> env) {
        JCTree tree = null;
        Env<AttrContext> localEnv =
                env.dup(tree, env.info.dup(env.info.scope.dupUnshared()));
        MethodSymbol msym = new MethodSymbol(flags | BLOCK |
                env.info.scope.owner.flags() & STRICTFP, names.empty, new Type.JCVoidType(),
                env.info.scope.owner);
        localEnv.info.scope.owner = msym;
        if ((flags & STATIC) != 0) localEnv.info.staticLevel++;
        return msym;
    }
    

}
