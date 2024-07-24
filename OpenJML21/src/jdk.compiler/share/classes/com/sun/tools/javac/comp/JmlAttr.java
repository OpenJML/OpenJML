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
import static com.sun.tools.javac.code.Kinds.Kind.*;
import static com.sun.tools.javac.code.Kinds.*;
import static com.sun.tools.javac.code.TypeTag.CLASS;
import static com.sun.tools.javac.code.TypeTag.ERROR;
import static com.sun.tools.javac.code.TypeTag.FORALL;
import static com.sun.tools.javac.code.TypeTag.METHOD;
import static com.sun.tools.javac.code.TypeTag.NONE;
import static com.sun.tools.javac.code.TypeTag.VOID;
import static com.sun.tools.javac.tree.JCTree.Tag.ASSIGN;
import static com.sun.tools.javac.tree.JCTree.Tag.METHODDEF;
import static com.sun.tools.javac.tree.JCTree.Tag.TYPEIDENT;
import static org.jmlspecs.openjml.ext.Modifiers.*;
import static org.jmlspecs.openjml.ext.MethodSimpleClauseExtensions.*;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.*;
import static org.jmlspecs.openjml.ext.RecommendsClause.*;
import static org.jmlspecs.openjml.ext.MethodDeclClauseExtension.*;
import static org.jmlspecs.openjml.ext.MethodResourceClauseExtension.*;
import static org.jmlspecs.openjml.ext.CallableClauseExtension.*;
import static org.jmlspecs.openjml.ext.FunctionLikeExpressions.nonnullelementsKind;
import static org.jmlspecs.openjml.ext.AssignableClauseExtension.*;
import static org.jmlspecs.openjml.ext.SignalsClauseExtension.*;
import static org.jmlspecs.openjml.ext.SignalsOnlyClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeExprClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeInClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeMapsClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeRepresentsClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeInitializerClauseExtension.*;
import static org.jmlspecs.openjml.ext.StatementExprExtensions.*;
import static org.jmlspecs.openjml.ext.StatementLocationsExtension.*;
import static org.jmlspecs.openjml.ext.SingletonExpressions.*;
import static org.jmlspecs.openjml.ext.QuantifiedExpressions.*;
import static org.jmlspecs.openjml.ext.MiscExtensions.*;
import static org.jmlspecs.openjml.ext.JmlPrimitiveTypes.*;
import static org.jmlspecs.openjml.ext.ShowStatement.*;
import com.sun.tools.javac.main.JmlCompiler;
import com.sun.tools.javac.parser.JmlToken;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.Stack;
import java.util.function.Function;

import javax.lang.model.type.TypeKind;
import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.IJmlClauseKind.LineAnnotationKind;
import org.jmlspecs.openjml.IJmlClauseKind.ModifierKind;
import org.jmlspecs.openjml.JmlSpecs.MethodSpecs;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;

import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.ext.*;

import static org.jmlspecs.openjml.ext.MethodSimpleClauseExtensions.*;
import static org.jmlspecs.openjml.ext.JmlOperatorKind.*;
import static org.jmlspecs.openjml.ext.StateExpressions.*;
import org.jmlspecs.openjml.ext.ArrayFieldExtension.JmlField;
import org.jmlspecs.openjml.ext.LineAnnotationClauses.ExceptionLineAnnotation;
import org.jmlspecs.openjml.visitors.IJmlVisitor;
import org.jmlspecs.openjml.visitors.JmlTreeCopier;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.smtlib.SymbolTable;

import com.sun.source.tree.IdentifierTree;
import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Scope.*;
import com.sun.tools.javac.code.Attribute.Compound;
import com.sun.tools.javac.code.Attribute.TypeCompound;
import com.sun.tools.javac.code.Kinds.KindSelector;
import com.sun.tools.javac.code.Symbol.BindingSymbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.CompletionFailure;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.OperatorSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.comp.ArgumentAttr.ArgumentType;
import com.sun.tools.javac.comp.ArgumentAttr.UniquePos;
import com.sun.tools.javac.comp.Attr.MethodAttrInfo;
import com.sun.tools.javac.comp.Attr.PostAttrAnalyzer;
import com.sun.tools.javac.comp.Attr.ResultInfo;
import com.sun.tools.javac.comp.Attr.TypeAnnotationsValidator;
import com.sun.tools.javac.comp.MatchBindingsComputer.MatchBindings;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.JmlScanner;
import com.sun.tools.javac.parser.JmlTokenizer;
import com.sun.tools.javac.tree.EndPosTable;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.Pretty;
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
import com.sun.tools.javac.util.PropagatedException;

/**
 * This class is an extension of the Attr class; it adds visitors methods so
 * that as the Attr class walks the entire AST, attributing all nodes 
 * (i.e., doing name lookup and type assignment), the JML parts of the source tree are
 * attributed and checked as well.
 * <P>
 * On input to this class all top-level types and all their members,
 * recursively, are already entered into the symbol table, but local classes and
 * declarations are not. The types of all annotations and of member
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
	
	final static boolean debugAttr = org.jmlspecs.openjml.Utils.debug("attr");
	
    public void validateTypeAnnotations(JCTree tree, boolean sigOnly) {
        tree.accept(new JmlTypeAnnotationsValidator(sigOnly));
    }
	public class JmlTypeAnnotationsValidator extends Attr.TypeAnnotationsValidator implements IJmlVisitor {

		public JmlTypeAnnotationsValidator(boolean sigOnly) {
			super(sigOnly);
		}
		
	}

    /** This is the compilation context for which this is the unique instance */
    /*@non_null*/ final public Context context;
    
    /** The Name version of resultVarString in the current context */
    /*@non_null*/ final public Name resultName;
    
    /** The Name version of exceptionVarString in the current context */
    /*@non_null*/ final public Name exceptionName;

    /** The fully-qualified name of the Runtime class */
    // Use .class on the class name instead of a string so that an error happens if the class is renamed
    // This class is in the runtime library
    /*@non_null*/ public static String runtimeClassName = "org.jmlspecs.runtime.Runtime";
    
    /** Cached symbol of the org.jmlspecs.runtiome.Runtime class */
    /*@non_null*/ public ClassSymbol runtimeClass;
    
    /** Cached identifier of the org.jmlspecs.runtime.Runtime class */
    /*@non_null*/ protected JCIdent runtimeClassIdent;
    
    /** Cached value of the datagroup class */
    /*@non_null*/ public ClassSymbol datagroupClass;
    
    /** The JmlSpecs instance for this context */
    /*@non_null*/ final protected JmlSpecs specs;
    
    /** The Utils instance for this context */
    /*@non_null*/ final public Utils utils;

    /** The Types instance for this context */
    /*@non_null*/ final public JmlTypes jmltypes;

    /** The Names table from the compilation context, initialized in the constructor */
    /*@non_null*/
    public final Names names;
    
    /** The tool used to read binary classes */
    /*@non_null*/ final public ClassReader classReader;
    
    /** The factory used to create AST nodes, initialized in the constructor */
    /*@non_null*/ final public JmlTree.Maker jmlMaker;
    
    /** A JmlResolve instance */
    /*@non_null*/ final public JmlResolve jmlresolve;
    
    /** An instance of the tree utility class */
    /*@non_null*/ public JmlTreeUtils treeutils; // initialized later to avoid circular tool instantiations

    /** A Literal for a boolean true */
    /*@non_null*/ protected JCLiteral trueLit;
    
    /** A Literal for a boolean false */
    /*@non_null*/ protected JCLiteral falseLit;
    
    /** A Literal for a null constant */
    /*@non_null*/ protected JCLiteral nullLit;
    
    /** A Literal for an int zero */
    /*@non_null*/ protected JCLiteral zeroLit;
    
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
    public Type Lock;// = new Type(1003,null);
    public Type LockSet;// = new Type(1004,null);
    public Type JMLValuesType;
    public Type JMLIterType;
    public Type JMLSetType;
    public Type JMLArrayLike;
    public Type JMLIntArrayLike;
    public Type JMLPrimitive;
    
    public Name oldLabel;
    public Name hereLabel;
    public Name preLabel;
    
    // The following fields are stacked as the environment changes as one
    // visits down the tree.
        
    /** Holds the env of the enclosing method for subtrees of a MethodDecl. */
    public Env<AttrContext> enclosingMethodEnv = null;
    
    /** Holds the env of the enclosing class for subtrees of a ClassDecl. */
    protected Env<AttrContext> enclosingClassEnv = null;
    
    /** Set to true when we are within a JML declaration */
    protected boolean isInJmlDeclaration = false;
 
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
        this.names = Names.instance(context);
        this.utils = Utils.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.jmlMaker = (JmlTree.Maker)super.make; // same as super.make
        //this.names = Names.instance(context);
        this.classReader = ClassReader.instance(context);
        this.jmltypes = (JmlTypes)super.types;  // same as super.types
        //this.classReader.init(syms);
        this.jmlresolve = (JmlResolve)super.rs;
        
        this.oldLabel = names.fromString(Strings.oldLabelBuiltin);
        this.preLabel = names.fromString(Strings.preLabelBuiltin);
        this.hereLabel = names.fromString(Strings.hereLabelBuiltin);
        jmlenv.currentOldLabel = preLabel;
        
        // Caution, because of circular dependencies among constructors of the
        // various tools, it can happen that syms is not fully constructed at this
        // point and syms.objectType will be null.
        if (syms.objectType == null) {
            System.err.println("INTERNAL FAILURE: A circular dependency among constructors has caused a failure to correctly construct objects.  Please report this internal problem.");
            // Stack trace is printed inside the constructor
            throw new JmlInternalError();
        }


        this.resultName = names.fromString(Strings.resultVarString);
        this.exceptionName = names.fromString(Strings.exceptionVarString);
        

    }
    
    public void init() {
        this.treeutils = JmlTreeUtils.instance(context);
        initAnnotationNames(context);
        runtimeClass = createClass(runtimeClassName);
        runtimeClassIdent = jmlMaker.Ident(runtimeClassName);
        runtimeClassIdent.type = runtimeClass.type;
        runtimeClassIdent.sym = runtimeClassIdent.type.tsym;

        JMLSetType = createClass(Strings.jmlSpecsPackage + ".JMLSetType").type;
        JMLValuesType = createClass(Strings.jmlSpecsPackage + ".JMLList").type;
        JMLArrayLike = createClass(Strings.jmlSpecsPackage + ".IJmlArrayLike").type;
        JMLIntArrayLike = createClass(Strings.jmlSpecsPackage + ".IJmlIntArrayLike").type;
        JMLPrimitive = createClass(Strings.jmlSpecsPackage + ".IJmlPrimitiveType").type;
        JMLIterType = createClass("java.util.Iterator").type;
        Lock = syms.objectType;
        LockSet = JMLSetType;
        trueLit = makeLit(syms.booleanType,1);
        falseLit = makeLit(syms.booleanType,0);
        nullLit = makeLit(syms.botType,null);
        zeroLit = makeLit(syms.intType,0);
    }
 
    /** Returns (creating if necessary) a class symbol for a given fully-qualified name */
    public ClassSymbol createClass(String fqName) {
        return classReader.enterClass(Names.instance(context).fromString(fqName));
    }
    
    protected Env<AttrContext> getAppropriateClassEnv(ClassSymbol sym) {
        var env = super.getAppropriateClassEnv(sym);
        if (utils.isModel(sym)) { env = specs.get(sym).specsEnv; }
        return env;
    }


    
    /** Overrides the super class call in order to perform JML checks on class
     * modifiers.  (Actually, the work was moved to attribClassBody since attribClass
     * gets called multiple times for a Class).
     * @param c The class to check
     * @throws CompletionFailure
     */
    @Override
    public void attribClass(ClassSymbol c) throws CompletionFailure {
        if (c == null) return; // Defensive. Should actually not get this case, but appears to result from previous errors sometimes.
        
//    	if (c.type instanceof Type.IntersectionClassType) {
//    		// FIXME - what should we do in this case?
//    		super.attribClass(c);
//    		return;
//    	}
    	boolean print = org.jmlspecs.openjml.Utils.isJML() && c.toString().contains("Enum");
    	if (debugAttr) System.out.println("Attributing class " + c + " " + level + " " + ((c.flags_field & UNATTRIBUTED) != 0));
    	if (!(c.owner instanceof ClassSymbol || c.owner instanceof PackageSymbol)) {
    		// A local class
    		var classEnv = typeEnvs.get(c);
    		if (classEnv == null) {
    			// This branch happens for calls to clone() (at least)
    			//System.out.println("NULL ENV FOR " + c + " " + c.owner);
                super.attribClass(c);
    			return;
    		}
    		JmlClassDecl tree = (JmlClassDecl)classEnv.tree;
    		if (specs.status(c).less(JmlSpecs.SpecsStatus.SPECS_LOADED)) {
    			var tspecs = new JmlSpecs.TypeSpecs(tree, tree, classEnv);
    			specs.putSpecs(c, tspecs);
    		}
    	}
        boolean isUnattributed =  (c.flags_field & UNATTRIBUTED) != 0;
//        if (!isUnattributed && c.isEnum()) {
//            JmlClassDecl tr = (JmlClassDecl)(typeEnvs.get(c).tree);
//            if (utils.isSpecFile(tr.sourcefile)) c.flags_field |= UNATTRIBUTED;
//        }
        level++;
        if (c != syms.predefClass) {
            if (utils.jmlverbose >= Utils.JMLVERBOSE) context.get(Main.IProgressListener.class).report(2,"typechecking " + c);
        }

        // We track jmlenv.inPureEnvironment since calls can be nested -
        // we can enter a pure environment from either an impure or pure
        // environment and we need to restore it properly.  Also, when in a
        // pure environment we may need to attribute a class, not all of which
        // is pure.
        var check = jmlenv = jmlenv.pushCopy();
        jmlenv.inPureEnvironment = false;  //System.out.println("PUREENV SET FALSE"); Utils.dumpStack();
        try {
            
            // Loading the specs makes sure that modifiers are present when nested declarations are attributed
            JmlSpecs.instance(context).getLoadedSpecs(c);
        	super.attribClass(c);

            // thisSymbol is needed in some cases (e.g. in creating default specs) before attributing the whiole class
            Env<AttrContext> e = enter.getEnv(c);
            if (e != null && e.tree instanceof JmlClassDecl) {
                Symbol thissym = thisSym(e.tree.pos(),e);
                if (thissym instanceof VarSymbol) ((JmlClassDecl)e.tree).thisSymbol = (VarSymbol)thissym;
            }

            specs.getAttrSpecs(c); // if not yet attributed, attribute the specs // FIXME - not needed
        	//if (org.jmlspecs.openjml.Utils.isJML()) System.out.println("ATTRIBCLASS-L " + c + " " + !isUnattributed);
            if (!isUnattributed) return;
        	//if (org.jmlspecs.openjml.Utils.isJML()) System.out.println("ATTRIBCLASS-M " + c);

            addClassInferredSpecs(c);
        } catch (Exception e) {
        	System.out.println("EXCEPTION IN attribClass-Y " + c + " " + c.type);
        	e.printStackTrace(System.out);
        	throw e;
        } finally {
            jmlenv = jmlenv.pop(check);
            level--;
            if (c != syms.predefClass) {
                if (utils.progress()) context.get(Main.IProgressListener.class).report(2,"typechecked " + c);
            }
            if (debugAttr) System.out.println("Attributing-complete " + c + " " + level);
        	//if (org.jmlspecs.openjml.Utils.isJML()) System.out.println("ATTRIBCLASS-Z " + c);
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
                        FieldSpecs fspecs = specs.getAttrSpecs(vdecl.sym);
                        if (fspecs != null) {
                        	attribAnnotationTypes(fspecs.mods.annotations, env);
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
        while (!todo.isEmpty()) {
            ClassSymbol sym = todo.remove(0);
            if (debugAttr) System.out.println("Retrieved for attribution " + sym + " " + todo.size());
            try {
                level++;
            	attribClass(sym);
            } catch (Exception e) {
            	System.out.println("EXCEPTION DURING attribClass of " + sym);
            	e.printStackTrace(System.out);
            	throw e;
            } finally {
                level--;
            }
        }
    }
    
    /** Adds a class symbol to the list of classes to be attributed later */
    public void addTodo(ClassSymbol c) {
        if (!todo.contains(c)) {
            if (!utils.isTypeChecked(c)) {
            	todo.add(c);
                if (debugAttr) System.out.println("Queueing for attribution " + c + " " + utils.isTypeChecked(c) + " " + todo.size());
            }
        }
    }
    
    boolean attribJmlDecls = true;
    
    /** Overrides in order to attribute class specs appropriately. */
    @Override
    protected void attribClassBody(Env<AttrContext> env, ClassSymbol c) {
        Env<AttrContext> prevClassEnv = enclosingClassEnv;
        enclosingClassEnv = env;

        // FIXME - for a binary class c, env.tree appears to be the tree of the specs
        // FIXME - why should we attribute the Java class body in the case of a binary class
        
        boolean prevIsInJmlDeclaration = isInJmlDeclaration;
        isInJmlDeclaration = utils.isJML(c.flags());  // REMOVED implementationAllowed ||
        ((JmlCheck)chk).setInJml(isInJmlDeclaration);
        JavaFileObject prev = log.useSource(((JmlClassDecl)env.enclClass).toplevel.sourcefile);  // FIXME - no write for multiple source files
        var savedAttribJmlDecls = this.attribJmlDecls;
        attribJmlDecls = utils.isJML(c.flags()) || true;
        try {
            // If the class is binary only, then we have not yet attributed the super/extending/implementing classes in the source AST for the specifications
            
            JmlClassDecl cd = (JmlClassDecl)env.tree;
            if (cd != null) {
                JCExpression e = cd.extending;
                if (e != null && e.type == null) attribType(e,env);
                for (JCExpression ee: cd.implementing) {
                    if (ee.type == null) attribType(ee,env);
                }
            }
            
            // The JML specs to check are are in the TypeSpecs structure

            //if (env.tree instanceof JCClassDecl cdd) System.out.println("JMLATTR " + c + " " + cdd.name + " " + cdd.sym + " " + (c == cd.sym) + " " + c.hashCode() + " " + cdd.sym.hashCode() + " " + env + " " + env.hashCode());
            super.attribClassBody(env,c);
            if (cd != null && cd.lineAnnotations != null) {
                for (ExceptionLineAnnotation a: cd.lineAnnotations) {
                    a.typecheck(this, env);
                }
            }
            
            specs.getAttrSpecs(c); // if not yet attributed, attribute the class specs
            
        } finally {
        	this.attribJmlDecls = savedAttribJmlDecls;
            isInJmlDeclaration = prevIsInJmlDeclaration;
            enclosingClassEnv = prevClassEnv;
            ((JmlCheck)chk).setInJml(isInJmlDeclaration);
            log.useSource(prev);
        }
    }
    
    @Override
    public Type attribStat(JCTree tree, Env<AttrContext> env) {
    	// The type clauses that need checking are the ones in the specs database, not those
    	// parsed in the class body (though they may be the same)
        if (tree instanceof JmlTypeClause) return null;
        try {
        return super.attribStat(tree,env);
        } catch (Exception e) {
            e.printStackTrace(System.out);
        	System.out.println("EXZCEPTION ON STAT " + env.enclClass.name + " " + tree + " RNV: " + env);
        	throw e;
        }
    }

    
    /** Attributes the specs (in the TypeSpecs structure) for the given class
     * 
     * @param env the current class environment
     * @param c the current class
     * @param prevIsInJmlDeclaration true if we are in a non-model JML declaration  (FIXME - this needs better evaluation)
     */
    public void attribClassBodySpecs(JmlClassDecl c) {
    	if (debugAttr) System.out.println("Attributing class body specs of " + c.sym + " " + specs.status(c.sym));
    	specs.getAttrSpecs(c.sym); // Attributing specs, if not already done
    	if (true || !utils.esc) {
    		for (var d: c.defs) {
    			if (d instanceof JCMethodDecl) {
    				var msym = ((JCMethodDecl)d).sym;
    				if (!utils.isJML(msym.flags())) specs.getAttrSpecs(msym);
    			}
    			else if (d instanceof JCVariableDecl) {
    				JCVariableDecl v = (JCVariableDecl)d;
    				if (v.sym != null) { // v.sym == null if there is an error in JmlEnter
    					if (v.type.isReference() && v.type.tsym instanceof ClassSymbol) specs.getAttrSpecs((ClassSymbol)v.type.tsym);
    					specs.getAttrSpecs(v.sym);
    				}
    			}
    			else if (d instanceof JCClassDecl) {
    				var csym = ((JCClassDecl)d).sym;
    				if (!utils.isJML(csym.flags())) specs.getAttrSpecs(csym);
    			}
    			else if (d instanceof JmlBlock) {
    				JmlBlock bl = (JmlBlock)d;
    				if (bl.blockSpecs != null) {
    					attrSpecs(bl.blockSpecs);
    				}
    			}
    		}
    		var saved = this.attribJmlDecls;
    		this.attribJmlDecls = true;
    		for (var s: c.sym.members().getSymbols()) {
    			// This will attribute the correct spec declarations, as entered in JmlEnter
    			// It may also repeat any of the above
    			// This will not include any Java initialization blocks
    			// TODO: Does it include JML initialization specs?
    			specs.getAttrSpecs(s);
    		}
    		this.attribJmlDecls = saved;
   	}

//        JmlSpecs.TypeSpecs tspecs = JmlSpecs.instance(context).get(c);
//        JmlClassDecl classDecl = (JmlClassDecl)env.tree;
//        JavaFileObject prev = log.currentSourceFile();
//        
////        if (c.flatName().toString().equals("java.lang.Throwable")) Utils.stop();
//        
//        // This is not recursive within a class, but we can call out to attribute 
//        // another class while in the middle of a clause
//        IJmlClauseKind prevClauseType = currentClauseType;
//        
//        try {
//            if (tspecs != null) {
//                Env<AttrContext> prevEnv = this.env;
//                this.env = env;
//
//                // The modifiers and annotations are checked in checkClassMods
//                // which is part of checking the class itself
//
//                // clauses and declarations
//                for (JmlTypeClause clause: tspecs.clauses) {
//                    currentClauseType = clause.clauseType;
//                    clause.accept(this);
//                }
//                currentClauseType = null;
//
//                // model types, which are not in clauses
//
////                for (JmlClassDecl mtype: tspecs.modelTypes) {
////                    mtype.accept(this);
////                }
//
//                //            // Do the specs for JML initialization blocks // FIXME - test the need for this - for initializatino blocks and JML initializations
//                //            for (JCTree.JCBlock m: tspecs.blocks.keySet()) {
//                //                m.accept(this);
//                //            }
//
//
//                if (tspecs.modifiers != null) {
//                    log.useSource(tspecs.file);
//                    attribAnnotationTypes(tspecs.modifiers.annotations,env);
//                    isInJmlDeclaration = prevIsInJmlDeclaration;
//                    ((JmlCheck)chk).setInJml(isInJmlDeclaration);
//                    if (tspecs.file != null) log.useSource(tspecs.file);
//                    checkClassMods(c,classDecl,tspecs);
//                } else {
////                    log.warning("jml.internal.notsobad","Unexpected lack of modifiers in class specs structure for " + c); // FIXME - testJML2
//                }
//                
//                // Checking all the in and maps clauses is delayed until all the fields have been processed 
//
//                for (JCTree t: classDecl.defs) {
//                    if (t instanceof JmlVariableDecl) {
//                        checkVarMods2((JmlVariableDecl)t);
//                    }
//                }
//
//                this.env = prevEnv;
//            } else if (c.type instanceof Type.IntersectionClassType){
//            	// FIXME - what should really be done here
//            } else {
//            	utils.warning("jml.internal.notsobad","Unexpected lack of class specs structure for " + c);
//            }
//        } finally {
//            currentClauseType = prevClauseType;
//            log.useSource(prev);
//        }
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
        
        // FIXME - what about initializer blocks - they also need an old environment
        // FIXME - this overlaps too much with the superclass method
        
        boolean prev = jmlresolve.allowJML();
        if (!prev && env.enclMethod == null) prev = jmlresolve.setAllowJML(utils.isJML(env.enclClass.mods));
        super.visitBlock(tree);
        if (env.info.scope.owner.kind == TYP || env.info.scope.owner.kind == ERR) {
            // An initialization block within a class -- we create a BlockSpecs, now that we know the env
            
        	JmlBlock block = (JmlBlock)tree;
        	Symbol fakeOwner =
        			new MethodSymbol(tree.flags | BLOCK | (block.flags & Flags.STATIC) |
        					env.info.scope.owner.flags() & STRICTFP, names.empty, null,
        					env.info.scope.owner);
        	jmlenv = jmlenv.pushCopy();
        	jmlenv.enclosingMethodDecl = null;
        	final Env<AttrContext> localEnv =
        			env.dup(tree, env.info.dup(env.info.scope.dupUnshared(fakeOwner)));
        	//System.out.println("CREATED BLOCK SPEC " + (block.flags & Flags.STATIC) + " " + (block.specificationCases==null) + " " + block.specificationCases);
        	if (block.specificationCases != null) {
                var prevEnv = this.env;
                this.env = localEnv;
                if (isStatic(tree.flags)) localEnv.info.staticLevel++;
        	    block.specificationCases.accept(this);
                if (isStatic(tree.flags)) localEnv.info.staticLevel--;
                this.env = prevEnv;
        	}
        	// FIXME - don't think this is needed
            JmlModifiers mods = jmlMaker.Modifiers(block.flags, null, null); // TODO - allow annotations?
        	block.blockSpecs = new JmlSpecs.BlockSpecs(mods,block.specificationCases, localEnv);
        	jmlenv = jmlenv.pop();
        }
        jmlresolve.setAllowJML(prev);
   }
   
    @Override
    protected void postInitBlock(JCBlock tree, Env<AttrContext> env) {
        JmlSpecs.MethodSpecs msp = JmlSpecs.instance(context).getAttrSpecs(env.enclClass.sym,tree);
        if (msp != null) {
            JmlMethodSpecs sp = msp.cases;
            attribStat(sp, env);
        }
    }
    
    @Override
    protected void preMethodBlock(Env<AttrContext> env, JCBlock tree) {
//    	boolean topMethodBodyBlock = env.enclMethod != null &&
//    			env.enclMethod.body == tree;
//    	if (!topMethodBodyBlock) return;
//    	
//    	// Scope is not duplicated
//    	enclosingMethodEnv = env.dup(env.tree,env.info.dupUnshared());
//
//    	//if (!isStatic(env.enclMethod.mods.flags)) {
//    	if (env.info.staticLevel == 0) {
//    		((JmlMethodDecl)env.enclMethod)._this = (VarSymbol)thisSym(tree.pos(),enclosingMethodEnv);
//    	}
//    	
//    	specs.get(env.enclMethod.sym).specsEnv = enclosingMethodEnv;
//
    }
    
    @Override
    public void visitUnary(JCUnary tree) {
        super.visitUnary(tree);
        if (jmlenv.inPureEnvironment) {
            // FIXME - this and the next two happen in pure model methods - should probably treat them as pure methods and not pureEnvironments
            if (tree.arg instanceof JCIdent && ((JCIdent)tree.arg).sym.owner.kind == Kinds.Kind.MTH) return;
            JCTree.Tag op = tree.getTag();
            if (op == JCTree.Tag.PREINC || op == JCTree.Tag.POSTINC ||
                    op == JCTree.Tag.PREDEC || op == JCTree.Tag.POSTDEC)
                log.error(tree.pos,"jml.no.incdec.in.pure");
        }
    }

    @Override
    public void visitAssign(JCAssign tree) {
        super.visitAssign(tree);
        if (jmlenv.inPureEnvironment) {
            // The following checks that the assignment is local (the symbol being assigned is owned by the method)
            if (tree.lhs instanceof JCIdent && ((JCIdent)tree.lhs).sym.owner.kind == MTH) return;
            log.error(tree.pos,"jml.no.assign.in.pure");
        }
        if (utils.isExtensionValueType(tree.rhs.type) && !utils.isExtensionValueType(tree.lhs.type)) {
//            System.out.println(tree.rhs + " " + tree.rhs.type + " " + tree.rhs.getClass() + " " + utils.isExtensionValueType(tree.rhs.type) + " " + tree.lhs.type + " " + !utils.isExtensionValueType(tree.lhs.type));
//            System.out.println(tree.rhs.type.isReference() + " " + jmltypes().isSubtype(ct, interfaceForPrimitiveTypes()));
            utils.error(tree, "jml.message", "A JML primitive type may not be assigned or cast to a non-JML type");
        }
        // FIXME
//        if (tree.lhs instanceof JCArrayAccess && jmltypes.isSubtype(((JCArrayAccess)tree.lhs).indexed.type, JMLArrayLike)) {
//            JCArrayAccess aa = (JCArrayAccess)tree.lhs;
//            JCExpression ex = ((JCArrayAccess)tree.lhs).indexed;
//            if (ex instanceof JCIdent) {
//                //Change ex[i] = v to ex = ex.put(i,v);
//                Symbol sym = null;
//                java.util.List<Symbol> sys = ex.type.tsym.getEnclosedElements();
//                for (Symbol e: sys) {
//                    if ("put".equals(e.name.toString())) { sym = e; break; }
//                }
//                if (sym == null) {
//                    log.error(tree.pos,"jml.message","Could not find a 'put' method for " + ex.type.toString());
////                    JCExpression method = jmlMaker.Select(ex, names.fromString("put"));
////                    // TODO: DO we need method.type set?
////                    List<JCExpression> args = List.<JCExpression>of(aa.index, tree.rhs);
////                    JCMethodInvocation app = jmlMaker.Apply(List.<JCExpression>nil(), method, args);
////                    attribExpr(app.meth,env);
////                    app.type = ex.type;
////                    tree.lhs = ex;
////                    tree.rhs = app;
//                } else {
//                    JCExpression method = jmlMaker.Select(ex, sym);
//                    // TODO: DO we need method.type set?
//                    List<JCExpression> args = List.<JCExpression>of(aa.index, tree.rhs);
//                    JCExpression app = jmlMaker.Apply(List.<JCExpression>nil(), method, args);
//                    app.type = ex.type;
//                    tree.lhs = ex;
//                    tree.rhs = app;
//                }
//            } else {
//                log.error(tree.pos, "jml.message", "Assignment not permitted for indexed immutable JML primitives");
//            }
//        }
        if (tree.lhs instanceof JCFieldAccess fa) {
        	if (fa.selected.type.tsym instanceof ClassSymbol cs) {
        		var sp = specs.getAttrSpecs(cs);
        		var m = utils.findModifier(sp.modifiers, Modifiers.IMMUTABLE);
                if (m != null) {
                    utils.error(tree.pos, "jml.message", "Fields of an object with immutable type may not be modified: " + tree.lhs + " (" + fa.selected.type + ")");
        			utils.error(m.source, m, "jml.associated.decl.cf", utils.locationString(tree.pos));
                }
        	}
        }
        if (tree.lhs.type instanceof JmlListType) {
            JmlListType lhst = (JmlListType)tree.lhs.type;
            if (!(tree.rhs.type instanceof JmlListType)) {
                Type rt = tree.rhs.type;
                // We want to allow multiple type errors within the tuple- FIXME - log does not allow this anymore?
                for (int i = 0; i<lhst.types.size(); i++) {
                    Type lt = lhst.types.get(i);
                    if (!types.isAssignable(rt, lt)) {
                        utils.error(((JmlTuple)tree.lhs).values.get(i),"jml.message","Type " + rt + " cannot be assigned to " + lt + " (position " + (i+1) + ")");
                    }
                }
            } else {
                JmlListType rhst = (JmlListType)tree.rhs.type;
                if (lhst.types.size() != rhst.types.size()) {
                    utils.error(tree,"jml.message","Tuples have different sizes: " + lhst.types.size() + " vs. " + rhst.types.size());
                } else {
                    for (int i = 0; i<lhst.types.size(); i++) {
                        Type lt = lhst.types.get(i);
                        Type rt = rhst.types.get(i);
                        if (!types.isAssignable(rt, lt)) {
                            utils.error(((JmlTuple)tree.lhs).values.get(i),"jml.message","Type " + rt + " cannot be assigned to " + lt + " (position " + (i+1) + ")");
                        }
                    }
                }
            }
        }
        if (currentSecretContext != null) checkWritable(tree.lhs);
    }

    @Override
    public void visitAssignop(JCAssignOp tree) {
        super.visitAssignop(tree);
        if (jmlenv.inPureEnvironment) {
            // The following checks that the assignment is local (the symbol being assigned is owned by the method)
            if (tree.lhs instanceof JCIdent && ((JCIdent)tree.lhs).sym.owner.kind == MTH) return;
            log.error(tree.pos,"jml.no.assign.in.pure");
        }
        // FIXME - fix the test here - cannot reference org.jmlspecs.lang directly in the JDK compiler code
        //if (tree.lhs instanceof JCArrayAccess && ((JCArrayAccess)tree.lhs).indexed.type instanceof org.jmlspecs.lang.IJmlArrayLike) {
        //    log.error(tree.pos, "jml.message", "Assign operation not permitted for indexed immutable JML primitives");
        //}
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
            utils.error(lhs,"jml.not.writable.in.secret");  // FIXME - see what relaxed rules we can support; rely on assignable?
        }
        
        result = saved;
    }

    
    public ModifierKind[] allowedTypeModifiers = new ModifierKind[]{
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        OPTIONS, PURE, SPEC_PURE, STRICTLY_PURE, NO_STATE, MODEL, QUERY, SKIPRAC, NULLABLE_BY_DEFAULT, NON_NULL_BY_DEFAULT, IMMUTABLE,
        SPEC_PUBLIC, SPEC_PROTECTED};

    public ModifierKind[] allowedNestedTypeModifiers = new ModifierKind[]{
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        OPTIONS, PURE, SPEC_PURE, STRICTLY_PURE, NO_STATE, MODEL, QUERY, SPEC_PUBLIC, SPEC_PROTECTED, NULLABLE_BY_DEFAULT, NON_NULL_BY_DEFAULT, IMMUTABLE};

    public ModifierKind[] allowedNestedModelTypeModifiers = new ModifierKind[]{
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        OPTIONS, PURE, SPEC_PURE, STRICTLY_PURE, NO_STATE, MODEL, QUERY, NULLABLE_BY_DEFAULT, NON_NULL_BY_DEFAULT, IMMUTABLE};

    public ModifierKind[] allowedLocalTypeModifiers = new ModifierKind[]{
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        OPTIONS, PURE, SPEC_PURE, STRICTLY_PURE, NO_STATE, MODEL, QUERY, IMMUTABLE};

    /** This is a set of the modifiers that may be used to characterize a type. */
    public ModifierKind[] typeModifiers = new ModifierKind[]{NULLABLE,NON_NULL,BSREADONLY};

    /** Checks the JML modifiers so that only permitted combinations are present. */
    public void checkClassMods(ClassSymbol classSymbol, /*@ nullable */ JmlClassDecl javaDecl, JmlClassDecl specsDecl, TypeSpecs tspecs, Env<AttrContext> env) { // env should be specsEnv
        //System.out.println("Checking " + javaDecl.name + " in " + javaDecl.sym.owner);
        JavaFileObject prev = log.useSource(tspecs.file);
        checkTypeMatch(classSymbol, tspecs.specDecl);
        Symbol owner = classSymbol.owner;
        boolean ownerIsJML = utils.isJML(owner.flags());
        boolean isLocal = !(owner instanceof ClassSymbol ||owner instanceof PackageSymbol);
        JmlModifiers specsModifiers = tspecs.modifiers;

        annotationsToModifiers(specsModifiers, (JCExpression)null);
        boolean inJML = utils.isJML(specsModifiers);
        boolean isModel = utils.hasModifier(specsModifiers,Modifiers.MODEL);
        if (ownerIsJML && isModel) {
        	utils.error(tspecs.file,specsDecl,"jml.no.nested.model.type", classSymbol.name + " in " + classSymbol.owner);
        } else if (inJML && !isModel && !ownerIsJML) {
        	utils.error(tspecs.file,specsDecl,"jml.missing.model", classSymbol);
        } else if (!inJML && isModel) {
            var loc = utils.findModifier(specsModifiers,Modifiers.MODEL);
            utils.error(tspecs.file,loc,"jml.ghost.model.on.java", classSymbol);
        }
        
        if (specsDecl != javaDecl && specsDecl != null) {
            Env<AttrContext> specEnv = specsDecl.specEnv;
            Type sup = classSymbol.getSuperclass();
            if (!classSymbol.isInterface() && sup.getKind() != TypeKind.ERROR) {
                boolean specIsEnum = (specsDecl.mods.flags & Flags.ENUM) != 0;
                boolean specIsRecord = (specsDecl.mods.flags & Flags.RECORD) != 0;
                if (classSymbol.isEnum()) {
                    if (!specIsEnum) {
                        utils.error(specsDecl.sourcefile, specsDecl, "jml.message",  "The specification declaration must be an enum, because the source/binary is");
                    }
                    if (specsDecl.extending != null) {
                        utils.error(specsDecl.sourcefile, specsDecl, "jml.message",  "An enum may not declare any superclass");
                    }
                } else if (specIsEnum) {
                    utils.error(specsDecl.sourcefile, specsDecl, "jml.message",  "The specification declaration may not be an enum, because the source/binary is not");
                   
                } else if ((classSymbol.flags() & Flags.RECORD) != 0) {
                    if (!specIsRecord) {
                        utils.error(specsDecl.sourcefile, specsDecl, "jml.message",  "The specification declaration must be a record, because the source/binary is");
                    }
                    if (specsDecl.extending != null) {
                        utils.error(specsDecl.sourcefile, specsDecl, "jml.message",  "A record may not declare any superclass");
                    }
                    // FIXME - any other checks for records?
                } else if (specIsRecord) {
                    utils.error(specsDecl.sourcefile, specsDecl, "jml.message",  "The specification declaration may not be a record, because the source/binary is not");
               } else if (specsDecl.extending != null) {
                    attribType(specsDecl.extending, specEnv);
                    if (classSymbol == syms.objectType.tsym || !jmltypes.isSameType(specsDecl.extending.type, sup)) {
                        utils.error(specsDecl.sourcefile, specsDecl, "jml.message", "The specification declaration must declare the same supertype as the source declaration: " 
                                                + specsDecl.extending.type + " vs. " + sup);
                    }
                } else {
                    if (classSymbol == syms.objectType.tsym) {
                        // OK - no parent class permitted
                    } else if (classSymbol.toString().contains("java.util.stream.Collector")) {
                        // OK - FIXME - why do we need this
                    } else if (sup.tsym != syms.objectType.tsym) {
                        utils.error(specsDecl.sourcefile, specsDecl, "jml.message", "The specification declaration must declare the same supertype as the source declaration: " + sup);
                    }
                }
            }
            if (specsDecl.implementing != null) {
                List<Type> ifaces = attribTypes(specsDecl.implementing, specEnv);
                outer: for (var sourceType: classSymbol.getInterfaces()) {
                    if (sourceType.getKind() == TypeKind.ERROR) continue;
                    for (var specType: ifaces) {
                        if (JmlTypes.instance(context).isSameType(sourceType, specType)) {
                            ListBuffer<Type> newifaces = new ListBuffer<>();
                            for (var st: ifaces) if (st != specType) newifaces.add(st);
                            ifaces = newifaces.toList();
                            continue outer;
                        }
                    }
                    if (sourceType.toString().equals("java.lang.annotation.Annotation")) {
                        // OK
                    } else {
                        utils.error(specsDecl.sourcefile, specsDecl, "jml.message", "The specification declaration must declare the same interfaces as the source declaration: " + sourceType);
                    }
                }
                if (ifaces.size() != 0) {
                    utils.error(specsDecl.sourcefile, specsDecl, "jml.message", "The specification declaration must declare the same interfaces as the source declaration: " + ifaces);
                }
            }
        }
        if (specsDecl != null) checkAnnotations(javaDecl == null ? null : javaDecl.mods, specsDecl.mods, specsDecl.sym);

        if (specsDecl != null) checkJavaFlags(specsDecl.sym.flags(), javaDecl, specsDecl.mods.flags, specsDecl, specsDecl.sym);

        if (specsModifiers == null) {
            // no annotations to check
        } else if (owner.kind == Kind.PCK) {  // Top level type declaration
            allAllowed(specsModifiers,allowedTypeModifiers,"type declaration");
        } else if (owner.kind != Kind.TYP) { // Local
            allAllowed(specsModifiers,allowedLocalTypeModifiers,"local type declaration");
        } else if (!isModel) { // Nested/inner type declaration
            allAllowed(specsModifiers,allowedNestedTypeModifiers,"nested type declaration");
        } else { // Nested model type declaration
            allAllowed(specsModifiers,allowedNestedModelTypeModifiers,"nested model type declaration");
        }
        if (!isImmutable(classSymbol)) {
        	var sc = classSymbol.getSuperclass();
        	if (sc != null && sc.tsym != null && isImmutable(sc.tsym)) {
                utils.error(specsDecl.sourcefile, specsDecl, "jml.message", "A class with an immutable superclass must itself be immutable: " + classSymbol);
        	}
        	for (var ity: classSymbol.getInterfaces()) {
            	if (ity.tsym != null && isImmutable(ity.tsym)) {
                    utils.error(specsDecl.sourcefile, specsDecl, "jml.message", "A type with an immutable interface must itself be immutable: " + classSymbol);
            	}
        	}
        }
//        if (!classSymbol.isInterface() && classSymbol.type != syms.objectType && !isImmutable(classSymbol) && isImmutable(classSymbol.getSuperclass().tsym)) {
//            utils.error(specsDecl.sourcefile, specsDecl, "jml.message", "A class extending an immutable class must itself be immutable: " + classSymbol);
//        }
        if (!isModel) {
            checkForConflict(specsModifiers,SPEC_PUBLIC,SPEC_PROTECTED);
            checkForRedundantSpecMod(specsModifiers);
        }
        checkForConflict(specsModifiers,NON_NULL_BY_DEFAULT,NULLABLE_BY_DEFAULT);
        checkForConflict(specsModifiers,PURE,SPEC_PURE,STRICTLY_PURE,NO_STATE);
        //checkForConflict(specsModifiers,PURE,QUERY);
        //checkForConflict(specsModifiers,SPEC_PURE,QUERY);
        //checkForConflict(specsModifiers,STRICTLY_PURE,QUERY);
        checkForDuplicateModifiers(specsModifiers);
        {
            // FIXME - these checks are already done 
        // FIXME - this attribution should be done in the Enter or MemberEnter phase? look in checkTypeMatch
            attribAnnotationTypes(specsModifiers.annotations,env); 
//            if (javaDecl != null) {
//                checkSameAnnotations(javaDecl.mods,specsModifiers,"class",classSymbol.toString()); 
//            } else {
//                long flags = classSymbol.flags();
//                JCModifiers m = jmlMaker.Modifiers(flags); // FIXME - should check annotations
//                checkSameAnnotations(m,specsModifiers,"class",classSymbol.toString()); 
//            }
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
        JmlClassDecl specsDecl = combinedTypeSpecs.specDecl;
        if (combinedTypeSpecs.file == null || combinedTypeSpecs.file.getKind() == JavaFileObject.Kind.SOURCE){
            // This is already checked in enterTypeParametersForBinary (for binary classes)
            List<Type> t = ((Type.ClassType)javaClassSym.type).getTypeArguments();
            if (specsClassDecl != null) { // FIXME
            List<JCTypeParameter> specTypes = specsClassDecl.typarams;
            // FIXME - this is already checked in JmlEnter
            if (t.size() != specTypes.size()) {
                utils.error(specsClassDecl,"jml.mismatched.type.arguments",javaClassSym.fullname,javaClassSym.type.toString());
            }
            // FIXME - check that the names and bounds are the same
            }
        }
        
        if (specsDecl != null) {
//          // FIXME - this is needed, but it is using the environment from the java class, not the 
//          // spec class, and so it is using the import statements in the .java file, not those in the .jml file
          attribAnnotationTypes(specsClassDecl.mods.annotations, Enter.instance(context).typeEnvs.get(javaClassSym));  // FIXME - this is done later; is it needed here?

        }
    }
    
//        // FIXME - this should be done in MemberEnter, not here -- needed for JmlVariableDecl, checking class mods
//    protected boolean checkSameAnnotations(JCModifiers javaMods, JCModifiers specMods, String kind, String name) {
//        //if (javaMods == specMods) return true;
//        boolean saved1 = JmlPretty.useFullAnnotationTypeName, saved2 = JmlPretty.useJmlModifier;
//        JmlPretty.useFullAnnotationTypeName = JmlPretty.useJmlModifier = false;
//        PackageSymbol p = annotationPackageSymbol;
//        boolean r = false;
//        for (JCAnnotation a: javaMods.getAnnotations()) {
//            // if sourcefile is null, the annotation was inserted to make an implicit annotation explicit; we don't complain about those, as the default may be superseded by a different explicit annotation
//            TypeSymbol tsym = a.annotationType.type.tsym;
//            if (((JmlTree.JmlAnnotation)a).sourcefile != null && tsym.owner.equals(p) && utils.findMod(specMods,tsym) == null) {
//                JavaFileObject prev = log.useSource(((JmlTree.JmlAnnotation)a).sourcefile);
//                utils.warning(a.pos,"jml.java.annotation.superseded",kind,name,a); 
//                log.useSource(prev);
//                r = true;
//            }
//        }
//        JmlPretty.useFullAnnotationTypeName = saved1; JmlPretty.useJmlModifier = saved2;
//        return r;
//    }

//  /** Checks that the jml annotations match Java annotations for annotations not in org.jmlspecs.annotation
//  * and are a superset of the Java annotations for annotations in org.jmlspecs.annotation) */
// // MUST HAVE log.useSource set to specs file!
// protected void checkSameAnnotations(Symbol sym, JCModifiers specsmods, JavaFileObject javaSource) {
//     // FIXME - check for null in annotations?
//     if (sym.isAnonymous()) return;
//     boolean saved1 = JmlPretty.useFullAnnotationTypeName, saved2 = JmlPretty.useJmlModifier;
//     JmlPretty.useFullAnnotationTypeName = JmlPretty.useJmlModifier = false;
//     PackageSymbol p = ((JmlAttr)attr).annotationPackageSymbol;
//     for (Compound a  : sym.getAnnotationMirrors()) {
//         if (a.type.tsym.owner.equals(p)) {
//             if (utils.findMod(specsmods,a.type.tsym) == null) {
//                 JavaFileObject prev = log.useSource(javaSource);
//                 log.error(specsmods.pos,"jml.java.annotation.superseded",a);
//                 log.useSource(prev);
//             }
//         } else {
//             if (utils.findMod(specsmods,a.type.tsym) == null && !a.toString().startsWith("@sun")) {
//                 log.error(specsmods.pos,"jml.missing.annotation",a);
//             }
//         }
//     }
//     JmlPretty.useFullAnnotationTypeName = saved1; JmlPretty.useJmlModifier = saved2;
// }
//
// /** Checks that the jml annotations are a superset of the Java annotations (for annotations in org.jmlspecs.annotation) */
// // MUST HAVE log.useSource set to specs file!
// protected void checkSameAnnotations(JCModifiers javaMods, JCModifiers specsmods, JavaFileObject javaSource) { // FIXME - don't need last argument
//     PackageSymbol p = ((JmlAttr)attr).annotationPackageSymbol;
//     boolean saved1 = JmlPretty.useFullAnnotationTypeName, saved2 = JmlPretty.useJmlModifier;
//     JmlPretty.useFullAnnotationTypeName = JmlPretty.useJmlModifier = false;
//     for (JCAnnotation a: javaMods.getAnnotations()) {
//         if (a.type.tsym.owner.equals(p)) {
//             if (utils.findMod(specsmods,a.type.tsym) == null) {
//                 JavaFileObject prev = log.useSource(((JmlTree.JmlAnnotation)a).sourcefile);
//                 log.error(specsmods.pos,"jml.java.annotation.superseded",a);
//                 log.useSource(prev);
//             }
//         } else {
//             if (utils.findMod(specsmods,a.type.tsym) == null && !a.toString().startsWith("@sun")) {
//                 log.error(specsmods.pos,"jml.missing.annotation",a);
//             }
//         }
//     }
//     JmlPretty.useFullAnnotationTypeName = saved1; JmlPretty.useJmlModifier = saved2;
// }
//

    
    public VarSymbol currentSecretContext = null;
    public VarSymbol currentQueryContext = null;
    
    boolean implementationAllowed = false;
    
    @Override
    protected boolean okAsEnum(Type clazztype) {
    	return !(isInJmlDeclaration && (clazztype.tsym.flags_field&Flags.ENUM) != 0);
    }

    @Override
    public void visitNewArray(JCNewArray tree) {
        if (currentMethodPurity != null && currentMethodPurity.jmlclausekind == Modifiers.STRICTLY_PURE) {
            utils.errorAndAssociatedDeclaration(log.currentSourceFile(), tree, currentMethodPurity.source, currentMethodPurity.pos(),
                    "jml.message", "Array allocations are not permitted in strictly_pure methods");
        }
    	super.visitNewArray(tree);
    	if (!quantifiedExprs.isEmpty()) {
    		// FIXME - it appears this gets triggered when specs with constructors
//    		System.out.println("QUANTIFIERS " + Arrays.toString(quantifiedExprs.toArray()));
//        	utils.error(tree, "jml.message", "Quantifier bodies may not contain constructors");
    	}
    }
    
    @Override
    public void visitNewClass(JCNewClass tree) {
    	// FIXME
        if (currentMethodPurity != null && currentMethodPurity.jmlclausekind == Modifiers.STRICTLY_PURE) {
            utils.errorAndAssociatedDeclaration(log.currentSourceFile(), tree, currentMethodPurity.source, currentMethodPurity.pos(),
                    "jml.message", "Object allocations are not permitted in strictly_pure methods");
        }
        boolean prev = implementationAllowed;
        boolean prevJml = isInJmlDeclaration;
        isInJmlDeclaration = true;  // FIXME - why is this true
        try {
            // Need to scan for ghost fields identifying captured variables
            // before we scan the body of the JmlNewClass, because we are
            // inserting an initializer block
            if (tree.def != null && tree instanceof JmlNewClass) {
                for (JCTree t: tree.def.defs) {
                    if (t instanceof JmlVariableDecl) {
                        JmlVariableDecl vd = (JmlVariableDecl)t;
                        if (isCaptured(vd) && vd.init == null) {
                            Name n = vd.name;
                            JCIdent id = jmlMaker.at(vd.pos).Ident(n);
                            attribExpr(id,env);
                            ((JmlNewClass)tree).capturedExpressions.put(n,id);
                        }
                    }
                }
//                JCBlock bl = jmlMaker.at(tree.pos).Block(0L,stats.toList());
//                tree.def.defs = tree.def.defs.append(bl);
            }
            
            implementationAllowed= true;
            super.visitNewClass(tree);
        	if (!quantifiedExprs.isEmpty()) {
            	utils.error(tree, "jml.message", "Quantifier bodies may not contain constructors: " + tree.constructor.toString());
        	}
            if (!(tree.type instanceof Type.ErrorType) && jmlenv.inPureEnvironment) {
                Symbol sym = tree.constructor;
                MethodSymbol msym = null;
                if (sym instanceof MethodSymbol) msym = (MethodSymbol)sym;
                boolean isAllowed = isPureMethod(msym) || isQueryMethod(msym);
                if (jmlenv.currentClauseKind != null && !JmlOption.isOption(context,JmlOption.NEWISPURE)) {
                    utils.error(tree, "jml.message", "Object allocation is not permitted in specification expressions");
                }
                if (!isAllowed) {
                    nonPureWarning(tree, msym);
                }
            }
            if (result != null) {
                var tcl = result.getAnnotationMirrors();
                boolean nullable = false;
                for (var tc: tcl) {
                    if (!tc.toString().equals("@org.jmlspecs.annotation.Nullable")) nullable = true;
                }
                boolean nonnull = false;
                for (var tc: tcl) {
                    if (!tc.toString().equals("@org.jmlspecs.annotation.NonNull")) nonnull = true;
                }
                //System.out.println("JMLATTR NEW " + result + " # " + nonnull + " # " + tree + " # " + tcl);
            }
//            Type saved = result;
//            TypeSymbol tsym = tree.clazz.type.tsym;
//            if (tsym instanceof ClassSymbol) {
//                isInJmlDeclaration = false;
//                attribClass((ClassSymbol)tsym); // FIXME - perhaps this needs to be checked when specs are retrieved
//            }
//            result = saved;
        } finally {
            implementationAllowed = prev;
            isInJmlDeclaration = prevJml;
        }
        
    }
    
    protected void nonPureWarning(DiagnosticPosition pos, MethodSymbol msym) {
    	//if (msym.owner.toString().startsWith("java.")) return; // FIXME - need to fix type parameters in binary files
    	utils.warning(pos,"jml.non.pure.method",utils.qualifiedMethodSig(msym));
    }
   
    boolean noBodyOK = false;
    @Override
    public boolean requireBody(JCMethodDecl tree) {
    	if ((tree.sym.flags() & Flags.GENERATEDCONSTR) != 0) return false;
    	return !noBodyOK;
    }
    
    /** Overridden to set the source file correctly and to set the type field */
    public void attribAnnotationTypes(List<JCAnnotation> annotations, // OPENJML package to public
            Env<AttrContext> env) {
    	var prev = log.currentSourceFile();
    	boolean possiblyChanged = false;
        for (JCAnnotation a : annotations) {
            log.useSource(((JmlAnnotation)a).sourcefile);
            possiblyChanged = true;
            attribType(a.annotationType, env);
            a.type = a.annotationType.type;
            if (a.type != null) {
                // In some cases that a.attribute field is not set, particularly for type annotations.
                // Don't know why - or whether it is a bug in OpenJDK.
                // The following code fixes that and avoids a crash in Annotate.fromAnnotations
                if (chk.isTypeAnnotation(a,false)) {
                    annotate.attributeTypeAnnotation(a, a.type, env);
                } else {
                    annotate.attributeAnnotation(a, a.type, env);
                }
            }
        }
        if (possiblyChanged) log.useSource(prev);
    }
    
    /** This is overridden in order to do correct checking of whether a method body is
     * present or not.
     */
    @Override 
    public void visitMethodDef(JCMethodDecl m) {
        var javaMethodDecl = (JmlMethodDecl)m;
        
    	//System.out.println("VISIT METHOD DEF " + m.name);
    	if (utils.verbose()) utils.note("Attributing method " + env.enclClass.sym + " " + javaMethodDecl.name + " " + javaMethodDecl.sourcefile + " " + javaMethodDecl);

        // Setting relax to true keeps super.visitMethodDef from complaining
        // that a method declaration in a spec file does not have a body
        // FIXME - what else is relaxed?  We should do the check under the right conditions?
        if (javaMethodDecl.sym == null) return; // Guards against specification method declarations that are not matched - FIXME

        jmlenv = jmlenv.pushCopy();
        jmlenv.enclosingMethodDecl = javaMethodDecl;
        
        JmlMethodDecl jmethod = javaMethodDecl;
        Map<Name,Env<AttrContext>> prevLabelEnvs = labelEnvs;
        labelEnvs = new HashMap<Name,Env<AttrContext>>();

        var savedEnclosingMethodEnv = enclosingMethodEnv;
        enclosingMethodEnv = env; // FIXME - not the method env that super.visitMethodDef creates
        
        VarSymbol previousSecretContext = currentSecretContext;
        VarSymbol previousQueryContext = currentQueryContext;
        JavaFileObject prevSource = null;
        try {
//        	MethodSpecs mspecs = specs.getLoadedSpecs(m.sym);
//            if (ms == null) {
//                log.getWriter(WriterKind.NOTICE).println("METHOD SPECS NOT COMBINED " + m.sym.owner + " " + m.sym);
//                        // The following line does happen with anonymous classes implementing an interface, with no constructor given
//                        // but what about FINISHING SPEC CLASS
//                
//                // FIXME: this also causes the Java file's specs to be used when the specs AST has been set to null
//                ms = new JmlSpecs.MethodSpecs(jmethod); // BUG recovery?  FIXME - i think this happens with default constructors
//                jmethod.methodSpecsCombined = ms;
//                specs.putSpecs(m.sym,ms);
//            }
//
//            // Do this before we walk the method body
//            determineQueryAndSecret(jmethod,ms);

            prevSource = log.useSource(javaMethodDecl.source());
            attribAnnotationTypes(javaMethodDecl.mods.annotations,env); // FIXME- CHECK : This is needed at least for the spec files of binary classes

            JmlSpecs.MethodSpecs mspecs = specs.getLoadedSpecs(javaMethodDecl.sym);
//            if (mspecs != null) { // FIXME - is mspecs allowed to be null?
//            	attrSpecs(jmethod.sym);
//            	enclosingMethodEnv = mspecs.specsEnv;
//                currentSecretContext = mspecs.secretDatagroup;
//                currentQueryContext = mspecs.queryDatagroup;
//                if (currentQueryContext != null) currentSecretContext = currentQueryContext;
//            }
            
            


            // FIXME - need a better test than this
            // Set relax to true if this method declaration is allowed to have no body
            // because it is a model declaration or it is in a specification file.
            boolean isJavaFile = jmethod.sourcefile != null && jmethod.sourcefile.getKind() == JavaFileObject.Kind.SOURCE;
            boolean isJmlDecl = utils.isJML(m.mods);
            boolean noBodyOKSaved = noBodyOK;
            noBodyOK = isJmlDecl || !isJavaFile;
            boolean prevAllowJML = jmlresolve.allowJML();
            if (isJmlDecl) prevAllowJML = jmlresolve.setAllowJML(true);
            
//            boolean prevChk = ((JmlCheck)chk).noDuplicateWarn;
//            ((JmlCheck)chk).noDuplicateWarn = false;
            super.visitMethodDef(m);
//            ((JmlCheck)chk).noDuplicateWarn = prevChk;
//            if (JmlOption.isOption(context, JmlOption.STRICT)) checkClauseOrder(jmethod.methodSpecsCombined);
            noBodyOK = noBodyOKSaved;
            if (isJmlDecl) jmlresolve.setAllowJML(prevAllowJML);
            {
//                if (m.body == null) {
//                    currentSecretContext = mspecs.secretDatagroup;
//                    currentQueryContext = null;
//                }
                // If the body is null, the specs are checked in visitBlock
                //else deSugarMethodSpecs(jmethod,jmethod.methodSpecs);
            }
//            if (isJavaFile && !isJmlDecl) {
//                // Java methods in Java files must have a body (usually)
//                if (m.body == null) {
//                    ClassSymbol owner = env.enclClass.sym;
//                    // Empty bodies are only allowed for
//                    // abstract, native, or interface methods, or for methods
//                    // in a retrofit signature class.
//                    if ((owner.flags() & INTERFACE) == 0 &&
//                        (m.mods.flags & (ABSTRACT | NATIVE)) == 0 )
//                        utils.error(m, "missing.meth.body.or.decl.abstract");
//                }
//            } else if (m.body != null && !isJmlDecl && !isJavaFile && !isInJmlDeclaration && (m.mods.flags & (Flags.GENERATEDCONSTR|Flags.SYNTHETIC)) == 0) {
//                // Java methods not in Java files may not have bodies (generated constructors do)
//                //log.error(m.pos(),"jml.no.body.allowed",m.sym);
//                // A warning is appropriate, but this is a duplicate.
//                // A warning is already given in JmlMemberEnter.checkMethodMatch
//            }
//            System.out.println("GETSPECS-METHOD " + jmethod.sym.owner + "#" + jmethod.sym);
            specs.getAttrSpecs(jmethod.sym);
  
        } catch (Exception e) {
        	utils.note("Exception attributing method " + m + " " + e);
        	Utils.conditionalPrintStack("Exception attributing method " + m, e);
        	throw e;
        } finally {
        	enclosingMethodEnv = savedEnclosingMethodEnv;
            currentSecretContext = previousSecretContext;
            currentQueryContext = previousQueryContext;
            if (prevSource != null) log.useSource(prevSource);
            labelEnvs.clear();
            labelEnvs = prevLabelEnvs;
        	if (utils.verbose()) utils.note("Completed Attributing method " + env.enclClass.sym + " " + m.name);
        	jmlenv = jmlenv.pop();
        }
    }
    
    @Override
    public void attribMethodSpecsAndBody(MethodSymbol methodSym, JCBlock body, Env<AttrContext>  env) {
    	//System.out.println("S&B " + methodSym.owner + " " + methodSym);
        saveEnvForLabel(null, env);
        saveEnvForLabel(this.preLabel, env);
        var methodSpecs = specs.getLoadedSpecs(methodSym);
        var prevAllow = jmlresolve.setAllowJML(true);
        var prevEnv = this.env;
        var prevMethodEnv = this.enclosingMethodEnv;
        this.env = env;
        this.enclosingMethodEnv = env;
        if (methodSpecs == null) {
            if ((methodSym.flags() & Flags.SYNTHETIC) == 0) System.out.println("NO SPECS FOR " + methodSym); // FIXME - error?
            super.attribMethodSpecsAndBody(methodSym, body, env);
            return;
        }
        if (methodSpecs.cases != null) { // FIXME - should we get the specs to check from JmlSpecs?
//            // Check the also designation
//            if (methodSpecs.cases.cases != null && methodSpecs.cases.cases.size() > 0) {
//                JmlSpecificationCase spec = methodSpecs.cases.cases.get(0);
//                boolean specHasAlso = spec.also != null;
//                boolean methodOverrides = utils.parents(methodSym).size() > 1;
//                if (specHasAlso && !methodOverrides) {
//                    if (!methodSym.name.toString().equals("compareTo") && !methodSym.name.toString().equals("definedComparison")) {// FIXME
//                        if (JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
//                            utils.error(spec, "jml.extra.also", methodSpecs.specSym.name.toString() );
//                        } else {
//                            utils.warning(spec, "jml.extra.also", methodSpecs.specSym.name.toString() );
//                        }
//                    }
//                } else if (!specHasAlso && methodOverrides) {
//                	var base = utils.parents(methodSym).get(0);
//                	String s = ((ClassSymbol)base.owner).flatname + "." + base;
//                    if (JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
//                        utils.warning(spec, "jml.missing.also", methodSym.name, s);
//                    } else {
//                        utils.warning(spec, "jml.missing.also", methodSym.name, s);
//                    }
//                }
//            }
//            methodSpecs.cases.accept(this);
        }
        
        // Having the same parameter names makes more readable specs
        // FIXME: At the moment we require it -- some improvements in method specEnv is needed to support differing names
        boolean ok = true;
        var javaMethodDecl = (JmlMethodDecl)env.enclMethod;
        var specMethodDecl = methodSpecs.specDecl;
        if (specMethodDecl != javaMethodDecl) {
            if (javaMethodDecl.params.size() != specMethodDecl.params.size()) {
                utils.error(javaMethodDecl.source(), javaMethodDecl, "jml.internal",
                    "A Java method matches a spec method with different numbers of parameters: "  + javaMethodDecl  );
            } else {
                var iter1 = javaMethodDecl.params.iterator();
                var iter2 = specMethodDecl.params.iterator();
                while (iter1.hasNext() && iter2.hasNext()) {
                    var javaParam = iter1.next();
                    var specParam = iter2.next();
                    if (javaParam.name != specParam.name) {
                        ok = false;
                        utils.error(specMethodDecl.source(), specParam, "jml.message",
                            "Parameter names in a specification file must match those in the Java source: " 
                            + specParam.name + " vs. " + javaParam.name + " in " + methodSym.owner + "." + methodSym);
                    }
                }
                if (iter1.hasNext() || iter2.hasNext()) {
                    // If this is reached, the method matching in JmlMemberEnter has gone wrong
                    ok = false;
                    utils.error(specMethodDecl.source(), specMethodDecl, "jml.internal",
                        "Unexpectedly have a Java method declaration and its specification counterpart with different numbers of parameters: "
                        + javaMethodDecl.sym);
                }
            }
        }
        
        if (ok) attrSpecs(methodSym, env); // FIXME - use a specsEnv here?
        else specs.setStatus(methodSym,  JmlSpecs.SpecsStatus.ERROR);
//    	this.env = prevEnv;
    	
        jmlresolve.setAllowJML(prevAllow);
        jmlresolve.addAllowJML(utils.isJML(env.enclMethod));
        boolean savedAttributeSpecs = this.attribJmlDecls;
        this.attribJmlDecls = true;
        super.attribMethodSpecsAndBody(methodSym, body, env);
        this.attribJmlDecls = savedAttributeSpecs;
        this.enclosingMethodEnv = prevMethodEnv;
    	jmlresolve.setAllowJML(prevAllow);
    }

    
    final static Map<IJmlClauseKind, int[]> stateTable = new HashMap<>();
    {
        // state -1 - error
        // state 0 - start
        // state 1 - postcondition
        // state 2 - start of spec group
        stateTable.put(requiresClauseKind, new int[]{0,-1,-1});
        stateTable.put(oldClause, new int[]{0,-1,-1});
        stateTable.put(assignableClauseKind, new int[]{1,1,1});
        stateTable.put(ensuresClauseKind, new int[]{1,1,1});
        stateTable.put(signalsClauseKind, new int[]{1,1,1});
        stateTable.put(signalsOnlyClauseKind, new int[]{1,1,1});
        stateTable.put(callableClause, new int[]{1,1,1});
        stateTable.put(specGroupStartClause, new int[]{0,1,-1});
//        stateTable.put(JmlTokenKind.ALSO, new int[]{-1,10,-1});
//        stateTable.put(JmlTokenKind.SPEC_GROUP_END, new int[]{-1,10,-1});
    }
    
    public void checkClauseOrder(JmlSpecs.MethodSpecs mspecs) {
        if (mspecs.cases == null) return;
        for (JmlSpecificationCase scase: mspecs.cases.cases) {
            int state = 0;
            checkClauseOrder(state,scase.clauses);
        }
    }
    
    // FIXME - finish this 
    public void checkClauseOrder(int state, List<JmlMethodClause> clauses) {
        for (JmlMethodClause clause: clauses) {
            IJmlClauseKind tk = clause.clauseKind;
            int[] next = stateTable.get(tk);
            if (next == null) {
                //                   log.warning(clause, "jml.message", "Unimplemented clause type in order checker: " + tk);
                return;
            }
            state = next[state];
            if (state == -1) {
                utils.warning(clause,  "jml.message", "Clause " + tk + " is out of order for JML strict mode");
                return;
            }
            if (tk == specGroupStartClause) {
                for (JmlSpecificationCase scase:  ((JmlMethodClauseGroup) clause).cases) {
                    checkClauseOrder(state,scase.clauses);
                }
            }
        }
    }
    
    /** The annotations allowed on non-model non-constructor methods */
    public final ModifierKind[] allowedMethodAnnotations =
        new ModifierKind[] {
        MODEL, PURE, SPEC_PURE, STRICTLY_PURE, NON_NULL, NULLABLE, OPTIONS, SPEC_PUBLIC, SPEC_PROTECTED, HELPER, EXTRACT, QUERY, SECRET, NO_STATE,
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        PEER, REP, READONLY, SKIPESC, SKIPRAC, INLINE // FIXME - allowing these until the rules are really implemented

    };
    
    /** The annotations allowed on non-model non-constructor methods in interfaces */
    public final ModifierKind[] allowedInterfaceMethodAnnotations =
        new ModifierKind[] {
        MODEL, PURE, SPEC_PURE, STRICTLY_PURE, NON_NULL, NULLABLE, OPTIONS, SPEC_PUBLIC, SPEC_PROTECTED, HELPER, QUERY, NO_STATE,
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        PEER, REP, READONLY, INLINE // FIXME - allowing these until the rules are really implemented

    };
    
    /** The annotations allowed on model non-constructor methods */
    public final ModifierKind[] allowedModelMethodAnnotations =
        new ModifierKind[] {
        MODEL, PURE, SPEC_PURE, STRICTLY_PURE, NON_NULL, NULLABLE, OPTIONS, HELPER, EXTRACT, QUERY, SECRET, NO_STATE,
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        PEER, REP, READONLY, SKIPESC, INLINE // FIXME - allowing these until the rules are really implemented

    };
    
    /** The annotations allowed on model non-constructor interface methods */
    public final ModifierKind[] allowedInterfaceModelMethodAnnotations =
        new ModifierKind[] {
        MODEL, PURE, SPEC_PURE, STRICTLY_PURE, NON_NULL, NULLABLE, OPTIONS, HELPER, QUERY, SECRET, NO_STATE,
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        PEER, REP, READONLY, INLINE // FIXME - allowing these until the rules are really implemented

    };
    
    /** The annotations allowed on non-model constructors */
    public final ModifierKind[] allowedConstructorAnnotations =
        new ModifierKind[] {
        MODEL, PURE, SPEC_PURE, STRICTLY_PURE, SPEC_PUBLIC, SPEC_PROTECTED, HELPER, EXTRACT,
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        PEER, REP, READONLY, OPTIONS, SKIPESC // FIXME - allowing these until the rules are really implemented

    };
    
    /** The annotations allowed on model constructors */
    public final ModifierKind[] allowedModelConstructorAnnotations =
        new ModifierKind[] {
        MODEL, PURE, SPEC_PURE, STRICTLY_PURE, HELPER, EXTRACT ,
        CODE_JAVA_MATH, CODE_SAFE_MATH, CODE_BIGINT_MATH, SPEC_JAVA_MATH, SPEC_SAFE_MATH, SPEC_BIGINT_MATH, 
        OPTIONS, SKIPESC, PEER, REP, READONLY, INLINE // FIXME - allowing these until the rules are really implemented

    };
    
    public void checkModelGhost(JmlMethodDecl specDecl, MethodSymbol msym) {
    	var mspecs = specs.getLoadedSpecs(msym);
    	if (mspecs == null) return; // TODO: Why might this happen?
        boolean inJML = utils.isJML(msym.flags());
        boolean ownerInJML = utils.isJML(msym.owner.flags());
        boolean classIsModel = isModelClass(msym.owner);
        boolean model = mspecs == null ? false : isModel(mspecs.mods);
        
    	JmlModifiers mods = (JmlModifiers)mspecs.mods;

    	if (specDecl != null) {
        	boolean isJML = utils.isJML(specDecl);
        	boolean isOwnerJML = utils.isJML(msym.owner.flags());
        	boolean isModel = utils.hasMod(specDecl.mods, Modifiers.MODEL);
        	if (isOwnerJML && isModel) {
        		utils.error(specDecl.sourcefile, specDecl, "jml.message", "A model type may not contain model declarations: " + msym.owner + "." + specDecl.sym);
        		// Attempt recovery by removing the offending annotation
        		utils.removeAnnotation(specDecl.mods,  Modifiers.MODEL);
        	} else if (!isJML && isModel ) {
        		var pos = utils.locMod(specDecl.mods, Modifiers.MODEL);
        		utils.error(specDecl.sourcefile, pos, "jml.message", "A Java method declaration must not be marked model: " + msym.owner + "." + specDecl.sym);
        		// Attempt recovery by removing the offending annotation
        		utils.removeAnnotation(specDecl.mods,  Modifiers.MODEL);
        	} else if (isJML && !isModel && !isOwnerJML && !msym.owner.isAnonymous()) {
        		utils.error(specDecl.sourcefile, specDecl, "jml.message", "A JML method declaration must be marked model: " + msym.owner + "." + specDecl.sym);
        		// Attempt recovery by adding a model annotation
        		JmlTreeUtils.instance(context).addAnnotation(specDecl.mods, specDecl.mods.pos, specDecl.mods.pos, Modifiers.MODEL, null);
        	}
        }
    }
    
    public void annotationsToModifiers(JCModifiers mods) {
        annotationsToModifiers((JmlModifiers)mods, mods.annotations);
    }
        
    public void annotationsToModifiers(JmlModifiers mods, JCExpression type) {
        annotationsToModifiers(mods, mods.annotations);
        if (type != null) typeAnnotationsToModifiers(mods, type);
    }
        
    public void annotationsToModifiers(JmlModifiers mods, List<JCAnnotation> annotations) {
        x: for (var a: annotations) {
            if (a instanceof JmlAnnotation jmla) {
                if (jmla.type == null) System.out.println("SKIPPING because type is null: " + jmla);
                if (jmla.type == null) continue; // no type if it is an unresolved name (or - a bug - if the annotation was never attributed)
                if (jmla.type.tsym.owner != annotationPackageSymbol) continue;
                // FIXME - why would a jmla.kind be null
                if (jmla.kind == null) System.out.println("SKIPPING because kind is null: " + jmla);
                if (jmla.kind == null || !jmla.kind.isNormalModifier()) continue;
                //if (!jmla.type.toString().startsWith("org.jmlspecs.annotation")) continue;
                int p = a.pos;
                var kind = jmla.kind;
                //System.out.println("KIND " + kind + " " + (kind == Modifiers.NULLABLE_BY_DEFAULT));
//                JmlToken newtoken = null;
//                for (JmlToken t: mods.jmlmods) {
//                    if (t.pos == p && t.jmlclausekind == kind) continue x;
//                }
                JmlToken newtoken = new JmlToken(jmla.kind, jmla.sourcefile, p, p, null); // FIXME - should really have the endposition
                mods.jmlmods.add(newtoken);
            }
        }
    }
    
    public void typeAnnotationsToModifiers(JmlModifiers mods, JCExpression type) {
        if (type instanceof JCAnnotatedType at) {
            annotationsToModifiers(mods, at.annotations);
        } else if (type instanceof JCTypeApply app) {
            typeAnnotationsToModifiers(mods, app.clazz);
        } else {
            // FIXME - other types of expression -- such as a array?
        }
    }
    
    /** Check all the modifiers in the method specs against those of the method symbol (msym).
     * javaMethodTree may be null (if we are checking the specs of a binary method)
     * javaMethodTree is just used to give location information for error messages
     * (we are presuming that the modifiers of javamethodTree are consistent with msym)
     * @param msym
     * @param javaMethodTree
     */
    public void checkMethodModifiers(MethodSymbol msym, JmlMethodDecl javaMethodTree) {
        if ((msym.flags() & SYNTHETIC) != 0) return;
        JavaFileObject prev = log.currentSourceFile();
        try {
        	var mspecs = specs.getLoadedSpecs(msym);
        	if (mspecs == null) return; // TODO: Why might this happen?
        	JmlModifiers mods = (JmlModifiers)mspecs.mods;
            if (mods == null) mods = (JmlModifiers)javaMethodTree.mods; // FIXME - this can happen for JML synthesized methods, such as are added for RAC - perhaps we should properly initialize the modifiers, but for now we just say they are OK

            annotationsToModifiers(mods, mspecs.javaDecl != null ? mspecs.javaDecl.restype : mspecs.specDecl.restype);
            boolean inJML = utils.isJML(mods);
            boolean ownerInJML = utils.isJML(msym.owner.flags());
            boolean model = isModel(mods);
        	var specDecl = mspecs.specDecl;
        	JCAnnotation a;
            
        	checkModelGhost(specDecl, msym);

            boolean synthetic = mods != null && (mods.flags & Flags.SYNTHETIC) != 0;
            boolean abst = mods != null && (mods.flags & Flags.ABSTRACT) != 0;
            boolean anon = msym.owner.isAnonymous();
            boolean isConstructor = msym.isConstructor();
            if (inJML && !model && !ownerInJML && !isInJmlDeclaration) {
                if (msym.isConstructor() && msym.params.isEmpty()) {
                    // OK
                    for (Symbol elem: msym.owner.getEnclosedElements()) {
                        if (elem != msym && elem instanceof Symbol.MethodSymbol && elem.isConstructor()) {
                            // Found another constructor
                        	// FIXME - fix this test
//                            utils.error(javaMethodTree.sourcefile,javaMethodTree,"jml.no.default.constructor");
                            break;
                        }
                    }
//                } else if (inJML && !model && javaMethodTree.sym.owner.isEnum()) {
//                    // OK
                } else if (abst) {
                    // OK
                }
            }
            
            // FIXME - this test is in the wrong place (NPE would happen above) and needs review inany case

            // Check that any annotations are allowed and no conflicting pairs occur
            if (!isConstructor) {
            	ClassSymbol enclClass = msym.enclClass();
            	if (enclClass == null) {
            		System.out.println("NULL ENCL CLASS: " + msym + " " + msym.owner + " " + msym.kind.matches(KindSelector.TYP) + " " + msym.type.hasTag(CLASS)  + " " + msym.type);
            		System.out.println("NULL ENCL CLASS-B: " + msym + " " + msym.owner + " " + msym.owner.kind.matches(KindSelector.TYP) + " " + msym.owner.type.hasTag(CLASS) + " " + msym.owner.type + " " + msym.owner.type.getTag());
            		enclClass = (ClassSymbol)javaMethodTree.sym.owner;
            	}
                if (enclClass.isInterface()) {
                    if (model) {
                        allAllowed(mods,allowedInterfaceModelMethodAnnotations,"interface model method declaration");
                    } else {
                        allAllowed(mods,allowedInterfaceMethodAnnotations,"interface method declaration");
                    }
                } else {
                    if (model) {
                        allAllowed(mods,allowedModelMethodAnnotations,"model method declaration");
                    } else {
                        allAllowed(mods,allowedMethodAnnotations,"method declaration");
                    }
                }
                checkForConflict(mods,NON_NULL,NULLABLE);
                checkForConflict(mods,PURE,SPEC_PURE,STRICTLY_PURE,NO_STATE,QUERY);
                var selfPurity = specs.determinePurity(msym);
                var loc = selfPurity != null ? selfPurity.pos() : javaMethodTree;
                boolean print = false; // msym.toString().contains("toString") && msym.owner.toString().contains("Locale");
                if (print) System.out.println("OVER " + msym.owner + " " + msym + " " + selfPurity);
                for (var ms: utils.parents(msym, false)) {
                    var parentPurity = specs.determinePurity(ms);
                    if (print) System.out.println("PARENT "+ ms.owner + " " + parentPurity);
                    if (parentPurity == null) continue; // OK for purity to become stronger
                    if (selfPurity == null) continue; // Inherits purity
                    
                    if (selfPurity == null ||
                            (selfPurity.jmlclausekind == PURE && parentPurity.jmlclausekind != PURE) ||
                            (parentPurity.jmlclausekind == NO_STATE && selfPurity.jmlclausekind != NO_STATE) ||
                            (parentPurity.jmlclausekind == STRICTLY_PURE && selfPurity.jmlclausekind == SPEC_PURE)) {
                        if (parentPurity.source != null && parentPurity.pos >= 0)
                            utils.errorAndAssociatedDeclaration(log.currentSourceFile(), loc, parentPurity.source, parentPurity, 
                                "jml.message", "A method must be at least as pure as a method it overrides: " +
                                (selfPurity == null ? "<no modifier>" : selfPurity.jmlclausekind.toString()) + " vs. " + parentPurity.jmlclausekind
                                );
                        else 
                            utils.error(log.currentSourceFile(), loc,  
                                    "jml.message", "A method must be at least as pure as a method it overrides (in " + ms.owner + "): " +
                                    (selfPurity == null ? "<no modifier>" : selfPurity.jmlclausekind.toString()) + " vs. " + parentPurity.jmlclausekind
                                    );
                            
                    }
                }
                
            } else { // Constructor
                if (model) {
                    allAllowed(mods,allowedModelConstructorAnnotations,"model constructor declaration");
                } else {
                    allAllowed(mods,allowedConstructorAnnotations,"constructor declaration");
                }            
            }
            checkForDuplicateModifiers(mods);
                        
//            if (!isPureMethod(msym) &&
//                utils.findMod(mods,modToAnnotationSymbol.get(IMMUTABLE))!=null) {
//                utils.error(javaMethodTree, "jml.message", "Methods of an immutable class must be pure");
//            }

            
            // Check rules about no_state
            JmlToken t = utils.findModifier(mods,NO_STATE);
            // FIXME - check that all specs are 'reads \nothing'
//            if (a != null && !utils.isJMLStatic(msym)) {
//                if (msym.owner instanceof ClassSymbol owner && !isImmutable(owner)) {
//                    utils.error(a,"jml.no_state.must.have.immutable",msym.name);
//                }
//            }
//            a=utils.findMod(mods,modToAnnotationSymbol.get(FUNCTION));
//            if (a != null && !utils.isJMLStatic(msym)) {
//                if (msym.owner instanceof ClassSymbol owner && !isImmutable(owner)) {
//                    utils.error(a,"jml.no_state.must.have.immutable",msym.name);
//                }
//            }
            
            // Check rules about helper
            if ( (t = utils.findModifier(mods,HELPER)) != null  &&
                    specs.determinePurity(msym) == null  && 
                    (specDecl.mods.flags & Flags.FINAL) == 0  && 
                    (specDecl.mods.flags & Flags.STATIC) == 0  && 
                    (    (mods.flags & Flags.PRIVATE) == 0 
                    || utils.hasModifier(mods,SPEC_PUBLIC, SPEC_PROTECTED) 
                    )
                    ) {
                utils.error(t.source, t.pos,"jml.helper.must.be.private",specDecl.name.toString());
            }
            if (!model) {
                checkForConflict(mods,SPEC_PUBLIC,SPEC_PROTECTED);
                checkForRedundantSpecMod(mods);
            }
            
            if ( (t = utils.findModifier(mods,INLINE)) != null  &&
                    ((msym.enclClass().flags() & Flags.FINAL) == 0)  &&
                    ((mods.flags & (Flags.FINAL|Flags.STATIC|Flags.PRIVATE)) == 0)  &&
                    !isConstructor
                    ) {
                utils.warning(t.source, t.pos,"jml.inline.should.be.final",msym.name.toString());
            }

            checkMethodJavaModifiersMatch(javaMethodTree, msym, specDecl, (ClassSymbol)specDecl.sym.owner);
            
//
//      // FIXME - we do need to exclude some anonymous classes,  but all of them?
//      if (!javaClassSymbol.isAnonymous()) checkSameAnnotations(match,specMethodDecl.mods,prev); // FIXME - is prev really the file object for Java
//      Iterator<JCVariableDecl> jmliter = specMethodDecl.params.iterator();
//      Iterator<Symbol.VarSymbol> javaiter = match.getParameters().iterator();
//      while (javaiter.hasNext() && jmliter.hasNext()) {
//          Symbol.VarSymbol javaparam = javaiter.next();
//          JmlVariableDecl jmlparam = (JmlVariableDecl)jmliter.next();
//          checkSameAnnotations(javaparam,jmlparam.mods,prev); // FIXME - is prev really the file object for Java
//      }
//
//
//
//      // Check that the return types are the same
//      if (specMethodDecl.restype != null) { // not a constructor
//          if (specMethodDecl.restype.type == null) Attr.instance(context).attribType(specMethodDecl.restype, match.enclClass());
////          if (match.name.toString().equals("defaultEmpty")) {
////              log.noticeWriter.println(match.name);
////          }
//          Type javaReturnType = match.type.getReturnType();
//          Type specReturnType = specMethodDecl.restype.type;
//          if (!Types.instance(context).isSameType(javaReturnType,specReturnType)) {
//              // FIXME - when the result type is parameterized in a static method, the java and spec declarations
//              // end up with different types for the parameter.  Is this also true for the regular parameters?  
//              // FIXME - avoud the probloem for now.
//              if (!(specReturnType instanceof Type.TypeVar) && specReturnType.getTypeArguments().isEmpty()
//                      && (!(specReturnType instanceof Type.ArrayType) || !(((Type.ArrayType)specReturnType).elemtype instanceof Type.TypeVar)) )
//                  utils.error(specMethodDecl.restype.pos(),"jml.mismatched.return.type",
//                          match.enclClass().fullname + "." + match.toString(),
//                          specReturnType, javaReturnType);
//          }
//      }
//
//      // Check that parameter names are the same (a JML requirement to avoid having to rename within specs)
//      if (javaMatch != null) {
//          for (int i = 0; i<javaMatch.getParameters().size(); i++) {
//              JCTree.JCVariableDecl javaparam = javaMatch.getParameters().get(i);
//              JCTree.JCVariableDecl jmlparam = specMethodDecl.params.get(i);
//              if (!javaparam.name.equals(jmlparam.name)) {
//                  utils.error(jmlparam.pos(),"jml.mismatched.param.names",i,
//                          match.enclClass().fullname + "." + match.toString(),
//                          javaparam.name, jmlparam.name);
//              }
//          }
//
//      } else {
//          for (int i = 0; i<match.getParameters().size(); i++) {
//              Symbol.VarSymbol javasym = match.getParameters().get(i);
//              JCTree.JCVariableDecl jmlparam = specMethodDecl.params.get(i);
//              if (!javasym.name.equals(jmlparam.name)) {
//                  utils.error(jmlparam.pos(),"jml.mismatched.param.names",i,
//                          match.enclClass().fullname + "." + match.toString(),
//                          javasym.name, jmlparam.name);
//              }
//          }
//      }
//
//      // Check that the specification method has no body if it is not a .java file
//      if (specMethodDecl.body != null && specMethodDecl.sourcefile.getKind() != Kind.SOURCE
//              && !((JmlAttr)attr).isModel(specMethodDecl.mods)
//              && !inModelTypeDeclaration
//              && match.owner == javaClassSymbol   // FIXME - this is here to avoid errors on methods of anonymous classes within specifications within a .jml file - it might not be fully robust
//              // FIXME - should test other similar locations - e.g. model classes, model methods, methods within local class declarations in model methods or methods of model classes
//              && (specMethodDecl.mods.flags & (Flags.GENERATEDCONSTR|Flags.SYNTHETIC)) == 0) {
//          utils.error(specMethodDecl.body.pos(),"jml.no.body.allowed",match.enclClass().fullname + "." + match.toString());
//      }
//
//
//      // FIXME - from a previous comparison against source
////      // A specification method may not have a body.  However, the spec
////      // method declaration may also be identical to the java method (if the
////      // java file is in the specification sequence) - hence the second test.
////      // There is an unusual case in which a method declaration is duplicated
////      // in a .java file (same signature).  In that case, there is already
////      // an error message, but the duplicate will be matched against the
////      // first declaration at this point, though they are different
////      // delcarations (so the second test will be true).  Hence we include the
////      // 3rd test as well. [ TODO - perhaps we need just the third test and not the second.]
////      if (specMethodDecl.body != null && match != specMethodDecl
////              && match.sourcefile != specMethodDecl.sourcefile
////              && (specMethodDecl.mods.flags & (Flags.GENERATEDCONSTR|Flags.SYNTHETIC)) == 0) {
////          log.error(specMethodDecl.body.pos(),"jml.no.body.allowed",match.sym.enclClass().fullname + "." + match.sym.toString());
////      }
////      
////      // Check that the return types are the same
////      if (specMethodDecl.restype != null) { // not a constructor
////          if (specMethodDecl.restype.type == null) Attr.instance(context).attribType(specMethodDecl.restype, match.sym.enclClass());
//////          if (match.name.toString().equals("defaultEmpty")) {
//////              log.noticeWriter.println(match.name);
//////          }
////          if (!Types.instance(context).isSameType(match.restype.type,specMethodDecl.restype.type)) {
////              // FIXME - when the result type is parameterized in a static method, the java and spec declarations
////              // end up with different types for the parameter.  Is this also true for the regular parameters?  
////              // FIXME - avoud the probloem for now.
////              if (!(specMethodDecl.restype.type.getTypeArguments().head instanceof Type.TypeVar))
////              log.error(specMethodDecl.restype.pos(),"jml.mismatched.return.type",
////                      match.sym.enclClass().fullname + "." + match.sym.toString(),
////                      specMethodDecl.restype.type,match.restype.type);
////          }
////      }
//
//  } finally {
//      log.useSource(prev);
//  }
//      // FIXME - what about covariant return types ?????
//      
//      // FIXME - check that JML annotations are ok
        
        
        } finally {
            log.useSource(prev);
        }
    }
    
	public void checkMethodJavaModifiersMatch(/* @nullable */ JmlMethodDecl javaMatch, MethodSymbol match,
			JmlMethodDecl specMethodDecl, ClassSymbol javaClassSymbol) {

		checkAnnotations(javaMatch == null ? null : javaMatch.mods, specMethodDecl.mods, match);
		log.useSource(specMethodDecl.sourcefile); // All logged errors are with respect to positions in the jml file
		try {
			if (javaMatch != specMethodDecl) {
				boolean isInterface = match.owner.isInterface();
				// Check that modifiers are the same
				long matchf = match.flags();
				long specf = specMethodDecl.mods.flags;
				matchf |= (specf & Flags.SYNCHRONIZED); // binary files do not seem to always have the synchronized
														// modifier? FIXME
				long diffs = (matchf ^ specf) & Flags.MethodFlags;
				if (diffs != 0) {
					boolean isEnum = (javaClassSymbol.flags() & Flags.ENUM) != 0;
					if ((Flags.NATIVE & matchf & ~specf) != 0)
						diffs &= ~Flags.NATIVE;
					if (isInterface)
						diffs &= ~Flags.PUBLIC & ~Flags.ABSTRACT;
					if (isEnum && match.isConstructor()) {
						specMethodDecl.mods.flags |= (matchf & 7);
						diffs &= ~7;
					} // FIXME - should only do this if specs are default
					if ((matchf & specf & Flags.ANONCONSTR) != 0 && isEnum) {
						diffs &= ~2;
						specMethodDecl.mods.flags |= 2;
					} // enum constructors can have differences
					if (diffs != 0 && !(match.isConstructor() && diffs == 3)) {
						// FIXME - hide this case for now because of default constructors in binary
						// files
						if (javaMatch != null) {
						    utils.errorAndAssociatedDeclaration(specMethodDecl.sourcefile, specMethodDecl,
								javaMatch.sourcefile, javaMatch,
								"jml.mismatched.method.modifiers", match.owner + "." + match,
								Flags.toString(diffs));
						} else {
						    utils.error(specMethodDecl.sourcefile, specMethodDecl,
	                                "jml.mismatched.method.modifiers", match.owner + "." + match,
	                                Flags.toString(diffs));
						}
					}
				}
			}

			if (javaMatch != null) {
				// Check that parameters have the same modifiers - FIXME - should check this in
				// the symbol, not just in the Java
				Iterator<JCVariableDecl> javaiter = javaMatch.params.iterator();
				Iterator<JCVariableDecl> jmliter = specMethodDecl.params.iterator();
				while (javaiter.hasNext() && jmliter.hasNext()) {
					JmlVariableDecl javaparam = (JmlVariableDecl) javaiter.next();
					JmlVariableDecl jmlparam = (JmlVariableDecl) jmliter.next();
					javaparam.specsDecl = jmlparam;
					jmlparam.sym = javaparam.sym;
					long diffs = (javaparam.mods.flags ^ jmlparam.mods.flags);
					if (diffs != 0) {
						utils.errorAndAssociatedDeclaration(specMethodDecl.sourcefile, jmlparam.pos(),
								javaMatch.sourcefile, javaparam.pos(), 
								"jml.mismatched.parameter.modifiers",
								jmlparam.name, javaClassSymbol.getQualifiedName() + "." + match.name,
								Flags.toString(diffs));
					}
				}
				// FIXME - should check names of parameters, names of type parameters
				if (javaiter.hasNext() || jmliter.hasNext()) {
					// Just in case -- should never have made a match if the signatures are
					// different
					utils.errorAndAssociatedDeclaration(specMethodDecl.sourcefile, specMethodDecl,
							javaMatch.sourcefile, javaMatch,
							"jml.internal",
							"Java and jml declarations have different numbers of arguments, even though they have been type matched");
				}
			}
		} finally {
		}
	}

	/**
	 * If there are specifications in a file separate from the .java file, then any
	 * annotations in the .java file are ignored. This condition is checked and
	 * warned about here.
	 */
	public void checkAnnotations(JCModifiers javaMods, JCModifiers specMods, Symbol owner) {

	    //System.out.println("CHECKING ANNOTATIONS " + owner + " " + javaMods + " # " + specMods);
	    // If there is an explicit Java declaration and if it has an JML @-annotations and there is
	    // a .jml file which does not have that annotation, then warn that the annotations in the .java file are ignored
        if (javaMods != null) for (var a : javaMods.annotations) {
            if (a instanceof JmlAnnotation) {
                var aa = (JmlAnnotation) a;
                if (aa.kind != null) {
                    if (!utils.hasMod(specMods, aa.kind)) {
                        String k = owner instanceof ClassSymbol ? "class"
                            : owner instanceof MethodSymbol ? "method" : owner instanceof VarSymbol ? "var" : "";
                        utils.warning(aa.sourcefile, aa, "jml.java.annotation.superseded", k, owner, aa.type);
                        break;
                    }
                }
            }
        }
        
        // For each @-annotation in the specification declaration, check that it is also in the .java declaration, 
        // else issue a warning that there is an extra annotation
        for (var annotation : specMods.annotations) {
            if (annotation instanceof JmlAnnotation jmlannotation) {
                if (jmlannotation.kind != null) continue;
                if (!utils.hasJavaAnnotation(owner,  jmlannotation)) {
                    String annotAsString = jmlannotation.type.toString();
                    if (annotAsString.contains("Override")) continue; // Not retained in binary
                    if (annotAsString.contains("FunctionalInterface")) continue; // Allow this one to be different
                    if (annotAsString.contains("SuppressWarnings")) continue; // Allow this one to be different
                    String kind = owner instanceof ClassSymbol ? "class"
                            : owner instanceof MethodSymbol ? "method" : owner instanceof VarSymbol ? "var" : "";
                    utils.warning(jmlannotation.sourcefile, jmlannotation, "jml.message", 
                        "Specification " + kind + " declaration contains an annotation that the Java declaration does not have: " + annotAsString);
                }
            }
        }
        
        // For each @-annotation in the java (binary) declaration, check that it is also in the specification declaration, 
        // else issue a warning that there is a missing annotation
        for (var a : owner.getAnnotationMirrors()) {
            // FIXME - implement this
//                boolean has = utils.hasMod(specMods, a.type);
//                if (!has) {
//                    String k = owner instanceof ClassSymbol ? "class"
//                            : owner instanceof MethodSymbol ? "method" : owner instanceof VarSymbol ? "var" : "";
//                    utils.warning(aa.sourcefile, aa, "jml.message", "Java " + k + " declaration (or binary) declares an annotation that the specification does not have: " + aa.toString());
//                }
//            }
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

        var query = utils.findModifier(tree.mods, Modifiers.QUERY);
        VarSymbol queryDatagroup = null;
        if (query != null) {
            // FIXME
//            List<JCExpression> args = query.getArguments();
//            Name datagroup = null;
//            int pos = 0;
//            if (args.isEmpty()) {
//                // No argument - use the name of the method
//                datagroup = tree.name;
//                pos = query.pos;
//            } else {
//                datagroup = getAnnotationStringArg(query);
//                pos = args.get(0).pos;
//            }
//            if (datagroup != null) {
//                // Find the field with that name
//                boolean prev = jmlresolve.setAllowJML(true);
//                Symbol v = rs.findField(env,env.enclClass.type,datagroup,env.enclClass.sym);  // FIXME - test that this does not look outside the class and supertypes
//                jmlresolve.setAllowJML(prev);
//                if (v instanceof VarSymbol) {
//                    //OK
//                    queryDatagroup = (VarSymbol)v;
//                    // Don't require datagroups to be model fields
//                    //                  if (!isModel(v)) {
//                    //                      // TODO - ideally would like this to point to the declaration of the VarSymbol - but it might not exist and we have to find it
//                    //                      log.error(pos,"jml.datagroup.must.be.model");
//                    //                  }
//                } else if (args.size() == 0) {
//                    // Create a default: public model secret \datagroup
//                    JmlTree.Maker maker = JmlTree.Maker.instance(context);
//                    JCTree.JCModifiers nmods = maker.Modifiers(Flags.PUBLIC);
//                    JCTree.JCAnnotation a = maker.Annotation(maker.Type(modToAnnotationSymbol.get(Modifiers.MODEL).type),List.<JCExpression>nil());
//                    JCTree.JCAnnotation aa = maker.Annotation(maker.Type(modToAnnotationSymbol.get(Modifiers.SECRET).type),List.<JCExpression>nil());
//                    boolean isStatic = utils.isJMLStatic(tree.sym);
//                    if (isStatic) {
//                        nmods.flags |= Flags.STATIC;
//                        nmods.annotations = List.<JCAnnotation>of(a,aa);
//                    } else {
//                        JCTree.JCAnnotation aaa = maker.Annotation(maker.Type(modToAnnotationSymbol.get(Modifiers.INSTANCE).type),List.<JCExpression>nil());
//                        nmods.annotations = List.<JCAnnotation>of(a,aa,aaa);
//                    }
//                    JCTree.JCExpression type = maker.Type(datagroupClass.type);
//                    JCTree.JCVariableDecl vd = maker.VarDef(nmods,datagroup,type,null);
//                    JmlMemberEnter.instance(context).memberEnter(vd,enclosingClassEnv);
//                    JmlTree.JmlTypeClauseDecl td = maker.JmlTypeClauseDecl(vd);
//                    utils.setJML(vd.mods);
//                    vd.accept(this); // attribute it
//                    queryDatagroup = vd.sym;
//                    specs.get(enclosingClassEnv.enclClass.sym).clauses.append(td);
//                } else {
//                    log.error(pos,"jml.no.such.field",datagroup);
//                }
//            }
        }
        mspecs.queryDatagroup = queryDatagroup;
        // Secret
        var secret = utils.findModifier(tree.mods, Modifiers.SECRET);
        VarSymbol secretDatagroup = null;
        if (secret != null) {
            // FIXME
//            List<JCExpression> args = secret.getArguments();
//            int pos = 0;
//            Name datagroup = null;
//            if (args.size()!=1) {
//                // No argument - error
//                utils.error(secret.pos(),"jml.secret.method.one.arg");
//                datagroup = null;
//            } else {
//                // FIXME - what if the string is a qualified name?
//                datagroup = getAnnotationStringArg(secret);
//                pos = args.get(0).pos;
//            }
//            if (datagroup != null) {
//                // Find the model field with that name
//                boolean prev = jmlresolve.setAllowJML(true);
//                Symbol v = rs.findField(env,env.enclClass.type,datagroup,env.enclClass.sym);
//                jmlresolve.setAllowJML(prev);
//                if (v instanceof VarSymbol) {
//                    secretDatagroup = (VarSymbol)v;
//                    //OK
//                    //                  if (!isModel(v)) {
//                    //                      // TODO - ideally would like this to point to the declaration of the VarSymbol - but it might not exist and we have to find it
//                    //                      log.error(pos,"jml.datagroup.must.be.model");
//                    //                  }
//                } else {
//                    log.error(pos,"jml.no.such.field",datagroup);
//                }
//            }
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
                JmlSpecs.MethodSpecs sp = specs.getAttrSpecs(tree.sym);
                try {
                    env = localEnv;
                	//if (Utils.debug()) System.out.println("ABOUT TO DO SPECS DIRECTLY " + tree.sym + " " + sp);
                    if (sp != null) sp.cases.accept(this);
                    deSugarMethodSpecs(tree.sym,sp);
                	// if (Utils.debug()) System.out.println("DID SPECS DIRECTLY " + tree.sym);
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
    protected JCLiteral makeLit(Type type, Object value) {  // FIXME - should be given a position
        return make.Literal(type.getTag(), value).setType(litType(type.getTag()).constType(value));
    }

    // FIXME - is there a faster way to do this?
    /** Returns a Symbol (in the current compilation context) for the given operator
     * with the given (lhs) type
     * @param op the operator (e.g. JCTree.AND)
     * @param type the type of the lhs, for disambiguation
     * @return the method Symbol for the operation
     */
    protected Symbol predefBinOp(JCTree.Tag op, Type type) {
		Name n = names.fromString(Pretty.operatorName(op));
        var e = syms.predefClass.members().getSymbolsByName(n);
        for (Symbol sym: e) {
            if (sym instanceof MethodSymbol) {
                MethodSymbol msym = (MethodSymbol)sym;
                Type t = msym.getParameters().head.type;
                if (t == type || (!type.isPrimitive() && t == syms.objectType)) return sym;
            }
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
     * @param specDecl the method declaration whose specs are being desugared
     * @param msp the method specs being desugared
     */
    // FIXME - base this on symbol rather than decl, but first check when all
    // the modifiers are added into the symbol
    // FIXME - check everything for position information
    public void deSugarMethodSpecs(MethodSymbol msym, JmlSpecs.MethodSpecs msp) {
        if (msp == null) return;
        //System.out.println("DESUGARING " + msym.owner + " " + msym + " " + msp.specDecl.toString());
        Env<AttrContext> prevEnv = env;
        var decl = msp.cases.decl;
        
        
        boolean specsCompletelyEmpty = msp.cases.cases.isEmpty();

//        env = enter.getEnv((ClassSymbol)decl.sym.owner);
//        JCMethodDecl prevEnclMethod = env == null ? null : env.enclMethod;
//        if (env != null) env.enclMethod = decl; // This is here to handle the situation when deSugarMethodSPecs
//                // is called from JmlSpecs to provide on demand desugaring.  In that case we are not within
//                // a tree hierarchy, so we have to set the enclosing method declaration directly.  If we were only
//                // calling deSugarMethodSpecs during AST attribution, then we would not need to set env or adjust
//                // env.enclMethod.
//        if (env == null) env = enclosingMethodEnv;
        
    	JCExpression nnexpr = treeutils.trueLit;
        {
        	int i = 0;
        	var iter = msp.specDecl == null ? null : msp.specDecl.params.iterator(); // FIXME - under what circumstances is msp.specDecl null? What do we do if there are no specs at all and we are assuming some param are non-null?
        	var syms = msp.specSym == null ? null : msp.specSym.params.iterator();
        	for (var param: msym.params) {
        		var p = iter == null ? null : iter.next();
        		var pos = p == null ? Position.NOPOS : p.pos;
        		var s = syms == null ? null : syms.next();
        		boolean nn = specs.isCheckNonNullFormal(param.type, i, msp, msym);
        		if (nn) {
        			JCIdent e = treeutils.makeIdent(pos, s!=null ? s :p != null ? p.sym : param);
        			//System.out.println("USING SYM " + e.name + " " + e.sym + " " + e.sym.hashCode() + " : " + Objects.hashCode(s) + " " + Objects.hashCode(p.sym) + " " + Objects.hashCode(param));
        			JCExpression ee = treeutils.makeNotNull(pos, e);
        			nnexpr = treeutils.makeAndSimp(pos, nnexpr, ee);
        		}
        		++i;
        	}
        }
        
        JavaFileObject prevSource = decl == null ? log.currentSourceFile() : log.useSource(decl.sourcefile);
        EndPosTable endPosTable = null;
        if (msp.specsEnv != null) {
        	endPosTable = msp.specsEnv.toplevel.endPositions;
            if (endPosTable == null) utils.error("jml.internal","Expected endPosTable to be non-null: " + log.currentSourceFile());
        }

        try {
            JmlTree.Maker jmlMaker = (JmlTree.Maker)make;
            desugaringPure = specs.determinePurity(msym) != null;
            
            if (specsCompletelyEmpty) {
                // If the local specs are completely empty, then the desugaring depends on what is inherited:
                // If the method at hand does not override anything, then we go on to add the default specs;
                // If the method at hand does override some parent methods, then we add no additional specs here
                if (!msym.isConstructor() && utils.parents(msym,true).size() > 1) { // The override list will always include the method itself
                    JmlMethodSpecs newspecs = jmlMaker.at(msp.cases.pos).JmlMethodSpecs(List.<JmlTree.JmlSpecificationCase>nil());
                    newspecs.decl = msp.cases.decl;
                    msp.cases.deSugared = newspecs;
                    //System.out.println("EMPTY WITH INHERITED " + msym.owner + " " + msym);
                    return;
                }
                JmlSpecs.MethodSpecs jms = JmlSpecs.instance(context).defaultSpecs(msp.cases.decl, msym, Position.NOPOS);
                msp.mods.flags |= jms.mods.flags;
                if (jms.mods.annotations != msp.mods.annotations) msp.mods.annotations = msp.mods.annotations.appendList(jms.mods.annotations);
                if (((JmlModifiers)msp.mods).jmlmods != ((JmlModifiers)jms.mods).jmlmods) ((JmlModifiers)msp.mods).jmlmods.addAll(((JmlModifiers)jms.mods).jmlmods);
                msp.cases = jms.cases;
            }
            JmlMethodSpecs methodSpecs = msp.cases;
            JmlToken pure = specs.determinePurity(msym);

            // A list in which to collect clauses
            ListBuffer<JmlMethodClause> commonClauses = new ListBuffer<JmlMethodClause>();

            // Desugar any specification cases
            JmlMethodSpecs newspecs;
            JCModifiers mods = methodSpecs.decl == null ? null : methodSpecs.decl.mods;
            if (!methodSpecs.cases.isEmpty()) {
                ListBuffer<JmlSpecificationCase> allcases = new ListBuffer<JmlSpecificationCase>();
                ListBuffer<JmlSpecificationCase> allitcases = new ListBuffer<JmlSpecificationCase>();
                ListBuffer<JmlSpecificationCase> allfecases = new ListBuffer<JmlSpecificationCase>();
                for (JmlSpecificationCase c: methodSpecs.cases) {
                    if (c.token == null && decl != null) mods = c.modifiers = decl.mods;
                    ListBuffer<JmlMethodClause> cl = new ListBuffer<JmlMethodClause>();
                    cl.appendList(commonClauses);  // FIXME - appending the same ASTs to each spec case - is this sharing OK
                    //System.out.println("DESUGARING CASE " + c);
                    ListBuffer<JmlSpecificationCase> newcases = deNest(cl,List.<JmlSpecificationCase>of(c),null,decl,msym,mods);
                    for (JmlSpecificationCase cs: newcases) {
                        addDefaultClauses(decl, mods, msym, pure, cs, nnexpr);
                    }
                    //System.out.println("DESUGARED " + newcases);
                    allcases.appendList(newcases);
                }
                for (JmlSpecificationCase c: methodSpecs.impliesThatCases) {
                    ListBuffer<JmlMethodClause> cl = new ListBuffer<JmlMethodClause>();
                    cl.appendList(commonClauses);
                    JCModifiers cmods = c.modifiers;
                    if (c.token == null && decl != null) cmods = c.modifiers = decl.mods;
                    ListBuffer<JmlSpecificationCase> newcases = deNest(cl,List.<JmlSpecificationCase>of(c),null,decl,msym,cmods);
                    for (JmlSpecificationCase cs: newcases) {
                        // Note: a model program spec case has no clauses
                        if (cs.clauses != null) {
                            addDefaultClauses(decl, mods, msym, pure, cs, nnexpr);
                        }
                    }
                    allitcases.appendList(newcases);
                }
                for (JmlSpecificationCase c: methodSpecs.forExampleCases) {
                    ListBuffer<JmlMethodClause> cl = new ListBuffer<JmlMethodClause>();
                    cl.appendList(commonClauses);
                    JCModifiers cmods = c.modifiers;
                    if (c.token == null && decl != null) cmods = c.modifiers = decl.mods;
                    ListBuffer<JmlSpecificationCase> newcases = deNest(cl,List.<JmlSpecificationCase>of(c),null,decl,msym,cmods);
                    for (JmlSpecificationCase cs: newcases) {
                        // Note: a model program spec case has no clauses
                        if (cs.clauses != null) {
                            addDefaultClauses(decl, mods, msym, pure, cs, nnexpr);
                        }
                    }
                    allfecases.appendList(newcases);
                }
                newspecs = jmlMaker.at(methodSpecs.pos).JmlMethodSpecs(allcases.toList());
                newspecs.impliesThatCases = allitcases.toList();
                newspecs.forExampleCases = allfecases.toList();
            } else if (decl != null) {
                int p = methodSpecs.pos;
                if (p <= 0) p = decl.pos;  // FIXME - this can happen with default constructors?
                if (p <= 0) p = env.enclClass.pos;  // Can be zero if the class text is right at the beginning of the file
                if (p <= 0) p = 1;
                if (p <= 0) log.error("jml.internal", "Bad position");
                JCModifiers cmods = jmlMaker.at(p).Modifiers(decl.mods.flags & Flags.AccessFlags);
                JmlSpecificationCase cs = jmlMaker.at(p).JmlSpecificationCase(cmods,false,null,null,commonClauses.toList(),null);
                addDefaultClauses(decl, mods, msym, pure, cs, nnexpr);
                newspecs = jmlMaker.at(p).JmlMethodSpecs(List.<JmlSpecificationCase>of(cs));
            } else {
                newspecs = jmlMaker.at(-1).JmlMethodSpecs(List.<JmlSpecificationCase>nil());
            }
            newspecs.decl = decl;
            msp.cases.deSugared = newspecs;
        } catch (Exception e) {
        	utils.unexpectedException(e,  "DESUGARING");
        } finally {
            log.useSource(prevSource);
        }
    }

    protected void addDefaultClauses(JmlMethodDecl decl, JCModifiers mods, MethodSymbol msym, JmlToken pure, JmlSpecificationCase cs, JCExpression nnexpr) {
//		boolean inliningCall = mods != null && utsl.hasModifier(mods, Modifiers.INLINE);
//		if (inliningCall) return;
		String constructorDefault = JmlOption.defaultsValue(context,"constructor","everything");
        boolean hasAssignableClause = false;
        boolean hasAccessibleClause = false;
        boolean hasCallableClause = false;
        boolean hasSignalsOnlyClause = false;
        for (JmlMethodClause clm: cs.clauses) {
            IJmlClauseKind ct = clm.clauseKind;
            if (ct == assignableClauseKind) { 
                hasAssignableClause = true; 
            } else if (ct == SignalsOnlyClauseExtension.signalsOnlyClauseKind) { 
                hasSignalsOnlyClause = true; 
            } else if (ct == accessibleClauseKind) { 
                hasAccessibleClause = true; 
            } else if (ct == CallableClauseExtension.callableClause) { 
                hasCallableClause = true; 
            }
        }
        ListBuffer<JmlMethodClause> newClauseList = new ListBuffer<>();
        if (!hasAssignableClause && cs.block == null) {
            JmlMethodClause defaultClause;
            if (utils.hasModifier(mods,Modifiers.INLINE)) {
                // If inlined, do not add any clauses
                defaultClause = null;
            } else if (pure != null || constructorDefault.equals("pure")) {
                if (msym.isConstructor()) {
                    // FIXME - or should this just be \nothing
                    JCIdent t = jmlMaker.Ident(names._this);
                    t.type = decl.sym.owner.type;
                    t.sym = decl.sym.owner;
                    defaultClause = jmlMaker.at(cs.pos).JmlMethodClauseStoreRef(assignableID, assignableClauseKind,
                            List.<JCExpression>of(jmlMaker.at(cs.pos).Select(t,(Name)null)));
                } else {
                    int pos = pure != null ? pure.pos : cs.pos;
                    var kw = jmlMaker.at(pos).JmlSingleton(nothingKind);
                    defaultClause = jmlMaker.at(pos).JmlMethodClauseStoreRef(assignableID, assignableClauseKind,
                            List.<JCExpression>of(kw));
                }
            } else {
                var kw = jmlMaker.at(cs.pos).JmlSingleton(everythingKind);
                defaultClause = jmlMaker.at(cs.pos).JmlMethodClauseStoreRef(assignableID, assignableClauseKind,
                        List.<JCExpression>of(kw));
            }
            if (defaultClause != null) {
                defaultClause.sourcefile = log.currentSourceFile();
                newClauseList.add(defaultClause);
            }
        }
        if (!hasAccessibleClause) {
            JmlMethodClause defaultClause;
            jmlMaker.at(cs.pos);
            if (utils.findModifier(mods,Modifiers.INLINE) != null) {
                // If inlined, do not add any clauses
                defaultClause = null;
            } else {
                defaultClause = jmlMaker.JmlMethodClauseStoreRef(accessibleID, accessibleClauseKind,
                        List.<JCExpression>of(jmlMaker.JmlSingleton(everythingKind)));
            }
            if (defaultClause != null) {
                defaultClause.sourcefile = log.currentSourceFile();
                newClauseList.add(defaultClause);
            }
        }
        // FIXME - add this in later
//        if (!hasSignalsOnlyClause) {
//            DiagnosticPosition p = decl.pos();
//            if (decl.thrown != null && !decl.thrown.isEmpty()) p = decl.thrown.get(0).pos();
//            ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
//            if (decl.thrown != null) list.addAll(decl.thrown);
//            list.add(factory.at(p).Type(syms.runtimeExceptionType));
//            JmlMethodClauseSignalsOnly defaultClause = (factory.at(p).JmlMethodClauseSignalsOnly(JmlTokenKind.SIGNALS_ONLY, list.toList()));
//            defaultClause.sourcefile = log.currentSourceFile();
//        newClauseList.add(defaultClause);

//        }
//        if (!hasCallableClause) {
//            jmlMaker.at(cs.pos);
//            JmlMethodClause defaultClause = jmlMaker.JmlMethodClauseStoreRef(JmlTokenKind.CALLABLE,
//                    List.<JCExpression>of(jmlMaker.JmlStoreRefKeyword(JmlTokenKind.BSEVERYTHING)));
//      newClauseList.add(defaultClause);
//        }

        // JmlAssertionAdder expects the first requires clause to be params nonnull test, even if it is 'true'
        	// FIXME - where?
        var req = jmlMaker.at(cs.pos).JmlMethodClauseExpr(requiresID, requiresClauseKind, nnexpr);
        cs.clauses = cs.clauses.appendList(newClauseList).prepend(req);
    }
    
    
    boolean desugaringPure = false;
    
    // FIXME - this ignores anything after a clause group.  That is OK in strict JML.  DO we want it?  There is no warning.
    public ListBuffer<JmlSpecificationCase> deNest(ListBuffer<JmlMethodClause> prefix, List<JmlSpecificationCase> cases, /*@ nullable */JmlSpecificationCase parent, JmlMethodDecl decl, MethodSymbol msym, JCModifiers mods) {
        ListBuffer<JmlSpecificationCase> newlist = new ListBuffer<JmlSpecificationCase>();
        if (cases.isEmpty()) {
            if (parent != null) {
                addDefaultSignalsOnly(prefix,parent,decl);
                newlist.append(((JmlTree.Maker)make).at(parent.pos).JmlSpecificationCase(mods,parent.code,parent.token,parent.also,prefix.toList(),null));
            }
            else {
                // ERROR - not allowed to have an empty collection of specification cases
                // at the top level
                log.error("jml.internal","Unexpected empty set of specification cases at the top-level in JmlAttr");
            }
        } else if (cases.size() == 1) {
            // common case that just avoids copying the prefix
            JmlSpecificationCase c = cases.get(0);
            handleCase(parent, decl, msym, newlist, c, prefix, mods);
        } else {
            for (JmlSpecificationCase cse: cases) {
                ListBuffer<JmlMethodClause> pr = copy(prefix);
                handleCase(parent, decl, msym, newlist, cse, pr, mods);
            }
        }
        return newlist;
    }
    
    // FIXME - document; remove parent
    protected void addDefaultSignalsOnly(ListBuffer<JmlMethodClause> prefix, JmlSpecificationCase parent, JmlMethodDecl decl) {
        if (parent.block != null) return; // If there is a model_program block, we do not add any default
        boolean anySOClause = false;
        boolean anyRecommendsClause = false;
        boolean signalsIsFalse = false;
        for (JmlMethodClause cl: prefix) {
            if (cl.clauseKind == signalsClauseKind && treeutils.isFalseLit(((JmlMethodClauseSignals)cl).expression)) signalsIsFalse = true;
            if (cl.clauseKind == signalsOnlyClauseKind) anySOClause = true;
            if (cl.clauseKind == recommendsClauseKind) anyRecommendsClause = true;
        }
        // FIXME - should incorporate the recommends exceptions somehow
        if (!anySOClause) {
            DiagnosticPosition p = decl != null ? decl.pos() : null;
            ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
            if (!signalsIsFalse || anyRecommendsClause) {
                if (decl != null && decl.thrown != null && !decl.thrown.isEmpty()) p = decl.thrown.get(0).pos();
                if (decl != null && decl.thrown != null) list.addAll(decl.thrown);
                list.add(jmlMaker.at(p).Type(syms.runtimeExceptionType));
            }
            JmlMethodClauseSignalsOnly cl = (jmlMaker.at(p).JmlMethodClauseSignalsOnly(signalsOnlyID, signalsOnlyClauseKind, list.toList()));
            cl.sourcefile = log.currentSourceFile();
            cl.defaultClause = true;
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
    
    protected void handleCase(JmlSpecificationCase parent, JmlMethodDecl decl, MethodSymbol msym,
            ListBuffer<JmlSpecificationCase> newlist, JmlSpecificationCase cse,
            ListBuffer<JmlMethodClause> pr, JCModifiers mods) {
        if (cse.token == modelprogramClause) {
            newlist.append(cse);  // FIXME - check that model programs are only at the outer level
            return;
        }
        if (parent == null) {
            JmlTree.Maker jmlF = (JmlTree.Maker)make;
            IJmlClauseKind t = cse.token;
            if (t == normalBehaviorClause || t == normalExampleClause) {
                JmlMethodClauseSignals cl = jmlF.at(cse.pos).JmlMethodClauseSignals(signalsID, signalsClauseKind,null,falseLit);
                cl.sourcefile = cse.sourcefile;
                pr.append(cl);
            } else if (t == exceptionalBehaviorClause || t == exceptionalExampleClause) {
                JmlMethodClauseExpr cl = jmlF.at(cse.pos).JmlMethodClauseExpr(ensuresID, ensuresClauseKind,falseLit);
                cl.sourcefile = cse.sourcefile;
                pr.append(cl);
            }
        }
        // FIXME - when is decl null
        newlist.appendList(deNestHelper(pr,cse.clauses,parent==null?cse:parent,decl,msym,mods));
    }
    
    public ListBuffer<JmlSpecificationCase> deNestHelper(ListBuffer<JmlMethodClause> prefix, List<JmlMethodClause> clauses, JmlSpecificationCase parent, JmlMethodDecl decl, MethodSymbol msym, JCModifiers mods) {
        ListBuffer<JmlSpecificationCase> newlist = new ListBuffer<JmlSpecificationCase>();
        ListBuffer<JmlMethodClause> exlist = null;
        JmlMethodClauseSignalsOnly signalsOnly = null;
        JmlMethodClauseExpr excRequires = null;
        JmlMethodClauseSignals signalsClause = null;
        boolean hasRecommendsBlock = false;
        boolean errorRecommendsBlock = false;
        for (JmlMethodClause m: clauses) {
            IJmlClauseKind t = m.clauseKind;
            JCExpression excType = null;
            if (t == recommendsClauseKind && (excType=((RecommendsClause.Node)m).exceptionType) != null) {
                // Generate these clauses for the exceptional behavior 
                //     requires disjunction of negation of each requires condition
                //     assigns \nothing
                //     signals_only list of exceptions in the else clauses
                //     signals (Exception) disjunction of (\exception instance of else-exception && negation of requires condition)
                //     ensures false
            	// System.out.println("RECOMMENDS " + m);
                boolean first = exlist == null;
                if (first && hasRecommendsBlock && !errorRecommendsBlock) {
                    log.error(m.pos,"jml.message","Only one block of recommends clauses is permitted");
                    errorRecommendsBlock = true;
                    continue;
                }
                if (first) {
                    exlist = copy(prefix);
                }
                RecommendsClause.Node rc = (RecommendsClause.Node)m;
                JmlMethodClauseExpr substRequires = jmlMaker.at(m.pos).JmlMethodClauseExpr(requiresID,requiresClauseKind,rc.expression);
                prefix.append(substRequires);
                JmlMethodClauseExpr nn = jmlMaker.at(m.pos).JmlMethodClauseExpr(requiresID,requiresClauseKind,
                        treeutils.makeNot(substRequires.pos, rc.expression));
                if (first) {
                    excRequires = nn;
                    exlist.add(excRequires);
                    signalsOnly = jmlMaker.at(m.pos).JmlMethodClauseSignalsOnly(signalsOnlyID,signalsOnlyClauseKind,List.<JCExpression>nil());
                    exlist.add(signalsOnly);
                    JCVariableDecl signalClauseVar = treeutils.makeVarDef(syms.exceptionType, null, msym, m.pos);
                    signalsClause = jmlMaker.at(m.pos).JmlMethodClauseSignals(signalsID,signalsClauseKind,signalClauseVar,treeutils.falseLit);
                    exlist.add(signalsClause);
                    exlist.add(jmlMaker.at(m.pos).JmlMethodClauseExpr(ensuresID,ensuresClauseKind,treeutils.falseLit));
//                    exlist.add(jmlMaker.JmlMethodClauseStoreRef(assignableID,assignableClauseKind,
//                            List.<JCExpression>of(jmlMaker.JmlStoreRefKeyword(nothingKind))));
                    exlist.add(jmlMaker.JmlMethodClauseStoreRef(assignableID,assignableClauseKind,
                            List.<JCExpression>of(jmlMaker.JmlSingleton(nothingKind))));
                } else {
                    excRequires.expression = treeutils.makeBitOr(m.pos,
                            excRequires.expression, nn.expression);
                }
                signalsOnly.list = signalsOnly.list.append(excType);
                JmlSingleton ee = jmlMaker.at(m.pos).JmlSingleton(exceptionKind);
                JCExpression iof = treeutils.makeInstanceOf(m.pos, ee, excType);
                JCExpression disjunct = treeutils.makeAnd(m.pos, iof, nn.expression);
                signalsClause.expression = treeutils.makeOrSimp(m.pos, signalsClause.expression, disjunct);
                hasRecommendsBlock = true;
                continue;
            }
            if (t == requiresClauseKind && m instanceof JmlMethodClauseExpr req && req.exception != null) {
                ListBuffer<JmlMethodClause> nprefix = new ListBuffer<>();
                for (var cl: prefix) if (cl.clauseKind == requiresClauseKind || cl.clauseKind == oldClause || cl.clauseKind == recommendsClauseKind) nprefix.add(cl);
                var nreq = jmlMaker.at(m).JmlMethodClauseExpr(req.keyword,  req.clauseKind, treeutils.makeNot(req.expression, req.expression));
                nreq.sourcefile = log.currentSourceFile();
                nprefix.add(nreq);
                JmlMethodClauseStoreRef asg = jmlMaker.at(m).JmlMethodClauseStoreRef(writesID,  assignableClauseKind, 
                        List.of(jmlMaker.at(m).JmlSingleton(nothingKind)));
                asg.sourcefile = log.currentSourceFile();
                nprefix.add(asg);
                nreq = jmlMaker.at(m).JmlMethodClauseExpr(ensuresID,  ensuresClauseKind, treeutils.falseLit);
                nreq.sourcefile = log.currentSourceFile();
                nprefix.add(nreq);
                var cl = (jmlMaker.at(req).JmlMethodClauseSignalsOnly(signalsOnlyID, signalsOnlyClauseKind, 
                        List.<JCExpression>of(req.exception)));
                cl.sourcefile = log.currentSourceFile();
                nprefix.add(cl);
                JmlSpecificationCase sc = jmlMaker.at(parent).JmlSpecificationCase(mods, false, exceptionalBehaviorClause, null,nprefix.toList(),null);
                sc.modifiers = parent.modifiers;
                newlist.append(sc);
                m = jmlMaker.at(m).JmlMethodClauseExpr(req.keyword,  req.clauseKind, req.expression); // no exception
                m.sourcefile = log.currentSourceFile();
           }

            if (exlist != null) {
                JmlSpecificationCase scase = jmlMaker.JmlSpecificationCase(mods,false,behaviorClause,null,exlist.toList(),null);
                newlist.append(scase);
                exlist = null;
                signalsOnly = null;
                signalsClause = null;
                excRequires = null;
            	//System.out.println("EXLIST NOT NULL-B " + scase);
            }
            if (m instanceof JmlMethodClauseGroup) {
                return deNest(prefix,((JmlMethodClauseGroup)m).cases, parent,decl, msym, mods);
            }
            if (t == ensuresClauseKind) {
                if (parent.token == exceptionalBehaviorClause || parent.token == exceptionalExampleClause) {
                    log.error(m.pos,"jml.misplaced.clause","Ensures","exceptional");
                    continue;
                }
            } else if (t == signalsClauseKind) {
                if (parent.token == normalBehaviorClause || parent.token == normalExampleClause) {
                    log.error(m.pos,"jml.misplaced.clause","Signals","normal");
                    continue;
                }
            } else if (t == signalsOnlyClauseKind) {
                if (parent.token == normalBehaviorClause || parent.token == normalExampleClause) {
                    log.error(m.pos,"jml.misplaced.clause","Signals_only","normal");
                    continue;
                }
                int count = 0;
                for (JmlMethodClause mc: prefix) {
                    if (mc.clauseKind == signalsOnlyClauseKind) count++;
                }
                if (count > 0) {
                    log.error(m.pos,"jml.multiple.signalsonly");
                }
            } else if (desugaringPure && t == assignableClauseKind) {
                JmlMethodClauseStoreRef asg = (JmlMethodClauseStoreRef)m;
                if (msym.isConstructor()) {
                    // A pure constructor allows assigning to class member fields
                    // So if there is an assignable clause the elements of the clause
                    // may only be members of the class
                    for (JCTree tt: asg.list) {
                        if (tt instanceof JmlSingleton k && k.kind == nothingKind) {
                            // OK
                        } else if (tt instanceof JmlStoreRefKeyword k && k.kind == nothingKind) {
                                // OK
                        } else if (tt instanceof JCIdent) {
                            // non-static Simple identifier is OK
                            // If the owner of the field is an interface, it
                            // is by default static. However, it might be a
                            // JML field marked as instance.
                            VarSymbol sym = (VarSymbol)((JCIdent)tt).sym;
                            if (sym != null && utils.isJMLStatic(sym)) {  // FIXME _ I don't think this should ever be null and is a problem if it is
                                utils.error(tt,"jml.pure.constructor",tt.toString());
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
                            if (!ok) utils.error(tt,"jml.pure.constructor",tt.toString());
                        } else {
                            // FIXME - also allow this.*  or super.* ?
                            utils.error(tt,"jml.pure.constructor",tt.toString());
                        }
                    }
                } else {
                    for (JCTree tt: asg.list) {
                    	var p = tt.pos != Position.NOPOS ? tt.pos : asg.pos != Position.NOPOS ? asg.pos : decl != null ? decl.pos : Position.NOPOS;
                        if (tt instanceof JmlStoreRefKeyword &&
                                ((JmlStoreRefKeyword)tt).kind == nothingKind) {
                                    // OK
                        } else if (tt instanceof JmlSingleton key &&
                                    key.kind == nothingKind) {
                                        // OK
                        } else if (decl != null && isHeapIndependent(decl.sym)) {
                            utils.error(asg.source(),p,"jml.no_state.method",tt.toString());
                        } else {
                            utils.error(asg.source(),p,"jml.pure.method", tt.toString() + " in " + msym.owner + "." + msym);
                        }
                    }
                }
            }
            prefix.append(m);
        }
        if (exlist != null) {
            JmlSpecificationCase scase = jmlMaker.JmlSpecificationCase(decl.mods,false,behaviorClause,null,exlist.toList(),null);
            scase.callee_only = true;
            newlist.append(scase);
            exlist = null;
            signalsOnly = null;
        	//System.out.println("EXLIST NOT NULL " + scase);
        }
        addDefaultSignalsOnly(prefix,parent,decl);
        JmlSpecificationCase sc = (((JmlTree.Maker)make).JmlSpecificationCase(parent,prefix.toList()));
        sc.modifiers = parent.modifiers;
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
        if (!specLocalEnv) return;
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
    
    @Override
    protected void checkInit(JCTree tree,
            Env<AttrContext> env,
            VarSymbol v,
            boolean onlyWarning) {
    	
    	boolean allowForwardRefSaved = allowForwardRef;
    	allowForwardRef = !(jmlenv.currentClauseKind == null || jmlenv.currentClauseKind == declClause); // FIXME - is this OK for oldClause - when is it ever needed?
    	super.checkInit(tree,env,v,onlyWarning);
    	allowForwardRef = allowForwardRefSaved;
    }
    
    protected void checkEnumInitializer(JCTree tree, Env<AttrContext> env, VarSymbol v) {
        if (isStaticEnumField(v)) {
            if (jmlenv.currentClauseKind != null) return;  // ASWemahy reference enums in specificatinos.  FIXME: always? everywhere?  interaction with JLS restriction?
        }
        super.checkEnumInitializer(tree,env,v);
    }

    
    public ModifierKind[] allowedFieldModifiers = new ModifierKind[] {
            SPEC_PUBLIC, SPEC_PROTECTED, MODEL, GHOST,
            NON_NULL, NULLABLE, INSTANCE, MONITORED, SECRET,
            PEER, REP, READONLY // FIXME - allowing these until the rules are really implemented
       };
       
    public ModifierKind[] allowedGhostFieldModifiers = new ModifierKind[] {
            GHOST, NON_NULL, NULLABLE, INSTANCE, MONITORED, SECRET,
            PEER, REP, READONLY // FIXME - allowing these until the rules are really implemented
       };
       
    public ModifierKind[] allowedModelFieldModifiers = new ModifierKind[] {
            MODEL, NON_NULL, NULLABLE, INSTANCE, SECRET,
            PEER, REP, READONLY // FIXME - allowing these until the rules are really implemented
       };
       
    public ModifierKind[] allowedFormalParameterModifiers = new ModifierKind[] {
            NON_NULL, NULLABLE, READONLY, REP, PEER, SECRET,
       };
       
    public ModifierKind[] allowedLocalVarModifiers = new ModifierKind[] {
            NON_NULL, NULLABLE, GHOST, UNINITIALIZED, READONLY, REP, PEER, SECRET
       };
    
    public ModifierKind[] allowedMethodSpecDeclModifiers = new ModifierKind[] {
            NON_NULL, NULLABLE, READONLY  // FIXME - should this include readonly?
       };
    
    public void checkTypeMods(JCVariableDecl tree) {
    	if (!org.jmlspecs.openjml.Main.useJML) return;
    	boolean hasNonNull = false;
    	boolean hasNullable = false;
    	for (var t: tree.type.getAnnotationMirrors()) {
    		String s = t.type.toString();
    		if (s.equals(Modifiers.NON_NULL.fullAnnotation)) hasNonNull = true;
    		if (s.equals(Modifiers.NULLABLE.fullAnnotation)) hasNullable = true;
    	}
    	if (hasNonNull && hasNullable) {
    		utils.error(tree.vartype, "jml.message", "A type may not be declared both non_null and nullable");
    	}
//    	System.out.println("VAR ANN " + tree.mods.annotations);
//    	System.out.println("VAR TYPE " + tree.type);
//    	System.out.println("VAR TYPE " + tree.type.getAnnotationMirrors());
//    	System.out.println("VAR SYM " + tree.sym);
//    	System.out.println("VAR SYM ANN " + tree.sym.getAnnotationMirrors());
    }
    
    public void checkVarDecl(JmlVariableDecl javaField) {
        var fspecs = specs.getLoadedSpecs(javaField.sym);
        if (fspecs != null) {
            annotationsToModifiers(fspecs.mods);
            if (fspecs.mods != fspecs.decl.mods) annotationsToModifiers(fspecs.mods); // FIXME - figure out which of these we actually need
            var specField = fspecs.decl;
            // check for no initializer
            if (specField.getInitializer() != null && // There is an initializer
                                    utils.isSpecFile(specField.sourcefile) && // Not in a .java file
                                    javaField != specField && // But there is a .java file
                                    !utils.isJML(specField.mods) && // The decl is not in JML
                                    specField.sym.owner.kind != Kinds.Kind.MTH && // The decl is not a local decl in a method body
                                    !specField.sym.owner.isEnum() // We are not an enum
                                    ) {
                utils.error(specField.sourcefile,specField.getInitializer(),"jml.no.initializer.in.specs",specField.sym.owner+"."+specField.name);
            }
            //if (javaField != null && javaField != specField) checkAnnotations(javaField.mods, specField.mods, javaField.sym.owner);
        } else {
            // Spec fields, such as old declarations in method specs and declarations in quantifiers and the like,
            // do not have specifications (so fspecs will be null)
            annotationsToModifiers(javaField.mods);
        }
        checkVarMods(javaField);
        checkTypeMods(javaField);
    }
    
    public void checkJavaFlags(long javaFlags, JmlSource javaTree, long specflags, JmlSource specTree, Symbol symForFlags) {
        boolean isInterface = symForFlags.owner.isInterface();
        // Check that modifiers are the same
        long matchf = javaFlags;
        long specf = specflags;
        matchf |= (specf & Flags.SYNCHRONIZED); // binary files do not seem to always have the synchronized
                                                // modifier? FIXME - and only for methods
        long diffs = (matchf ^ specf);
        String key = null;
        if (symForFlags instanceof MethodSymbol) {
            diffs &= Flags.MethodFlags;
            if (isInterface) {
                diffs &= ~Flags.PUBLIC;
                diffs &= ~Flags.ABSTRACT;
            }
            key = "jml.mismatched.method.modifiers";
        }
        if (symForFlags instanceof ClassSymbol) {
            isInterface = symForFlags.isInterface();
            diffs &= Flags.ClassFlags;
            if (isInterface) {
                diffs &= ~Flags.PUBLIC;
                diffs &= ~Flags.ABSTRACT;
            }
            boolean isEnum = (javaFlags & Flags.ENUM) != 0;
            boolean isRecord = (javaFlags & Flags.RECORD) != 0;
            if (isEnum||isRecord) diffs &= ~Flags.FINAL;
            
            key = "jml.mismatched.modifiers";
        }
        if (symForFlags instanceof VarSymbol) {
            diffs &= Flags.VarFlags;
            if (isInterface) {
                diffs &= ~Flags.STATIC;
                diffs &= ~Flags.PUBLIC; // FIXME - this one needs fixing I think -- should instance fields in interfaces be default public? 
                if ((specf & Flags.FINAL) == 0) diffs &= ~Flags.FINAL;
            }
            key = "jml.mismatched.field.modifiers";
            if ((javaFlags & Flags.PARAMETER) != 0) key = "jml.mismatched.parameter.modifiers";
        }
        if (diffs != 0) {
            boolean isEnum = (javaFlags & Flags.ENUM) != 0;
            boolean isRecord = (javaFlags & Flags.RECORD) != 0;
            if ((Flags.NATIVE & matchf & ~specf) != 0)
                diffs &= ~Flags.NATIVE;
            if (isEnum && symForFlags.isConstructor()) {
                ((JmlMethodDecl)specTree).mods.flags |= (matchf & 7);
                diffs &= ~7;
            } // FIXME - should only do this if specs are default
            if ((matchf & specf & Flags.ANONCONSTR) != 0 && isEnum) {
                diffs &= ~2;
                ((JmlMethodDecl)specTree).mods.flags |= 2;
            } // enum constructors can have differences
            if (diffs != 0 && !(symForFlags.isConstructor() && diffs == 3)) {
                // FIXME - hide this case for now because of default constructors in binary
                // files
                if (specTree == null) {
                    utils.error(javaTree.source(), javaTree.pos(),
                        key, symForFlags instanceof ClassSymbol cs ? cs : symForFlags.owner + "." + symForFlags,
                            Flags.toString(diffs));
               } else {
                   if (javaTree != null) {
                    utils.errorAndAssociatedDeclaration(specTree.source(), specTree.pos(),
                        javaTree.source(), javaTree.pos(),
                        key, symForFlags instanceof ClassSymbol cs ? cs : symForFlags.owner + "." + symForFlags,
                            Flags.toString(diffs));
                   } else {
                       utils.error(specTree.source(), specTree.pos(),
                           key, symForFlags instanceof ClassSymbol cs ? cs : symForFlags.owner + "." + symForFlags,
                               Flags.toString(diffs));
                   }
                }
            }
        }
        
        // class mod checks from elsewhere
//        if (specsDecl != null) {
//            // FIXME - no way to skip the loop if the specsDecl is the javaDecl
//            
//            // Check that modifiers are the same
//            long matchf = javaClassSym.flags();
//            long specf = specsDecl.mods.flags;
//            long diffs = (matchf ^ specf)&Flags.ClassFlags; // Includes whether both are class or both are interface
//            if (diffs != 0) {
//                boolean isInterface = (matchf & Flags.INTERFACE) != 0;
//                boolean isEnum = (matchf & Flags.ENUM) != 0;
//                if ((Flags.ABSTRACT & matchf & ~specf) != 0 && (isInterface||isEnum)) diffs &= ~Flags.ABSTRACT; // FIXME - why for enum?
//                if ((Flags.STATIC & matchf & ~specf) != 0 && isEnum) diffs &= ~Flags.STATIC; 
//                if ((Flags.FINAL & matchf & ~specf) != 0 && isEnum) diffs &= ~Flags.FINAL; 
//                if ((Flags.FINAL & matchf & ~specf) != 0 && javaClassSym.name.isEmpty()) diffs &= ~Flags.FINAL; // Anonymous classes are implicitly final
//                if (diffs != 0) {
//                    //JavaFileObject prev = log.useSource(specsClassDecl.source());
//                    utils.error(specsDecl.sourcefile, specsDecl.pos(),"jml.mismatched.modifiers", specsClassDecl.name, javaClassSym.fullname, Flags.toString(diffs));  // FIXME - test this
//                    //log.useSource(prev);
//                }
//                // FIXME - how can we tell where in which specs file the mismatched modifiers are
//                // SHould probably check this in the combining step
//            }
//            // FIXME - this is needed, but it is using the environment from the java class, not the 
//            // spec class, and so it is using the import statements in the .java file, not those in the .jml file
//            attribAnnotationTypes(specsClassDecl.mods.annotations, Enter.instance(context).typeEnvs.get(javaClassSym));  // FIXME - this is done later; is it needed here?
//
//            //checkSameAnnotations(javaDecl.mods,specsClassDecl.mods);
//            // FIXME - check that both are Enum; check that both are Annotation
//        }


    }
       
    public void checkVarMods(JmlVariableDecl tree) {
        // tree.type.isErroneous() can be true during resolution of lambda expressions
        if (tree.name == names.error || tree.type == null || tree.type.isErroneous()) return;
        var mods = tree.mods;
        long javaflags = tree.sym.flags();
        String kind;
        JavaFileObject prev = log.useSource(tree.source());
        long specflags = mods.flags;
        var specmods = tree.mods;
        JmlVariableDecl treeForMods = tree;
        if (tree.specsDecl != null) {
            specmods = tree.specsDecl.mods;
            specflags = tree.specsDecl.mods.flags;
            treeForMods = tree.specsDecl;
            prev = log.useSource(tree.specsDecl.source());
            //attribAnnotationTypes(specmods.annotations,env);
        }
        try {
            //annotationsToModifiers(specmods);
            
            // The following was in JmlEnter -- FIXME - Review that it is now implemented here (or somewhere in JmlAttr)
//            VarSymbol javaSym = match;
//            long javaFlags = match.flags();
//            boolean isInterface = javaSym.owner.isInterface();
//            long specFlags = specVarDecl.mods.flags;
//            if (isInterface) {
//                if (isInterface && (specFlags & Flags.AccessFlags) == 0)
//                    specFlags |= Flags.PUBLIC;
//                long wasFinal = specFlags & Flags.FINAL;
//                if ((specVarDecl.mods.flags & Flags.AccessFlags) == 0)
//                    specVarDecl.mods.flags |= Flags.PUBLIC;
//                if (utils.isJML(specFlags)) {
//                    if (wasFinal == 0)
//                        specVarDecl.mods.flags &= ~Flags.FINAL;
//                    if (utils.hasMod(specVarDecl.mods, Modifiers.INSTANCE))
//                        specVarDecl.mods.flags &= ~Flags.STATIC;
//                }
//            }

        	// specmods is the mods from the JML declaration, if it exists, otherwise the mods from the Java declaration
        	// This is because mods in JML supersede those in the Java file; there is a check thats the two are consistent
        	boolean specsinJML = utils.isJML(specmods);
        	boolean modsinJML = utils.isJML(mods);
        	boolean ownerInJML = utils.isJML(tree.sym.owner.flags());
        	boolean ghost = isGhost(specmods);
        	boolean model = isModel(specmods);
        	boolean modelOrGhost = model || ghost;
        	//if (tree.name.toString().contains("m1")) System.out.println(" DATA " + tree.sym.owner + " " + tree.name + " " + specsinJML + " " + ownerInJML + " " + modelOrGhost);
        	if (tree.sym.owner.kind == Kind.TYP) {  // Field declarations
        		kind = "field";
        		if (ghost) {
        			allAllowed(specmods, allowedGhostFieldModifiers, "ghost field declaration");
        		} else if (model) {
        			allAllowed(specmods, allowedModelFieldModifiers, "model field declaration");
        		} else {
        			allAllowed(specmods, allowedFieldModifiers, "field declaration");
        		}
        		// A corner case: the declaration is a Java declaration, but the corresponding declaration in the specs
        		// is in JML. This would have already been reported as a duplicate declaration.
        		if (ownerInJML && modelOrGhost) {
        			if (ghost) utils.error(log.currentSourceFile(),treeForMods.pos,"jml.no.nested.ghost.type", tree.name + " in " + tree.sym.owner);
        			else       utils.error(log.currentSourceFile(),treeForMods.pos,"jml.no.nested.model.type", tree.name + " in " + tree.sym.owner);
        		} else if (specsinJML && !modelOrGhost && !ownerInJML  && !tree.sym.owner.isAnonymous()) {
        			utils.error(log.currentSourceFile(),treeForMods,"jml.missing.ghost.model", tree.sym.owner + "." + tree.sym);
        		} else if (modelOrGhost && !specsinJML) {
                	var loc = model ? utils.findModifier(specmods,Modifiers.MODEL) : utils.findModifier(specmods,Modifiers.GHOST);
        			utils.error(log.currentSourceFile(),loc,"jml.ghost.model.on.java", tree.sym.owner + "." + tree.sym);
        		} 
        		JmlAnnotation a;
        		if (!model) {
        			checkForConflict(specmods,SPEC_PUBLIC,SPEC_PROTECTED);
        			checkForRedundantSpecMod(specmods);
        		}
        		JmlToken t = utils.findModifier(specmods,INSTANCE);
        		if (t != null && isStatic(specmods)) {
        			utils.error(t.source,t.pos(),"jml.conflicting.modifiers","instance","static");
        		}
        		//            if (model && ((tree.mods.flags & Flags.FINAL)!=0)) {   // FIXME - WHy would model and final conflict
        		//                a = utils.findMod(tree.mods,MODEL);
        		//                utils.error(a.sourcefile,a.pos(),"jml.conflicting.modifiers","model","final");
        		//            }
        		checkForConflict(specmods,NON_NULL,NULLABLE);
        	} else if ((tree.mods.flags & Flags.PARAMETER) != 0) { // formal parameters
        		kind = "parameter";
        		if (tree.specsDecl != null) {
        		    // FIXME - is this needed?
        			attribAnnotationTypes(specmods.annotations,env);
        		}
        		allAllowed(specmods, allowedFormalParameterModifiers, "formal parameter");
        		checkForConflict(specmods,NON_NULL,NULLABLE);

        	} else if (jmlenv.currentClauseKind == MethodDeclClauseExtension.oldClause) {
                allAllowed(specmods, allowedMethodSpecDeclModifiers, "old clause declaration");

        	} else { // local declaration - there is no separate spec in this case
        		kind = "local variable declaration";
        		// Note that all annotations here are type-annotations
        		boolean ghostX = utils.hasModifier(specmods, Modifiers.GHOST);  // FIXME - are we checking the specification mods?
                boolean modelOrGhostX = ghostX || utils.hasModifier(specmods, Modifiers.MODEL);
        		allAllowed(specmods, allowedLocalVarModifiers, kind);
        		if (modsinJML && !ghost  && !isInJmlDeclaration && !ownerInJML && !jmlenv.inExpressionScope) {
        			utils.error(tree.source(),tree.pos,"jml.missing.ghost", tree.sym + " in " + tree.sym.owner.owner + "." + tree.sym.owner);
        		} else if (!modsinJML && ghost) {
        			utils.error(tree.source(),tree.pos,"jml.ghost.on.java", tree.sym + " in " + tree.sym.owner.owner + "." + tree.sym.owner);
        		} else if (modelOrGhostX && jmlenv.inExpressionScope) {
        			utils.error(log.currentSourceFile(),treeForMods.pos,"jml.message","ghost or model modifiers not permitted on an expression-local declaration");
        		} 
        		checkForConflict(mods,NON_NULL,NULLABLE);
        	}
            checkForDuplicateModifiers((JmlModifiers)mods);
//            if (tree.specsDecl != null) {
//                checkSameAnnotations(tree.mods,tree.specsDecl.mods,kind,tree.name.toString());
//            }
            
            checkJavaFlags(javaflags, (JmlSource)tree, specflags, tree.specsDecl, tree.sym);
                 
            // Check that types match 
            if (tree.specsDecl != null) { // tree.specsDecl can be null if there is a parsing error
                Type specType = attribType(tree.specsDecl.vartype,env);
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
        } finally {
        	log.useSource(prev);
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
        var secret = utils.findModifier(mods, Modifiers.SECRET);
        VarSymbol secretDatagroup = null;
        // FIXME
//        if (secret != null) {
//            List<JCExpression> args = secret.getArguments();
//            if (!args.isEmpty()) {
//                utils.error(secret.source,args.get(0).pos,"jml.no.arg.for.field.secret");
//            }
//        }
        
        // Note that method parameters, which belong to Methods, have
        // null FieldSpecs
        if (tree.sym.owner.kind == Kind.TYP) {
            // Check all datagroups that the field is in
            JmlSpecs.FieldSpecs fspecs = specs.getAttrSpecs(tree.sym);
            jmlenv = jmlenv.pushCopy();
            if (fspecs != null) try {
                for (JmlTypeClause tc: fspecs.list) {
                    if (tc.clauseType == inClause) {
                        JmlTypeClauseIn tcin = (JmlTypeClauseIn)tc;
                        jmlenv.currentClauseKind = inClause;
                        jmlenv.jmlVisibility = tcin.parentVar.mods.flags & Flags.AccessFlags;
                        for (JmlGroupName g: tcin.list) {
                            attributeGroup(g);
                            if (g.sym == null) continue; // Happens if there was an error in finding g
                            if (hasAnnotation(g.sym,Modifiers.SECRET) != (secret != null)) {
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
                jmlenv = jmlenv.pop();
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
    
    Type attribBase(JCTree tree,
            Env<AttrContext> env, JCClassDecl owningTree,
            boolean classExpected,
            boolean interfaceExpected,
            boolean checkExtensible) {
    	var saved = jmlresolve.allowJML();
    	if (utils.isJML(owningTree.mods)) {
    		//System.out.println("SETTING TO ALLOW JML FOR " + tree + " IN " + env.enclClass.name  + " " + saved);
    		jmlresolve.setAllowJML(true);
    	}
    	//if (org.jmlspecs.openjml.Utils.isJML()) utils.warning(tree,"jml.message","ATTRIB BASE " + env.enclClass.name  + " " + utils.isJML(env.enclClass.mods) + " " + tree.toString().substring(0,tree.toString().length() < 50 ? tree.toString().length() : 50) + " " + jmlresolve.allowJML());
    	try {
    		return super.attribBase(tree, env, classExpected, interfaceExpected, checkExtensible); // FIXME - removed owningTree
    	} finally {
    		jmlresolve.setAllowJML(saved);
    	}
    }
    
    /** Overridden in order to be sure that the type specs are attributed. */
    public Type attribType(JCTree tree, Env<AttrContext> env) { // FIXME _ it seems this will automatically happen - why not?
        Type result;
        if (tree instanceof JCIdent id && Extensions.findKeyword(id.name) instanceof JmlPrimitiveTypes.JmlTypeKind kt) {
            // Backslash identifier -- user added type
            result = kt.getType(context);
            tree.type = result;
            id.sym = tree.type.tsym;
        } else {
            result = super.attribType(tree,env);
        }
        if (result.getTag() != TypeTag.VOID && !result.isErroneous() && 
                result.tsym instanceof ClassSymbol cs &&
                !result.isPrimitive()) {
            addTodo(cs);
        }
        return result;
    }

    
    public void visitJmlGroupName(JmlGroupName tree) {
        JCExpression nm = tree.selection;
        Type saved = result = attribExpr(nm,env,Type.noType);
        Symbol sym = null;
        if (nm.type.getTag() == TypeTag.ERROR) return;
        else if (nm instanceof JCIdent) sym = ((JCIdent)nm).sym;
        else if (nm instanceof JCFieldAccess) sym = ((JCFieldAccess)nm).sym;
        else if (nm instanceof JCErroneous) return;

        if (sym == null) {
            utils.error(tree,"jml.message","Unexpectedly did not find a resolution for this data group expression");
            return;
        }
        if (!(sym instanceof VarSymbol)) {
            utils.error(tree,"jml.message","data group expression incorrectly resolved as something other than a field: " + sym);
            return;
        }
        tree.sym = (VarSymbol)sym;
        
        JmlSpecs.FieldSpecs fspecs = specs.getAttrSpecs((VarSymbol)sym);
        boolean isSpecPublic = utils.hasMod(fspecs.mods,Modifiers.SPEC_PUBLIC);
        boolean isSpecProtected = utils.hasMod(fspecs.mods,Modifiers.SPEC_PROTECTED);
        
        if (!isModel(fspecs.mods) && !isSpecPublic && !isSpecProtected) {
            log.error(tree.pos,"jml.datagroup.must.be.model.in.maps");
        }
        if (inVarDecl != null && utils.isJMLStatic(sym) && !utils.isJMLStatic(inVarDecl.sym)) {
            log.error(tree.pos,"jml.instance.in.static.datagroup");
        }
        result = saved;
    }
    
    JmlVariableDecl inVarDecl = null;
    
    public void visitJmlTypeClauseIn(JmlTypeClauseIn tree) {
        JmlVariableDecl prevDecl = inVarDecl;
        jmlenv = jmlenv.pushCopy();
        jmlenv.currentClauseKind = tree.clauseType;
        jmlenv.inPureEnvironment = true;
        jmlenv.representsHead = null;
        //var localEnv = enter.typeEnvs.get(env.enclClass.sym);
        var localEnv = localEnv(env,enter.typeEnvs.get(env.enclClass.sym).tree);
        localEnv.info.staticLevel = 0;
        var savedEnv = env;
        env = localEnv;
        boolean isStaticParent = utils.isJMLStatic(tree.parentVar.sym);
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        try {
            inVarDecl = tree.parentVar;
            jmlenv.jmlVisibility = tree.parentVar.mods.flags & Flags.AccessFlags; // FIXME - don't thnk this is needed here
            tree.list.forEach(v -> attributeGroup(v));
            java.util.List<VarSymbol> circList = checkForCircularity(inVarDecl.sym);
            if (circList != null) {
                Iterator<VarSymbol> iter = circList.iterator();
                String chain = iter.next().name.toString();
                while (iter.hasNext()) chain = chain + " -> " + iter.next().name.toString();
                
                // FIXME - this would be better with a beginning and ending position
                log.error(tree.parentVar.sym.pos,"jml.circular.datagroup.inclusion",chain);
            }
        } finally {
            inVarDecl = prevDecl;
            jmlenv = jmlenv.pop();
            jmlresolve.setAllowJML(prevAllowJML);
            env = savedEnv;
            result = null;
        }
    }
    
    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps tree) {
        boolean prev = jmlresolve.setAllowJML(true);
        jmlenv = jmlenv.pushCopy();
        jmlenv.currentClauseKind = tree.clauseType;
        jmlenv.inPureEnvironment = true;
        // Also check that the member reference field matches the declaration FIXME
        // FIXME - static environment?
        // FIXME - check visibility
        boolean prevj = justAttribute;
        justAttribute = true;
        try {
            // FIXME : jmlVisibility = tree.parentVar.mods.flags & Flags.AccessFlags;
            tree.expressions.forEach(e -> attribExpr(e,env,Type.noType));
            for (JmlGroupName n: tree.list) {
                attributeGroup(n);
            }
        } finally {
        	justAttribute = prevj;
            jmlenv = jmlenv.pop();
            jmlresolve.setAllowJML(prev);
        }
    }

//    public void annotate(final List<JCAnnotation> annotations,
//            final Env<AttrContext> localEnv) {
//        Set<TypeSymbol> annotated = new HashSet<TypeSymbol>();
//        for (List<JCAnnotation> al = annotations; al.nonEmpty(); al = al.tail) {
//            JCAnnotation a = al.head;
//            Attribute.Compound c = annotate.attributeAnnotation(a,
//                                                            syms.annotationType,
//                                                            env);
////            if (c == null) continue;
//            if (!annotated.add(a.type.tsym))
//                log.error(a.pos, "duplicate.annotation");
//        }
//    }

    /** Attributes invariant, axiom, initially clauses */
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr tree) {
        var check = jmlenv = jmlenv.pushCopy();
        try {
            jmlenv.inPureEnvironment = true;
            tree.clauseType.typecheck(this, tree, env);
        } catch (Exception e) {
            utils.unexpectedException("Typechecking clause: " + tree, e);
            throw e;
        } finally {
            jmlenv = jmlenv.pop(check);
        }
    }

    public Name getAnnotationStringArg(JCAnnotation a) {
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
        var secret = utils.findModifier(mods,Modifiers.SECRET);
        if (secret == null) return null;
        // FIXME
//        if (secret.args.size() == 0) {
//            utils.error(secret,"jml.secret.requires.arg");
//            return null;
//        }
//        Name n = getAnnotationStringArg(secret);
//        boolean prev = jmlresolve.setAllowJML(true);
//        Symbol sym = rs.resolveIdent(secret.args.get(0).pos(),env,n,KindSelector.VAR);
//        jmlresolve.setAllowJML(prev);
//        if (sym instanceof VarSymbol) return (VarSymbol)sym;
//        utils.error(secret,"jml.no.such.field",n.toString());
        return null;
    }
    
    protected VarSymbol getQuerySymbol(JCMethodInvocation tree, JCModifiers mods) {
        var query = utils.findModifier(mods, Modifiers.QUERY);
        if (query == null) return null;
        // FIXME
//        List<JCExpression> args = query.getArguments();
//        Name datagroup = null;
//        DiagnosticPosition pos = tree.meth.pos();
//        if (args.isEmpty()) {
//            // No argument - use the name of the method
//            if (tree.meth instanceof JCIdent) datagroup = ((JCIdent)tree.meth).name;
//            else if (tree.meth instanceof JCFieldAccess) datagroup = ((JCFieldAccess)tree.meth).name;
//            pos = query.pos();
//        } else {
//            datagroup = getAnnotationStringArg(query);
//            pos = args.get(0).pos();
//        }
//        boolean prev = jmlresolve.setAllowJML(true);
//        Symbol sym = rs.resolveIdent(pos,env,datagroup,KindSelector.VAR);
//        jmlresolve.setAllowJML(prev);
//        if (sym instanceof VarSymbol) return (VarSymbol)sym;
//        utils.error(pos,"jml.no.such.field",datagroup.toString());
        return null;
    }
    
    ModifierKind[] clauseAnnotations = new ModifierKind[]{ INSTANCE };
    ModifierKind[] invariantAnnotations = new ModifierKind[]{ SECRET, INSTANCE, CAPTURED };
    ModifierKind[] representsAnnotations = new ModifierKind[]{ SECRET, INSTANCE };
    ModifierKind[] noAnnotations = new ModifierKind[]{  };

    public void checkTypeClauseMods(JCTree tree, JCModifiers mods,String where, IJmlClauseKind token) {
        long f = 0;
        if (token != axiomClause) f = Flags.AccessFlags | Flags.STATIC | Flags.FINAL;
        long diff = utils.hasOnly(mods,f);
        if (diff != 0) utils.error(tree,"jml.bad.mods",Flags.toString(diff));
        var a = utils.findModifier(mods,INSTANCE);
        if (a != null && isStatic(mods) ) {
            utils.error(a,"jml.conflicting.modifiers","instance","static");
        }
        attribAnnotationTypes(mods.annotations,env);
        annotationsToModifiers(mods); // FIXME - check that htis is not already done -- if it is then the attribution above is done as well
        switch (token.keyword()) {
            case axiomID:
                allAllowed(mods,noAnnotations,where);
                break;
            case invariantID:
                allAllowed(mods,invariantAnnotations,where);
                var t = utils.findModifier(mods, Modifiers.CAPTURED);
                if (t != null) {
                    if (!((JmlClassDecl)enclosingClassEnv.tree).sym.isAnonymous()) {
                        utils.error(t,"jml.message","The captured modifier may only modify anonymous class invariants that contain only captured variables");
                    } else {
                        // FIXME - need to check that all variables are captured
                    }
                }
                break;
            case representsID:
                allAllowed(mods,representsAnnotations,where);
                break;
            default:
                allAllowed(mods,clauseAnnotations,where);
                break;
        }
        if (token != axiomClause) {
            Check.instance(context).checkDisjoint(tree.pos(),mods.flags,Flags.PUBLIC,Flags.PROTECTED|Flags.PRIVATE);
            Check.instance(context).checkDisjoint(tree.pos(),mods.flags,Flags.PROTECTED,Flags.PRIVATE);
        }
    }
    
    /** Attributes a constraint clause */
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint tree) {
        JavaFileObject old = log.useSource(tree.source);
        jmlenv = jmlenv.pushCopy();
        jmlenv.inPureEnvironment = true;
        jmlenv.currentClauseKind = tree.clauseType;
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        try {
            // constraint
            boolean isStatic = (tree.modifiers.flags & STATIC) != 0;
            Env<AttrContext> localEnv = env;
            jmlenv.jmlVisibility = tree.modifiers.flags & Flags.AccessFlags;
            if (isStatic) localEnv.info.staticLevel++;
            ResultInfo prevResultInfo = resultInfo;
            resultInfo = new ResultInfo(KindSelector.of(KindSelector.VAL,KindSelector.TYP),Type.noType);
            attribExpr(tree.expression, localEnv, syms.booleanType);
            resultInfo = prevResultInfo;
            if (isStatic) localEnv.info.staticLevel--;
            checkTypeClauseMods(tree,tree.modifiers,"constraint clause",tree.clauseType);
            if (tree.sigs != null) for (JmlTree.JmlMethodSig sig: tree.sigs) {
                if (sig.argtypes == null) {
                    // FIXME - not implemented
                } else {
                    sig.accept(this);
                    Symbol s = sig.methodSymbol;
                    if (s != null && s.isConstructor()
                            && !isStatic) {
                        utils.error(sig,"jml.no.constructors.allowed");
                    }
                    if (s != null && s.kind != Kind.ERR){
                        if (s.owner != localEnv.enclClass.sym) {
                            utils.error(sig,"jml.incorrect.method.owner");
                        }
                    }

                }
            }
        } finally {
            jmlresolve.setAllowJML(prevAllowJML);
            jmlenv = jmlenv.pop();
            log.useSource(old);
        }
    }
    
   
    /** Attributes a declaration within a JML annotation - that is, a
     * model method, model type, or ghost or model field
     */
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl tree) {
    	//System.out.println("ATTR TYPE CLAUSE DECL " + tree);
    	jmlenv = jmlenv.pushCopy();
        JavaFileObject old = log.useSource(tree.source);
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        try {
            jmlenv.jmlVisibility = tree.modifiers.flags & Flags.AccessFlags;
            attribStat(tree.decl,env);
        } finally {
            jmlresolve.setAllowJML(prevAllowJML);
            log.useSource(old);
            jmlenv = jmlenv.pop();
        }
    }
    
    
    /** Attributes a initializer or static_initializer declaration */
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer tree) {
        JavaFileObject old = log.useSource(tree.source);
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        try {
            if (tree.modifiers != null && tree.modifiers.annotations != null && !tree.modifiers.annotations.isEmpty()) {
                utils.error(tree.modifiers.annotations.head.pos, "jml.message", "An initializer clause may not have annotations");
                tree.modifiers.annotations = null;
            }
            if (tree.modifiers != null && !((JmlModifiers)tree.modifiers).jmlmods.isEmpty()) {
                utils.error(((JmlModifiers)tree.modifiers).jmlmods.get(0).pos, "jml.message", "An initializer clause may not have annotations");
                ((JmlModifiers)tree.modifiers).jmlmods.clear();
            }
            long diff = 0;
            if (tree.modifiers != null && (diff = tree.modifiers.flags & ~0x7) != 0) {
                log.error(tree.modifiers.pos, "jml.message", "Invalid modifiers for an initializer clause: " + Flags.toString(diff));
                tree.modifiers.flags &= 0x7;
            }
            if (tree.specs != null) {
            	// FIXME - test declarations within specs
            	Symbol fakeOwner =
            			new MethodSymbol(Flags.PRIVATE | BLOCK, names.empty, null,
            					env.info.scope.owner);
            	final Env<AttrContext> localEnv =
            			env.dup(tree, env.info.dup(env.info.scope.dupUnshared(fakeOwner)));
            	if (tree.clauseType == staticinitializerClause) localEnv.info.staticLevel++;
            	attribStat(tree.specs,localEnv);
            }
        } finally {
            jmlresolve.setAllowJML(prevAllowJML);
            log.useSource(old);
        }
    }
    
    public boolean bad(JCExpression e) {
    	return e == null || e instanceof JCErroneous;
    }
    
    /** Attributes a represents clause */
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents tree) {
    	if (bad(tree.ident)|| bad(tree.expression)) return; 
        jmlenv = jmlenv.pushCopy();
        jmlenv.inPureEnvironment = true;
        jmlenv.currentClauseKind = tree.clauseType;
        JavaFileObject old = log.useSource(tree.source);
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        VarSymbol prevSecret = currentSecretContext;
        try {
            //attribExpr(tree.ident,env,Type.noType);
            // Do this by hand to avoid issues with secret
            jmlenv.jmlVisibility = tree.modifiers.flags & Flags.AccessFlags;
            Symbol sym = null;
            Type type = null;
            if (tree.ident instanceof JCIdent) {
                JCIdent id = (JCIdent)tree.ident;
                type = attribExpr(id, env, Type.noType);
                sym = id.sym;
            } else if (tree.ident instanceof JCArrayAccess aa) {
            	Type t = tree.ident.type = attribExpr(aa.indexed,env,Type.noType);
            	if (aa.index instanceof JmlRange range) {
                	if (range.hi != null || range.lo != null) {
                        utils.error(tree.ident, "jml.message", "Array ranges are not permitted in a represents clause");
                	}
                	if (!(t instanceof ArrayType)) {
                		// FIXME - I don't understand this message  or why it is here
                		utils.error(aa, "jml.message", "Represents target with wild-card index must be an array: " + tree.ident);
                		type = types.createErrorType(t);
                	} else {
                		type = ((ArrayType)t).elemtype;
                	}
            	} else {
            		utils.error(tree.ident, "jml.message", "Array elements are not permitted in a represents clause");
            	}
                return;
//            } else if (tree.ident instanceof JmlStoreRefArrayRange) {
//            	var aa = (JmlStoreRefArrayRange)tree.ident;
//            	if (aa.hi != null || aa.lo != null) {
//                    utils.error(tree.ident, "jml.message", "Array ranges are not permitted in a represents clause");
//            	}
//            	Type t = attribExpr(aa.expression,env,Type.noType);
//            	if (!(t instanceof ArrayType)) {
//            		utils.error(aa, "jml.message", "Represents target with wild-card index must be an array: " + tree.ident);
//            		type = types.createErrorType(t);
//            	} else {
//            		type = ((ArrayType)t).elemtype;
//            	}
//            	// FIXME - sym?
            } else if (tree.ident instanceof JCFieldAccess fa) {
            	type = attribExpr(fa,env,Type.noType);
                utils.error(tree.ident, "jml.message", "Field accesses are not permitted in a represents clause");
                return;
            } else {
                utils.error(tree.ident, "jml.message", "Unknown kind of represents target: " + tree.ident + " (" + tree.ident.getClass() + ")");
                return;
            }
            
            // FIXME check that sym and represents are both secret or both not
            attribAnnotationTypes(tree.modifiers.annotations,env);
            annotationsToModifiers(tree.modifiers);
            var a = utils.findModifier(tree.modifiers,Modifiers.SECRET);
            boolean representsIsSecret = a != null;
            // FIXME
//            if (a != null && a.args.size() != 0) {
//                utils.error(a,"jml.no.arg.for.secret.represents");
//            }
//            if (sym != null) {
//                boolean symIsSecret = sym.attribute(modToAnnotationSymbol.get(Modifiers.SECRET)) != null;
//                if (symIsSecret != representsIsSecret) {
//                    utils.error(tree,"jml.represents.does.not.match.id.secret");
//                }
//            }
            
            if (representsIsSecret && sym instanceof VarSymbol) currentSecretContext = (VarSymbol)sym;
            
            Env<AttrContext> localEnv = env; //envForClause(tree,sym);
            if ((tree.modifiers.flags & STATIC) != 0) localEnv.info.staticLevel++;
            
            Symbol s = tree.ident instanceof JCIdent ? ((JCIdent)tree.ident).sym : tree.ident instanceof JCFieldAccess ? ((JCFieldAccess)tree.ident).sym : null;
            // If an error happened in attributing the clause, then 's' may be a ClassSymbol
            if (s instanceof VarSymbol) jmlenv.representsHead = (VarSymbol)s;

            if (tree.suchThat) {
                attribExpr(tree.expression, localEnv, syms.booleanType);
            } else if (type == null) {
                // skip
            } else if (type.getKind() == TypeKind.ERROR) {
                // skip
            } else if (type.getKind() == TypeKind.NONE) {
                // ERROR - parser should not let us get here - FIXME
            } else {
            	//System.out.println("CHECKING REPRESENTS " +  jmlenv.representsHead + " " + tree);
                attribExpr(tree.expression, localEnv, type);
            }
            if ((tree.modifiers.flags & STATIC) != 0) localEnv.info.staticLevel--;

            checkTypeClauseMods(tree,tree.modifiers,"represents clause",tree.clauseType);
            if (sym != null && type != null && !type.isErroneous() && type.getTag() != TypeTag.ERROR) {
                if ( isStatic(sym.flags()) != isStatic(tree.modifiers)) {
                    // Note: we cannot use sym.isStatic() in the line above because it
                    // replies true when the flag is not set, if we are in an 
                    // interface and not a method.  Model fields do not obey that rule.
                    log.error(tree.pos,"jml.represents.bad.static");
                    // Presume that the model field is correct and proceed
                    if (isStatic(sym.flags())) tree.modifiers.flags |= Flags.STATIC;
                    else tree.modifiers.flags &=  ~Flags.STATIC;
                }
                specs.getLoadedSpecs((ClassSymbol)sym.owner);
                if (specs.statusOK((ClassSymbol)sym.owner)) { 
                	FieldSpecs fspecs = specs.getAttrSpecs((VarSymbol)sym);
                	if (fspecs == null || !isModel(fspecs.mods)) {
                		utils.error(tree.ident,"jml.represents.expected.model", sym.owner, sym);
                		if (fspecs != null && fspecs.decl != null) {
                			utils.note(fspecs.decl.sourcefile, fspecs.decl, "jml.associated.decl.cf", utils.locationString(tree.ident.pos));
                		}
                	}
                	if (env.enclClass.sym != sym.owner && isStatic(sym.flags())) {
                		utils.error(tree.ident,"jml.misplaced.static.represents", sym.owner, sym);
                		if (fspecs != null && fspecs.decl != null) {
                			utils.note(fspecs.decl.sourcefile, fspecs.decl, "jml.associated.decl.cf", utils.locationString(tree.ident.pos));
                		}
                	}
                }
            }
            
            // FIXME - need to check that ident refers to a model field
        } finally {
            jmlresolve.setAllowJML(prevAllowJML);
            jmlenv = jmlenv.pop();
            log.useSource(old);
            currentSecretContext = prevSecret;
            jmlenv.currentClauseKind = null;
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
        if ((tree.modifiers.flags & STATIC) != 0 ||
                ((env.enclClass.sym.flags() & INTERFACE) != 0 && env.enclMethod == null))
            localEnv.info.staticLevel++;
        return localEnv;
    }
    
    /** Attributes the monitors_for clause */
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor tree) {
        jmlenv = jmlenv.pushCopy();
        jmlenv.inPureEnvironment = true;
        JavaFileObject old = log.useSource(tree.source);
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        try {
            jmlenv.jmlVisibility = tree.modifiers.flags & Flags.AccessFlags;
            attribExpr(tree.identifier,env,Type.noType);

            Symbol sym = tree.identifier.sym;
            if (sym.owner != env.enclClass.sym) {
                log.error(tree.identifier.pos,"jml.ident.not.in.class",sym,sym.owner,env.enclClass.sym);
            } else {
                // FIXME - should this be done elsewhere?
                specs.getAttrSpecs((VarSymbol)sym).list.append(tree);
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
            jmlresolve.setAllowJML(prevAllowJML);
            jmlenv = jmlenv.pop();
            log.useSource(old);
        }
    }
    
    /** Attributes the readable-if and writable-if clauses */
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional tree) {
        JavaFileObject old = log.useSource(tree.source);
        jmlenv = jmlenv.pushCopy();
        jmlenv.inPureEnvironment = true;
        jmlenv.currentClauseKind = tree.clauseType;
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        try {
            attribExpr(tree.identifier,env,Type.noType);
            
            Symbol sym = tree.identifier.sym;
            jmlenv.jmlVisibility = sym.flags() & Flags.AccessFlags;
            long clauseVisibility = tree.modifiers.flags & Flags.AccessFlags;
            if (clauseVisibility != 0 && clauseVisibility != jmlenv.jmlVisibility) {
                log.error(tree.identifier.pos,"jml.visibility.is.different",Flags.toString(clauseVisibility), Flags.toString(jmlenv.jmlVisibility));
            }
            
//            if (sym.owner != env.enclClass.sym) {
//                log.error(tree.identifier.pos,"jml.ident.not.in.class",sym,sym.owner,env.enclClass.sym);
//            } else {
//                // FIXME _ should this be done elsewhere
//                VarSymbol vsym = (VarSymbol)sym;
//                JmlSpecs.FieldSpecs fs = specs.getSpecs(vsym);
//                //if (fs == null) specs.putSpecs(vsym,fs=new JmlSpecs.FieldSpecs(tree.sym.));
//                fs.list.append(tree);
//            	System.out.println("ADDING TO " + vsym + " " + tree + " " + tree.identifier + " " + tree.identifier.sym + " " + tree.identifier.type);
//            }
            
            boolean isStatic = sym.isStatic();
            if (isStatic) // ||(env.enclClass.sym.flags() & INTERFACE) != 0) // FIXME - what about interfaces
                env.info.staticLevel++;
            attribExpr(tree.expression, env, syms.booleanType);
            if (isStatic) // ||(env.enclClass.sym.flags() & INTERFACE) != 0) // FIXME - what about interfaces
                env.info.staticLevel--;
        } finally {
            jmlresolve.setAllowJML(prevAllowJML);
            jmlenv = jmlenv.pop();
            log.useSource(old);
        }
    }
    
    /** Attributes a method-clause group (the stuff within {| |} ) */
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {
        for (JmlSpecificationCase c: tree.cases) {
            c.accept(this);
        }
    }
    
    boolean specLocalEnv = false;
    
    /** Attributes old clauses within the specs of a method */
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl tree) {
        IJmlClauseKind t = tree.clauseKind;
        for (JCTree.JCVariableDecl decl: tree.decls) {
            if (decl instanceof JmlVariableDecl vdecl) {
            	JCModifiers mods = vdecl.mods;
                boolean statik = (env.enclMethod.mods.flags & Flags.STATIC) != 0; // method is static; so OK if var is static
                long flags = 0;
                if (statik) {
                    flags |= Flags.STATIC;  // old decls are implicitly static for a static method
                }
                long badFlags = utils.hasOnly(mods,flags);
                if (badFlags != 0) {
                    log.error(mods.pos,"jml.no.java.mods.allowed","old clause declaration", TreeInfo.flagNames(badFlags));
                    mods.flags &= ~badFlags; // Remove erroneous flags
                }
                jmlenv = jmlenv.pushCopy();
                jmlenv.currentClauseKind = oldClause;
                boolean prevLocalEnv = specLocalEnv;
                specLocalEnv = statik;
                var savedInJmlDeclaration = this.isInJmlDeclaration;
                this.isInJmlDeclaration = true;
                var savedDoJML = this.attribJmlDecls;
                try {
                	this.attribJmlDecls = true;
                    mods.flags &= ~flags; // Remove these flags or we will get additional complaints
                    decl.accept(this);
                    if (decl.sym == null) {
                        if (toRemove == null) toRemove = new ListBuffer<>();
                        toRemove.add(tree);
                    }
                } finally {
                    mods.flags |= flags; // Restore the flags
                    jmlenv = jmlenv.pop();
                	this.attribJmlDecls = savedDoJML;
                    this.isInJmlDeclaration = savedInJmlDeclaration;
                    //JmlCheck.instance(context).staticOldEnv = specLocalEnv;
                    specLocalEnv = prevLocalEnv;
                    if (env.enclMethod.sym.isStatic()) {
                        ((JmlVariableDecl)decl).mods.flags &= ~Flags.STATIC; // FIXME - is this necessary
                    }
                }
                JCTree.JCExpression init = ((JmlVariableDecl)decl).init;
                if (init == null) utils.error(((JmlVariableDecl)decl).pos,"jml.old.must.have.init");
            } else {
                utils.error(decl.pos(),"jml.internal.notsobad","Unexpected " + decl.getClass() + " object type in a JmlMethodClauseDecl list");
            }
        }
    }
    
    // FIXME - test the name lookup with old clauses
    
    public Env<AttrContext> savedMethodClauseOutputEnv = null;

    /** This is an implementation that does the type attribution for 
     * method specification clauses
     * @param tree the method specification clause being attributed
     */
    
    public void helperAttr(JmlAttr attr, IJmlClauseKind kind, JmlMethodClause tree, Env<AttrContext> env) {
        try {
            jmlenv = jmlenv.pushCopy();
            savedMethodClauseOutputEnv = this.env;
            jmlenv.currentClauseKind = tree.clauseKind;
            kind.typecheck(this, tree, env);
            savedMethodClauseOutputEnv = null;
            jmlenv.currentClauseKind = null;
        } catch (Exception e) {
            utils.error(tree.sourcefile, tree.pos(), "jml.internal", "typechecking failure in " + tree);
            e.printStackTrace();
        } finally {
            jmlenv = jmlenv.pop();
        }
    }
    
    public void visitJmlMethodClauseBehaviors(JmlMethodClauseBehaviors tree) {
        helperAttr(this, tree.clauseKind, tree, env);
    }
    public void visitJmlMethodClauseInvariants(JmlMethodClauseInvariants tree) {
        helperAttr(this, tree.clauseKind, tree, env);
    }
    
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) {
    	try {
    		jmlenv = jmlenv.pushCopy();
        savedMethodClauseOutputEnv = this.env;
        jmlenv.currentClauseKind = tree.clauseKind;
        var kw = tree.clauseKind.keyword();
        if (tree.exception != null) {
            if (kw.equals(requiresID) || kw.equals("recommends")) {
                // OK
            } else {
                utils.error(tree.exception, "jml.message", "only requires and recommends clauses may have 'else' suffixes");
            }
        } else if (kw.equals("recommends")) {
            utils.error(tree, "jml.message", "a recommends clause must have an 'else' suffix");
        }
        Type t = null;
        switch (kw) {
            case "recommends":
                t = tree.clauseKind.typecheck(this,tree,env);
                break;
            case divergesID:
                if (isPureMethod(jmlenv.enclosingMethodDecl.sym) && !treeutils.isFalseLit(tree.expression)) {
                    log.error(tree.pos, "jml.message", "pure methods must be terminating (explicitly diverges false)");
                }
                t = attribExpr(tree.expression, env, syms.booleanType);
                break;

            case requiresID:
                t = attribExpr(tree.expression, env, syms.booleanType);
                if (tree.exception != null) {
                    var exc = attribType(tree.exception, env, Type.noType);
                    // FIXME - exc must be an Exception type
                }
                break;
            case ensuresID:
            case "when":
            case "returns":
                t = attribExpr(tree.expression, env, syms.booleanType);
                break;
                
            case "continues":
            case "breaks":
                // FIXME - what about the label
                t = attribExpr(tree.expression, env, syms.booleanType);
                break;
            case "callable":
                // FIXME - should be implemented somewhere else
                break;
                
            default:
                log.error(tree.pos,"jml.unknown.construct",tree.keyword,"JmlAttr.visitJmlMethodClauseExpr");
                break;
        }
        savedMethodClauseOutputEnv = null;
        jmlenv.currentClauseKind = null;
//        if (t == null || t.isErroneous()) {
//        	System.out.println("BADCLAUSE " + tree + " " + t + " " + tree.expression.type + " " + (t==null?"?":t.getClass()));
//        	if (tree.expression instanceof JCBinary) {
//        		var b = (JCBinary)tree.expression;
//        		System.out.println("  LHS " + b.lhs.type + "   RHS " + b.rhs.type);
//        	}
//        }
    	} catch (Exception e) {
    		System.out.println("EXCEPTION visitJmlMethodClauseExpr");
    		e.printStackTrace();
    	} finally {
    		jmlenv = jmlenv.pop();
    	}
    }
    
    public static class SpecificationException extends RuntimeException {
        private static final long serialVersionUID = 1L;
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
        switch (tree.clauseKind.keyword()) {
            case durationID:
            case workingspaceID:
                attribExpr(tree.expression, env, syms.longType);
                break;
                
            case measuredbyID:
                attribExpr(tree.expression, env, syms.intType);
                break;
                
            default:
                log.error(tree.pos,"jml.unknown.construct",tree.keyword,"JmlAttr.visitJmlMethodClauseConditional");
                break;
        }
    }
    

    /** This is an implementation that does the type attribution for 
     * a signals method specification clause
     * @param tree the method specification clause being attributed
     */
    @Override
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals tree) {
        Env<AttrContext> localEnv = localEnv(env,tree);
        jmlenv = jmlenv.pushCopy();
        
        if (tree.vardef == null) {
            jmlenv.currentExceptionType = syms.exceptionType;
            
        } else {
        
            if (tree.vardef.name == null) {
                tree.vardef.name = names.fromString(Strings.syntheticExceptionID);
            }


            // FIXME - is this assignment needed? Why not elsewhere?
            tree.vardef.vartype.type = attribTree(tree.vardef.vartype, localEnv, new ResultInfo(KindSelector.TYP, syms.exceptionType));
            attribTree(tree.vardef, localEnv, new ResultInfo(KindSelector.VAR, syms.exceptionType));

            jmlenv.currentExceptionType = tree.vardef.vartype.type;
        }
        try {
            attribExpr(tree.expression, localEnv, syms.booleanType);
        } finally {
            jmlenv= jmlenv.pop();
        }
    }
    
    /** This is an implementation that does the type attribution for 
     * a signals_only method specification clause
     * @param tree the method specification clause being attributed
     */
    @Override
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly tree) {
        for (JCExpression e: tree.list) {
            if (e instanceof JCAnnotatedType at) {
                utils.warning(tree.sourcefile, e, "jml.message", "Annotations on signals_only exception types are meaningless and are ignored");
            }
            e.type = attribTree(e, env, new ResultInfo(KindSelector.TYP, syms.throwableType));
        }
        // FIXME - need to compare these to the exceptions in the method declaration
    }
    
    protected boolean isLocalOrParameter(JCTree e) {
        return (e instanceof JCIdent && ((JCIdent)e).sym.owner instanceof MethodSymbol);
    }
    
    protected boolean isLocalNotParameter(Symbol sym) {
        return sym instanceof Symbol.VarSymbol && sym.owner instanceof MethodSymbol
                        && (sym.flags() & Flags.PARAMETER) == 0;
    }
    
    protected boolean isParameter(Symbol sym) {
        return sym instanceof Symbol.VarSymbol && sym.owner instanceof MethodSymbol
                        && (sym.flags() & Flags.PARAMETER) != 0;
    }
    
    protected void checkIfParameter(JCIdent e) {
        if (isParameter(e.sym)) {
            utils.error(e,"jml.no.formals.in.assignable",e.toString());
        }
    }
    
    /** This is an implementation that does the type attribution for 
     * assignable/accessible/captures method specification clauses
     * @param tree the method specification clause being attributed
     */
    @Override
    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef tree) {
        jmlenv = jmlenv.pushCopy();
        jmlenv.currentClauseKind = tree.clauseKind;
        for (JCTree e: tree.list) {
            attribExpr(e, env, Type.noType);
            if (!isRefining && e instanceof JCIdent) checkIfParameter((JCIdent)e);
            if (jmlenv.currentClauseKind == assignableClauseKind) {
                if (e instanceof JCFieldAccess) {
                    if (isImmutable(((JCFieldAccess)e).selected.type.tsym)) {
                        log.error(tree.pos, "jml.message", "Fields of an object with immutable type may not be modified");
                    }
                }
            }
        }
//        var sr = treeutils.convertAssignableToLocsetExpression(tree,tree.list);
//        System.out.println("SRLIST " + sr);
        jmlenv = jmlenv.pop();
        // FIXME - check the result
    }

    // FIXME - need JmlAttr implementation for CALLABLE clauses
    
    @Override
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        for (JCTree t: that.list) {
            attribExpr(t,env,Type.noType);
        }
        if (!postClauses.contains(jmlenv.currentClauseKind)) {
            log.error(that.pos+1, "jml.misplaced.token", that.token.internedName(), jmlenv.currentClauseKind == null ? "jml declaration" : jmlenv.currentClauseKind.keyword());
        }
        result = check(that, syms.booleanType, KindSelector.VAL, resultInfo);
    }
    
    @Override
    public void visitJmlStoreRef(JmlStoreRef that) {
        //System.out.println("VISITING JML STORE REF " + that.originalStoreRef);
        JCExpression e = that.originalStoreRef;
        try {
            if (e instanceof JCIdent id) {
                attribExpr(id, env, Type.noType);
                var sym = id.sym;
                if (sym == null) {
                    // ERROR
                    System.out.println("NO SYM " + id);
                } else if (sym.owner instanceof Symbol.MethodSymbol) {
                    // local
                    that.local = sym;
                    //System.out.println("LOCAL " + sym.owner + " " + sym);
                } else if (sym.isStatic()) {
                    that.field = (VarSymbol)sym;
                    //System.out.println("STATIC FIELD " + sym.owner + " " + sym);
                } else {
                    System.out.println("THIS FIELD " + sym.owner + " " + sym);
                    var idthis = jmlMaker.Ident(names._this);
                    visitIdent(idthis);
                    that.receiver = idthis;
                    that.field = (VarSymbol)sym;
                }
            } else if (e instanceof JCArrayAccess aa) {
                // An array store-ref, perhaps with a range
                attribExpr(aa.indexed, env, Type.noType);
                // FIXME - check that it is an array; attribute range
                JmlRange r;
                if (aa.index == null) {
                    r = jmlMaker.at(aa.index).JmlRange(
                        treeutils.makeZeroEquivalentLit(aa, JmlPrimitiveTypes.bigintTypeKind.getType(context)),
                        treeutils.makeLengthM1(e.pos(), aa.indexed));
                } else if (!(aa.index instanceof JmlRange rr)) {
                    r = jmlMaker.at(aa.index).JmlRange(aa.index, aa.index);
                } else {
                    r = jmlMaker.at(aa.index)
                                            .JmlRange(
                                                rr.lo != null ? rr.lo
                                                    : treeutils.makeZeroEquivalentLit(rr,
                                                            JmlPrimitiveTypes.bigintTypeKind.getType(context)),
                                                    rr.hi != null ? rr.hi : treeutils.makeLengthM1(e.pos(), aa.indexed));
                }
                that.receiver = aa.indexed;
                that.range = r;
            } else if (e instanceof JCFieldAccess fa) {
                if (fa.name != null) {
                    attribExpr(fa, env, Type.noType);
                    that.field = (VarSymbol)fa.sym;
                    if (!that.field.isStatic()) that.receiver = fa.selected;
                    //System.out.println("JSR ATTR " + that + " " + e + " " + fa.selected.type + " " + fa.type);
                } else {
                    attribExpr(fa.selected, env, Type.noType);
                    that.receiver = fa.selected; // FIXME - check whether a type
                }
            } else if (e instanceof JmlSingleton s) {
                // \nothing or \everything
                if (s.kind == JmlPrimitiveTypes.everythingKind) {
                    that.isEverything = true;
                } else if (s.kind == JmlPrimitiveTypes.nothingKind) {
                    // set nothing
                } else {
                    // error should be already given
                    if (utils.jmlverbose == Utils.JMLVERBOSE) log.error(s.pos, "jml.message", "Not a store-ref expression: " + e);
                }
                //        } else if (e instanceof JmlMethodInvocation mi && mi.kind == LocsetExtensions.unionKind) {
                //            // A call of union -- we flatten the call
                //            mi.args.stream().forEach(arg -> list.addAll(makeJmlStoreRef(pos, arg, baseClassSym, expand)));
            } else {
                // ERROR
                // A locset expression
                that.expression = e;
                attribExpr(that.expression, env, Type.noType);
                // FIXME - should check that the result is locset
            }
            result = that.type = JmlPrimitiveTypes.locsetTypeKind.getType(context);
        } catch (Exception ee) {
            ee.printStackTrace(System.out);
        }
        //System.out.println("END VISITING JML STORE REF " + that.type + " " + that);
    }



    /** The JML modifiers allowed for a specification case */
    ModifierKind[] specCaseAllowed = new ModifierKind[]{};
    
    ListBuffer<JmlMethodClause> toRemove = null;
    
    /** This implements the visiting of a JmlSpecificationCase, initiating
     * a visit of each clause in the case, setting the currentClauseType field
     * before visiting each one.
     */
    
    public void visitJmlSpecificationCase(JmlSpecificationCase tree) {
    	//if (org.jmlspecs.openjml.Main.useJML) System.out.println("SPECCASE " + tree);
        JavaFileObject old = log.useSource(tree.sourcefile);
        Env<AttrContext> localEnv = null;
        Env<AttrContext> prevEnv = env;
        jmlenv = jmlenv.pushCopy(); // Just in case there is recursion
        try {
            if (tree.modifiers != null) {
                attribAnnotationTypes(tree.modifiers.annotations,env);
                // Specification cases may not have Java annotations. The only
                // modifiers are visibility modifiers. If Java annotations are allowed
                // in the future, note that the following code does not attribute 
                // any arguments of the annotations.
                // Another semantics could be to connect the Java annotations to the 
                // owning method. This would then allow the sequence
                // <Java annotations> <specification case> <method declaration>
                // Currently one must reorder the above to
                // <specification case> <Java annotations> <method declaration>
                ListBuffer<JCAnnotation> newlist = new ListBuffer<>();
                for (List<JCAnnotation> al = tree.modifiers.annotations; al.nonEmpty(); al = al.tail) {
                    JCAnnotation a = al.head;
                    if (!a.annotationType.toString().startsWith(Strings.jmlAnnotationPackage)) {
                        utils.error(a,"jml.message", "A specification case may not have annotations");
                        // FIXME - perhaps move these to the owning method
                    } else {
                        // We keep the JML annotations because these are checked separately
                        newlist.add(a);
                    }
                }
                tree.modifiers.annotations = newlist.toList();
                if (tree.token == null) {
                    if (!utils.hasNone(tree.modifiers) && env.enclMethod != null && tree.modifiers != env.enclMethod.mods) {
                        utils.error(tree,"jml.no.mods.lightweight");
                    }
                    if (env.enclMethod != null) tree.modifiers = env.enclMethod.mods;
                } else {
                    long diffs = utils.hasOnly(tree.modifiers,Flags.AccessFlags);
                    if (diffs != 0) utils.error(tree,"jml.bad.mods.spec.case",Flags.toString(diffs));
                    Check.instance(context).checkDisjoint(tree.pos(),tree.modifiers.flags,Flags.PUBLIC,Flags.PROTECTED|Flags.PRIVATE);
                    Check.instance(context).checkDisjoint(tree.pos(),tree.modifiers.flags,Flags.PROTECTED,Flags.PRIVATE);

                    // "code" is parsed specifically and is not considered a modifier
                    allAllowed(tree.modifiers,specCaseAllowed,"specification case");
                }
            }
            if (tree.code && tree.token == null) {
                // Lightweight specs may not be labeled "code"
            	utils.error(tree,"jml.no.code.lightweight");
            }
            // Making this sort of local environment restricts the scope of new
            // declarations but does not allow a declaration to hide earlier
            // declarations.  Thus old declarations may rename
            // class fields, but may not rename method parameters or earlier old
            // declarations.
            if (env.tree instanceof JmlStatementSpec) {
            	// specification for a statement spec (e.g. in a method body)
            	//System.out.println("SPECCASE-S " + (enclosingMethodEnv!=null));
            	localEnv = env;
            } else if (jmlenv.enclosingMethodDecl == null) {
                // contract for an initialization block
               localEnv = env; // env already set in visitBlock
            } else if (enclosingMethodEnv != null) {
            	// typical method specification
            	//System.out.println("SPECCASE-A");
            	localEnv = localEnv(env,enclosingMethodEnv.tree);
            } else { // For initializer declarations with specs
            	//System.out.println("SPECCASE-B");
                localEnv = localEnv(env,enclosingClassEnv.tree);
            }
            env = localEnv;

            if (tree.token == null) {
                if (env.enclMethod != null)
                    jmlenv.jmlVisibility = env.enclMethod.mods.flags & Flags.AccessFlags;
                else 
                    jmlenv.jmlVisibility = env.enclClass.mods.flags & Flags.AccessFlags; // FIXME - should this be the visibilty of the initializer block?
            } else {
                jmlenv.jmlVisibility = tree.modifiers == null ? 0 : (tree.modifiers.flags & Flags.AccessFlags);
            }
            
            if (tree.clauses != null) {
                toRemove = null;
                for (JmlMethodClause c: tree.clauses) {
                    jmlenv.currentClauseKind = c.clauseKind;
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
                jmlenv = jmlenv.pushCopy();
                jmlenv.inPureEnvironment = false;  //System.out.println("PUREENV SET FALSE"); Utils.dumpStack();
                jmlenv.currentClauseKind = modelprogramClause;
                var savedEnv = this.env;
                try {
                	this.env = JmlMemberEnter.instance(context).methodEnv(this.env.enclMethod, this.env);
                    tree.block.accept(this);
                } finally {
                	this.env = savedEnv;
                    jmlenv = jmlenv.pop();
                }
            } 
//            if (isPureMethod(jmlenv.enclosingMethodDecl.sym)) {
//                if (tree.token != exceptionalBehaviorClause && !isEffectivelyNormal(tree)) {
//                    utils.warning(tree,  "jml.message", "this specification case of a pure method is not effectively normal and will be ignored when the method is used in a specification");
//                }
//            }
        } finally {
        	// FIXME - why might env be null?
            if (env != null) labelEnvs.put(tree.name,env.dup(tree,env.info.dupUnshared()));
            if (prevEnv != localEnv) localEnv.info.scope.leave();
            env = prevEnv;
            jmlenv = jmlenv.pop();
            log.useSource(old);
        }
    }
    
    /** Visits a JmlMethodSpecs by visiting each of its JmlSpecificationCases */
    
    public void visitJmlMethodSpecs(JmlMethodSpecs tree) {
        jmlenv = jmlenv.pushCopy();
        jmlenv.inPureEnvironment = true;
        try {
        	for (JmlSpecificationCase c: tree.cases) {
        		try {
//        		    long viz = c.modifiers.flags & Flags.AccessFlags;
//        		    if (c.token == null) viz = jmlenv.enclosingMethodDecl == null ? Flags.PRIVATE : jmlenv.enclosingMethodDecl.mods.flags & Flags.AccessFlags;
//        		    jmlenv.jmlVisibility = viz;
        		    
        			// This check is put here rather than inside visitJmlSpecificationCase
        			// so it is not checked for specification cases that are part of a 
        			// refining statement
        			if (c.modifiers != null && tree.decl != null) { // tree.decl is null for initializers and refining statements
        				JCMethodDecl mdecl = tree.decl; // OR env.enclMethod
        				long methodMod = jmlAccess(mdecl.mods);
        				long caseMod = c.modifiers.flags & Flags.AccessFlags;
        				if (methodMod == 0 && env.enclClass.sym.isInterface()) methodMod = Flags.PUBLIC;
        				if (methodMod != caseMod && c.token != null) {
        					if (caseMod == Flags.PUBLIC ||
        							methodMod == Flags.PRIVATE ||
        							(caseMod == Flags.PROTECTED && methodMod == 0)) {
        						DiagnosticPosition p = c.modifiers.pos();
        						if (p.getPreferredPosition() == Position.NOPOS) p = tree.pos();
        						if (!env.enclMethod.name.toString().equals("clone")) {
        							JavaFileObject prevsource = log.useSource(c.source());
        							utils.warning(p,"jml.no.point.to.more.visibility", 
        									Flags.toString(caseMod) + " vs. " + Flags.toString(methodMod) + " FOR " + mdecl.sym.owner + "." + mdecl.sym);
        							log.useSource(prevsource);
        						}
        					}
        				}
        			}

        			c.accept(this);
        		} catch (JmlInternalAbort|PropagatedException e) {
        			throw e;
        		} catch (Exception e) {
        			System.out.println("EXCEPTION-JmlMethodSpecs " + e);
        			e.printStackTrace(System.out);
        		}
        	}
        	if (tree.feasible != null) for (JmlMethodClause cl: tree.feasible) {
        		cl.accept(this);
        	}
        } finally {
        	jmlenv = jmlenv.pop();
        }
    }
    
//    // These are the annotation types in which \pre and \old with a label can be used (e.g. assert)
//    public Set<IJmlClauseKind> preTokens = JmlTokenKind.methodStatementTokens;
//    
//    // These are the annotation, method and type spec clause types in which \old without a label can be used
//    public Set<IJmlClauseKind> oldNoLabelTokens = JmlTokenKind.methodStatementTokens;
//    {
//        Set<IJmlClauseKind> t = new HashSet<>();
//        t.addAll(oldNoLabelTokens);
//        t.addAll(Utils.asSet(ensuresClauseKind,signalsClauseKind,constraintClause,durationClause,workingspaceClause,declClause)); // FIXME - double check JMLDECL
//        oldNoLabelTokens = t;
//    }

    public void visitJmlTuple(JmlTuple tree) {
        ListBuffer<Type> types = new ListBuffer<>();
        for (JCExpression e: tree.values) {
            Type t = attribExpr(e, env, Type.noType);
            types.append(t);
        }
        Type t = new JmlListType(types.toList());
        tree.type = result = t;
    }
    
    // FIXME - limit these to a method body
    public Map<Name,Env<AttrContext>> labelEnvs = new HashMap<Name,Env<AttrContext>>();
    
    public void visitLabelled(JCLabeledStatement tree) {
        saveEnvForLabel(tree.label, env);
        super.visitLabelled(tree);
    }
    
    public void visitJmlMethodInvocation(JmlMethodInvocation tree) {
        if (tree.kind != null && tree.typeargs != null && tree.typeargs.size() != 0) {
            // At present the parser cannot produce anything with typeargs, but just in case
            // one squeaks through by some means or another
        	System.out.println("METH "+ tree.meth);
        	utils.error(tree.typeargs.head,"jml.no.typeargs.for.fcn",tree.meth);
        }
        //System.out.println("VISIT JMLAPPLY " + tree);
        
//        Env<AttrContext> localEnv = env.dup(tree, env.info.dup( env.info.scope.dup()));
//        // This local environment is for good measure.  It is normally needed as
//        // a scope to hold type arguments.  But there are not any of those for
//        // these JML methods, so it should not technically be needed.
        Env<AttrContext> localEnv = env;
        
//        if (!(tree.kind instanceof IJmlClauseKind.ExpressionKind)) {
//        	utils.error(tree,"jml.message","Expected a " + tree.kind + "to be a IJmlClauseKind.Expression");
//        	result = tree.type = syms.errType;
//        } else {
 //           if (tree.kind == null) System.out.println("JMLIN " + tree.getClass() + " " + tree.meth + " " + tree.args);
        	Type ttt;
        	if (tree.kind != null) {
        		ttt = tree.kind.typecheck(this, tree, localEnv);
            	result = check(tree, ttt, KindSelector.VAL, resultInfo);
        	} else {
        		super.visitApply(tree);
        		result = tree.type;
        	}
//        }
    }
    
    public void saveEnvForLabel(Name label, Env<AttrContext> env) {
        labelEnvs.put(label,env.dup(env.enclMethod,env.info.dupUnshared()));
    }
    
    public Env<AttrContext> envForLabel(DiagnosticPosition pos, Name label, Env<AttrContext> oldenv) {
        if (enclosingMethodEnv == null) {
            // Just a precaution
            utils.warning(pos,"jml.internal","Unsupported context for pre-state reference (anonymous class? initializer block?): " + label + ".  Please report the program.");
        } else if (label != null) {
            Env<AttrContext> labelenv = labelEnvs.get(label);
            if (labelenv == null) {
                utils.error(pos,"jml.unknown.label",label);
            } else {
                oldenv = labelenv;
            }
        }
        return oldenv;
    }
    
    public void checkForWildcards(JCExpression e, JCExpression arg) { // OPENJML _ changed from protected to public
        if (e instanceof JCWildcard) {
            utils.error(e,"jml.no.wildcards.in.type",JmlPretty.write(arg));
        }
        if (!(e instanceof JCTypeApply)) return;
        JCTypeApply t = (JCTypeApply)e;
        for (JCExpression ee: t.arguments) {
            checkForWildcards(ee,arg);
        }
    }
    
    Symbol identOrSelectSym(JCExpression e) {
    	if (e instanceof JCIdent) return ((JCIdent)e).sym;
    	return ((JCFieldAccess)e).sym;
    }
    
    boolean alreadyReported = false;
    /** This is overridden to check that if we are in a pure environment,
     * the method is declared pure.  Also to make sure any specs are attributed.
     */
    @Override
    public void visitApply(JCTree.JCMethodInvocation tree) {
    	//if (org.jmlspecs.openjml.Main.useJML) System.out.println("VISITAPPLY " + tree);
        int nerrors = log.nerrors;
    	try {
    		super.visitApply(tree);
//    		if (tree.toString().contains("prepend")) {
//    		    System.out.println("JML_VISITAPPLY " + tree + " " + tree.type + " " + TreeInfo.symbolFor(tree.meth));
//    		    if (TreeInfo.symbolFor(tree.meth) != null) System.out.println("   TYPE " + ((MethodSymbol)TreeInfo.symbolFor(tree.meth)).getReturnType() + " " + TreeInfo.symbolFor(tree.meth).type + " " + TreeInfo.symbolFor(tree.meth).type.getReturnType());
//    		}
    	} catch (Exception e) {
    		e.printStackTrace(System.out);
            System.out.println("VISIT APPLY EXCEPTION " + tree.type );
            System.out.println("VISIT APPLY EXCEPTION " + tree);
            if (result == null) System.out.println("RESULT NULL");
            if (result.isErroneous()) System.out.println("RESULT ERRONEOUS");
    	}
        if (currentMethodPurity != null && currentMethodPurity.jmlclausekind == Modifiers.STRICTLY_PURE) {
            MethodSymbol msym = (MethodSymbol)(tree.meth instanceof JCFieldAccess f? f.sym : ((JCIdent)tree.meth).sym);
            var cp = specs.determinePurity(msym);
            if (cp == null || cp.jmlclausekind != Modifiers.STRICTLY_PURE) {
                utils.errorAndAssociatedDeclaration(log.currentSourceFile(), tree, currentMethodPurity.source, currentMethodPurity.pos(),
                    "jml.message", "strictly_pure methods may only call strictly_pure methods");
            }
        }
        if (result.isErroneous() && nerrors == log.nerrors) {
            // Some resolution errors are discovered during speculative attribution and not reported then.
            // FIXME: But sometimes not ever reported (cf. linkedBugs test), though that seems either a bug in OpenJDK or
            // a bug in OpenJML's overriding of OpenJDK. In the known case it is a failure to find the identifier that is the receiver of this method call.
            // The class has type parameters but the method does not.
            // So we report an error if no errors were reported in the super.visitApply call.
            // FIXME - also should figure out how to report the original error message and location
//            utils.error(tree,  "jml.message", "Failed to find a type for " + tree + " " + tree.type + " " + result );
//            String msg = tree.meth instanceof JCFieldAccess fa ? ("    Receiver = " + fa.type ) : "    ";
//            for (var a: tree.args) { msg += (" ARG: " + a + " " + a.type); }
//            utils.error(tree, "jml.message", msg);
//            System.out.println("VISITAPPY-ERROR " + tree);
            return;
        }
        if (result.isErroneous()) return;
        Type savedResult = result;
        
        // Make sure that we have attributed specs for the method
        Symbol sym = identOrSelectSym(tree.meth);  // FIXME - use TreeInfo.symbol
        if (sym == null || !(sym instanceof MethodSymbol)) return; // An error happened
        MethodSymbol msym = (MethodSymbol)sym;
        var mspecs = specs.getLoadedOrDefaultSpecs(msym, tree.pos);
        if (jmlenv.inPureEnvironment && tree.meth.type != null && tree.meth.type.getTag() != TypeTag.ERROR) {
            // Check that the method being called is pure
            if (msym != null) {
                boolean isAllowed = specs.isSpecOKMethod(msym);
                isAllowed |= msym.owner.toString().startsWith("java."); // FIXME - edit libraries o avoid this
                if (!isAllowed) {
                    nonPureWarning(tree, msym);
                }
                if (isAllowed && jmlenv.currentClauseKind == invariantClause
                        && msym.owner == enclosingClassEnv.enclClass.sym
                        && !isHelper(msym)
                        && utils.rac) {
                    utils.warning(tree,"jml.possibly.recursive.invariant",msym);
                }
            } else {
                // We are expecting that the expression that is the method
                // receiver (tree.meth) is either a JCIdent or a JCFieldAccess
                // If it is something else we end up here.
                if (sym == null) log.error("jml.internal.notsobad","Unexpected parse tree node for a method call in JmlAttr.visitApply: " + tree.meth.getClass());
                else log.error("jml.internal.notsobad","Unexpected symbol type for method expression in JmlAttr.visitApply: ", sym.getClass());
            }
            // FIXME - could be a super or this call
        }
        if (jmlenv.currentClauseKind == representsClause) {
            if (!isHelper(msym)) {
                utils.error(tree,"jml.helper.required.in.represents",msym.owner + "." + msym);
            }
        }
// FIXME        if (msym != null) checkSecretCallable(tree,msym);
        result = savedResult;
    }

    /** This handles JML statements such as assert and assume and unreachable. */
    public void visitJmlStatementExpr(JmlTree.JmlStatementExpr tree) {
    	result = tree.clauseType.typecheck(this,tree,env);
    }
    
    public void visitLetExpr(LetExpr tree) { 
    	if (tree instanceof JmlLetExpr && ((JmlLetExpr)tree).explicit) {
        	jmlenv.pushCopy();
        	jmlenv.inExpressionScope = true;
        	Env<AttrContext> localEnv;
        	if (env.info.scope.owner.kind == TYP) {
                // This branch is for let expressions in class-level clauses (e.g. invariant)
                Symbol fakeOwner =
                    new MethodSymbol(BLOCK, names.empty, null, // FIXME - or'd other flags with BLOCK
                                     env.info.scope.owner);
                localEnv =
                        env.dup(tree, env.info.dup(env.info.scope.dupUnshared(fakeOwner)));
            } else {
                // Create a new local environment with a local scope.
                localEnv =
                    env.dup(tree, env.info.dup(env.info.scope.dup()));
            }
            boolean saved = this.attribJmlDecls; // TODO - check where this is used
            this.attribJmlDecls = true;
            attribStats(tree.defs,localEnv);
            attribExpr(tree.expr,localEnv,Type.noType);
            this.attribJmlDecls = saved;
            Type resultType = tree.expr.type;
            if (resultType.constValue() != null) resultType = resultType.constType(null);
            result = check(tree, resultType, KindSelector.VAL, resultInfo);

            localEnv.info.scope.leave();
            jmlenv.pop();
    	} else {
    		super.visitLetExpr(tree);
    	}
    }


    /** This handles JML statements such as assert and assume and unreachable and hence_by. */
    public void visitJmlStatementHavoc(JmlTree.JmlStatementHavoc tree) {
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        jmlenv = jmlenv.pushCopy();
        jmlenv.inPureEnvironment = true;
        try {
            if (tree.storerefs != null) {
                for (JCTree e: tree.storerefs) {
                    attribExpr(e, env, Type.noType);
                }
            }
        } finally {
            jmlenv = jmlenv.pop();
            jmlresolve.setAllowJML(prevAllowJML);
        }
        result = null; // Statements do not return types
    }

    boolean savedSpecOK = false; // FIXME - never read
    
    public void attribLoopSpecs(List<JmlTree.JmlStatementLoop> loopSpecs, Env<AttrContext> loopEnv) {
        savedSpecOK = false;
        if (loopSpecs == null || loopSpecs.isEmpty()) return;
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        jmlenv = jmlenv.pushCopy();
        jmlenv.inPureEnvironment = true;
        try {
        	for (JmlTree.JmlStatementLoop tree: loopSpecs) {
        		jmlenv.currentClauseKind = tree.clauseType;
        		if (tree.clauseType == loopinvariantClause) {
        			attribExpr(((JmlStatementLoopExpr)tree).expression,loopEnv,syms.booleanType);
        		} else if (tree.clauseType == loopdecreasesClause){
        			Type t = attribExpr(((JmlStatementLoopExpr)tree).expression,loopEnv);
        			if (!jmltypes.isAnyIntegral(t) && !t.isErroneous()) {
        				log.error(((JmlStatementLoopExpr)tree).expression.getStartPosition(),"jml.message", "Expected an integral type in loop_decreases, not " + t.toString());
        			}
        		} else if (tree.clauseType == loopwritesStatement) {
        			for (JCExpression stref: ((JmlStatementLoopModifies)tree).storerefs) {
        				attribExpr(stref,loopEnv,Type.noType);
        			}
        		} else {
        			// FIXME - ERROR - Unknown token type
        		}
        	}
        } finally {
        	jmlenv = jmlenv.pop();
        	jmlresolve.setAllowJML(prevAllowJML);
        }
    }
    
    boolean isRefining = false;
    
    /** This handles JML statements that give method-type specs for method body statements. */
    public void visitJmlStatementSpec(JmlTree.JmlStatementSpec tree) {
        tree.label = names.fromString("`SSL"+tree.pos); 
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        jmlenv = jmlenv.pushCopy();
        jmlenv.currentClauseKind = null;
        boolean saved = isRefining;
        isRefining = false; // FIXME - why false? put in jmlenv?
        saveEnvForLabel(tree.label, env);
        jmlenv.currentBlockContract = tree;
        jmlenv.currentOldLabel = tree.label;
        if (tree.statements != null) {
            jmlresolve.setAllowJML(prevAllowJML);
            attribStats(tree.statements,env);
            jmlresolve.setAllowJML(true);
        }
        try {
            for (JCIdent id: tree.exports) {
                attribExpr(id, env);
                if (!isLocalNotParameter(id.sym)) {
                    log.error("jml.message", "Identifiers here must be local: " + id.name);
                }
            }
            isRefining = true;
            if (tree.statementSpecs != null) {
                Env<AttrContext> localEnv = localEnv(env,tree);
            	attribStat(tree.statementSpecs,localEnv);
            }
        } finally {
            isRefining = saved;
        }
        jmlenv = jmlenv.pop();
        jmlresolve.setAllowJML(prevAllowJML);
    }
    
    /** This handles JML declarations (method and ghost fields, methods, types) */
    public void visitJmlStatementDecls(JmlTree.JmlStatementDecls tree) {
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        jmlenv = jmlenv.pushCopy();
        jmlenv.currentClauseKind = declClause;
        var saved = this.attribJmlDecls;
        this.attribJmlDecls = true;
        for (JCTree.JCStatement s : tree.list) {
            attribStat(s,env);
        }
        this.attribJmlDecls = saved;
        jmlenv = jmlenv.pop();
        jmlresolve.setAllowJML(prevAllowJML);
    }
    
    boolean isGhost(JCExpression lhs) {
    	if (lhs instanceof JCArrayAccess) return isGhost(((JCArrayAccess)lhs).indexed);
    	if (lhs instanceof JCIdent) {
    		return utils.isJML(((JCIdent)lhs).sym.flags());
    	}
    	if (lhs instanceof JCFieldAccess) {
    		var fa = (JCFieldAccess)lhs;
    		return utils.isJML(fa.sym.flags()) || isGhost(fa.selected);
    	}
    	if (lhs instanceof JmlTuple) {
    		for (var e: ((JmlTuple)lhs).values) {
    			if (!isGhost(e)) return false;
    		}
    		return true;
    	}
		utils.error(lhs, "jml.message", "Unexpected kind of LHS in a set statement: " + lhs);
		//utils.error(lhs, "jml.message", "Unexpected kind of LHS in a set statement: " + lhs + " (" + lhs.getClass() + ")");
		return false;
    }
    
    /** This handles JML statements such as set and debug */
    public void visitJmlStatement(JmlTree.JmlStatement tree) {  // FIXME - need to test appropriately for purity
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        jmlenv = jmlenv.pushCopy();
        jmlenv.currentClauseKind = tree.clauseType;
        if (tree.statement != null) {
        	attribStat(tree.statement,env);
        	if (tree.statement instanceof JCExpressionStatement) {
        		JCExpression expr = ((JCExpressionStatement)tree.statement).expr;
        		if (expr instanceof JCAssign) {
        			JCExpression lhs = ((JCAssign)expr).lhs;
        			if (!isGhost(lhs)) {
        				utils.error(lhs, "jml.message", "The LHS in a set statement must be a ghost variable");
        			}
        		} else if (expr instanceof JCAssignOp) {
        			JCExpression lhs = ((JCAssignOp)expr).lhs;
        			if (!isGhost(lhs)) {
        				utils.error(lhs, "jml.message", "The LHS in a set statement must be a ghost variable");
        			}
        		} else {
        			// TODO - if this is some other kind of stastement, it must have only ghost effects
        		}
        	}
        }
        jmlenv = jmlenv.pop();
        jmlresolve.setAllowJML(prevAllowJML);
    }

    /** This handles JML show statement */
    public void visitJmlStatementShow(JmlTree.JmlStatementShow tree) { 
        boolean prevAllowJML = jmlresolve.setAllowJML(true);
        jmlenv = jmlenv.pushCopy();
        jmlenv.currentClauseKind = tree.clauseType;
        if (tree.expressions != null) for (JCExpression e: tree.expressions) attribExpr(e,env);
        jmlenv.pop();
        jmlresolve.setAllowJML(prevAllowJML);
    }

    /** This handles JML primitive types */
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        if (that.jmlclausekind != null) {
            result = that.type = ((JmlTypeKind)that.jmlclausekind).getType(context);
            that.repType = that;
        } else {
//            JmlType type = //that.token == JmlTokenKind.BSTYPEUC ? jmltypes.TYPE :
//                that.token == JmlTokenKind.BSBIGINT ? jmltypes.BIGINT :
// //                   that.token == JmlTokenKind.BSREAL ? jmltypes.REAL :
//                        null;
//
//            if (type == null) {
                result = syms.errType;
                log.error(that.pos,"jml.unknown.type.token",that.token.internedName(),"JmlAttr.visitJmlPrimitiveTypeTree");
//                return;
//            }
//            that.type = type;
//            that.repType = jmltypes.repType(that.pos(), type);
//            attribType(that.repType,env);
//            result = type;
        }
//        if (utils.rac) {
//            result = type.repType.type;
//            that.type = result;
//        }
    }
    
    /** This set holds method clause types in which the \result token may appear 
     * (and \not_assigned \only_assigned \only_captured \only_accessible \not_modified) */
    public Collection<IJmlClauseKind> resultClauses = Utils.asSet(ensuresClauseKind,durationClause,workingspaceClause);
    
    /** This set holds method clause types in which the \exception token may appear  */
    public Collection<IJmlClauseKind> exceptionClauses = Collections.singleton(signalsClauseKind);
    
    /** This set holds method clause types in which the these tokens may appear:
     *  \not_assigned \only_assigned \only_captured \only_accessible \not_modified */
    public Collection<IJmlClauseKind> postClauses = Utils.asSet(ensuresClauseKind,signalsClauseKind,durationClause,workingspaceClause,assertClause,assumeClause,checkClause);
    public Collection<IJmlClauseKind> freshClauses = new LinkedList<>();
    { freshClauses.addAll(Utils.asSet(loopinvariantClause,assertClause,checkClause,assumeClause,showClause));  freshClauses.addAll(postClauses); }

    /** This handles expression constructs with no argument list such as \\result */
    public void visitJmlSingleton(JmlSingleton that) {
        Type t = that.kind.typecheck(this,that,env);
        result = check(that, t, KindSelector.VAL, resultInfo);
    }
    
    public void visitJmlRange(JmlRange that) {
        var BIGINT = JmlPrimitiveTypes.bigintTypeKind.getType(context);
    	if (that.lo != null) {
    		Type t = attribExpr(that.lo, env, Type.noType);
    		if (!t.isIntegral() && t != BIGINT) {
    			utils.error(that.lo, "jml.message", "Expected an integral type, not " + t);
    		}
    	}
    	if (that.hi != null) {
    		Type t = attribExpr(that.hi, env, Type.noType);
    		if (!t.isIntegral() && t != BIGINT) {
    			utils.error(that.hi, "jml.message", "Expected an integral type, not " + t);
    		}
    	}
    	result = that.type = JmlPrimitiveTypes.rangeTypeKind.getType(context);
    }
    
//    public void visitJmlFunction(JmlFunction that) {
//        // Actually, I don't think this gets called.  It would get called through
//        // visitApply.
//        result = that.type = Type.noType;
//    }
    
    public final String[] predefinedLabels = { "Pre", "Old", "Here"};
    
    public Name checkLabel(JCTree tr) {
        if (tr.getTag() != JCTree.Tag.IDENT) {
        	utils.error(tr,"jml.bad.label");
            return null;
        } else {
            Name label = ((JCTree.JCIdent)tr).getName();
            if (labelEnvs.get(label) == null) {
            	String s = label.toString();
            	boolean bs = !s.isEmpty() && s.charAt(0) == '\\';
            	final String sf = bs ? s.substring(1) : s;
            	if (!Arrays.stream(predefinedLabels).anyMatch(ss->ss.equals(sf))) {
            		utils.error(tr,  "jml.message", "Unknown label: " + label);
            		return null;
            	}
            	if (!bs) label = names.fromString("\\"+s);
            };
            return label;
        }

    }

    public void visitImport(JCImport that) {
        super.visitImport(that);
        // FIXME - ignoring model
    }
    
    public void visitJmlInlinedLoop(JmlInlinedLoop that) {
        loopStack.add(0,treeutils.makeIdent(that.pos, "loopIndex_" + (++loopIndexCount), syms.intType));
        Env<AttrContext> loopEnv =
                env.dup(env.tree, env.info.dup(env.info.scope.dup()));
        savedSpecOK = true;

        attribLoopSpecs(that.loopSpecs, loopEnv);
        // FIXME - should this be before or after the preceding statement

        loopEnv.info.scope.leave();
        loopStack.remove(0);
        result = null;
    }
    
    public Type attribTree(JCTree tree, Env<AttrContext> env, ResultInfo resultInfo) { 
    	//if (JmlMemberEnter.attrdebug) System.out.println("ATTR " + tree.getClass() + " " + tree);
    	var t = super.attribTree(tree, env, resultInfo);
    	if (t instanceof Type.ClassType ct && !t.isErroneous() && ct.tsym instanceof ClassSymbol cs) {
    	    // If we have just attributed a valid class type, enter a request for the specs for that class
    	    if (cs.kind == Kinds.Kind.TYP) JmlEnter.instance(context).requestSpecs(cs);
    	    else if (cs.kind != Kinds.Kind.ERR) utils.error("jml.internal","Unexpected kind of class symbol: " + cs + " " + cs.kind);
    	    // We don't have a position for the error message above -- tree is a good position but we aren't sure if the sourcefile is correct
    	}
    	return t;
    }
    
    
    @Override
    Type condType(List<DiagnosticPosition> positions, List<Type> condTypes) {
        var BIGINT = JmlPrimitiveTypes.bigintTypeKind.getType(context);
        var REAL = JmlPrimitiveTypes.realTypeKind.getType(context);
        if (condTypes.stream().anyMatch(t->t==REAL) && condTypes.stream().allMatch(t->jmltypes.isNumeric(t))) return REAL;
        if (condTypes.stream().anyMatch(t->t==BIGINT) && condTypes.stream().anyMatch(t->jmltypes.isNumeric(t)&&!jmltypes.isIntegral(t))) return REAL;
    	if (condTypes.stream().anyMatch(t->t==BIGINT) && condTypes.stream().allMatch(t->jmltypes.isIntegral(t))) return BIGINT;
    	return super.condType(positions, condTypes);
    }
    
    @Override
    public void visitConditional(JCConditional that) {
        super.visitConditional(that);
        // The following is primarily to handle cases like b ? 0 : bigint-expression
        // Note -- need to check both as expressions and declaration initializers
        result = that.type = condType(List.of(that.truepart, that.falsepart), List.of(that.truepart.type, that.falsepart.type));
//                ;        var BIGINT = JmlPrimitiveTypes.bigintTypeKind.getType(context);
//        var REAL = JmlPrimitiveTypes.realTypeKind.getType(context);
//        if (that.truepart.type == BIGINT && jmltypes.isAnyIntegral(that.falsepart.type)) {
//            result = that.type = BIGINT;
//        } else if (that.falsepart.type == BIGINT && jmltypes.isAnyIntegral(that.truepart.type)) {
//            result = that.type = BIGINT;
//        } else if (that.truepart.type == REAL && jmltypes.isNumeric(that.falsepart.type)) {
//            result = that.type = REAL;
//        } else if (that.falsepart.type == REAL && jmltypes.isNumeric(that.truepart.type)) {
//            result = that.type = REAL;
//        } else if (that.truepart.type == BIGINT && jmltypes.isNumeric(that.falsepart.type)) {
//            result = that.type = REAL;
//        } else if (that.falsepart.type == BIGINT && jmltypes.isNumeric(that.truepart.type)) {
//            result = that.type = REAL;
//        }
    }

    @Override
    public void visitBinary(JCBinary that) {
        super.visitBinary(that);
    }
    
    @Override 
    public Type jmlBinary(JCBinary that, OperatorSymbol operator, Type left, Type right) {
        Type rt = operator.getReturnType();
        if (utils.isExtensionValueType(rt) || utils.isExtensionValueType(left) ||  utils.isExtensionValueType(right)) {
            // Treating this specially avoids attempts at unboxing for some operators
            // FIXME - this skips any implicit conversions?
            // FIXME - what about inferred type parameters
            that.type = rt;
            return rt;
        }
        return null;
    }
    
    @Override
    public void visitJmlBinary(JmlBinary that) {  // FIXME - how do we handle unboxing, casting
        Type TYPE = JmlPrimitiveTypes.TYPETypeKind.getType(context);
        switch (that.op.keyword()) {
            case equivalenceID:
            case inequivalenceID:
            case impliesID:
            case reverseimpliesID:
                attribExpr(that.lhs,env,syms.booleanType);
                attribExpr(that.rhs,env,syms.booleanType);
                result = syms.booleanType;
                break;
                
            case lockltID:
            case lockleID:
                attribExpr(that.lhs,env,syms.objectType);
                attribExpr(that.rhs,env,syms.objectType);
                result = syms.booleanType;
                break;
                
            case wfltID:
            case wfleID:
                attribExpr(that.lhs,env,syms.objectType);
                attribExpr(that.rhs,env,syms.objectType);
                result = syms.booleanType;
                break;
                
            case subtypeofID:
            case subtypeofeqID: {
                // Note: the method of comparing types here ignores any type
                // arguments.  If we use isSameType, for example, then Class
                // and Class<Object> are different.  In this case, all we need 
                // to know is that the operands are some type of Class.
                // FIXME - what about subclasses of Class
                attribExpr(that.lhs,env,Type.noType);
                Type t = that.lhs.type;
                boolean errorAlready = false;
                if (t.isErroneous()) errorAlready = true;
                else if (t != TYPE
                        && !t.tsym.equals(syms.classType.tsym)) {
                    errorAlready = true;
                    utils.error(that.lhs.pos(),"jml.subtype.arguments",that.lhs.type);
                }
                attribExpr(that.rhs,env,Type.noType);
                Type tt = that.rhs.type;
                if (tt.isErroneous()) errorAlready = true;
                else if (tt != TYPE
                        && !tt.tsym.equals(syms.classType.tsym)) {
                    errorAlready = true;
                    utils.error(that.rhs.pos(),"jml.subtype.arguments",that.rhs.type);
                }
                if ((t == TYPE) != (tt == TYPE) && !errorAlready) {
                    utils.error(that.rhs.pos(),"jml.subtype.arguments.same",that.rhs.type);
                }
                if (t != TYPE) that.op = jsubtypeofKind; // Java subtyping
                
                result = syms.booleanType;
                break;
            }
                
            case jsubtypeofID:
            case jsubtypeofeqID: {
                attribExpr(that.lhs,env,Type.noType);
                Type t = that.lhs.type;
                boolean errorAlready = false;
                if (t.isErroneous()) errorAlready = true;
//                else if (!t.equals(jmltypes.TYPE)
//                        && !t.tsym.equals(syms.classType.tsym)) {
//                    errorAlready = true;
//                    utils.error(that.lhs.pos(),"jml.subtype.arguments",that.lhs.type);
//                }
                attribExpr(that.rhs,env,Type.noType);
                Type tt = that.rhs.type;
                if (tt.isErroneous()) errorAlready = true;
//                else if (!tt.equals(jmltypes.TYPE)
//                        && !tt.tsym.equals(syms.classType.tsym)) {
//                    errorAlready = true;
//                    utils.error(that.rhs.pos(),"jml.subtype.arguments",that.rhs.type);
//                }
//                if ((t == jmltypes.TYPE) != (tt == jmltypes.TYPE) && !errorAlready) {
//                    utils.error(that.rhs.pos(),"jml.subtype.arguments.same",that.rhs.type);
//                }
                // FIXME 
                
                result = syms.booleanType;
                break;
            }

            default:
                utils.error(that.pos(),"jml.unknown.operator",that.op.keyword(),"JmlAttr");
                break;
        }
        result = check(that, result, KindSelector.VAL, resultInfo);
    }
    
    public void visitJmlChained(JmlChained that) {
        // FIXME - doubly checks interior expressions
        for (JCTree.JCBinary b: that.conjuncts) {
            attribExpr(b, env, syms.booleanType);
        }
        result = that.type = syms.booleanType;
    }
    
//    /** 
//     */
//    public void visitJmlLabeledStatement(JmlLabeledStatement that) {
//        visitLabelled(that);
//    }
    
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
        Type t = that.kind == MiscExpressions.lblanyKind ? Type.noType : syms.booleanType;
        attribExpr(that.expression, env, t);
        Type resultType = that.expression.type;
        //if (resultType.constValue() != null) resultType = resultType.constType(resultType.constValue());
        result = check(that, resultType, KindSelector.VAL, resultInfo);
    }
    
//    public void visitNewClass(JCNewClass that) {
//        super.visitNewClass(that);
//    }

    public void visitJmlMatchExpression(JmlMatchExpression that) {
        Type seltype = attribExpr(that.expression, env, Type.noType);
        Type at = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.lang.IJmlDatatype")).type;
        if (!jmltypes.isAssignable(seltype,at)) {
            log.error(that.pos, "jml.message", "Match expression must be a datatype, not a " + seltype.toString());
            result = syms.errType;
            return;
        }
        Env<AttrContext> switchEnv =
                env.dup(that, env.info.dup(env.info.scope.dup()));
        Type topType = null;
        try {
            for (JmlMatchExpression.MatchCase c: that.cases) {
                Env<AttrContext> caseEnv =
                        switchEnv.dup(that, env.info.dup(switchEnv.info.scope.dup()));
                try {
                    attrMatchCase(c.caseExpression, seltype, caseEnv);
                    attribExpr(c.value, caseEnv, Type.noType);
                    Type nt = c.value.type;
                    if (topType == null) topType = nt;
                    else {
                        if (!jmltypes.isAssignable(nt, topType)) {
                            if (jmltypes.isAssignable(topType, nt)) topType = nt; 
                            else {
                                // calculate a least upper bound  // FIXME
                                topType = syms.objectType;
                            }
                        }
                    }
                } finally {
                    caseEnv.info.scope.leave();
                }
            }
        } finally {
            switchEnv.info.scope.leave();
        }
        result = check(that, topType, KindSelector.VAL, resultInfo);
    }
    
    public void attrMatchCase(JCExpression expr, Type datatype, Env<AttrContext> caseEnv) {
        if (expr instanceof JCMethodInvocation) {
            visitMatchConstructor((JCMethodInvocation)expr,datatype,caseEnv);
        } else {
            utils.error(expr, "jml.message", "Expected a constructor application here: " + expr.toString());
        }
    }
    
    public boolean visitMatchConstructor(JCMethodInvocation expr, Type datatype, Env<AttrContext> caseEnv) {
        Name underscore = names.fromString("_");
        JCExpression caller = expr.meth;
        if (!(caller instanceof JCIdent)) {
            utils.error(expr, "jml.message", "Expected a constructor application here: " + expr.toString());
            return false;
        }
        Name cn = ((JCIdent)caller).getName();
        MethodSymbol msym = null;
        x:{
            for (Symbol e: datatype.tsym.getEnclosedElements()) {
                if (e instanceof MethodSymbol) {
                    msym = (MethodSymbol)e;
                    Name n = e.getSimpleName();
                    if (n.equals(cn)) break x;
                }
            }
            utils.error(expr, "jml.message", "Method " + cn + " is not a constructor of datatype " + datatype.toString());
            return false;
        }
        expr.type = msym.getReturnType();
        ((JCIdent)caller).sym = msym;
        ((JCIdent)caller).type = msym.type;
        boolean ok = true;
        if (msym.params.size() != expr.args.size()) {
            utils.error(expr, "jml.message", "Constructor " + cn + " has incorrect number of arguments: " + expr.args.size() + " vs. " + msym.params.size() + " expected");
            ok = false;
        }
        Iterator<VarSymbol> formals = msym.params.iterator();
        Iterator<JCExpression> actuals = expr.args.iterator();
        while (formals.hasNext() && actuals.hasNext()) {
            VarSymbol formal = formals.next();
            JCExpression actual = actuals.next();
            if (actual instanceof JCIdent) {
                Name n = ((JCIdent)actual).getName();
                if (n.equals(underscore)) continue;
                // Add identifier to current environment
                JCVariableDecl vd = jmlMaker.VarDef(jmlMaker.Modifiers(0), n, jmlMaker.Type(formal.type), null);
                memberEnter.memberEnter(vd, caseEnv);
            } else if (actual instanceof JCMethodInvocation) {
                // FIXME - formal type should be datatype
                ok = visitMatchConstructor((JCMethodInvocation)actual, datatype, caseEnv) && ok;
            } else {
                utils.error(actual, "jml.message", "Expected an identifier or constructor call here");
                ok = false;
            }
        }
        return ok;
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
    public Env<AttrContext> envForExpr(JCTree tree,  Env<AttrContext> env) {
        Env<AttrContext> localEnv;
        // We can't use a delegated scope - they are used for variable initializers
        // and don;'t accept any new variable declarations.
        Scope.WriteableScope sco = env.info.scope;
// FIXME        while (sco instanceof Scope.DelegatedScope) sco = ((Scope.DelegatedScope)sco).next;

        long flags = 0L;
        if (sco.owner.kind != MTH) {
            // Block is a static or instance initializer;
            // let the owner of the environment be a freshly
            // created BLOCK-method.
            
            Symbol fakeOwner =
                new MethodSymbol(flags | BLOCK, names.empty, null, sco.owner);
            localEnv =
                    env.dup(tree, env.info.dup(sco.dupUnshared(fakeOwner)));
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
    
    public java.util.List<JmlQuantifiedExpr> quantifiedExprs = new LinkedList<JmlQuantifiedExpr>();
    
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        boolean saved = this.attribJmlDecls;
        quantifiedExprs.add(0,that);
        try {
        	this.attribJmlDecls = true;
        	result = that.kind.typecheck(this, that, env);
        } finally {
        	quantifiedExprs.remove(0);
            this.attribJmlDecls = saved;
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
            
            JmlTree.Maker F = jmlMaker;
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

            switch (q.kind.keyword()) {
            case qforallID:
            case qexistsID:
                break;
            case qchooseID:
                break;
            case qnumofID: 
            	restype = syms.longType; // FIXME - not working for bigint yet -- as this is RAC, we need to use BigInteger -- same for \sum etc.
                initialDecl = F.VarDef(F.Modifiers(0), names.fromString("_count$$$"), F.Type(restype), F.Literal(restype.getTag(),0).setType(restype));
                break;
            case qsumID:
                initialDecl = F.VarDef(F.Modifiers(0), names.fromString("_sum$$$"), F.Type(restype), F.Literal(restype.getTag(),0).setType(syms.intType));
                initialDecl.type = restype;
                break;
            case qproductID:
                initialDecl = F.VarDef(F.Modifiers(0), names.fromString("_prod$$$"), F.Type(restype), F.Literal(restype.getTag(),1).setType(syms.intType));
                initialDecl.type = restype;
                break;
            case qmaxID:
            case qminID:
                firstDecl = F.VarDef(F.Modifiers(0), names.fromString("_first$$$"), F.TypeIdent(TypeTag.BOOLEAN), F.Literal(TypeTag.BOOLEAN,1).setType(syms.booleanType));
                initialDecl = F.VarDef(F.Modifiers(0), names.fromString(q.kind == qminKind ? "_min$$$" : "_max$$$"), F.Type(restype), F.Literal(restype.getTag(),0).setType(restype));
                initialDecl.type = restype;
                valueDecl = F.VarDef(F.Modifiers(0), names.fromString("_val$$$"), F.Type(restype), null);
                break;
            default:
                utils.error(q, "jml.internal", "Encountered unsupported quantifier: " + q.kind.keyword());
                return;
            }
            if (initialDecl != null) {
            	// Just the needed pieces from memberEnter.memberEnter(initialDecl, env);
            	// FIXME - but isn't the whole expression attriubuted later?
                initialDecl.sym = new VarSymbol(0, initialDecl.name, restype, enter.enterScope(env).owner);
                initialDecl.sym.flags_field = 0; // FIXME - perhaps FINAL
                initialDecl.type = restype;
                initialDecl.vartype.type = restype;
            	bodyStats.add(initialDecl);
            }
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
            methodDecl.mods.annotations = methodDecl.mods.annotations.append(utils.modToAnnotationAST(Modifiers.PURE,0,0)); // FIXME- fix positions?
            // methodDecl is (RT is the result type): public RT value(Object[] args) { ... decls... }
            
            List<JCTree> defs = List.<JCTree>of(methodDecl);
            JmlClassDecl classDecl = (JmlClassDecl)F.AnonymousClassDef(F.Modifiers(0), defs) ;
            classDecl.specsDecl = classDecl;
            classDecl.toplevel = ((JmlClassDecl)enclosingClassEnv.enclClass).toplevel;
            //var e = enter.topLevelEnv(classDecl.toplevel);
            //e = enter.classEnv(classDecl, e); // This needs classDecl.sym set, via enter.classEnter?
            classDecl.typeSpecs = new JmlSpecs.TypeSpecs(classDecl, classDecl, null); // FIXME - putSpecs?

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
            
            q.racexpr = treeutils.makeZeroEquivalentLit(q, q.type);

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
            if (q.kind == qforallKind || q.kind == qexistsKind) { 
                if (q.kind == qforallKind) {
                    cond = treeutils.makeNot(cond.pos, cond);
//                    cond = F.Unary(JCTree.NOT, cond).setType(syms.booleanType); 
//                    ((JCUnary)cond).operator = rs.resolveUnaryOperator(cond.pos(), JCTree.NOT, env, newvalue.type);
                }
                update = F.If(cond, q.kind == qforallKind ? retfalse : rettrue , null);
                retStat = q.kind == qforallKind  ? rettrue : retfalse;
            } else if (q.kind == qnumofKind) {
                JCIdent id = F.Ident(initialDecl.name);
                id.setType(initialDecl.type);
                id.sym = initialDecl.sym;
                JCUnary op = (JCUnary)treeutils.makeUnary(id.pos, JCTree.Tag.PREINC, id);
                update = F.If(cond, F.Exec(op) , null);
                retStat = F.Return(id); // Is it OK to reuse the node?
            } else if (q.kind == qsumKind) {
                JCIdent id = F.Ident(initialDecl.name);
                id.setType(initialDecl.type);
                id.sym = initialDecl.sym;
                JCAssignOp asn = treeutils.makeAssignOp(Position.NOPOS, JCTree.Tag.PLUS_ASG, id, cond);
                update = F.Exec(asn);
                retStat = F.Return(id); // Is it OK to reuse the node?
            } else if (q.kind == qproductKind) {
                JCIdent id = F.Ident(initialDecl.name);
                id.pos = Position.NOPOS;
                id.setType(initialDecl.type);
                id.sym = initialDecl.sym;
                JCAssignOp asn = treeutils.makeAssignOp(Position.NOPOS, JCTree.Tag.MUL_ASG, id, cond);
                update = F.Exec(asn);
                retStat = F.Return(id);
            } else if (q.kind == qmaxKind || q.kind == qminKind) {
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
                                                    ( q.kind == qminKind ? JCTree.Tag.LT : JCTree.Tag.GT), 
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
                op2.operator = ((JmlResolve)rs).resolveBinaryOperator(op2.pos(),op2.getTag(), env, op2.lhs.type, op2.rhs.type);
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
                    bin.operator = ((JmlResolve)rs).resolveBinaryOperator(bin.pos(), bin.getTag(), env, id.type, hi.type);
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
       
        if (utils.hasOnly(mods,0)!=0) log.error(that.pos,"jml.no.java.mods.allowed","set comprehension expression", TreeInfo.flagNames(mods.flags));
        annotationsToModifiers((JmlModifiers)mods, mods.annotations);
        allAllowed(mods, typeModifiers, "set comprehension expression");

        result = check(that, that.newtype.type, KindSelector.VAL, resultInfo);
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
    
    public Type expectedType() {
    	return resultInfo == null ? Type.noType : pt();
    }

    
    @Override
    public void visitIdent(JCIdent tree) {
        boolean print = false; // tree.toString().contains("tring") && !tree.toString().contains("String");
        if (print) System.out.println("JML-VISITIDENT " + tree + " # " + tree.name + " # " + Utils.join(" ", quantifiedExprs) + " # " + tree.sym);
    	// Attributing an ident can instigate loading of new classes
    	// Every routine is responsible for saving and restoring state
    	// However we save and restore it here even though we don't change it here, defensively
        jmlenv = jmlenv.pushCopy();
//        var rep = jmlenv.representsHead;
//        jmlenv.representsHead = null; // To avoid datagroup containment checks if checkSecretReadable attribs in clauses

        try {
        	// First check quantified variables. If we are an old environment, they will not necessarily be in the
        	// environment scope.
        	for (var q: quantifiedExprs) {
        		for (var d: q.decls) {
        			if (tree.name == d.name) {
        				tree.sym = d.sym;
        				tree.type = d.type;
        				result = d.type;
        				return;
        			}
        		}
        	}
        	Name nm = tree.name;
            var ck = Extensions.findKeyword(tree.name);
            if (ck instanceof JmlTypeKind jtk) {
                // Get here when a type-name is used as the expression in a static dot-selection
                // FIXME - I think
        	    result = tree.type = jtk.getType(context);
        	    tree.sym = tree.type.tsym;
                if (print) System.out.println("JMLIDENT " + tree.name + " # " + ck + " # " + tree.type + " # " + tree.type.tsym + " # " + tree.sym);
                //                if (jtk.numTypeArguments() != 0) {
//                    utils.error(tree,  "jml.message", "The generic JML type " + tree.name + " must have " + jtk.numTypeArguments() + " type arguments");
//                }
            } else {
                super.visitIdent(tree);
            }
            
            Type saved = result;
            if (print) System.out.println("JML-VISITIDENT-A " + tree + " " + tree.sym + " " + tree.type + " " + tree.sym.getClass() + " " + tree.sym.owner + " " + 
                                    tree.sym.owner.getClass() + " " + (tree.sym instanceof PackageSymbol ps ? ps.sourcefile : tree.sym.outermostClass().sourcefile) + " " + env);
        	if (tree.sym == null) {
        		System.out.println("IDENT NULL SYM " + tree + " " + env.info.scope);
        	}
        	if ((tree.sym instanceof VarSymbol || tree.sym instanceof MethodSymbol)
        			&& enclosingMethodEnv != null
        			&& enclosingMethodEnv.enclMethod != null 
        			&& enclosingMethodEnv.enclMethod.sym.isConstructor() 
        			&& !utils.isJMLStatic(tree.sym) 
        			&& tree.sym.owner == enclosingClassEnv.enclClass.sym
        			&& interpretInPreState(tree,jmlenv.currentClauseKind)
        			) {
        		String k = (jmlenv.currentClauseKind == requiresClauseKind) ? "preconditions: " :
        			(jmlenv.currentClauseKind.keyword() + " clauses: ");
        		k += tree.toString();
        		if (tree.sym.name != names._this)
        			utils.error(tree,"jml.message","Implicit references to 'this' are not permitted in constructor " + k);
        		else
        			utils.error(tree,"jml.message","References to 'this' are not permitted in constructor "+ k);
        	}


        	// The above call erroneously does not set tree.type for method identifiers
        	// if the method failed to result, even though a symbol with an error
        	// type is set, so we patch that here.  See also the comment at visitSelect.
        	if (tree.type == null) tree.type = tree.sym.type;

        	if (!justAttribute && tree.sym instanceof VarSymbol) {
        		var qsaved = quantifiedExprs;
        		try {
        			quantifiedExprs = new LinkedList<JmlQuantifiedExpr>();
        			checkSecretReadable(tree,(VarSymbol)tree.sym);
        		} finally {
        			quantifiedExprs = qsaved;
        		}
        	}// Could also be a method call, and error, a package, a class...

        	checkVisibility(tree, jmlenv.jmlVisibility, tree.sym, null);

            var rep = jmlenv.representsHead;
        	if (rep != null && jmlenv.currentClauseKind == representsClause && tree.sym instanceof VarSymbol && tree.sym.owner instanceof ClassSymbol && tree.sym.name != names._this && tree.sym.name != names._super) {  // FIXME - also need to check the reads statement of method calls
        		//System.out.println("CHECKING DG " + (VarSymbol)tree.sym + " IN " + jmlenv.representsHead + " " + jmlenv.currentClauseKind);
        		if (!isContainedInDatagroup((VarSymbol)tree.sym, jmlenv.representsHead)) {
        			utils.error(tree,"jml.message", "Because '" + rep + "' reads '" + tree.sym + "' in a represents clause, '" + tree.sym + "' must be 'in' the model field '" + rep + "'");
        		}
        	}
        	result = saved;
            if (print) System.out.println("JMLIDENT-Z " + ck + " # " + tree.type + " # " + tree.type.tsym + " # " + tree.sym);
        } catch (Exception e) {
            System.out.println("JMLATTR EXC " + e.getMessage());
            e.printStackTrace(System.out);
        	utils.unexpectedException(e, "JmlAttr.visitIdent: " + tree);
        } finally {
            jmlenv = jmlenv.pop();
        }
    }
        
    protected long jmlAccess(JCModifiers mods) {
        long v = mods.flags & Flags.AccessFlags;
        if (utils.hasModifier(mods,Modifiers.SPEC_PUBLIC)) v = Flags.PUBLIC;
        if (utils.hasModifier(mods,Modifiers.SPEC_PROTECTED)) v = Flags.PROTECTED;
        return v;
    }
    
    protected void checkVisibility(DiagnosticPosition pos, long jmlVisibility, Symbol sym, JCExpression selected) {
        if (jmlenv.currentBlockContract != null) return;
        if (jmlVisibility != -1) {
            long v = (sym.flags() & Flags.AccessFlags);
            if (sym instanceof ClassSymbol) {
                // FIXME - the code below crashes for class symbols. What should we do?
                // FIXME - we also get this case for annotations on a clause
            } else if (sym.name == names.length || sym.name == names._class) {
            	v = Flags.PUBLIC;
            } else {
                JCModifiers mods = null;
                if (sym.owner != null && sym.owner.kind == TYP) {
                    if (sym.kind == VAR) {
                        VarSymbol vsym = (VarSymbol)sym;
                        mods = specs.getSpecsModifiers((VarSymbol)sym);
                   }
                    if (sym.kind == MTH) {
                        mods = specs.getSpecsModifiers((MethodSymbol)sym);
                    }
                }
                if (mods != null && utils.hasMod(mods,SPEC_PROTECTED)) {
                    v = Flags.PROTECTED;
                }
                if (mods != null && utils.hasMod(mods,SPEC_PUBLIC)) {
                    v = Flags.PUBLIC;
                }
            }
                        
            if (jmlenv.currentClauseKind == invariantClause || jmlenv.currentClauseKind == constraintClause) {
                // An ident used in an invariant must have the same visibility as the invariant clause - no more, no less
                // Is the symbol more visible? OK if the symbol is not a modifiable variable
                if (jmlVisibility != v && moreOrEqualVisibleThan(v,jmlVisibility) 
                        && sym instanceof VarSymbol && !utils.isExprLocal(sym.flags()) && !special(v,sym)
                        && (sym.flags() & Flags.FINAL)==0 ) { 
                    utils.error(pos, "jml.visibility", visibility(v), visibility(jmlVisibility), jmlenv.currentClauseKind.keyword());
                }
                // Is the symbol less visible? not OK
                if (jmlVisibility != v && !moreOrEqualVisibleThan(v,jmlVisibility)
                        && !utils.isExprLocal(sym.flags()) && !special(v,sym)) { 
                    utils.error(pos, "jml.visibility", visibility(v), visibility(jmlVisibility), jmlenv.currentClauseKind.keyword());
                }
            } else if (jmlenv.currentClauseKind == representsClause) {
                //log.error(tree.pos,"jml.internal","Case not handled in JmlAttr.visitIdent: " + jmlenv.currentClauseKind.internedName());
                if (!moreOrEqualVisibleThan(v,jmlVisibility) && !special(v,sym)) {
                    utils.error(pos, "jml.visibility", visibility(v), visibility(jmlVisibility), jmlenv.currentClauseKind.keyword());
                }

            } else if (jmlenv.currentClauseKind == inClause) {
                // In    V type x; //@ in y;
                // identifier y must be at least as visible as x (i.e., as V)
                if (!moreOrEqualVisibleThan(v,jmlVisibility)) {
                    utils.error(pos, "jml.visibility", visibility(v), visibility(jmlVisibility), jmlenv.currentClauseKind.keyword());
                }

            } else if (jmlenv.currentClauseKind == ensuresClauseKind || jmlenv.currentClauseKind == signalsClauseKind) {
                // An identifier mentioned in a clause must be at least as visible as the clause itself.
                if (!moreOrEqualVisibleThan(v,jmlVisibility) && !special(v,sym)) {
                    utils.error(pos, "jml.visibility", visibility(v), visibility(jmlVisibility), jmlenv.currentClauseKind.keyword());
                }
                
                if (jmlenv.currentLabel != null && jmlenv.enclosingMethodDecl.sym.isConstructor()) {
                    if (sym.owner instanceof ClassSymbol && !sym.isStatic() && 
                            (selected == null || (selected instanceof JCIdent && 
                                 (((JCIdent)selected).name == names._this || ((JCIdent)selected).name == names._super)))) {
                    	utils.error(pos,  "jml.no.old.in.constructor", sym);
                    }
                }

            } else  {
                // Default case -- requires, old, ...
                // An identifier mentioned in a clause must be at least as visible as the clause itself.
                if (!moreOrEqualVisibleThan(v,jmlVisibility) && !special(v,sym)) {
                    utils.error(pos, "jml.visibility", visibility(v), visibility(jmlVisibility), jmlenv.currentClauseKind.keyword());
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
        if (jmlresolve.allowJML()) {
            Type owntype = types.createErrorType(tree.type);
            Type atype = attribExpr(tree.indexed, env);
            Type t = attribExpr(tree.index, env);
            if (jmltypes.isArray(atype))
                owntype = jmltypes.elemtype(atype);
            else if (!atype.hasTag(ERROR))
                utils.error(tree.indexed, "array.req.but.found", atype);
            if (t == rangeTypeKind.getType(context)) {
            	if (!(tree.index instanceof JmlRange)) {
            		utils.error(tree.index,"jml.message", "Index ranges are implemented only for explicit range expressions (using ..)");
            	}
            } else {
            	if (jmltypes.isIntArray(atype) && !jmltypes.isAnyIntegral(t) && !t.isErroneous()) {
            		utils.error(tree.index, "jml.message", "Expected an integral type as an index, not " + t.toString());
            	}
            }
        	if (!pkind().contains(KindSelector.VAR)) owntype = types.capture(owntype);
        	result = check(tree, owntype, KindSelector.VAR, resultInfo);

        } else {
            super.visitIndexed(tree);
        }
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
        
        JmlSpecs.MethodSpecs mspecs = specs.getAttrSpecs(msym);
        VarSymbol calledSecret = null;
        VarSymbol calledQuery = null;
        boolean calledPure = false;
        if (mspecs != null) {
            calledSecret = getSecretSymbol(mspecs.mods);
            calledQuery = getQuerySymbol(tree,mspecs.mods);
            calledPure = utils.hasModifier(mspecs.mods,Modifiers.PURE);
        }
        
        if (currentQueryContext != null) {
            // query method - may call query methods for a contained datagroup
            //              - may call secret methods for a contained datagroup
            //              - may call open pure method
            if (calledSecret != null) {
                if (!isContainedInDatagroup(calledSecret,currentQueryContext)) {
                    utils.error(pos,"jml.incorrect.datagroup");
                }
            }
            if (calledQuery != null) {
                if (!isContainedInDatagroup(calledQuery,currentQueryContext)) {
                	utils.error(pos,"jml.incorrect.datagroup");
                }
            }
            if (calledSecret == null && calledQuery == null) {
                if (!calledPure) {
                	utils.error(pos,"jml.incorrect.datagroup");
                }
            }
        }
        if (currentSecretContext != null && currentSecretContext != currentQueryContext) {
            if (calledSecret != null) {
                if (!isContainedInDatagroup(calledSecret,currentSecretContext)) {
                	utils.error(pos,"jml.incorrect.datagroup");
                }
            }
            if (calledQuery != null) {
                if (!isContainedInDatagroup(calledQuery,currentSecretContext)) {
                	utils.error(pos,"jml.incorrect.datagroup");
                }
            }
            if (calledSecret == null && calledQuery == null) {
                if (!calledPure) {
                	utils.error(pos,"jml.incorrect.datagroup");
                }
            }        }
        if (currentQueryContext == null && currentSecretContext == null) {
            // open method - may call query methods, but no secret methods
            if (calledSecret != null) {
            	utils.error(pos,"jml.open.may.not.call.secret");
            }
        }
    }
    
    protected void checkSecretReadable(DiagnosticPosition pos, VarSymbol vsym) {
        // If the variable is local to the method, then secret/query rules do not apply
    	if (justAttribute) return;
        if (vsym.owner instanceof MethodSymbol) return;

        JmlSpecs.FieldSpecs fspecs = specs.getLoadedSpecs(vsym);
        boolean identIsSecret = fspecs != null && utils.hasModifier(fspecs.mods,Modifiers.SECRET);
        // Rules:
        // If method is open, then ident may not be secret
        // If method is query and we are in the method specs, then ident may not be secret
        // If method is query, then ident is open or is secret for the same datagroup
        // If method is secret, then ident is open or is secret for the same datagroup
        
        if (identIsSecret) {
            boolean prevAllow = ((JmlResolve)rs).setAllowJML(true);
            if (currentSecretContext != null && isContainedInDatagroup(vsym,currentSecretContext)) {
                // OK - we are in a secret context and the variable is in that context
            } else if (jmlenv.currentClauseKind == inClause || jmlenv.currentClauseKind == mapsClause) {
                // OK - this is the target of an in or maps clause - secrecy restrictions are checked there
            } else if (currentQueryContext != null && isContainedInDatagroup(vsym,currentQueryContext)) {
                // OK - we are in a query context and the variable in secret for that context
            } else if (currentSecretContext != null) {
                utils.error(pos,"jml.not.in.secret.context",vsym.getQualifiedName(),currentSecretContext.getQualifiedName());
            } else {
                // in open context
                utils.error(pos,"jml.no.secret.in.open.context",vsym.getQualifiedName());
            }
            ((JmlResolve)rs).setAllowJML(prevAllow);
        }
    }
    
    protected void checkSecretWritable(DiagnosticPosition pos, VarSymbol vsym) {
        // If the variable is local to the method, then secret/query rules do not apply
        if (vsym.owner instanceof MethodSymbol) return;

        JmlSpecs.FieldSpecs fspecs = specs.getAttrSpecs(vsym);
        boolean identIsSecret = fspecs != null && utils.hasModifier(fspecs.mods,Modifiers.SECRET);
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
                utils.error(pos,"jml.not.writable.in.secret.context",vsym.getQualifiedName(),currentSecretContext.getQualifiedName());
                error = true;
            }
        }
        if (currentQueryContext != null && !error) {
            if (!identIsSecret || !isContainedInDatagroup(vsym,currentQueryContext)) {
                // ERROR - may not write a non-secret field in a secret context
                // ERROR - field is not in the correct secret context to be written
                utils.error(pos,"jml.not.writable.in.secret.context",vsym.getQualifiedName(),currentQueryContext.getQualifiedName());
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
            boolean prev = JmlResolve.instance(context).setAllowJML(true);
            try {
                g.accept(this);
            } finally {
                JmlResolve.instance(context).setAllowJML(prev);
                justAttribute = prevj;
            }
        }
    }
    
    // Returns true if contextSym is contained (transitively) in the varSym datagroup
    protected boolean isContainedInDatagroup(/*@nullable*/ VarSymbol varSym, /*@nullable*/ VarSymbol contextSym) {
        if (varSym == contextSym) return true;
        JmlSpecs.FieldSpecs fspecs = specs.getAttrSpecs(varSym);
        if (fspecs == null) System.out.println("NO SPECS FOR " + varSym + " " + contextSym);
        for (JmlTypeClause t: fspecs.list) {
            if (t.clauseType == inClause) {  // FIXME - relies on variable IN clauses being attributed before a method that uses them
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
    
    public java.util.List<VarSymbol> checkForCircularity(VarSymbol varsym) {
        Set<VarSymbol> roots = new HashSet<>();
        return checkForCircularity(varsym, roots);
    }
    
    // A null return means no circularity; a non-null return contains variables that participate in the circularity
    public java.util.List<VarSymbol> checkForCircularity(VarSymbol varsym, Set<VarSymbol> roots) {
        if (!roots.add(varsym)) {
        	 // If already present, we have a circularity
        	java.util.List<VarSymbol> circularList = new LinkedList<>();
            circularList.add(varsym);
            return circularList;
        }
        JmlSpecs.FieldSpecs fspecs = specs.getLoadedSpecs(varsym);
        for (JmlTypeClause t: fspecs.list) {
            if (t.clauseType == inClause) {
                for (JmlGroupName g: ((JmlTypeClauseIn)t).list) {
                    attributeGroup(g);
                    if (g.sym == null) {
                        continue; // Unattributed variable -- presumably already reported
                    }
                    if (g.sym == varsym) {
                    	// FIXME - this highlights one character too many
// FIXME                        if (!t.clauseType.isRedundant) 
                        utils.warning(g,"jml.circular.datagroup.inclusion.self",varsym.name.toString());

                    } else {
                        java.util.List<VarSymbol> circularList = checkForCircularity(g.sym,roots);
                        if (circularList != null) {
                            circularList.add(0,varsym);
                            return circularList;
                        }
                    }
                }
            }
        }
        roots.remove(varsym);
        return null;
    }
    
    protected long flags(Symbol sym) { // OPENJML - added to permit some overriding
    	if (!JmlResolve.instance(context).allowJML) return sym.flags();
        JmlSpecs specs = JmlSpecs.instance(context);
        JCTree.JCModifiers mods = null;
        if (sym instanceof Symbol.VarSymbol) {
        	if (sym.owner instanceof ClassSymbol) {
        		JmlSpecs.FieldSpecs f = specs.getLoadedSpecs((Symbol.VarSymbol)sym); // FIXME - do not need attributed specs
        		if (f != null) mods = f.mods;
        	} else {
        		return sym.flags();
        	}
        } else if (sym instanceof Symbol.MethodSymbol) {
            JmlSpecs.MethodSpecs f = specs.getLoadedSpecs((Symbol.MethodSymbol)sym); // FIXME - do not need attributed specs
            if (f != null) mods = f.mods;
        } else if (sym instanceof Symbol.ClassSymbol) {
        	if (sym.type.isPrimitiveOrVoid()) return Flags.PUBLIC; // Primitive type
            JmlSpecs.TypeSpecs f = specs.getLoadedSpecs((Symbol.ClassSymbol)sym);
            if (f != null) mods = f.modifiers;
        }

        boolean isSpecPublic = utils.hasMod(mods,Modifiers.SPEC_PUBLIC);
        if (isSpecPublic) return Flags.PUBLIC;

        boolean isSpecProtected = utils.hasMod(mods,Modifiers.SPEC_PROTECTED);
        if (isSpecProtected) return Flags.PROTECTED;
        return sym.flags();
    }

    
    
    /** Attributes a member select expression (e.g. a.b); also makes sure
     * that the type of the selector (before the dot) will be attributed;
     * that makes sure that the specifications of members are properly
     * attributed when needed later in esc or rac.
     */
    @Override
    public void visitSelect(JCFieldAccess tree) {
        boolean print = false;//tree.toString().contains("oldjlinks") || tree.toString().contains("oldlinks");
        if (tree.name == null) {
            // This is a store-ref with a wild-card field
            // FIXME - the following needs some review
            attribTree(tree.selected, env, new ResultInfo(KindSelector.of(KindSelector.TYP,KindSelector.VAR), Infer.anyPoly));
            result = tree.type = locsetTypeKind.getType(context);
        } else if (tree.name.toString().startsWith("_$T")) {
            attribTree(tree.selected, env, new ResultInfo(KindSelector.VAR, Infer.anyPoly));
            int n = Integer.parseInt(tree.name.toString().substring(3));
            Type t = tree.selected.type;
            if (t instanceof JmlListType) {
                List<Type> types = ((JmlListType)t).types;
                if (n < 1 || n > types.size()) {
                    log.error(tree.pos, "jml.message", "The tuple selector must be from 1 to " + types.size());
                    t = syms.errType;
                } else {
                    t = types.get(n-1);
                }
            } else {
                log.error(tree.pos, "jml.message", "The tuple selector must be applied to a tuple type, not a "+ t.toString());
                t = syms.errType;
            }
            result = tree.type = check(tree, t, KindSelector.VAL, resultInfo);
        } else {
            IJmlClauseKind fext = Extensions.findKeyword(tree.name);
            // TODO: Not sure under what conditions resultInfo.pkind might be both VAL and TYP and what would happen then
            if (fext instanceof JmlField && this.jmlresolve.allowJML() && !resultInfo.pkind.contains(KindSelector.TYP)) {
            	// <expr>.array
                Type t = attribExpr(tree.selected, env, Type.noType); // Any type is allowed
                Type atype = tree.selected.type;
                if (atype instanceof Type.ArrayType) { 
                    Type elemtype = ((Type.ArrayType)atype).elemtype;
                    Type at = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.lang.array")).type;
                    t = new ClassType(Type.noType,List.<Type>of(elemtype),at.tsym);
                } else if (atype.isErroneous()) {
                    t = atype;
                } else {
                    utils.error(tree,"jml.message","The .array suffix is permitted only for array expressions: " );
                    t = types.createErrorType(atype);
                }
                result = tree.type = check(tree, t, KindSelector.VAL, resultInfo);
            } else {
            	// <package>.array, or something illegal or the normal case
                super.visitSelect(tree);
                // The super call does not always call check... (which assigns the
                // determined type to tree.type, particularly if an error occurs,
                // so we fill it in
                if (tree.type == null) tree.type = result;
                //if (tree.toString().contains("function")) System.out.println("SELECT-TYPE " + tree + " " + result + " " + result.getClass() + " " + tree.sym.getClass());
//                if (result instanceof Type.ClassType ct && ct.tsym instanceof ClassSymbol cs) {
//                    System.out.println("GET SPECS FOR " + cs + " " + specs.status(cs) + " " + JmlEnter.instance(context).nestingLevel);
//                    specs.getLoadedSpecs(cs);
//                    JmlEnter.instance(context).completeBinaryEnterTodo();
//                }
            }
        }
        Type saved = result;
        
        Symbol s = tree.selected.type.tsym;
        if (tree.selected.type instanceof JmlListType) {
        } else if (!(s instanceof PackageSymbol)) {
            ClassSymbol c = null;
            if (s instanceof ClassSymbol) c = (ClassSymbol)s;
            else  c = s.enclClass();
            if (c != null) addTodo(c); // FIXME - why this?
        }
        
        if (tree.sym != null) checkVisibility(tree, jmlenv.jmlVisibility, tree.sym, tree.selected);

        // For selections that are fields with an enclosing class, we check whether it is readable
        // The check on the enclosing class omits fields such as .class
        if (tree.sym instanceof VarSymbol && tree.sym.enclClass() != null) {
            checkSecretReadable(tree.pos(),(VarSymbol)tree.sym);
        } // FIXME - what else could it be, besides an error?
//        if (tree.sym instanceof ClassSymbol) ((JmlCompiler)JmlCompiler.instance(context)).loadSpecsForBinary(env,(ClassSymbol)tree.sym);
        result = saved;
    }
    
    @Override // This is called after tree.selected is attributed, but before the name is sought
    protected boolean visitSelectHelper(JCFieldAccess tree) {
    	if (tree.selected.type instanceof JmlListType) {
    		utils.error(tree, "jml.message", "A " + tree.selected.type.toString() + " value may not be dereferenced");
    		return false;
    	}
    	// Need to be sure that the specs are loaded for the receiver -- otherwise any JML fields mightnot be known
    	TypeSymbol s = tree.selected.type.tsym; // might be a PackageSymbol; also might be int.class
    	if (s instanceof ClassSymbol && s.type.isReference()) specs.getLoadedSpecs((ClassSymbol)s);
    	return true;
    }

    
//    @Override
//    public void visitTypeArray(JCArrayTypeTree tree) {
//        super.visitTypeArray(tree);
//        if (tree.elemtype.type.isPrimitiveOrVoid()) {
//            ClassSymbol t = (ClassSymbol)tree.type.tsym;
//            jmlcompiler.loadSpecsForBinary(env,t);
////            System.out.println(t.toString());
//        }
//    }
    
    @Override
    public void visitTypeCast(JCTypeCast tree) {
        boolean prev = jmlresolve.setAllowJML(jmlenv.currentClauseKind != null);
        Type clazztype = attribType(tree.clazz, env);  // FIXME - this call is repeated later in super.visitTypeCast
        chk.validate(tree.clazz, env);
        result = tree.type = check(tree, clazztype, KindSelector.VAL, resultInfo);
        jmlresolve.setAllowJML(prev);
        //System.out.println("JMLATTR " + tree.clazz + " " + tree.clazz.type + " " + (tree.clazz instanceof JmlPrimitiveTypeTree) + " " + tree.clazz.getClass());
        var BIGINT = JmlPrimitiveTypes.bigintTypeKind.getSymbol(context);
        var REAL = JmlPrimitiveTypes.realTypeKind.getType(context);
        var STRING = JmlPrimitiveTypes.stringTypeKind.getType(context);
        var TYPE = JmlPrimitiveTypes.TYPETypeKind.getType(context);
        if (utils.isExtensionValueType(clazztype)) {
            prev = jmlresolve.setAllowJML(jmlenv.currentClauseKind != null);
            Type exprtype = attribExpr(tree.expr, env, Infer.anyPoly);
            jmlresolve.setAllowJML(prev);
            result = tree.type = clazztype; // Even if there is an error or the cast is not allowed, set the result to the new type to avoid cascading errors
            if (clazztype.tsym == tree.expr.type.tsym) return;
            if (clazztype.tsym == BIGINT) {
                if (tree.expr.type.isNumeric()) return;
                if (tree.expr.type.tsym == REAL.tsym) return;
                if (tree.expr.type.toString().contains("BigInteger")) return;
                utils.error(tree.expr, "jml.message", "Only numeric types may be cast to \\bigint, not " + tree.expr.type);
                return;
            }
            if (clazztype.tsym == REAL.tsym) {
                if (tree.expr.type.tsym == BIGINT) return;
                if (tree.expr.type.isNumeric()) return;
                if (tree.expr.type.toString().contains("BigInteger")) return;
                utils.error(tree.expr, "jml.message", "Only numeric types may be cast to \\real, not " + tree.expr.type);
                return;
            }
            if (clazztype == TYPE) {
                if (exprtype.tsym == syms.classType.tsym) return;
                utils.error(tree.expr.pos,"jml.only.class.cast.to.type",exprtype);
                return;
            }
            if (clazztype == STRING) {
                if (jmltypes.isSameType(tree.expr.type, syms.stringType)) return;
                utils.error(tree.expr, "jml.message", "Only String may be cast to \\string, not " + tree.expr.type);
                return;
            }
            utils.error(tree.expr, "jml.message", "A " + tree.expr.type + " may not be cast to " + clazztype);
            return;
        }
        if (tree.clazz instanceof JmlPrimitiveTypeTree) {
            Type exprtype = attribExpr(tree.expr, env, Infer.anyPoly);
            if (utils.isExtensionValueType(exprtype)) {
                if (exprtype.tsym == BIGINT && clazztype.isIntegral()) return;
                if (exprtype == REAL && clazztype.isNumeric()) return;
                utils.error(tree, "jml.message", "May not cast a " + exprtype + " to " + clazztype);
                return;
            }
        }
        super.visitTypeCast(tree);
    }
    
    @Override
    public void visitTypeApply(JCTypeApply tree) {
        if (tree.clazz instanceof JCIdent id) {
            IJmlClauseKind ck = Extensions.findKeyword(id.name);
            if (ck instanceof JmlTypeKind jtk) {
                Name saved = id.name;
                id.name = jtk.name;
                super.visitTypeApply(tree);
                id.name = saved;
                return;
            }
        }
        super.visitTypeApply(tree);
    }
        
    /** Attributes an array-element-range (a[1 .. 2]) store-ref expression */
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        if (that.lo != null) {
            Type t = attribExpr(that.lo,env);
            if (!jmltypes.isAnyIntegral(t) && !t.isErroneous()) {
                utils.error(that.lo, "jml.message", "Expected an integral type, not " + t.toString());
            }
        }
        if (that.hi != null && that.hi != that.lo) {
            Type t = attribExpr(that.hi,env);
            if (!jmltypes.isAnyIntegral(t) && !t.isErroneous()) {
                utils.error(that.lo, "jml.message", "Expected an integral type, not " + t.toString());
            }
        }
        Type t = attribExpr(that.expression,env,Type.noType);
        if (t.getKind() != TypeKind.ARRAY) {
            if (t.getKind() != TypeKind.ERROR) utils.error(that.expression,"jml.not.an.array",t);
            t = syms.errType;
            result = check(that, t, KindSelector.VAL, resultInfo);
        } else {
            t = ((ArrayType)t).getComponentType();
            result = check(that, t, KindSelector.VAR, resultInfo);
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
    //public EnumMap<JmlTokenKind,ClassSymbol> tokenToAnnotationSymbol = new EnumMap<JmlTokenKind,ClassSymbol>(JmlTokenKind.class);
    public Map<ModifierKind,ClassSymbol> modToAnnotationSymbol = new HashMap<>();
    
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
        Name n = names.fromString("jdk.compiler");
        Symbol.ModuleSymbol mod = syms.unnamedModule;
        for (IJmlClauseKind kk: Extensions.allKinds.values()) {
            if (!(kk instanceof ModifierKind)) continue;
            ModifierKind k = (ModifierKind)kk;
            ClassSymbol sym = syms.enterClass(mod, names.fromString(k.fullAnnotation));
            modToAnnotationSymbol.put(k,sym);
        }
        annotationPackageSymbol = modToAnnotationSymbol.get(Modifiers.PURE).packge();

        nullablebydefaultAnnotationSymbol = modToAnnotationSymbol.get(Modifiers.NULLABLE_BY_DEFAULT);
        nonnullbydefaultAnnotationSymbol = modToAnnotationSymbol.get(Modifiers.NON_NULL_BY_DEFAULT);
        nonnullAnnotationSymbol = modToAnnotationSymbol.get(Modifiers.NON_NULL);
        nullableAnnotationSymbol = modToAnnotationSymbol.get(Modifiers.NULLABLE);
    }
    
    public boolean checkAnnotationType(JCTree.JCAnnotation a) {
    	if (a.annotationType.type != null) return true;
    	if (a.type == null) {
    		a.type = a.annotationType.type;
    		//System.out.println("NULL a.type for " + a);
    	}
    	String s = a.annotationType.toString();
    	if (a.type == null) for (var mod: modToAnnotationSymbol.entrySet()) {
    		if (mod.getKey().fullAnnotation.equals(s)) {
    			a.type = a.annotationType.type = mod.getValue().type;
    			if (Utils.debug()) if (a instanceof JmlAnnotation) utils.note(((JmlAnnotation)a).sourcefile, a, "jml.internal.notsobad", "Had to lookup type of a annotation with null type: " + s);
    			return true;
    		}
    	}
    	if (a.toString().contains("@Deprecated")) return false; // FIXME - why is this not attributed
    	if (a.toString().contains("@Override")) return false; // FIXME - why is this not attributed
    	utils.error(((JmlAnnotation)a).sourcefile, a.pos, "jml.message", "Null annotation type: " + a );
    	return false;
    }
    
    /** Checks that all of the JML annotations present in the first argument
     * are also present in the second argument, issuing error messages if they
     * are not.
     * @param annotations a list of annotations to check
     * @param allowed the set of allowed annotations
     * @param place a description of where the annotations came from, for error messages
     */
    public void allAllowed(JCModifiers mods, ModifierKind[] allowed, String place) {
        allAllowed(((JmlModifiers)mods).jmlmods, allowed, place);
//        outer: for (JCTree.JCAnnotation a: annotations) {
//        	if (!checkAnnotationType(a)) continue; // FIXME - why might the annotation type be null?
//            Symbol tsym = a.annotationType.type.tsym;
//            for (ModifierKind c: allowed) {
//            	if (((JmlAnnotation)a).kind == c) continue outer; // Found it
//            	var asym = modToAnnotationSymbol.get(c);
//                if (tsym.equals(asym)) continue outer; // Found it
//            }
//            // a is not in the list, but before we complain, check that it is
//            // one of our annotations
//            if (tsym.packge().flatName().equals(annotationPackageName)) { // FIXME - change to comparing symbols instead of strings?
//                JavaFileObject prev = log.useSource(((JmlTree.JmlAnnotation)a).sourcefile);
//                log.error(a.pos,"jml.illegal.annotation",place);
//                log.useSource(prev);
//            }
//        }
    }
    
    public void allAllowed(java.util.List<JmlToken> jmlmods, ModifierKind[] allowed, String place) {
        outer: for (JmlToken t: jmlmods) {
            for (ModifierKind c: allowed) {
            	if (t.jmlclausekind == c) continue outer; // Found it
            }
            JavaFileObject prev = log.useSource(t.source);
            utils.error(t.pos,t.endPos,"jml.illegal.annotation",place);
            log.useSource(prev);
        }
    }
    
    /** This checks that the given modifier set does not have annotations for
     * both of a pair of mutually exclusive annotations; it prints an error
     * message if they are both present; returns true if an error happened
     * @param mods the modifiers to check
     * @param ta the first JML token
     * @param tb the second JML token
     */
//    public boolean checkForConflict(JCModifiers mods, ModifierKind ta, ModifierKind tb) {
//        JmlToken a,b;
//        a = utils.findModifier(mods,ta);
//        b = utils.findModifier(mods,tb);
//        if (a != null && b != null) {
//            JavaFileObject prev = log.useSource(b.sourcefile);
//            utils.error(b.pos(),"jml.conflicting.modifiers",a,b);
//            log.useSource(prev);
//            return true;
//        }
//        return false;
//    }
    
    public boolean checkForDuplicateModifiers(JmlModifiers mods) {
        if (mods == null || mods.jmlmods == null) return false;
        boolean error = false;
        for (JmlToken m: mods.jmlmods) {
            if (m.jmlclausekind == null) continue; // FIXME - why does this happen?
            if (((ModifierKind)m.jmlclausekind).isTypeAnnotation()) continue;
            for (JmlToken mm: mods.jmlmods) {
                if (m == mm) break;
                if (m.jmlclausekind == mm.jmlclausekind) {
                    utils.errorAndAssociatedDeclaration(m.source, m, mm.source, mm, "jml.message", "modifier " + m.jmlclausekind + " may not be repeated");
                    error = true;
                }
            }
        }
        return error;
    }
    
    public boolean checkForConflict(JCModifiers mods, ModifierKind ta, ModifierKind tb) {
        var a = utils.findModifier(mods,ta);
        if (a == null) return false;
        var b = utils.findModifier(mods,tb);
        if (b == null) return false;
        var t = a.pos <= b.pos ? b : a;
        utils.error(t.source, t.pos,"jml.conflicting.modifiers",a.jmlclausekind,b.jmlclausekind); // FIXME add Assocated location
        return true;
    }
    
    public boolean checkForConflict(JCModifiers mods, ModifierKind... ts) {
        for (var ta: ts) {
            var a = utils.findModifier(mods,ta);
            if (a != null) for (var tb: ts) {
                if (tb == ta) break;
                var b = utils.findModifier(mods,tb);
                if (b != null) {
                    var t = a.pos <= b.pos ? b : a;
                    utils.error(t.source, t.pos,"jml.conflicting.modifiers",a.jmlclausekind,b.jmlclausekind); // FIXME add Assocated location
                    return true;
                }
            }
        }
        return false;
    }
    
    public boolean checkForRedundantSpecMod(JCModifiers mods) {
        JmlToken a;
        boolean result = false;
        if ((mods.flags & Flags.PROTECTED) != 0 &&
                (a=utils.findModifier(mods,SPEC_PROTECTED)) != null ) {
            JavaFileObject prev = log.useSource(a.source); // FIXME - put source in warning call
            utils.warning(a.pos,"jml.redundant.visibility","protected","spec_protected");
            log.useSource(prev);
            result = true;
        }
        if ((mods.flags & Flags.PUBLIC) != 0 &&
                (a=utils.findModifier(mods,SPEC_PROTECTED)) != null ) {
            JavaFileObject prev = log.useSource(a.source); // FIXME - put source in warning call
            utils.warning(a.pos,"jml.redundant.visibility","public","spec_protected");
            log.useSource(prev);
            result = true;
        }
        if ((mods.flags & Flags.PUBLIC) != 0 &&
                (a=utils.findModifier(mods,SPEC_PUBLIC)) != null ) {
            JavaFileObject prev = log.useSource(a.source); // FIXME - put source in warning call
            utils.warning(a.pos,"jml.redundant.visibility","public","spec_public");
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
        return utils.findMod(mods,modToAnnotationSymbol.get(ta));
    }
    
    public boolean has(java.util.List<JmlToken> mods, ModifierKind ta) {
        for (var t: mods) if (t.jmlclausekind == ta) return true;
        return false;
    }
    

//    //@ nullable
//    public JmlAnnotation findMod(/*@nullable*/JCModifiers mods, ModifierKind ta) {
//        if (mods == null) return null;
//        return utils.findMod(mods,modToAnnotationSymbol.get(ta));
//    }

    /** Returns true if the given symbol has non_null or does not have nullable annotation */
    public boolean isNonNull(Symbol sym, /*@ nullable */ JCModifiers mods) {
        if (mods != null) {
        	if (has(((JmlModifiers)mods).jmlmods, Modifiers.NON_NULL)) return true;
        	if (has(((JmlModifiers)mods).jmlmods, Modifiers.NULLABLE)) return false;
            List<JCAnnotation> list = mods.getAnnotations();
            if (list != null) for (JCAnnotation a: list) {
            	if (a.annotationType.type == null) continue; // FIXME - need to have annotations attributed
                if (a.annotationType.type.tsym == nonnullAnnotationSymbol) return true;
                if (a.annotationType.type.tsym == nullableAnnotationSymbol) return false;
            }
        }
        if (sym.owner instanceof PackageSymbol) return specs.defaultNullity(null) == Modifiers.NON_NULL;
        var s = sym;
        while (!(s.owner instanceof ClassSymbol) && s.owner != null) s = s.owner;
        return specs.defaultNullity((ClassSymbol)s.owner) == Modifiers.NON_NULL;
    }
    
    /** Returns true if the given symbol has non_null or does not have nullable annotation */
    public boolean isNonNull(VarSymbol vsym) {
        FieldSpecs fspecs = specs.getLoadedSpecs(vsym);
        if (fspecs == null) return true; // FIXME - what should this be?
        JCModifiers mods = fspecs.mods;
        return isNonNull(vsym, mods);
    }
    

    /** Returns true if the given modifiers includes model
     * @param mods the modifiers to check
     * @return true if the model modifier is present, false if not
     */
    public boolean isModel(/*@nullable*/JCModifiers mods) {
    	return utils.hasModifier((JmlModifiers)mods, Modifiers.MODEL);
    }
    
    /** Returns true if the given modifiers includes instance
     * @param mods the modifiers to check
     * @return true if the modifier is present, false if not
     */
    public boolean isInstance(/*@nullable*/JCModifiers mods) {
    	return utils.hasModifier((JmlModifiers)mods, Modifiers.INSTANCE);
    }
    
    /** Returns true if the given symbol has a given annotation 
     * @param symbol the symbol to check
     * @return true if the symbol has a given annotation, false otherwise
     */
    public boolean hasAnnotation(Symbol symbol, JmlTokenKind t) {
        return symbol.attribute(modToAnnotationSymbol.get(t)) != null;

    }
    
    public boolean hasAnnotation(Symbol symbol, ModifierKind t) {
        return symbol.attribute(modToAnnotationSymbol.get(t)) != null;
    }
    
    public boolean hasAnnotation2(Symbol symbol, ModifierKind t) {
        for (var a: symbol.getAnnotationMirrors()) {
            if (a.toString().endsWith(t.fullAnnotation)) return true; // FIXME - improve this
        }
        return false;
    }
    
    public boolean hasAnnotation2(Type type, ModifierKind t) {
    	for (var a: type.getAnnotationMirrors()) {
    		if (a.toString().endsWith(t.fullAnnotation)) return true; // FIXME - improve this
    	}
        return false;
    }
    
    public boolean hasAnnotation(List<JCAnnotation> list, ModifierKind t) {
    	for (var a: list) {
    		if (((JmlAnnotation)a).kind == t) return true;
    	}
        return false;
    }
    
    /** Returns true if the given symbol has a Immutable annotation */
    public boolean isImmutable(Symbol symbol) {
        return symbol.attribute(modToAnnotationSymbol.get(Modifiers.IMMUTABLE))!=null; // FIXME - need to get this from the spec
    }

  
    /** Returns true if the given symbol has a given annotation 
     * @param symbol the symbol to check
     * @return true if the symbol has a given annotation, false otherwise
     */
    public Attribute.Compound findAnnotation(Symbol symbol, JmlTokenKind t) {
        return symbol.attribute(modToAnnotationSymbol.get(t));
    }
    public Attribute.Compound findAnnotation(Symbol symbol, ModifierKind t) {
        return symbol.attribute(modToAnnotationSymbol.get(t));
    }
  
    /** Returns true if the given symbol has a model annotation 
     * @param symbol the symbol to check
     * @return true if the symbol has a model annotation, false otherwise
     */
    public boolean isModelClass(Symbol symbol) {  // FIXME
    	TypeSpecs tspecs = specs.getLoadedSpecs((ClassSymbol)symbol);
    	return tspecs != null && isModel(tspecs.modifiers);
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
    
//    public boolean isPureMethodRaw(MethodSymbol symbol) {
//        java.util.List<MethodSymbol> overrideList = Utils.instance(context).parents(symbol);
//        java.util.ListIterator<MethodSymbol> iter = overrideList.listIterator(overrideList.size());
//        while (iter.hasPrevious()) {
//            MethodSymbol msym = iter.previous();
//            MethodSpecs mspecs = specs.getLoadedSpecs(msym);
//            if (mspecs == null) {  // FIXME - observed to happen for in gitbug498 for JMLObjectBag.insert
//                // FIXME - A hack - the .jml file should have been read for org.jmlspecs.lang.JMLList
//                if (msym.toString().equals("size()") && msym.owner.toString().equals(Strings.jmlSpecsPackage + ".JMLList")) return true;
//                // FIXME - check when this happens - is it because we have not attributed the relevant class (and we should) or just because there are no specs
//                return specs.isPure((ClassSymbol)msym.owner);
//            }
//            boolean isPure = specs.isPure(msym);
//            if (isPure) return true;
//        }
//        return false;
//    }

    public boolean isPureMethod(MethodSymbol msym) {
        return specs.isPureMethod(msym);
    }
    
    public boolean isSpecPureMethod(MethodSymbol msym) {
        return specs.isSpecPureMethod(msym);
    }
    
    public boolean isStrictlyPureMethod(MethodSymbol msym) {
        return specs.isStrictlyPureMethod(msym);
    }
    
    public boolean isQueryMethod(MethodSymbol symbol) {
        for (MethodSymbol msym: Utils.instance(context).parents(symbol,true)) {
            MethodSpecs mspecs = specs.getLoadedSpecs(msym);
            if (mspecs == null) {
                // FIXME - A hack - the .jml file should have been read for org.jmlspecs.lang.JMLList
                if (msym.toString().equals("size()") && msym.owner.toString().equals(Strings.jmlSpecsPackage + ".JMLList")) return true;
                // FIXME - check when this happens - is it because we have not attributed the relevant class (and we should) or just because there are no specs
                continue;
            }
            boolean isPure = specs.isQuery(symbol);
            if (isPure) return true;
        }
        return false;
    }
    
    /** Returns true if the given symbol has a helper annotation 
     * @param symbol the symbol to check
     * @return true if the symbol has a model annotation, false otherwise
     */
    public boolean isHelper(MethodSymbol symbol) {
        // Remove the following line when we add the helper annotation to the implicit enum specs
        if (symbol.owner.isEnum() && (symbol.name == names.values || symbol.name == names.ordinal || symbol.name == names._name)) return true;
        MethodSpecs mspecs = specs.getLoadedSpecs(symbol);
        if (mspecs == null) {
            // FIXME - check when this happens - is it because we have not attributed the relevant class (and we should) or just because there are no specs
            return false;
        }
        if (utils.hasModifier((JmlModifiers)mspecs.mods, Modifiers.HELPER,  Modifiers.NO_STATE)) return true;
        return false;
    }
    
    public boolean isHelper(VarSymbol symbol) {
        FieldSpecs fspecs = specs.getLoadedSpecs(symbol);
        return fspecs != null && utils.hasModifier(fspecs.mods,Modifiers.HELPER);
    }
    
    public boolean isGhost(VarSymbol symbol) {
        FieldSpecs fspecs = specs.getLoadedSpecs(symbol);
        return utils.hasModifier(fspecs.mods,Modifiers.GHOST);
    }
    
    public boolean isSpecPublic(MethodSymbol symbol) {
        MethodSpecs mspecs = specs.getLoadedSpecs(symbol);
        return utils.hasModifier((JmlModifiers)mspecs.mods, Modifiers.SPEC_PUBLIC);
    }
    
    public boolean isSpecProtected(MethodSymbol symbol) {
        MethodSpecs mspecs = specs.getLoadedSpecs(symbol);
        return utils.hasModifier((JmlModifiers)mspecs.mods, Modifiers.SPEC_PROTECTED);
    }
    
    public void addHelper(MethodSymbol symbol) {
        addAnnotation(symbol,Modifiers.HELPER);
        if (!utils.isHelper(symbol)) System.out.println("ISHELPER FAILED AFTER ADD HELPER " + symbol);
        return;
    }
    
    public void addAnnotation(MethodSymbol symbol, ModifierKind kind) {
        MethodSpecs mspecs = specs.getLoadedSpecs(symbol);
        if (mspecs == null) {
            // FIXME - check when this happens - is it because we have not attributed the relevant class (and we should) or just because there are no specs
            return ;
        }
        // FIXME - what if mspecs.mods is null
        Symbol ansym = modToAnnotationSymbol.get(kind);
        // OPENJML - FIXME - wrapped the below line with TypeCompound -- not sure about the final null
        Attribute.TypeCompound a = new Attribute.TypeCompound(new Attribute.Compound(ansym.type,List.<Pair<MethodSymbol,Attribute>>nil()), null);
        JmlAnnotation an = (JmlAnnotation)jmlMaker.TypeAnnotation(a);
        an.type = ansym.type;
        an.kind = kind;
        mspecs.mods.annotations = mspecs.mods.annotations.append(an);
        for (JCTree.JCAnnotation aa: mspecs.mods.annotations) {
        	if (((JmlTree.JmlAnnotation)aa).kind == kind) return;
        }
        System.out.println("ANNOTATION NOT FOUND AFTER ADD HELPER " + symbol);
        return;
    }
    
    public boolean isHeapIndependent(MethodSymbol symbol) {
        MethodSpecs mspecs = specs.getLoadedSpecs(symbol);
        if (mspecs == null) {
            // FIXME - check when this happens - is it because we have not attributed the relevant class (and we should) or just because there are no specs
            return false;
        }
        return utils.findModifier(mspecs.mods,Modifiers.NO_STATE) != null;
    }
    
    public boolean isImmutable(ClassSymbol symbol) {
        TypeSpecs mspecs = specs.getLoadedSpecs(symbol);
        if (mspecs == null) {
            // FIXME - check when this happens - is it because we have not attributed the relevant class (and we should) or just because there are no specs
            return false;
        }
        return utils.findModifier(mspecs.modifiers,Modifiers.IMMUTABLE) != null;
    }
        
    public boolean hasAnnotation(JmlVariableDecl decl, ModifierKind token) {
        if (decl.specsDecl != null) {
            return utils.hasModifier(decl.specsDecl.mods, token);
        } else {
            return utils.hasModifier(decl.mods, token);
        }
    }


    public boolean isCaptured(JmlVariableDecl vd) {
        return utils.findModifier(vd.mods,Modifiers.CAPTURED) != null;
        
    }

    /** Returns true if the given modifiers/annotations includes ghost
     * @param mods the modifiers to check
     * @return true if the ghost modifier is present, false if not
     */
    public boolean isGhost(/*@nullable*/JCModifiers mods) {
        return utils.hasModifier(mods,Modifiers.GHOST);
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
        var e = runtimeClass.members().getSymbolsByName(names.fromString("assertionFailure"));
        Symbol ms = e.iterator().next();
        JCFieldAccess m = make.Select(runtimeClassIdent,names.fromString("assertionFailure"));
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
//        // org.jmlspecs.runtime.Utils.assertionFailure();
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
//        // org.jmlspecs.runtime.Utils.assertionFailure();
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
    
    public java.util.List<JCIdent> loopStack = new java.util.LinkedList<JCIdent>();
    public java.util.List<JmlEnhancedForLoop> foreachLoopStack = new java.util.LinkedList<JmlEnhancedForLoop>();

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
            chk.checkNonVoid(tree.pos(), exprType);
            Type elemtype = types.elemtype(exprType); // perhaps expr is an array?
            if (elemtype == null) {
                // or perhaps expr implements Iterable<T>?
                Type base = types.asSuper(exprType, syms.iterableType.tsym);
                if (base == null) {
                    utils.error(tree.expr.pos(),
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
            if (tree.var.isImplicitlyTyped()) {
                Type inferredType = chk.checkLocalVarType(tree.var, elemtype, tree.var.name);
                setSyntheticVariableType(tree.var, inferredType);
            }
            attribStat(tree.var, loopEnv);
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

            boolean isArray = tree.expr.type.getTag() == TypeTag.ARRAY;
            if (isArray) {
                Type varType = tree.var.type;
                Type elemType = ((Type.ArrayType)tree.expr.type).getComponentType();
                if (isNonNullWithDefault(varType) && !isNonNullWithDefault(elemType)) {
                    utils.warning(tree.var, "jml.message", tree.var.name + " is non_null but the type of " + tree.expr + " allows null array elements");
                }
            }
        
        } finally {
            loopEnv.info.scope.leave();
            loopStack.remove(0);
            foreachLoopStack.remove(0);
        }
    }

    public boolean isNonNullWithDefault(Type type) {
        return specs.isNonNull(type, ((JCClassDecl)enclosingClassEnv.tree).sym);
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
        jmlMaker.at(e.pos);
        //Type boxed = Types.instance(context).boxedClass(vartype).type;
        Name valueof = names.fromString("valueOf");
        JCExpression s = jmlMaker.Select(jmlMaker.Type(boxedtype),valueof);
        s = jmlMaker.Apply(null,s,List.<JCExpression>of(e));
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
        
        jmlMaker.at(e.pos);
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
                return jmlMaker.Erroneous();
        }
        
        Name value = names.fromString(name);
        JCFieldAccess s = jmlMaker.Select(e,value);
        s.type = vartype;  // FIXME - no sym set? or is this a method type?
        JCMethodInvocation ss = jmlMaker.Apply(null,s,List.<JCExpression>nil());
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
        jmlMaker.at(tree.pos); // Sets the position until reset
        
        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
        ListBuffer<JCExpressionStatement> step = new ListBuffer<JCExpressionStatement>();

        // tree.indexDecl:     int  $$index$nnn = 0
        Name name = names.fromString("$$index$"+tree.pos);
        tree.indexDecl = makeVariableDecl(name,syms.intType,zeroLit,tree.pos);
        tree.indexDecl.sym.owner = tree.var.sym.owner;

        jmlMaker.at(tree.pos+1);
        JCIdent ident = jmlMaker.Ident(tree.indexDecl.sym);        
        JCExpressionStatement st = jmlMaker.Exec(jmlMaker.Unary(JCTree.Tag.PREINC,ident));  // ++ $$index;
        st.type = syms.intType;
        stats.append(tree.indexDecl);   // stats gets    int  $$index$nnn = 0;
        step.append(st);                // step  gets    ++ $$index$nnn;
        jmlMaker.at(tree.pos);

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
//        	Type t = runtimeClass.type;
//        	var tt = jmlMaker.Type(t);
//        	var eee = utils.nametree(Position.NOPOS, Position.NOPOS, "org.jmlspecs.runtime.Runtime.defaultEmpty", null);
        	
            JCFieldAccess sel = jmlMaker.Select(jmlMaker.Type(runtimeClass.type),defempty);
            JCExpression e = jmlMaker.Apply(List.<JCExpression>of(jmlMaker.Type(boxedVarType)),sel,List.<JCExpression>nil()); 
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
            
            jmlMaker.at(tree.pos+2);
            Name add = names.fromString("add");
            sel = jmlMaker.Select(jmlMaker.Ident(tree.valuesDecl),add);  // $$values$ppp.add
            //sel.type = 
            JCExpression ev = jmlMaker.Ident(tree.var);   // elem
            if (vartype.isPrimitive()) ev = autobox(ev,boxedVarType);
            JCMethodInvocation app = jmlMaker.Apply(null,sel,List.<JCExpression>of(ev));  // $$values$ppp.add(autobox(ev)); [autoboxing only if necessary]
            //app.type = tree.valuesDecl.type; // FIXME _ check this
            //
            
            jmlMaker.at(tree.pos+3);
            JCAssign asgn = jmlMaker.Assign(jmlMaker.Ident(tree.valuesDecl),app);
            asgn.type = asgn.lhs.type;
            step.append(jmlMaker.Exec(asgn));
            
            jmlMaker.at(tree.pos);

        }
        
        JCExpression cond = null;
        
        ListBuffer<JCStatement> bodystats = new ListBuffer<JCStatement>();

        JCExpression newvalue;
        JmlStatementLoopExpr inv = null;
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
            
            JCExpression arraylen = jmlMaker.Select(tree.expr,syms.lengthVar);
            cond = jmlMaker.Binary(JCTree.Tag.LT,ident,arraylen);
            cond.type = syms.booleanType;

            newvalue = jmlMaker.Indexed(tree.expr,ident); // newvalue :: expr[$$index]
            // FIXME newvalue.type = ???
            if (elemtype.isPrimitive() && !vartype.isPrimitive()) {
                newvalue = autobox(newvalue,vartype);
            } else if (!elemtype.isPrimitive() && vartype.isPrimitive()) {
                newvalue = autounbox(newvalue,vartype);
            }
            
            JCBinary invexpr = jmlMaker.Binary(JCTree.Tag.AND,jmlMaker.Binary(JCTree.Tag.LE,zeroLit,ident),jmlMaker.Binary(JCTree.Tag.LE,ident,arraylen));
            invexpr.type = invexpr.lhs.type = invexpr.rhs.type = syms.booleanType;
            inv = jmlMaker.JmlStatementLoopExpr(loopinvariantClause,invexpr);

            
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
            JCFieldAccess sel = jmlMaker.Select(jmlMaker.Ident(tree.iterDecl),hasNext);
            cond = jmlMaker.Apply(null,sel,List.<JCExpression>nil()); // cond :: $$iter . hasNext()
            cond.type = syms.booleanType;

            Name next = names.fromString("next");
            sel = jmlMaker.Select(jmlMaker.Ident(tree.iterDecl),next);
            newvalue = jmlMaker.Apply(null,sel,List.<JCExpression>nil());  // newvalue ::  $$iter . next()
            // FIXME - newvalue.type = ???
        }
        
        bodystats.append(jmlMaker.VarDef(tree.var.mods, tree.var.name, tree.var.vartype, newvalue)); // t = newvalue;
        // FIXME - assign types
        bodystats.append(tree.body);
        
        jmlMaker.at(tree.pos+1);
        Name sz = names.fromString("size");
        JCFieldAccess sel = jmlMaker.Select(jmlMaker.Ident(tree.valuesDecl),sz);
        // FIXME sel.type ??? invexpr2.type
        JCExpression invexpr2 = jmlMaker.Apply(null,sel,List.<JCExpression>nil());  // invexpr2 ::  $$values . size()
        JCBinary invexpr3 = jmlMaker.Binary(JCTree.Tag.AND,jmlMaker.Binary(JCTree.Tag.NE,nullLit,jmlMaker.Ident(tree.valuesDecl)),jmlMaker.Binary(JCTree.Tag.EQ,ident,invexpr2));
        invexpr3.type = invexpr3.lhs.type = invexpr3.rhs.type = syms.booleanType;
        JmlStatementLoopExpr inv2 = jmlMaker.JmlStatementLoopExpr(loopinvariantClause,invexpr3);
        
        jmlMaker.at(tree.pos);
        JCBlock block = jmlMaker.Block(0,bodystats.toList());
        block.endpos = (tree.body instanceof JCBlock) ? ((JCBlock)tree.body).endpos : tree.body.pos;
        
        JCForLoop forstatement = jmlMaker.ForLoop(List.<JCStatement>nil(),cond,step.toList(),block);
        JmlForLoop jmlforstatement = jmlMaker.JmlForLoop(forstatement,tree.loopSpecs);
        {
            ListBuffer<JmlStatementLoop> list = new ListBuffer<JmlStatementLoop>();
            list.append(inv2);
            if (inv != null) list.append(inv);
            if (tree.loopSpecs != null) list.appendList(tree.loopSpecs);
            jmlforstatement.loopSpecs = list.toList();
        }
        stats.append(jmlforstatement);

        JCBlock blockk = jmlMaker.Block(0,stats.toList());
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
    	MatchBindings condBindings = MatchBindingsComputer.EMPTY;
    	try {
            savedSpecOK = true;
            attribStats(tree.init, loopEnv);
            Env<AttrContext> labelenvi = env.dup(tree,loopEnv.info.dupUnshared());
            saveEnvForLabel(names.fromString("LoopInit"),labelenvi);
    		if (tree.cond != null) {
    			attribExpr(tree.cond, loopEnv, syms.booleanType);
    			// include condition's bindings when true in the body and step:
    			condBindings = matchBindings;
    		}
            loopEnv.tree = tree; // before, we were not in loop!
            saveEnvForLabel(names.fromString("LoopBodyBegin"),loopEnv);


            attribLoopSpecs(tree.loopSpecs, loopEnv);
            // FIXME - should this be before or after the preceding statement

            Env<AttrContext> bodyEnv = bindingEnv(loopEnv, condBindings.bindingsWhenTrue);
    		try {
    			bodyEnv.tree = tree; // before, we were not in loop!
    			attribStats(tree.step, bodyEnv);
    			attribStat(tree.body, bodyEnv);
    		} finally {
    			bodyEnv.info.scope.leave();
    		}
    		result = null;
            loopStack.remove(0);
    	}
    	finally {
    		loopEnv.info.scope.leave();
    	}
    	// FIXME - not sure where this came from
//    	if (!breaksOutOf(tree, tree.body)) {
//    		//include condition's body when false after the while, if cannot get out of the loop
//    		condBindings.bindingsWhenFalse.forEach(env.info.scope::enter);
//    		condBindings.bindingsWhenFalse.forEach(BindingSymbol::preserveBinding);
//    	}
    }

    public void visitJmlWhileLoop(JmlWhileLoop that) {
        loopStack.add(0,treeutils.makeIdent(that.pos, "loopIndex_" + (++loopIndexCount), syms.intType));
        attribLoopSpecs(that.loopSpecs,env);
        super.visitWhileLoop(that);
        loopStack.remove(0);
    }

    public void visitJmlStatementLoopExpr(JmlStatementLoopExpr that) {
        attribExpr(that.expression,env);
    }

    public void visitJmlStatementLoopModifies(JmlStatementLoopModifies that) {
        for (JCExpression st: that.storerefs) attribExpr(st,env);
    }

    public void visitJmlChoose(JmlChoose that) {
        // FIXME - fill in
    }

    public void visitJmlClassDecl(JmlClassDecl that) {
    	//if (that.sym != null && (env.enclMethod==null) && utils.isJML(that.mods.flags) && !this.attribJmlDecls) return;
        // Typically, classes are attributed by calls to attribClass and
        // then to attibClassBody and attribClassBodySpecs, but local
        // classes do end up here.
    	//if (org.jmlspecs.openjml.Utils.isJML()) System.out.println("VISITCLASSDECL " + that.sym);
        that.toplevel = (JmlCompilationUnit)enclosingClassEnv.toplevel;
        var saved = jmlresolve.allowJML();
        if (utils.isJML(that.mods)) jmlresolve.setAllowJML(true);

        if (env.enclMethod != null) {
        	// Local class
        	that.specsDecl = that;
        }        

        visitClassDef(that);
        var cspec = specs.getAttrSpecs(that.sym); // if not yet attributed, attribute the specs
        if (env.enclMethod != null && specs.status(that.sym).less(JmlSpecs.SpecsStatus.SPECS_ATTR)) {
        	utils.warning(that,"jml.message","UNEXPECTED RE-PUTTING LOCAL CLASS SPECS " + that.sym);
        	// Note: We need that.sym in order to register a local class's specs, but the local class
        	// is attributed as a method statement.
        	//((JmlEnter)enter).specsClassEnter(that.sym.owner, that, typeEnvs.get(that.sym), that);
        	specs.putSpecs(that.sym, cspec = new JmlSpecs.TypeSpecs(that, that, typeEnvs.get(that.sym)));
        	specs.getAttrSpecs(that.sym);
        	//FIXME - not at all sure about correctness of this branch
        }
        jmlresolve.setAllowJML(saved);
        
    }

    @Override
    public void visitClassDef(JCClassDecl tree) {
    	//if (org.jmlspecs.openjml.Utils.isJML()) System.out.println("VISITCLASSDEF " + tree.sym);
        // The superclass calls classEnter if the env is owned by a VAR or MTH.
        // But JML has the case of an anonymous class that occurs in a class
        // specification (e.g. an invariant), or in a method clause (so it is
        // owned by the method)
    	var prevSpecEnv = ((JmlEnter)enter).specEnv;
    	try {
    		((JmlEnter)enter).specEnv = env;
    		if (!env.info.scope.owner.kind.matches(KindSelector.VAL_MTH) && tree.sym == null) {
    			enter.classEnter(tree, env);
    		}
    		super.visitClassDef(tree);
    	} finally {
    		((JmlEnter)enter).specEnv = prevSpecEnv;
    	}
    }
    
    public void addClassInferredSpecs(ClassSymbol csym) {
        // Add inferred/default clauses
        var cspec = specs.get(csym);
        JCExpression[] initclauses = new JCExpression[5];
        var M = JmlTree.Maker.instance(context);
        var parent = csym;
//        for (var parent: utils.parents(csym, true)) {
            for (var sym: parent.getEnclosedElements()) {
                if (!(sym instanceof VarSymbol vsym)) continue;
                if (!vsym.isFinal()) continue;
                if (vsym.name.toString().equals("NaN")) continue; // Equality comparisons on NaN are squirrely
                if (!utils.isPrimitiveType(vsym.type.tsym)) continue; // FIXME - does not do constant Strings
                Object o = vsym.getConstValue();
                if (o == null) continue;
                int access = (int)(vsym.flags() & Flags.AccessFlags);
//                if (access == Flags.PRIVATE && sym != csym) continue;
                var literal = treeutils.makeLit(Position.NOPOS, vsym.type, o);
                if (vsym.type == syms.booleanType && o instanceof Integer i) literal = treeutils.makeBooleanLiteral(Position.NOPOS, 0 != (int)i);
                JCBinary e = treeutils.makeEquality(Position.NOPOS, M.Ident(vsym), literal); // FIXME - should put in positions
                e.lhs.type = vsym.type;
                e.type = syms.booleanType;
                int k = access;
//                if (true || utils.locallyJMLVisible(csym, parent, k)) { // FIXME - not sure the visibility test is corrrect
                    if (initclauses[k] == null) initclauses[k] = e;
                    else initclauses[k] = treeutils.makeAnd(initclauses[k], initclauses[k], e);
                    initclauses[k].type = syms.booleanType;
//                }
            }
//        }
        var id = org.jmlspecs.openjml.ext.TypeExprClauseExtension.invariantID;
        var kind = org.jmlspecs.openjml.ext.TypeExprClauseExtension.invariantClause;
        if (initclauses[Flags.PUBLIC] != null) {
            var cl = M.JmlTypeClauseExpr(M.Modifiers(Flags.PUBLIC|Flags.FINAL), id, kind, initclauses[Flags.PUBLIC]);
            cspec.clauses.add(cl);
        }
        if (initclauses[Flags.PRIVATE] != null) {
            var cl = M.JmlTypeClauseExpr(M.Modifiers(Flags.PRIVATE|Flags.FINAL), id, kind, initclauses[Flags.PRIVATE]);
            cspec.clauses.add(cl);
        }
        if (initclauses[Flags.PROTECTED] != null) {
            var cl = M.JmlTypeClauseExpr(M.Modifiers(Flags.PROTECTED|Flags.FINAL), id, kind, initclauses[Flags.PROTECTED]);
            cspec.clauses.add(cl);
        }
        if (initclauses[0] != null) {
            var cl = M.JmlTypeClauseExpr(M.Modifiers(0|Flags.FINAL), id, kind, initclauses[0]);
            cspec.clauses.add(cl);
        }
    }
    
    public JmlToken currentMethodPurity = null;

    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        var savedPurity = currentMethodPurity;
        currentMethodPurity = specs.determinePurity(that.sym);
        boolean prev = JmlResolve.instance(context).addAllowJML(utils.isJML(that));
        try {
            visitMethodDef(that);
        } catch (Exception e) {
            utils.error(that, "jml.internal", "Exception while attributing method: " + that);
            e.printStackTrace(System.out);
        } finally {
            currentMethodPurity = savedPurity; 
            JmlResolve.instance(context).setAllowJML(prev);
        }
    }
    
    public static class SpecialDiagnosticPosition extends com.sun.tools.javac.util.JCDiagnostic.SimpleDiagnosticPosition {
        String message;
        public SpecialDiagnosticPosition(String message) {
            super(-1);
            this.message = message;
        }
    }
    
    public JCExpression insertDefaultNullityInTypeArg(JCExpression arg, ModifierKind defaultNullity) {
        var tt = arg;
        if (tt instanceof JCTypeApply ttt) {
            var a = insertDefaultNullityInTypeArg(ttt.clazz, defaultNullity);
            var args = insertDefaultNullityInTypeArgs(ttt.arguments, defaultNullity);
            return a == ttt.clazz && args == ttt.arguments ? tt : jmlMaker.at(arg).TypeApply(a, args);
        } else if (tt instanceof JCAnnotatedType atype) {
            if (specs.findAnnotation(atype.annotations, Modifiers.NON_NULL) != null
                    || specs.findAnnotation(atype.annotations, Modifiers.NULLABLE) != null) return tt;
            
            JCAnnotation ann = utils.modToAnnotationAST(defaultNullity, arg.pos, arg.pos); // FIXME - better position
            atype.annotations = atype.annotations.append(ann);
            return tt;
        } else {
            JCAnnotation ann = utils.modToAnnotationAST(defaultNullity, arg.pos, arg.pos); // FIXME - better position
            return jmlMaker.at(arg).AnnotatedType(List.<JCAnnotation>of(ann), arg);
       }
    }
    
    public List<JCExpression> insertDefaultNullityInTypeArgs(List<JCExpression> args, ModifierKind defaultNullity) {
        ListBuffer<JCExpression> ntypes = new ListBuffer<>();
        boolean change = false;
        for (var a: args) {
            var t = insertDefaultNullityInTypeArg(a, defaultNullity);
            change |= (t != a);
            ntypes.add(t);
        }
        return change ? ntypes.toList() : args;
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
        if (utils.isJML(that.mods.flags) && !this.attribJmlDecls) return;
        if (utils.verbose()) utils.note("Attributing " + that.vartype + " " + that.name + " " + that.getClass());
        if (env.enclMethod != null) {
            if (that.vartype instanceof JCTypeApply ft) {
                var nn = specs.defaultNullity(env.enclClass.sym);
                var nt = insertDefaultNullityInTypeArgs(ft.arguments, nn);
                if (nt != ft.arguments) ft.arguments = nt;
            }
        	if (utils.verbose()) utils.note("Adjusted nullity " + that);
        }
        JavaFileObject prevSource = null;
        boolean isReplacementType = that.jmltype;
        boolean prev = ((JmlResolve)rs).setAllowJML(utils.isJML(that.mods) || isReplacementType);
        try {
            if (that.source() != null) prevSource = log.useSource(that.source());

            // If there is a .jml file containing the specifications, then just use those instead of the annotations in the
            // .java file. FIXME - really we should always be looking in the specs database, rather than modifying the ast
            JCModifiers originalMods = that.mods;
            JCModifiers newMods = originalMods;
            if (that.specsDecl != null) newMods = that.mods = that.specsDecl.mods;

            // FIXME - we should not need these two lines I think, but otherwise we get NPE faults on non_null field declarations
            attribAnnotationTypes(that.mods.annotations,env); 
            annotate.flush(); // FIXME _ this does not do anything if annotations are blocked
            for (JCAnnotation a: that.mods.annotations) a.type = a.annotationType.type;

            if (that.originalVartype != null && that.originalVartype.type == null) attribType(that.originalVartype,env);
            if (env.info.lint == null) { // FIXME: Without this we crash in Attr, but how is this handled elsewhere?
            	Env<AttrContext> lintEnv = env;
                while (lintEnv.info.lint == null)
                    lintEnv = lintEnv.next;
                env.info.lint = lintEnv.info.lint;
            }

            visitVarDef(that);
            
            checkVarDecl(that); // FIXME - why isn't this part of visitVarDef?
            
            if (that.init == null && (that.sym.flags() & Flags.PARAMETER) == 0 
                    && !utils.isModel(that.sym)
                    && utils.isExtensionValueType(that.type)) {
                String full = that.type.toString();
                int k = full.indexOf('<');
                var part = (k < 0 ? full : full.substring(0, k));
                String name = part.substring(part.lastIndexOf('.')+1);
                if (name.equals("string")) {
                    var id = jmlMaker.at(that.pos).Ident("\\" + name);
                    var fa = jmlMaker.at(that.pos).Select(id, names.fromString("empty"));
                    var e = jmlMaker.at(that.pos).Apply(null, fa, List.<JCExpression>nil());
                    that.init = e;
                    attribExpr(e,env); // FIXME - spec env?
                } else if (name.endsWith("seq") || name.endsWith("set") || name.endsWith("map")) {
                    // FIXME - THis (and string above) should be delgated to makeZeroEquivalentLit
                    var id = jmlMaker.at(that.pos).Ident("\\" + name);
                    id.type = that.type;
                    id.sym = that.type.tsym;
                    var fa = jmlMaker.at(that.pos).Select(id, names.fromString("empty"));
                    var e = jmlMaker.at(that.pos).Apply(null, fa, List.<JCExpression>nil());
                    // FIXME - do we need the method symbol?
                    // FIXME - do we need to add the type arguments?
                    //e.type = that.type;
                    that.init = e;
                    attribExpr(e,env); // FIXME - spec env?
                } else {
                    that.init = treeutils.makeZeroEquivalentLit(that, that.type);
                }
            }

            // FIXME - should this be checking for error types?
            if (that.init != null && that.init.type != null && !that.init.type.isErroneous() &&
                    utils.isExtensionValueType(that.init.type) && !utils.isExtensionValueType(that.type)) {
                //System.out.println(that.init.type + " TO " + that.type + " " + that.init + " " + that.init.getClass());
                utils.error(that, "jml.message", "A JML primitive type may not be assigned or cast to a non-JML type");
            }

        	if (env.enclMethod != null) {
                if (that.vartype instanceof JCTypeApply) {
                	var ft = (JCTypeApply)that.vartype;
                	ListBuffer<JCExpression> ntypes = new ListBuffer<>();
        			for (var t: ft.arguments) {
        				if (t instanceof JCAnnotatedType && t.type instanceof Type.TypeVar) {
        					ntypes.add( ((JCAnnotatedType)t).underlyingType);
        				} else {
        					ntypes.add(t);
        				}
           			}
        			ft.arguments = ntypes.toList();
                } // FIXME - but sym is still now out of synch
        	}

        	//((JmlMemberEnter)memberEnter).dojml = false;
            if (that.sym == null) return; // Duplicate to be removed 
            // Anonymous classes construct synthetic members (constructors at least)
            // which are not JML nodes.
            //FieldSpecs fspecs = specs.getSpecs(that.sym);
            
            // We do the checking of in and maps clauses after all fields and methods have been attributed
            //if (fspecs != null) for (JmlTypeClause spec:  fspecs.list) spec.accept(this);

            ModifierKind nullness = specs.defaultNullity(enclosingClassEnv.enclClass.sym);
            if (!that.type.isPrimitive()) {
                if (that.type.tsym == datagroupClass) {
                    nullness = Modifiers.NULLABLE;                    
                    // OPENJML - FIXME - wrapped the below line with TypeCompound -- not sure about the final null
                    Attribute.TypeCompound a = new Attribute.TypeCompound(new Attribute.Compound(nullableAnnotationSymbol.type,List.<Pair<MethodSymbol,Attribute>>nil()), null);
                    JCAnnotation an = jmlMaker.at(that).TypeAnnotation(a);
                    an.type = an.annotationType.type;
                    ((JmlTree.JmlAnnotation)an).sourcefile = that.sourcefile;
                    ((JmlTree.JmlAnnotation)an).kind = nullness;
                    that.mods.annotations = that.mods.annotations.append(an);
                    // that.mods == fspecs.mods
                    that.mods.flags |= Flags.FINAL; // datagroup declarations are implicitly final
                    if (that.init != null) {
                        utils.error(that.init, "jml.message", "\\datagroup declarations may not have initializers");
                    }
                    //that.init = jmlMaker.at(that).Literal(TypeTag.BOT,null);
                    //that.init.type = datagroupClass.type;
                } else if (utils.hasMod(that.mods,Modifiers.NULLABLE) || specs.isNonNullNoDefault(that.sym)) { 
                    nullness = Modifiers.NON_NULL;
                } else if (utils.hasMod(that.mods,Modifiers.NULLABLE) || specs.isNullableNoDefault(that.sym)|| skipDefaultNullity) {
                    nullness = Modifiers.NULLABLE;
//                } else {
//                    Symbol s = (nullness == Modifiers.NON_NULL) ? nonnullAnnotationSymbol : nullableAnnotationSymbol;
//                    Attribute.Compound a = new Attribute.Compound(s.type,List.<Pair<MethodSymbol,Attribute>>nil());
//                    that.sym.appendAttributes(List.<Compound>of(a));
//                    JCAnnotation an = jmlMaker.at(that).Annotation(a);  // FIXME - needs a position and a source - we should get the NonNullByDefault if possible
//                    ((JmlTree.JmlAnnotation)an).sourcefile = that.sourcefile;
//                    ((JmlTree.JmlAnnotation)an).kind = nullness;
//                    an.type = an.annotationType.type;
//                    var ft = that.vartype;
//                    while (ft instanceof JCTree.JCTypeApply ftp) ft = ftp.clazz;
//                    if (ft instanceof JCIdent id) {
//                        that.mods.annotations = that.mods.annotations.append(an);
//                    } else if (ft instanceof JCFieldAccess fta) {
//                        System.out.println("FT " + ft + " " + ft.getClass());
//                    } else {
//                    	// FIXME ???
//                        that.mods.annotations = that.mods.annotations.append(an);
//                    }
                }
            }
            //        if (newMods != originalMods) for (JCAnnotation a: originalMods.annotations) { a.type = attribType(a,env); }

            // Check the mods after the specs, because the modifier checks depend on
            // the specification clauses being attributed

            if (that.sym.owner instanceof MethodSymbol ms) {
                // vars owned by the class are fields; they have already had specs put during Entering
                // so have formal parameters
                var s = specs.getFormal(that.sym);
                if (s == null) {
                    specs.putSpecs(that.sym, that, new JmlSpecs.LocalSpecs(that, nullness == Modifiers.NON_NULL, ms));
                }
            }
            specs.getAttrSpecs(that.sym); // Attributing specs, if not already done // Also checks the modifiers

            if (that.sym.owner.isInterface()) {
                if (isModel(that.mods)) {
                    if (!isStatic(that.mods) && !isInstance(that.mods)) {
                        utils.warning(that,"jml.message","Model fields in an interface should be explicitly declared either static or instance: " + that.name);
                    }
                }
            }
            //        if (that.specsDecl != null) {
            //            that.mods.annotations = that.specsDecl.mods.annotations;
            //        }
            
            // non-final model fields should not have initializers
            if (that.init != null && isModel(that.mods) && (that.mods.flags & Flags.FINAL) == 0) {
                utils.warning(that.init, "jml.message", "A non-final model field may not have an initializer");
                that.init = null;
            }
            
            // that.init.type can be null if there was an error already in attributing that.init
            if (that.init != null && that.init.type != null &&
                    utils.isExtensionValueType(that.type) && !types.isSameType(that.type, that.init.type)) {
                if (types.isSameType(that.type, JmlPrimitiveTypes.stringTypeKind.getType(context))) {
                    JmlPrimitiveTypes.stringTypeKind.typecheck(this, that, env);
                }
            }
            if (that.init != null && !utils.isJML(that.mods.flags)) {
                Object v = that.sym.getConstValue();
                JCExpression initExpr = that.init;
                if (v != null && initExpr instanceof JCLiteral lit) {
                    if (!v.equals(lit.value)) {
                        //System.out.println("INIT " + v.getClass() + " " + v + " " + lit.value.getClass() + " " + lit.value + " " + v.equals(lit.value));
                        utils.error(that, "jml.message", "Initializer does not match compiled value: " + lit + " vs. " + v);
                    }
                }
                //if (v instanceof Double) System.out.println("NAN " + String.format("0x%16X", Double.doubleToLongBits(Double.NaN)));
                //if (v instanceof Float) System.out.println("NAN " + String.format("0x%08X", Float.floatToIntBits(Float.NaN)));
            }
        } catch (PropagatedException e) {
        	throw e;
        } catch (Exception e) {
        	utils.error(that, "jml.internal", "Exception attributing VariableDecl " + that);
        	e.printStackTrace(System.out);
        	throw new PropagatedException(new RuntimeException(e));
        } finally {
            ((JmlResolve)rs).setAllowJML(prev);
            if (prevSource != null) log.useSource(prevSource);
            //if (utils.verbose()) utils.note("    Attributed " + that.sym.owner + " " + that.sym); // that.sym may be null
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
        Type savedResult = result;
        if (that instanceof JmlLambda) {
            JmlLambda jmlthat = (JmlLambda) that;
            if (jmlthat.jmlType != null) {
                boolean prev = jmlresolve.setAllowJML(true);
                if (that.type.isErroneous()) {
                    attribTree(jmlthat.jmlType, env, new ResultInfo(KindSelector.TYP, syms.objectType));
                } else {
                    // Issues an error if the type of jmlType is not a subtype of 
                    // that.type - which is precisely the check that we want,
                    // so we don't need to retest.
                    Type t = attribTree(jmlthat.jmlType, env, new ResultInfo(KindSelector.TYP, that.type));
                    if (!t.isErroneous()) {
                        that.type = t;
                    }
                }
                jmlresolve.setAllowJML(prev);
            }
        } else {
            // FIXME _ ERROR
        }
        result = savedResult;
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
    // Overridden to make public
    @Override
    public KindSelector attribArgs(KindSelector initialKind, List<JCExpression> trees, Env<AttrContext> env, ListBuffer<Type> argtypes) {
        return super.attribArgs(initialKind, trees, env, argtypes);
    }
    
    public KindSelector attribArgs(List<JCExpression> trees, Env<AttrContext> env, ListBuffer<Type> argtypes) {
        return super.attribArgs(KindSelector.VAL, trees, env, argtypes);
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
            KindSelector kind = KindSelector.VAL; // FIXME - could also be POLY
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
    
//    public void jmlerror(int begin, int end, String key, Object... args) {
//        utils.error(new Utils.DiagnosticPositionSE(begin,end-1),key,convertErrorArgs(args));
//    }
//
//    public void jmlerror(DiagnosticPosition tree, String key, Object... args) {
//        utils.error(new Utils.DiagnosticPositionSE(tree.getPreferredPosition(),tree.getEndPosition(log.currentSource().getEndPosTable())),key,convertErrorArgs(args));
//    }
//    
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
        
        @SuppressWarnings("unchecked")
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
        
        public static class RCheckEx extends RuntimeException {
			private static final long serialVersionUID = 1L;
        }
        
        boolean checkInternal;
        List<JCVariableDecl> decls;
        
        public RACCheck(List<JCVariableDecl> decls) {
        	super(null);
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
            if (that.kind == resultKind) {
                // external
                if (checkInternal) throw new RCheckEx();
            }
        }
        
        @Override
        public void visitJmlMethodInvocation(JmlMethodInvocation that) {
            if (that.kind == oldKind || that.kind == pastKind || that.kind == preKind) {
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
                IJmlClauseKind kind = ((JmlSingleton)tree).kind;
                if (kind == informalCommentKind) return true;
                if (kind == resultKind) {
                    JCTree.JCMethodDecl md = enclosingMethodEnv.enclMethod;
                    JCTree res = md.getReturnType(); 
                    TypeTag t = res.type.getTag();
                    if (t == TypeTag.BOOLEAN || t == TypeTag.INT || t == TypeTag.LONG || t == TypeTag.SHORT || t == TypeTag.CHAR || t == TypeTag.BYTE) return true;
                    return false;
                }
            }
            utils.error(tree,"jml.internal", "Unimplemented option in JmlAttr:isBooleanOrNumeric -- "  + tree.getClass());
            return false;
        }
        return super.isBooleanOrNumeric(env,tree);
    }

    public MethodSymbol makeInitializerMethodSymbol(long flags, Env<AttrContext> env) {
        JCTree tree = null;
        MethodSymbol fakeOwner = new MethodSymbol(flags | BLOCK |
                env.info.scope.owner.flags() & STRICTFP, names.empty, new Type.JCVoidType(),
                env.info.scope.owner);
        Env<AttrContext> localEnv =
                env.dup(tree, env.info.dup(env.info.scope.dupUnshared(fakeOwner)));
        if ((flags & STATIC) != 0) localEnv.info.staticLevel++;
        return fakeOwner;
    }
    
    public boolean interpretInPreState(DiagnosticPosition pos, IJmlClauseKind kind) {
        if (kind == ensuresClauseKind ||
                kind == signalsClauseKind ||
                kind == signalsOnlyClauseKind) return false;
        if (kind instanceof IJmlClauseKind.MethodSpecClauseKind) return true;
        return false;
    }
    
    @Override
    public Type check(final JCTree tree, final Type found, final Kinds.KindSelector ownkind, final ResultInfo resultInfo) {
        tree.type = found;
        if (resultInfo.pt instanceof JmlListType) {
            return found;
        }
        if (found == null) {
            System.out.println("FOUND TYPE IS NULL " + resultInfo.pt + " " + tree);
            Utils.dumpStack();
            return (tree.type = types.createErrorType(resultInfo.pt));
        }
        if (utils.isExtensionValueType(resultInfo.pt)) {
        	// We should check for conversions from found to resultInfo.pt,
        	// but currently no such implicit conversions are allowed
            if (types.isSameType(resultInfo.pt, utils.extensionValueType("string"))
                    && types.isSameType(found, syms.stringType)) {
                return found; // FIXME - explain why this test for strings
            }
            if (types.isSameType(resultInfo.pt, found)) return found;

            var BIGINT = JmlPrimitiveTypes.bigintTypeKind.getType(context);
            if (resultInfo.pt.tsym == BIGINT.tsym) {
                if (jmltypes.isAnyIntegral(found)) return resultInfo.pt;
                if (found.toString().contains("BigInteger")) return resultInfo.pt;
                if (tree instanceof JCConditional cc) {
                    if (jmltypes.isAnyIntegral(cc.truepart.type) && jmltypes.isAnyIntegral(cc.falsepart.type)) return resultInfo.pt;
                }
            }
            var REAL = JmlPrimitiveTypes.realTypeKind.getType(context);
            if (resultInfo.pt.tsym == REAL.tsym) {
                if (jmltypes.isNumeric(found)) return resultInfo.pt;
                if (tree instanceof JCConditional cc) {
                    if (jmltypes.isNumeric(cc.truepart.type) && jmltypes.isNumeric(cc.falsepart.type)) return resultInfo.pt;
                }
            }
            if (found.isParameterized() == resultInfo.pt.isParameterized()) {
            	if (found.tsym == resultInfo.pt.tsym) {
            		// There are cases where two parameterized types with type variable parameters appear equal
            		// but test unequal. We'll resort to string comparison for now
            		if (found.toString().equals(resultInfo.pt.toString())) return found;
            	}
            }
            
            utils.error(tree.pos(), "jml.message",
            		"illegal conversion: " + found +
            		" to " + resultInfo.pt.toString().replace("org.jmlspecs.lang.","\\")); // FIXME - use a stored name somewhere
            return (tree.type = types.createErrorType(found));
        }
        return super.check(tree, found, ownkind, resultInfo);
    } 
    
    public Env<AttrContext> addStatic(Env<AttrContext> env) {
    	env.info.staticLevel++;
    	return env;
    }
    
    public int countStatic(Env<AttrContext> env) {
        return env.info.staticLevel;
    }
    
    public Env<AttrContext> removeStatic(Env<AttrContext> env) {
    	env.info.staticLevel--;
    	return env;
    }
    
    @Override
    protected void saveMethodEnv(MethodSymbol msym, Env<AttrContext> env) {
//    	if (org.jmlspecs.openjml.Main.useJML && !utils.rac && !env.enclClass.sym.isAnnotationType()) {
//    		String s = env.toplevel.packge.toString();
//    		if (s.startsWith("java.") || s.startsWith("javax.") || s.startsWith("com.sun") || s.startsWith("sun.tools")) return false;
//    	}
    	specs.get(msym).setEnv(env);
    	super.saveMethodEnv(msym,env);
    }
    
    static public void printEnv(Env<AttrContext> env, String mark) {
		System.out.print("PRINTING ENV " + mark + ": ");
		if (env == null) System.out.print(" <null> ");
		else for (Symbol s: env.info.scope.getSymbols()) System.out.print(s + " " );
		System.out.println("!!END");
    }
    
    public void attrSpecs(MethodSymbol msym, Env<AttrContext> specenv) {
    	int nerrors = log.nerrors;
		var saved = this.env;
		var savedEnclosingClassEnv = this.enclosingClassEnv;
		var savedEnclosingMethodEnv = this.enclosingMethodEnv;
		jmlenv = jmlenv.pushInit();
		JmlSpecs.MethodSpecs sp = null;
		JmlSpecs.SpecsStatus stat = JmlSpecs.SpecsStatus.SPECS_ATTR;
		specs.setStatus(msym, stat); // Set status at the beginning of the work to avoid recursive calls
		JavaFileObject prev = null;
		try {
    		if (utils.verbose()) utils.note("Attributing specs for " + msym.owner + " " + msym);
    		specs.getAttrSpecs((ClassSymbol)msym.owner);
    		sp = specs.getLoadedSpecs(msym);
    		if (sp == null) {
    			if (utils.verbose()) utils.note("Specs are null for " + msym.owner + "." + msym);
    			return;
    		}
    		//if (sp.specsEnv == null) return;  // Default specs? already attributed? -- e.g. default constructor with no source
    		if (sp.specDecl != null) prev = log.useSource(sp.specDecl.sourcefile);
    		this.env = this.enclosingMethodEnv = specenv == null ? sp.specsEnv : specenv;
			this.enclosingClassEnv = specs.getLoadedSpecs(msym.enclClass()).specsEnv;
			//System.out.println("THISENV " + this.env + " " + this.env.info.scope);
    		specs.getLoadedSpecs((ClassSymbol)msym.owner); // Checking all the type clauses and declarations, if not already done
            //System.out.println("ATTR--METHOD_SPECS " + msym.owner + " " + msym + " " +(this.env.enclMethod==null));
    		jmlenv.enclosingMethodDecl = sp.specDecl;
    		jmlenv.inPureEnvironment = true;
    		if (utils.verbose()) utils.note("    Lint " + msym.owner + " " + msym + " " + (sp.specsEnv.info.lint != null));
    		if (utils.verbose()) utils.note("    Specs are " + sp);
    		var biter = msym.params.iterator();
    		boolean prevAllowJML = jmlresolve.setAllowJML(true);
    		VarSymbol savedSecret = currentSecretContext;
    		VarSymbol savedQuery = currentQueryContext;
    		try {
    			currentSecretContext = sp.secretDatagroup;
    			currentQueryContext = null;
    			if (sp != null) {
    				//this.env = sp.specsEnv;
    				// FIXME    				deSugarMethodSpecs(msym,sp); // FIXME - needed?
        			var specDecl = sp.specDecl;
    				checkMethodModifiers(msym, sp.javaDecl);

//        			if (specDecl != null) {
//        				boolean isJML = utils.isJML(specDecl);
//        				boolean isOwnerJML = utils.isJML(msym.owner.flags());
//        				boolean isModel = utils.hasMod(specDecl.mods, Modifiers.MODEL);
//        				if (isOwnerJML && isModel) {
//        					utils.error(specDecl.sourcefile, specDecl, "jml.message", "A model type may not contain model declarations: " + specDecl.name + " in " + msym.owner);
//        					// Attempt recovery by removing the offending annotation
//        					utils.removeAnnotation(specDecl.mods,  Modifiers.MODEL);
//        				} else if (!isJML && isModel ) {
//        					var pos = utils.locMod(specDecl.mods, Modifiers.MODEL);
//        					utils.error(specDecl.sourcefile, pos, "jml.message", "A Java method declaration must not be marked model: " + specDecl.name + " (owner: " + msym.owner +")");
//        					// Attempt recovery by removing the offending annotation
//        					utils.removeAnnotation(specDecl.mods,  Modifiers.MODEL);
//        				} else if (isJML && !isModel && !isOwnerJML) {
//        					utils.error(specDecl.sourcefile, specDecl, "jml.message", "A JML method declaration must be marked model: " + specDecl.name + " (owner: " + msym.owner +")");
//        					// Attempt recovery by adding a model annotation
//        					JmlTreeUtils.instance(context).addAnnotation(specDecl.mods, specDecl.mods.pos, specDecl.mods.pos, Modifiers.MODEL, null);
//        				}
//        			}

        			if (specDecl != null && utils.isSpecFile(specDecl.sourcefile) && !utils.isJML(specDecl) && !utils.isGeneratedConstructor(specDecl.sym) && specDecl.body != null) {
        			    // No body if (a) declared in a .jml file (b) is not a model method (c) and not a generated constructor
        				utils.error(specDecl.sourcefile, specDecl.body, "jml.message", "The specification of the method " + ((ClassSymbol)specDecl.sym.owner).flatname + "." + specDecl.sym + " must not have a body");
        			}
        			var jmethod = sp;
    	            if (sp.cases != null) { // FIXME - should we get the specs to check from JmlSpecs?
    	                // Check the also designation
    	                if (sp.cases.cases != null && jmethod.cases.cases.size() > 0) {
    	                    JmlSpecificationCase spec = jmethod.cases.cases.get(0);
    	                    boolean specHasAlso = spec.also != null;
    	                    var parents = utils.parents(msym,false);
    	                    boolean methodOverridesOthers = !parents.isEmpty();
    	                    if (specHasAlso && !methodOverridesOthers) {
//    	                        if (!jmethod.name.toString().equals("compareTo") && !jmethod.name.toString().equals("definedComparison")) {// FIXME
    	                            if (JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
    	                                utils.error(spec.alsoPos, "jml.extra.also", specDecl.name.toString() );
    	                            } else {
    	                                utils.warning(spec.alsoPos, "jml.extra.also", specDecl.name.toString() );
    	                            }
 //   	                        }
    	                    } else if (!specHasAlso && methodOverridesOthers) {
    	                    	var base = parents.get(0); // Expected to be the top of the override chain
    	                    	String s = msym.owner + "." + msym + " overrides " + base.owner + "." + base;
    	                        if (JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
    	                            utils.warning(spec.source(), spec,  
    	                            		"jml.missing.also", specDecl.name.toString(), s);
    	                        } else {
    	                            utils.warning(spec.source(), spec, 
    	                            		"jml.missing.also", specDecl.name.toString(), s);
    	                        }
    	                    }
    	                }
    	            }
    	            
    	            if (specDecl != null && specDecl.body == null) {
    	                var t = utils.findModifier(sp.mods, Modifiers.INLINE);
    	                if (t != null) {
    	                    utils.error(t, "jml.message", "Cannot inline a method that does not have a body");
    	                }
    	            }

    				sp.cases.accept(this); // FIXME - use desugared?
    				deSugarMethodSpecs(msym,sp);
    			}
    		} catch (SpecificationException e) {
    			// error already reported
    			stat = JmlSpecs.SpecsStatus.ERROR;
//    			System.out.println("SPECIFICATIONEXCEPTION");
//    			e.printStackTrace(System.out);
//    			Utils.dumpStack();
    		} catch (JmlInternalAbort|PropagatedException e) {
    			throw e;
    		} catch (Exception e) {
    			System.out.println("EXCEPTION");
    			e.printStackTrace(System.out);
    			Utils.dumpStack();
    			stat = JmlSpecs.SpecsStatus.ERROR;
    			if (e instanceof PropagatedException) throw e;
    			utils.note("Exception while attributing specs for " + msym);
    			throw new PropagatedException(new RuntimeException(e));
    		} finally {
    			specs.setStatus(msym, stat);
    			this.env = saved;
    			currentSecretContext = savedSecret;
    			currentQueryContext = savedQuery;
    			jmlresolve.setAllowJML(prevAllowJML);
    		}
//    		if (JmlCompiler.instance(context).errorCount() > 0) {
//    			String msg = "Aborting because of type or parse error in specs: " + msym.owner + "." + msym;
//    			utils.error("jml.message", msg);
//    			throw new SpecificationException();
//    		}
    		utils.note(true, "    Attributed specs for " + msym.owner + " " + msym);
    	} catch (SpecificationException e) {
    		throw new JmlInternalAbort();
    	} catch (JmlInternalAbort|PropagatedException e) {
    		// continue to clean exit - already reported
    		throw e;
    	} catch (Exception e) {
    		utils.unexpectedException("Exception while attributing method specs: " + msym.owner + "." + msym, e);
    	} finally {
    		this.enclosingClassEnv = savedEnclosingClassEnv;
    		this.enclosingMethodEnv = savedEnclosingMethodEnv;
    		jmlenv = jmlenv.pop();
			if (prev != null) log.useSource(prev);
    		if (nerrors != log.nerrors) {
    			specs.setStatus(msym, JmlSpecs.SpecsStatus.ERROR);
//    			System.out.println("SERRORS" + msym);
//    			Utils.dumpStack();
    			//System.out.println("ATTRSPECS-DONE " + msym.owner + " " + msym );
    		}
    	}
    }
    
    public void attrTypeClause(JmlTypeClause cl, Env<AttrContext> env, ResultInfo ri) {
    	if (cl == null) return;
    	var prev = log.useSource(cl.source());
    	try {
    		attribTree(cl, env, ri);
    	} catch (Exception e) {
    		utils.error(cl, "jml.internal", "Exception while attributing type clause: " + cl);
    		e.printStackTrace(System.out);
    	} finally {
    		log.useSource(prev);
    	}
    }
    
    public void attrSpecs(JmlSpecs.BlockSpecs bspecs) {
    	//System.out.println("ATTRIBUTING BLOCK SPEC " + bspecs.specCases + " "  + bspecs.status);
    	//System.out.println("ATTRIBUTING BLOCK SPEC-ENV " + bspecs.specsEnv.enclClass + " "  + bspecs.specsEnv.info.staticLevel);
    	if (!bspecs.status.less(JmlSpecs.SpecsStatus.SPECS_ATTR)) return;
    	var prevEnv = this.env;
    	var prevMEnv = this.enclosingMethodEnv;
    	var prevCEnv = this.enclosingClassEnv;
    	this.env = bspecs.specsEnv;
    	this.enclosingMethodEnv = null;
    	this.enclosingClassEnv = env;
    	try {
        	if (bspecs.specCases != null) for (var c: bspecs.specCases.cases) {
    			//System.out.println("CASE " + c);
    			visitJmlSpecificationCase(c);
    		}
    	} finally {
    		this.env = prevEnv;
    		this.enclosingMethodEnv = prevMEnv;
    		this.enclosingClassEnv = prevCEnv;
    		bspecs.status = JmlSpecs.SpecsStatus.SPECS_ATTR;
    	}
    }
    
    public void attrSpecs(ClassSymbol csym) {
    	boolean isLocal = !(csym.owner instanceof ClassSymbol || csym.owner instanceof PackageSymbol);
		var savedEnclosingClassEnv = this.enclosingClassEnv;
		var savedEnv = this.env;
		jmlenv = jmlenv.pushInit();
		var saved = jmlresolve.allowJML();
		try {
			jmlresolve.setAllowJML(true);
    		if (utils.verbose()) utils.note("Attributing specs for " + csym);
    		TypeSpecs tspecs = specs.getLoadedSpecs(csym);
    		specs.setStatus(csym, JmlSpecs.SpecsStatus.SPECS_ATTR);
    		ResultInfo ri = new ResultInfo(KindSelector.VAL_TYP, Type.noType);
    		this.env = tspecs.specsEnv;
    		this.enclosingClassEnv = enter.getEnv(csym);
    		jmlenv.inPureEnvironment = true;
     		checkClassMods(csym, tspecs.javaDecl, tspecs.specDecl, tspecs, tspecs.specsEnv);
    		boolean hasStaticInit = false;
    		boolean hasInstanceInit = false;
    		for (var clause: tspecs.clauses) {
    			attrTypeClause(clause, tspecs.specsEnv, ri);
    		}
    		attrTypeClause(tspecs.initializerSpec, tspecs.specsEnv, ri);
    		attrTypeClause(tspecs.staticInitializerSpec, tspecs.specsEnv, ri);
    	} catch (Exception e) {
    		utils.error("jml.message", "Exception while attributing class specs: " + csym);
    		e.printStackTrace(System.out);
    		JmlSpecs.instance(context).setStatus(csym, JmlSpecs.SpecsStatus.ERROR);
    	} finally {
			jmlresolve.setAllowJML(saved);
    		this.enclosingClassEnv = savedEnclosingClassEnv;
    		this.env = savedEnv;
    		jmlenv = jmlenv.pop();
    		if (utils.verbose()) utils.note("    Attributed specs for " + csym + specs.status(csym));
    	}
    }

    public void attrSpecs(VarSymbol vsym) {
    	var savedEnv = this.env;
    	if (vsym.enclClass() == null) System.out.println("NULL CSYM " + vsym);
		TypeSpecs cspecs = specs.getLoadedSpecs(vsym.enclClass());
		FieldSpecs fspecs = specs.getLoadedSpecs(vsym);
		if (debugAttr) System.out.println("Attributing specs for " + vsym.owner + " " + vsym + " " + (fspecs != null));
		ResultInfo ri = new ResultInfo(KindSelector.VAL_TYP, vsym.type);
		var stat = JmlSpecs.SpecsStatus.SPECS_ATTR;
		JmlSpecs.instance(context).setStatus(vsym, stat);
		int nerrors = log.nerrors;
		if (fspecs != null) {
			// The following copied from Attr.visitVarDef
//	        Lint lint = env.info.lint == null ? null : env.info.lint.augment(vsym);
//	        Lint prevLint = chk.setLint(lint);
            Env<AttrContext> initEnv = memberEnter.initEnv(fspecs.decl, cspecs.specsEnv); // FIXME - interface instance vars are not static
//            initEnv.info.lint = lint;
//            initEnv.info.enclVar = vsym;
            var prevSource = fspecs.decl == null ? null : log.useSource(fspecs.decl.sourcefile);            
    		jmlenv = jmlenv.pushCopy();
    		jmlenv.jmlVisibility = -1;
            boolean prevAllow = ((JmlResolve)rs).setAllowJML(utils.isJML(vsym.flags()));
            if (fspecs.decl != null && fspecs.decl.init != null && fspecs.decl.init.type == null) {
        		ResultInfo rri = new ResultInfo(KindSelector.VAL_TYP, vsym.type);
        		jmlenv.inPureEnvironment = utils.isJML(fspecs.decl.mods);
            	Type t = fspecs.decl.init.type = attribTree(fspecs.decl.init, initEnv, rri);
            	if (t.isErroneous()) stat = JmlSpecs.SpecsStatus.ERROR;
            }
            ((JmlResolve)rs).setAllowJML(prevAllow);

            if (!vsym.type.isErroneous()) {
            	this.env = cspecs.specsEnv;
        		//checkVarDecl(fspecs.decl);
    			for (var cl: fspecs.list) {
    				var prev = log.useSource(cl.source());
    				try {
    					jmlenv.inPureEnvironment = true;
    					if (!utils.isJMLStatic(vsym)) initEnv.info.staticLevel = 0;
    					attribTree(cl, initEnv, ri);
    				} catch (Exception e) {
    					utils.error(cl, "jml.internal", "Exception while attributing field clause: " + cl);
    					e.printStackTrace(System.out);
    				} finally {
    					log.useSource(prev);
    				}
    			}
            }
    		this.env = savedEnv;
        	jmlenv = jmlenv.pop();
			if (prevSource != null) log.useSource(prevSource);
//            chk.setLint(prevLint);
		}
		if (log.nerrors > nerrors) stat = JmlSpecs.SpecsStatus.ERROR;
		JmlSpecs.instance(context).setStatus(vsym, stat);
		if (utils.verbose()) utils.note("    Attributed specs for " + vsym.owner + " " + vsym + " " + stat);
    }

    public static class JmlArgumentAttr extends ArgumentAttr implements IJmlVisitor {
    	
    	public JmlArgumentAttr(Context context) {
    		super(context);
    	}
    	
    	public static void preRegister(Context context) {
    		new JmlArgumentAttr(context);// self registers
    	}
    	
        public void visitBlock(JmlBlock tree)                          { visitTree(tree); }
        public void visitImport(JCImport tree)                         { visitTree(tree); }
        public void visitNewClass(JCNewClass tree)                     { visitTree(tree); }
        public void visitJmlBinary(JmlBinary tree)                     { visitTree(tree); }
        public void visitJmlChained(JmlChained tree)                   { visitTree(tree); }
        public void visitJmlChoose(JmlChoose tree)                     { visitTree(tree); }
        public void visitJmlClassDecl(JmlClassDecl tree)               { visitTree(tree); }
        public void visitJmlMethodSig(JmlMethodSig tree)               { visitTree(tree); }
        public void visitJmlDoWhileLoop(JmlDoWhileLoop tree)           { visitTree(tree); }
        public void visitJmlEnhancedForLoop(JmlEnhancedForLoop tree)   { visitTree(tree); }
        public void visitJmlForLoop(JmlForLoop tree)                   { visitTree(tree); }
        public void visitJmlGroupName(JmlGroupName tree)               { visitTree(tree); }
        public void visitJmlInlinedLoop(JmlInlinedLoop tree)           { visitTree(tree); }
        public void visitLabelled(JCLabeledStatement tree)             { visitTree(tree); }
        public void visitJmlLblExpression(JmlLblExpression tree)       { visitTree(tree); }
        public void visitJmlMatchExpression(JmlMatchExpression tree)   { visitTree(tree); }
        public void visitJmlMethodClauseCallable(JmlMethodClauseCallable tree) { visitTree(tree); }
        public void visitJmlMethodClauseConditional(JmlMethodClauseConditional tree) { visitTree(tree); }
        public void visitJmlMethodClauseDecl(JmlMethodClauseDecl tree) { visitTree(tree); }
        public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) { visitTree(tree); }
        public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) { visitTree(tree); }
        public void visitJmlMethodClauseSignals(JmlMethodClauseSignals tree) { visitTree(tree); }
        public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly tree) { visitTree(tree); }
        public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef tree) { visitTree(tree); }
        public void visitJmlMethodDecl(JmlMethodDecl tree)             { visitTree(tree); }
        public void visitJmlMethodInvocation(JmlMethodInvocation tree) { visitTree(tree); }
        public void visitJmlMethodSpecs(JmlMethodSpecs tree)           { visitTree(tree); }
        public void visitJmlModelProgramStatement(JmlModelProgramStatement tree){ visitTree(tree); }
        public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree tree){ visitTree(tree); }
        public void visitJmlQuantifiedExpr(JmlQuantifiedExpr tree)     { visitTree(tree); }
        public void visitJmlRange(JmlRange tree)                       { visitTree(tree); }
        public void visitJmlSetComprehension(JmlSetComprehension tree) { visitTree(tree); }
        public void visitJmlSingleton(JmlSingleton tree)               { visitTree(tree); }
        public void visitJmlSpecificationCase(JmlSpecificationCase tree){ visitTree(tree); }
        public void visitJmlStatement(JmlStatement tree)               { visitTree(tree); }
        public void visitJmlStatementShow(JmlStatementShow tree)       { visitTree(tree); }
        public void visitJmlStatementDecls(JmlStatementDecls tree)     { visitTree(tree); }
        public void visitJmlStatementExpr(JmlStatementExpr tree)       { visitTree(tree); }
        public void visitJmlStatementHavoc(JmlStatementHavoc tree)     { visitTree(tree); }
        public void visitJmlStatementLoopExpr(JmlStatementLoopExpr tree)           { visitTree(tree); }
        public void visitJmlStatementLoopModifies(JmlStatementLoopModifies tree)       { visitTree(tree); }
        public void visitJmlStatementSpec(JmlStatementSpec tree)       { visitTree(tree); }
        public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange tree){ visitTree(tree); }
        public void visitJmlStoreRefKeyword(JmlStoreRefKeyword tree)   { visitTree(tree); }
        public void visitJmlStoreRefListExpression(JmlStoreRefListExpression tree){ visitTree(tree); }
        public void visitJmlTuple(JmlTuple tree)                       { visitTree(tree); }
        public void visitJmlTypeClauseConditional(JmlTypeClauseConditional tree) { visitTree(tree); }
        public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint tree) { visitTree(tree); }
        public void visitJmlTypeClauseDecl(JmlTypeClauseDecl tree)     { visitTree(tree); }
        public void visitJmlTypeClauseExpr(JmlTypeClauseExpr tree)     { visitTree(tree); }
        public void visitJmlTypeClauseIn(JmlTypeClauseIn tree)         { visitTree(tree); }
        public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer tree) { visitTree(tree); }
        public void visitJmlTypeClauseMaps(JmlTypeClauseMaps tree)     { visitTree(tree); }
        public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor tree) { visitTree(tree); }
        public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents tree) { visitTree(tree); }
        public void visitJmlVariableDecl(JmlVariableDecl tree)         { visitTree(tree); }
        public void visitJmlWhileLoop(JmlWhileLoop tree)               { visitTree(tree); }
    }
    
    public JmlEnv jmlenv = new JmlEnv();
    
    public class JmlEnv {
    	public JmlEnv previous;
    	public Name currentLabel; // null is here
    	public Name currentOldLabel; // current interpretation of Old

        /** This field stores the clause type when a clause is visited (before 
         * visiting its components), in order that various clause-type-dependent
         * semantic tests can be performed (e.g. \result can only be used in some
         * types of clauses).
         */
    	public IJmlClauseKind currentClauseKind;
    	
        /** When true, we are visiting subtrees that allow only pure methods and
         * pure operations */
    	public boolean inPureEnvironment;
    	
    	/** true when in an expression-nested scope, that is, in the body of an expression that
    	 * declares some variables, e.g. let or quantifiers
    	 */
    	public boolean inExpressionScope;
    	
    	public VarSymbol representsHead;
        /**
         * Holds the visibility of JML construct that is currently being visited.
         * Values are 0=package, Flags.PUBLIC=public, Flags.PROTECTED=protected,
         *      Flags.PRIVATE=private, -1=not in JML
         */  // FIXME - isa this Java visibility or JML visibility?
        public long jmlVisibility = -1;
        
        /** This value is valid within a Signals clause */
        public Type currentExceptionType = null;
        
        //@ nullable
        public JmlStatementSpec currentBlockContract;

        //@ nullable
        public JmlMethodDecl enclosingMethodDecl = null;
        
    	public JmlEnv() {
    		previous = null;
    		currentLabel = null;
    		currentOldLabel = preLabel;
    		currentClauseKind = null;
    		inPureEnvironment = false;
    		inExpressionScope = false;
    		jmlVisibility = -1;
    		representsHead = null;
    		currentBlockContract = null;
    	}
    	
    	public JmlEnv(JmlEnv e) {
    		previous = e;
    		currentLabel = e.currentLabel;
    		currentOldLabel = e.currentOldLabel;
    		currentClauseKind = e.currentClauseKind;
    		inPureEnvironment = e.inPureEnvironment;
    		inExpressionScope = e.inExpressionScope;
    		jmlVisibility = e.jmlVisibility;
    		representsHead = e.representsHead;
    		currentBlockContract = e.currentBlockContract;
    		enclosingMethodDecl = e.enclosingMethodDecl;
    	}
    	
    	String stackline(int n) {
    		return (new Exception()).getStackTrace()[n+1].toString();
    	}
    	
    	static public boolean envprint = false;
    	
    	public JmlEnv pushCopy() {
    		var j = new JmlEnv(this);
    		if (envprint) System.out.println("PUSHCOPY " + this.hashCode() + " " + jmlenv.hashCode() + " " + j.hashCode() + " " + stackline(1));
    		JmlAttr.this.jmlenv = j;
    		return j;
    	}
    	
    	public JmlEnv pushInit() {
    		var j = new JmlEnv();
    		if (envprint) System.out.println("PUSHINIT " + this.hashCode() + " " + jmlenv.hashCode() + " " + j.hashCode() + " " + stackline(1));
    		j.previous = this;
    		JmlAttr.this.jmlenv = j;
    		return j;
    	}
    	
    	public JmlEnv pop() {
    		if (envprint) System.out.println("POPENV " + previous.inPureEnvironment + " " + this.hashCode() + " " + jmlenv.hashCode() + " " + previous.hashCode() + " " + stackline(1));
    		JmlAttr.this.jmlenv = previous;
    		return previous;
    	}
    	
    	public JmlEnv pop(JmlEnv check) {
    		if (check != jmlenv) { System.out.println("MISMATCHED JMLENV " + check.hashCode() + " " + jmlenv.hashCode()); Utils.dumpStack(); }
    		return pop();
    	}
    	
    	public void check(JmlEnv check) {
    		if (check != JmlAttr.this.jmlenv) { System.out.println("MISMATCHED JMLENV-CHECK " + check.hashCode() + " " + jmlenv.hashCode()); Utils.dumpStack(); }
    	}
    }


//  /** Checks that the modifiers and annotations in the .java and .jml declarations match appropriately,
//  * for both the method declaration and any parameter declarations;
//  * does not do any semantic checks of whether the modifiers or annotations are allowed.
//  */
    // FIXME - move to JmlAttr
    public void checkMethodMatch(/* @nullable */ JmlMethodDecl javaMatch, MethodSymbol match,
            JmlMethodDecl specMethodDecl, ClassSymbol javaClassSymbol) {
        if (javaMatch == null || javaMatch == specMethodDecl)
            return;
        checkAnnotations(javaMatch.mods, specMethodDecl.mods, match);
        JavaFileObject prev = log.currentSourceFile();
        log.useSource(specMethodDecl.sourcefile); // All logged errors are with respect to positions in the jml file
        try {
            if (javaMatch != specMethodDecl) {
                boolean isInterface = match.owner.isInterface();
                // Check that modifiers are the same
                long matchf = match.flags();
                long specf = specMethodDecl.mods.flags;
                matchf |= (specf & Flags.SYNCHRONIZED); // binary files do not seem to always have the synchronized
                                                        // modifier? FIXME
                long diffs = (matchf ^ specf) & Flags.MethodFlags;
                if (diffs != 0) {
                    boolean isEnum = (javaClassSymbol.flags() & Flags.ENUM) != 0;
                    if ((Flags.NATIVE & matchf & ~specf) != 0)
                        diffs &= ~Flags.NATIVE;
                    if (isInterface)
                        diffs &= ~Flags.PUBLIC & ~Flags.ABSTRACT;
                    if (isEnum && match.isConstructor()) {
                        specMethodDecl.mods.flags |= (matchf & 7);
                        diffs &= ~7;
                    } // FIXME - should only do this if specs are default
                    if ((matchf & specf & Flags.ANONCONSTR) != 0 && isEnum) {
                        diffs &= ~2;
                        specMethodDecl.mods.flags |= 2;
                    } // enum constructors can have differences
                    if (diffs != 0 && !(match.isConstructor() && diffs == 3)) {
                        // FIXME - hide this case for now because of default constructors in binary
                        // files
                        utils.error(specMethodDecl.pos(), "jml.mismatched.method.modifiers", specMethodDecl.name,
                                match.toString(), Flags.toString(diffs));
                    }
                }
            }

            if (javaMatch != null) {
                // Check that parameters have the same modifiers - FIXME - should check this in
                // the symbol, not just in the Java
                Iterator<JCVariableDecl> javaiter = javaMatch.params.iterator();
                Iterator<JCVariableDecl> jmliter = specMethodDecl.params.iterator();
                while (javaiter.hasNext() && jmliter.hasNext()) {
                    JmlVariableDecl javaparam = (JmlVariableDecl) javaiter.next();
                    JmlVariableDecl jmlparam = (JmlVariableDecl) jmliter.next();
                    javaparam.specsDecl = jmlparam;
                    jmlparam.sym = javaparam.sym;
                    long diffs = (javaparam.mods.flags ^ jmlparam.mods.flags);
                    if (diffs != 0) {
                        utils.errorAndAssociatedDeclaration(specMethodDecl.sourcefile, jmlparam.pos(),
                                javaMatch.sourcefile, javaparam.pos(), "jml.mismatched.parameter.modifiers",
                                jmlparam.name, javaClassSymbol.getQualifiedName() + "." + match.name,
                                Flags.toString(diffs));
                    }
                }
                // FIXME - should check names of parameters, names of type parameters
                if (javaiter.hasNext() || jmliter.hasNext()) {
                    // Just in case -- should never have made a match if the signatures are
                    // different
                    log.error("jml.internal",
                            "Java and jml declarations have different numbers of arguments, even though they have been type matched");
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

            // Check that parameter names are the same (a JML requirement to avoid having to
            // rename within specs)
            if (javaMatch != null) {
//              for (int i = 0; i<javaMatch.getParameters().size(); i++) {
//                  JCTree.JCVariableDecl javaparam = javaMatch.getParameters().get(i);
//                  JCTree.JCVariableDecl jmlparam = specMethodDecl.params.get(i);
//                  if (!javaparam.name.equals(jmlparam.name)) {
//                      utils.error(jmlparam.pos(),"jml.mismatched.param.names",i,
//                              match.enclClass().fullname + "." + match.toString(),
//                              javaparam.name, jmlparam.name);
//                  }
//              }

//          } else {
//              // FIXME - do not really need this alternative since without a java Decl there is no body
//              for (int i = 0; i<match.getParameters().size(); i++) {
//                  Symbol.VarSymbol javasym = match.getParameters().get(i);
//                  JCTree.JCVariableDecl jmlparam = specMethodDecl.params.get(i);
//                  if (!javasym.name.equals(jmlparam.name)) {
//                      utils.error(jmlparam.pos(),"jml.mismatched.param.names",i,
//                              match.enclClass().fullname + "." + match.toString(),
//                              javasym.name, jmlparam.name);
//                  }
//              }
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
    
    // Must be either normal_behavior
    // or have a signals_only \nothing clause
    // or have a signals (Exception) false clause
    public boolean isEffectivelyNormal(JmlSpecificationCase scase) {
        if (scase.token == exceptionalBehaviorClause) return false;
        return true;
//        if (scase.token == normalBehaviorClause) return true;
//        for (var clause: scase.clauses) {
//            if (clause.clauseKind == SignalsOnlyClauseExtension.signalsOnlyClauseKind) {
//                var sco = (JmlMethodClauseSignalsOnly)clause;
//                if (sco.list.isEmpty()) return true;
//            }
//            if (clause.clauseKind == SignalsClauseExtension.signalsClauseKind) {
//                var scg = (JmlMethodClauseSignals)clause;
//                if (treeutils.isFalseLit(scg.expression) && (scg.vardef == null || scg.vardef.type == syms.exceptionType)) return true;
//            }
//        }
//        return false;
    }

}
