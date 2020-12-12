package org.jmlspecs.openjml;

import static com.sun.tools.javac.code.Flags.BLOCK;
import static com.sun.tools.javac.code.Flags.FINAL;
import static com.sun.tools.javac.code.Flags.PUBLIC;
import static com.sun.tools.javac.code.Flags.STATIC;
import static com.sun.tools.javac.code.Flags.STRICTFP;

import java.util.Arrays;
import java.util.Map;

import javax.lang.model.type.TypeKind;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.ext.MiscExpressions;

import static org.jmlspecs.openjml.ext.FunctionLikeExpressions.*;
import static org.jmlspecs.openjml.ext.MiscExpressions.*;
import static org.jmlspecs.openjml.ext.StateExpressions.*;
import static org.jmlspecs.openjml.ext.StatementExprExtensions.*;

import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.code.Type.IntersectionClassType;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.code.Type.TypeVar;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.JCArrayTypeTree;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCAssignOp;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCCatch;
import com.sun.tools.javac.tree.JCTree.JCConditional;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCPrimitiveTypeTree;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCTypeApply;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.JCWildcard;
import com.sun.tools.javac.tree.JCTree.Tag;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;

/** This class holds a number of utility functions that create fragments of AST trees
 * (using a factory); the created trees are fully type and symbol attributed and so
 * are to be used in tree transformations after type attribution is complete
 * and successful.  It is the user's responsibility to ensure that the resulting
 * tree is legal (including flow checks) since there will be no further checking;
 * errors may easily result in crashes in code generation.
 * It is expected that these utilities will also be used by extension classes.
 * 
 * @author David Cok
 *
 */
public class JmlTreeUtils {

    /** The key to use to retrieve the instance of this class from the Context object. */
    //@ non_null
    public static final Context.Key<JmlTreeUtils> jmltreeutilsKey =
        new Context.Key<JmlTreeUtils>();

    /** A method that returns the unique instance of this class for the given Context
     * (creating it if it does not already exist).
     * 
     * @param context the Context whose JmlTreeUtils instance is wanted
     * @return the singleton instance (per Context) of this class
     */
    //@ non_null
    public static JmlTreeUtils instance(Context context) {
        JmlTreeUtils instance = context.get(jmltreeutilsKey);
        if (instance == null) {
            instance = new JmlTreeUtils(context);  // registers itself
        }
        return instance;
    }
    
    /** The qualified name of the Utils class that contains runtime utility methods */
    @NonNull final public static String utilsClassQualifiedName = org.jmlspecs.utils.Utils.class.getCanonicalName();

    /** The Context in which this object was constructed */ 
    //@ non_null
    @NonNull final protected Context context;
    
    /** The Attr tool for this context */
    @NonNull final protected JmlAttr attr;
    
    /** The Log tool for this context */
    @NonNull final protected Log log;
    
    /** The symbol table from the compilation context, initialized in the constructor */
    @NonNull final public Symtab syms;
    
    /** The Names table from the compilation context, initialized in the constructor */
    @NonNull final public Names names;
    
    /** The Utils tool for this context */
    @NonNull final protected Utils utils;
    
    /** The Resolve tool for this compilation context */
    @NonNull final protected JmlResolve rs;

    /** The Types utilities object for this compilation context */
    @NonNull final protected JmlTypes types;
    
//    /** The Env in which to do resolving */
//    @NonNull protected Env<AttrContext> attrEnv;
        
    /** The factory used to create AST nodes, initialized in the constructor */
    final public /*@ non_null */ JmlTree.Maker factory;

    // Cached values of all of these symbols
    final public ClassSymbol utilsClass;
    final public JCIdent utilsClassIdent;
    final public Symbol andSymbol;
    final public Symbol orSymbol;
    final public Symbol intbitandSymbol;
    final public Symbol longbitandSymbol;
    final public Symbol bitandSymbol;
    final public Symbol bitorSymbol;
    final public Symbol notSymbol;
    final public Symbol objecteqSymbol;
    final public Symbol objectneSymbol;
    final public Symbol booleqSymbol;
    final public Symbol boolneSymbol;
    final public Symbol intminusSymbol;
    final public Symbol intplusSymbol;
    final public Symbol intmultiplySymbol;
    final public Symbol intdivideSymbol;
    final public Symbol inteqSymbol;
    final public Symbol intneqSymbol;
    final public Symbol intgtSymbol;
    final public Symbol intltSymbol;
    final public Symbol intleSymbol;
    final public Symbol longeqSymbol;
    final public Symbol longleSymbol;
    final public Symbol longltSymbol;
    final public Symbol longminusSymbol;
    final public Symbol longplusSymbol;
    final public Symbol longmultiplySymbol;
    final public Symbol longdivideSymbol;
    final public JCLiteral trueLit;
    final public JCLiteral falseLit;
    final public JCLiteral zero;
    final public JCLiteral longzero;
    final public JCLiteral one;
    final public JCLiteral longone;
    final public JCLiteral nullLit;
    final public JCLiteral maxIntLit;

    final public ClassSymbol assertionFailureClass;
    final public Name resultName;
    final public Name caughtException;
    final public Name TYPEName;
    
    /** Creates an instance in association with the given Context; 
     * do not call the constructor 
     * directly, except from derived classes.
     * 
     * @param context The compilation context
     */
    protected JmlTreeUtils(Context context) {
        this.context = context;
        context.put(jmltreeutilsKey, this); // self register
        this.attr = JmlAttr.instance(context);
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        this.factory = JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.rs = JmlResolve.instance(context);
        this.syms = Symtab.instance(context);
        this.types = JmlTypes.instance(context);

        ClassReader reader = ClassReader.instance(context);

        Name utilsName = names.fromString(utilsClassQualifiedName); // flatname
        this.utilsClass = reader.enterClass(utilsName);
        utilsClassIdent = factory.Ident(utilsName);  // FIXME - should this be some sort of Qualified Ident - a simple Ident seems to work
        utilsClassIdent.type = utilsClass.type; // ident containing flatname
        utilsClassIdent.sym = utilsClassIdent.type.tsym;
        andSymbol = findOpSymbol(JCTree.Tag.AND,syms.booleanType);
        orSymbol = findOpSymbol(JCTree.Tag.OR,syms.booleanType);
        intbitandSymbol = findOpSymbol(JCTree.Tag.BITAND,syms.intType);
        longbitandSymbol = findOpSymbol(JCTree.Tag.BITAND,syms.longType);
        bitandSymbol = findOpSymbol(JCTree.Tag.BITAND,syms.booleanType);
        bitorSymbol = findOpSymbol(JCTree.Tag.BITOR,syms.booleanType);
        notSymbol = findOpSymbol(JCTree.Tag.NOT,syms.booleanType);
        objecteqSymbol = findOpSymbol(JCTree.Tag.EQ,syms.objectType);
        objectneSymbol = findOpSymbol(JCTree.Tag.NE,syms.objectType);
        booleqSymbol = findOpSymbol(JCTree.Tag.EQ,syms.booleanType);
        boolneSymbol = findOpSymbol(JCTree.Tag.NE,syms.booleanType); 
        intminusSymbol = findOpSymbol(JCTree.Tag.MINUS,syms.intType); // subtract
        intplusSymbol = findOpSymbol(JCTree.Tag.PLUS,syms.intType); // binary add
        intmultiplySymbol = findOpSymbol(JCTree.Tag.MUL,syms.intType);
        intdivideSymbol = findOpSymbol(JCTree.Tag.DIV,syms.intType);
        inteqSymbol = findOpSymbol(JCTree.Tag.EQ,syms.intType);
        intneqSymbol = findOpSymbol(JCTree.Tag.NE,syms.intType);
        intgtSymbol = findOpSymbol(JCTree.Tag.GT,syms.intType);
        intltSymbol = findOpSymbol(JCTree.Tag.LT,syms.intType);
        intleSymbol = findOpSymbol(JCTree.Tag.LE,syms.intType);
        longleSymbol = findOpSymbol(JCTree.Tag.LE,syms.longType);
        longltSymbol = findOpSymbol(JCTree.Tag.LT,syms.longType);
        longeqSymbol = findOpSymbol(JCTree.Tag.EQ,syms.longType);
        longminusSymbol = findOpSymbol(JCTree.Tag.MINUS,syms.longType);
        longplusSymbol = findOpSymbol(JCTree.Tag.PLUS,syms.longType);
        longmultiplySymbol = findOpSymbol(JCTree.Tag.MUL,syms.longType);
        longdivideSymbol = findOpSymbol(JCTree.Tag.DIV,syms.longType);
        trueLit = makeLit(0,syms.booleanType,1);
        falseLit = makeLit(0,syms.booleanType,0);
        zero = makeLit(0,syms.intType,0);
        one = makeLit(0,syms.intType,1);
        longzero = makeLit(0,syms.longType,Long.valueOf(0L));
        longone = makeLit(0,syms.longType,Long.valueOf(1L));
        nullLit = makeLit(0,syms.botType, null);
        maxIntLit = makeLit(0,syms.intType,Integer.MAX_VALUE);

        assertionFailureClass = reader.enterClass(names.fromString(utilsClassQualifiedName+"$JmlAssertionFailure"));
        
        this.resultName = attr.resultName;
        this.caughtException = names.fromString("_JML$$$caughtException");   // FIXME - do we need this?
        this.TYPEName = names.fromString("TYPE");

    }
    
    /** This sets the end position of newnode to be the same as that of srcnode;
     * the nodes are assumed to reference the same source file. */
    public void copyEndPosition(JCTree newnode, JCTree srcnode) {
        EndPosTable z = log.currentSource().getEndPosTable();
        try {
        if (z != null) {
        	int end = srcnode.getEndPosition(z);
        	z.storeEnd(newnode, end);
        }
        } catch (StackOverflowError e) {
            System.out.println();
        }
    }

    /** Finds the Symbol for the operator given an optag (e.g. JCTree.Tag.AND) and an
     * argument type.  Note that for object equality, the argument type must be
     * Object, not another reference class - better to use makeEqObject in that
     * case.
     * @param optag the optag of the builtin operator, e.g. JCTree.Tag.AND
     * @param argtype the argument type
     * @return the symbol of the operator
     */
    public Symbol findOpSymbol(JCTree.Tag optag, Type argtype) {
        Name opName = TreeInfo.instance(context).operatorName(optag);
        Scope.Entry e = syms.predefClass.members().lookup(opName);
        //Type unboxedArgtype = unboxedType(argtype);
        if (true) {// || unboxedArgtype == argtype) {
            while (e != null && e.sym != null) {
                MethodType mt = (MethodType)e.sym.type;
                if (types.isSameType(mt.argtypes.head,argtype)) return e.sym;
                e = e.next();
            }
            if (argtype != syms.objectType && !argtype.isPrimitive()) return findOpSymbol(optag,syms.objectType);
//        } else {
//            argtype = unboxedArgtype;
//            while (e != null && e.sym != null) {
//                MethodType mt = (MethodType)e.sym.type;
//                if (types.isSameType(mt.argtypes.head,argtype)) return e.sym;
//                e = e.next();
//            }
        }
        throw new JmlInternalError("The operation symbol " + opName + " for type " + argtype + " could not be resolved");
    }
    
    // FIXME - duplicated in JmlAssertionAdder
    protected Type unboxedType(Type t) {
        Type tt = types.unboxedType(t);
        if (tt == Type.noType) tt = t;
        return tt;
    }

    
    /** Returns an attributed AST for "org.jmlspecs.utils.Utils.<methodName>" */
    public JCFieldAccess findUtilsMethod(int pos, String methodName) {
        Name n = names.fromString(methodName);
        // Presumes there is just one method with the given name - no overloading
        // by argument type
        Scope.Entry e = utilsClass.members().lookup(n);
        Symbol ms = e.sym;
        if (ms == null) {
            throw new JmlInternalError("Method " + methodName + " not found in Utils");
        }
        JCFieldAccess m = factory.Select(utilsClassIdent,n);
        m.pos = pos;
        m.sym = ms;
        m.type = m.sym.type;
        return m;
    }
    
    public Symbol getSym(JCTree tree) {
        if (tree instanceof JCMethodInvocation) tree = ((JCMethodInvocation)tree).meth;
        if (tree instanceof JCIdent) {
            return ((JCIdent)tree).sym;
        } else if (tree instanceof JCFieldAccess) {
            return ((JCFieldAccess)tree).sym;
        } else {
            return null;
        }
    }
    

    // FIXME _ document; does this work correctly for this and super?
    /** Returns true if the argument is a reference type name (e.g., A or tt.A)
     * rather than an identifier for a variable or field or other
     * kind of expression.
     */
    public boolean isATypeTree(JCExpression tree) {
        if (tree instanceof JCIdent) { 
            Name n = ((JCIdent)tree).name;
            if (n == names._this || n == names._super) return false; // this (and super I think) are ClassSymbol, not VarSymbol
            return !(((JCIdent)tree).sym instanceof VarSymbol);
        }
        if (tree instanceof JCFieldAccess) {
            return !(((JCFieldAccess)tree).sym instanceof VarSymbol);
        }
        return false;
    }


    /** Makes an attributed JCTree for a class literal corresponding to the given type. */
    public JCExpression makeType(int pos, Type type) {
        // factory.Type does produce an attributed tree - after all we start knowing the type
        JCExpression tree = factory.at(pos).Type(type);
//        // Need to replace any <?> with a new type variable
//        replaceQuestionMarks(tree);
        return tree;
    }
    
//    public void replaceQuestionMarks(JCExpression tree) {
//        if (!(tree instanceof JCTypeApply)) return;
//        List<JCExpression> args = ((JCTypeApply)tree).arguments;
//        while (args != null) {
//            if (args.head instanceof JCTypeApply) replaceQuestionMarks(args.head);
//            if (args.head instanceof JCWildcard) {
//                if (args.head.toString().equals("?")) {
//                    args.head = factory.TypeVar
//                }
//            }
//            args = args.tail;
//        }
//    }
    
    /** Make an attributed tree representing a literal - NOT FOR BOOLEAN or CHARACTER values.
     *  @param pos        The node position
     *  @param type       The literal's type. (syms.botType for null)
     *  @param value      The literal's value; use 0 or 1 for Boolean; use an int for char literals.
     */
    public JCLiteral makeLit(int pos, Type type, Object value) {
        return factory.at(pos).Literal(type.getTag(), value).setType(type.constType(value));
    }
    
    /** Returns true if the argument is a boolean Literal with value true */
    public boolean isNullLit(JCTree tree) {
        if (tree == nullLit) return true;
        if (!(tree instanceof JCLiteral)) return false;
        if (((JCLiteral)tree).typetag != TypeTag.BOT) return false;
        return true;
    }
    
    /** Returns true if the argument is a boolean Literal with value true */
    public boolean isTrueLit(JCTree tree) {
        if (tree == trueLit) return true;
        if (!(tree instanceof JCLiteral)) return false;
        if (((JCLiteral)tree).typetag != TypeTag.BOOLEAN) return false;
        return (Boolean)((JCLiteral)tree).getValue();
    }
    
    /** Returns true if the argument is a boolean Literal with value true */
    public boolean isFalseLit(JCTree tree) {
        if (tree == falseLit) return true;
        if (!(tree instanceof JCLiteral)) return false;
        if (((JCLiteral)tree).typetag != TypeTag.BOOLEAN) return false;
        return !(Boolean)((JCLiteral)tree).getValue();
    }
    
    /** Makes an attributed AST that is a copy of a given literal AST,
     * but with the new position. */
    public JCLiteral makeDuplicateLiteral(DiagnosticPosition pos, JCLiteral lit) {
        // Note that lit.typetag can be different from lit.type.tag - e.g for null values
        JCLiteral r = factory.at(pos).Literal(lit.typetag, lit.value).setType(lit.type.constType(lit.value));
        if (r.getValue() == null && r.type != syms.botType) { // This check is just because null sometimes has a Object type, and that causes problems in RAC
            r.type = syms.botType;  // FIXME - ti seems a bug that this should ever be needed
        }
        return r;
    }
    
    public JCLiteral makeDuplicateLiteral(int pos, JCLiteral lit) {
        // Note that lit.typetag can be different from lit.type.tag - e.g for null values
        JCLiteral r = factory.at(pos).Literal(lit.typetag, lit.value).setType(lit.type.constType(lit.value));
        if (r.getValue() == null && r.type != syms.botType) { // This check is just because null sometimes has a Object type, and that causes problems in RAC
            r.type = syms.botType;  // FIXME - ti seems a bug that this should ever be needed
        }
        return r;
    }
    
    /** Make an attributed tree representing an integer literal. */
    public JCLiteral makeIntLiteral(int pos, int value) {
        return factory.at(pos).Literal(TypeTag.INT, value).setType(syms.intType.constType(value));
    }

    /** Make an attributed tree representing an integer literal. */
    public JCLiteral makeIntLiteral(DiagnosticPosition pos, int value) {
        return factory.at(pos).Literal(TypeTag.INT, value).setType(syms.intType.constType(value));
    }

    /** Make an attributed tree representing an long literal. */
    public JCLiteral makeLongLiteral(int pos, long value) {
        return factory.at(pos).Literal(TypeTag.LONG, value).setType(syms.longType.constType(value));
    }

    /** Make an attributed tree representing an long literal. */
    public JCLiteral makeLongLiteral(DiagnosticPosition pos, long value) {
        return factory.at(pos).Literal(TypeTag.LONG, value).setType(syms.longType.constType(value));
    }

    /** Make an attributed tree representing a null literal. */
    public JCLiteral makeNullLiteral(int pos) {
        return makeDuplicateLiteral(pos,nullLit);
    }

    /** Make an attributed tree representing a null literal. */
    public JCLiteral makeNullLiteral(DiagnosticPosition pos) {
        return makeDuplicateLiteral(pos,nullLit);
    }

    /** Makes a constant boolean literal AST node.
     * @param pos the position to use for the node
     * @param value the boolean value of the constant node
     * @return the AST node
     */
    public JCLiteral makeBooleanLiteral(int pos, boolean value) {
        int v = value?1:0;
        JCLiteral r = factory.at(pos).Literal(TypeTag.BOOLEAN,v);
        r.type = syms.booleanType.constType(v);
        return r;
    }

    public JCLiteral makeBooleanLiteral(DiagnosticPosition pos, boolean value) {
        int v = value?1:0;
        JCLiteral r = factory.at(pos).Literal(TypeTag.BOOLEAN,v);
        r.type = syms.booleanType.constType(v);
        return r;
    }

    /** Makes a constant String literal AST node.
     * @param pos the position to use for the node
     * @param value the String value of the constant node
     * @return the AST node
     */
    public JCLiteral makeStringLiteral(int pos, String value) {
        JCLiteral r = factory.at(pos).Literal(TypeTag.CLASS,value);
        r.type = syms.stringType.constType(value);
        return r;
    }

    /** Makes a constant char literal AST node.
     * @param pos the position to use for the node
     * @param value the char value of the constant node
     * @return the AST node
     */
    public JCLiteral makeCharLiteral(int pos, char value) {
        JCLiteral r = factory.at(pos).Literal(TypeTag.CHAR,(int)value);
        r.type = syms.charType.constType(value);
        return r;
    }

    /** Make a zero-equivalent constant node of the given type
     * @param type the type of the node, e.g. syms.intType
     * @return the AST node
     */ 
    public JCLiteral makeZeroEquivalentLit(int pos, Type type) {
        if (type == types.BIGINT) {
            return makeLit(pos,syms.intType,0);
           
        } else if (type == types.REAL) {
            return makeLit(pos,syms.doubleType,0.0);
            
        } else if (type == types.TYPE) {
            log.error(pos, "jml.message","old clause is not implemented for \\TYPE variables");
            // FIXME - ???
            return null;//makeTypelc(null);  // FIXME _ should have a pos argument
            
        } else {
        switch (type.getTag()) {
            case CHAR:
                return makeLit(pos,type,0); // Character literal requires an int value
            case LONG:
                return makeLit(pos,type,(long)0);
            case INT:
            case SHORT:
            case BYTE:
            case BOOLEAN:
                return makeLit(pos,type,0); // Boolean literal requires an int value
            case FLOAT:
                return makeLit(pos,type,0.0f);
            case DOUBLE:
                return makeLit(pos,type,0.0);
            case CLASS:
            case ARRAY:
            default:
                return makeNullLiteral(pos);
        }
        }
    }

    // FIXME - the following method appears to be misnamed

    /** Makes an AST for a primitive type literal, e.g. "int"
     * @param s the text string corresponding to the type
     * @return the AST
     */
    public JCExpression makePrimitiveClassLiteralExpression(String s) {
        Name n = names.fromString(s); // FIXME - pass in a Name?
        // The following only ever loads the class once, despite multiple calls
        Type type = ClassReader.instance(context).enterClass(n).type; // TODO - don't call instance all the time
        JCIdent id = factory.Ident(n);
        id.pos = Position.NOPOS;
        id.type = type;
        id.sym = type.tsym;
        JCFieldAccess f = factory.Select(id,TYPEName);
        f.pos = Position.NOPOS;
        f.type = syms.objectType;
        Scope.Entry e = type.tsym.members().lookup(TYPEName);
        f.sym = e.sym;
        return f;
    }


    /** Makes a new AST for an identifier that references the given symbol
     * @param sym the symbol for which to make an identifier
     * @return the AST
     */ 
    public JCIdent makeIdent(int pos, Symbol sym) {
        JCIdent id = factory.Ident(sym);
        id.pos = pos;
        // id.type is set in Ident
        return id;
    }
    
    /** Makes a new AST for an identifier that references the given symbol
     * @param sym the symbol for which to make an identifier
     * @return the AST
     */ 
    public JCIdent makeIdent(/*@ nullable */ DiagnosticPosition pos, Symbol sym) {
        JCIdent id = factory.Ident(sym);
        id.pos = pos == null ? Position.NOPOS: pos.getPreferredPosition();
        // id.type is set in Ident
        return id;
    }
    
    /** Makes a new AST for an identifier that references the given symbol
     * @param sym the symbol for which to make an identifier
     * @return the AST
     */ 
    public JCIdent makeIdent(int pos, Name name, Symbol sym) {
        JCIdent id = sym != null ? factory.Ident(sym) : factory.Ident(name);
        id.name = name;
        id.pos = pos;
        // id.type is set in Ident, if sym is not null
        return id;
    }
    
    /** Makes a new AST and VarSymbol for an identifier with the given name and type
     * @param sym the symbol for which to make an identifier
     * @return the AST
     */ 
    public JCIdent makeIdent(int pos, String name, Type type) {
        VarSymbol sym = makeVarSymbol(0,names.fromString(name),type,pos);
        return makeIdent(pos,sym);
    }
      
    /** Makes an AST for a field selection (attributed)
     * @param sym the symbol for which to make an identifier
     * @return the AST
     */ 
    public JCFieldAccess makeSelect(int pos, JCExpression lhs, Symbol sym) {
        JCFieldAccess fa = factory.Select(lhs, sym.name);
        fa.pos = pos;
        fa.type = sym.type;
        fa.sym = sym;
        return fa;
    }

    /** Makes an AST for a field selection (attributed)
     * @param sym the symbol for which to make an identifier
     * @return the AST
     */ 
    public JCFieldAccess makeSelect(int pos, JCExpression lhs, Name name) {
        JCFieldAccess fa = factory.Select(lhs, name);
        fa.pos = pos;
        fa.type = null;
        fa.sym = null;
        return fa;
    }


    /** Makes an attributed assignment expression; the expression type is the type of the lhs. */
    public JCAssign makeAssign(int pos, JCExpression lhs, JCExpression rhs) {
        JCAssign tree = factory.at(pos).Assign(lhs, rhs);
        tree.type = lhs.type;
        return tree;
    }
    
    /** Makes an attributed assignment expression; the expression type is the type of the lhs. */
    public JCExpressionStatement makeAssignStat(int pos, JCExpression lhs, JCExpression rhs) {
        JCAssign tree = factory.at(pos).Assign(lhs, rhs);
        tree.type = lhs.type;
        return factory.Exec(tree);
    }
    
    /** Makes an attributed assignment-op expression; the expression type is the type of the lhs. */
    public JCAssignOp makeAssignOp(int pos, JCTree.Tag op, JCExpression lhs, JCExpression rhs) {
        JCAssignOp asn = factory.at(pos).Assignop(op, lhs, rhs);
        asn.setType(lhs.type);
        asn.operator = findOpSymbol(op.noAssignOp(),asn.lhs.type);
        return asn;
    }

    /** Makes a JML assume statement */
    public JmlStatementExpr makeAssume(DiagnosticPosition pos, Label label, JCExpression expr) {
        JmlStatementExpr e = factory.at(pos).JmlExpressionStatement(assumeID, assumeClause, label, expr);
        e.associatedPos = Position.NOPOS;
        e.associatedSource = null;
        return e;
    }

    /** Makes a JML assert statement */
    public JmlStatementExpr makeAssert(DiagnosticPosition pos, Label label, JCExpression expr) {
        JmlStatementExpr e = factory.at(pos).JmlExpressionStatement(assertID, assertClause, label, expr);
        e.associatedPos = Position.NOPOS;
        e.associatedSource = null;
        return e;
    }

    /** Returns the larger type of two numeric types;
     * not appropriate for Boolean types */
    public Type maxType(Type lhs, Type rhs) {
        // Note: getTag().ordinal() is not relaible
        TypeTag ltag = lhs.getTag();
        TypeTag rtag = rhs.getTag();
        if (ltag == TypeTag.NONE && lhs == types.REAL) return lhs;
        if (rtag == TypeTag.NONE && rhs == types.REAL) return rhs;
        if (ltag == TypeTag.NONE && lhs == types.BIGINT) {
            if (rtag == TypeTag.DOUBLE || rtag == TypeTag.FLOAT) return types.REAL;
            return lhs;
        }
        if (rtag == TypeTag.NONE && rhs == types.BIGINT) {
            if (ltag == TypeTag.DOUBLE || ltag == TypeTag.FLOAT) return types.REAL;
            return rhs;
        }
        if (ltag == TypeTag.DOUBLE) return lhs;
        if (rtag == TypeTag.DOUBLE) return rhs;
        if (ltag == TypeTag.FLOAT && rtag == TypeTag.LONG) return syms.doubleType;
        if (ltag == TypeTag.LONG && rtag == TypeTag.FLOAT) return syms.doubleType;
        if (ltag == TypeTag.FLOAT) return lhs;
        if (rtag == TypeTag.FLOAT) return rhs;
        if (ltag == TypeTag.LONG) return lhs;
        if (rtag == TypeTag.LONG) return rhs;
        if (ltag == TypeTag.INT) return lhs;
        if (rtag == TypeTag.INT) return rhs;
        if (ltag == TypeTag.SHORT) return lhs;
        if (rtag == TypeTag.SHORT) return rhs;
        if (ltag == TypeTag.CHAR) return lhs;
        if (rtag == TypeTag.CHAR) return rhs;
        if (ltag == TypeTag.BYTE) return lhs;
        if (rtag == TypeTag.BYTE) return rhs;
        return lhs; // Only if non-numeric types, such as boolean
    }
    
    public boolean isIntegral(TypeTag tag) {
        return tag == TypeTag.INT || tag.ordinal() <= TypeTag.LONG.ordinal();
    }
    
    
    public Type opType(Type lhs, Type rhs) {
        Type lhsu = unboxedType(lhs);
        Type rhsu = unboxedType(rhs);
        if (lhsu.getTag() == TypeTag.BOOLEAN) return syms.booleanType;
        if (!lhsu.isPrimitive() || !rhsu.isPrimitive()) return syms.stringType;
        if (lhsu == types.REAL || rhsu == types.REAL) return types.REAL;
        if (lhsu == types.BIGINT || rhsu == types.BIGINT) return types.BIGINT;
        if (lhsu == types.TYPE || rhsu == types.TYPE) return types.TYPE;
        TypeTag ltag = lhsu.getTag();
        TypeTag rtag = rhsu.getTag();
        
        if (ltag == TypeTag.DOUBLE) return lhs;
        if (rtag == TypeTag.DOUBLE) return rhs;
        if (ltag == TypeTag.FLOAT) return lhs;
        if (rtag == TypeTag.FLOAT) return rhs;
        if (ltag == TypeTag.LONG) return lhs;
        if (rtag == TypeTag.LONG) return rhs;
        return syms.intType;
    }
    
    /** Makes a Java unary operator node; it may be constant-folded
     * @param pos the pseudo source code location of the node
     * @param optag the unary operator, e.g. JCTree.Tag.NOT, JCTree.Tag.NEG, JCTree.Tag.COMPL, ...
     * @param expr the argument expression
     * @return the new node
     */
    public JCExpression makeUnary(DiagnosticPosition pos, JCTree.Tag optag, JCExpression expr) {
        JCUnary e = factory.at(pos).Unary(optag,expr);
        e.operator = findOpSymbol(optag,expr.type);
        e.type = e.operator.type.getReturnType();
        copyEndPosition(e,expr);
        return e;
    }
    public JCExpression makeUnary(int pos, JCTree.Tag optag, JCExpression expr) {
        JCUnary e = factory.at(pos).Unary(optag,expr);
        e.operator = findOpSymbol(optag,expr.type);
        e.type = e.operator.type.getReturnType();
        copyEndPosition(e,expr);
        return e;
    }

    /** Makes a Java unary operator node, to be used when the opsymbol is
     * already known.
     * @param pos the pseudo source code location of the node
     * @param optag the unary operator, e.g. JCTree.NOT, JCTree.NEG, JCTree.COMPL, ...
     * @param opsymbol the symbol corresponding to the optag
     * @param expr the argument expression
     * @return the new node
     */
    public JCExpression makeUnary(int pos, JCTree.Tag optag, Symbol opsymbol, JCExpression expr) {
        JCUnary e = factory.at(pos).Unary(optag,expr);
        e.operator = opsymbol;
        e.type = e.operator.type.getReturnType();
        if (expr.type.getTag() == TypeTag.NONE) e.type = expr.type; // For \bigint and \real operations
        copyEndPosition(e,expr);
        return e;
    }

    /** Make an attributed unary NOT(!) expression
     *  @param pos    The position at which to put the new AST.
     *  @param arg    The operator's argument.
     */
    public JCExpression makeNot(DiagnosticPosition pos, JCExpression arg) {
        return makeUnary(pos,JCTree.Tag.NOT,arg);
    }
    public JCExpression makeNot(int pos, JCExpression arg) {
        return makeUnary(pos,JCTree.Tag.NOT,arg);
    }
    public JCExpression makeNotSimp(DiagnosticPosition pos, JCExpression arg) {
        if (isTrueLit(arg)) return makeBooleanLiteral(pos,false);
        else if (isFalseLit(arg)) return makeBooleanLiteral(pos,true);
        else return makeUnary(pos,JCTree.Tag.NOT,arg);
    }
    public JCExpression makeNotSimp(int pos, JCExpression arg) {
        if (isTrueLit(arg)) return makeBooleanLiteral(pos,false);
        else if (isFalseLit(arg)) return makeBooleanLiteral(pos,true);
        else return makeUnary(pos,JCTree.Tag.NOT,arg);
    }

    /** Make an attributed binary expression.
     *  @param pos      The pseudo-position at which to place the node
     *  @param optag    The operator's operation tag (e.g. JCTree.PLUS).
     *  @param opSymbol The symbol for the operation
     *  @param lhs      The operator's left argument.
     *  @param rhs      The operator's right argument.
     */
    public JCBinary makeBinary(DiagnosticPosition pos, JCTree.Tag optag, Symbol opSymbol, JCExpression lhs, JCExpression rhs) {
        JCBinary tree = factory.at(pos).Binary(optag, lhs, rhs);
        tree.operator = opSymbol;
        tree.type = tree.operator.type.getReturnType();
        //copyEndPosition(tree,rhs);
        return tree;
    }
    
    public JCBinary makeBinary(int pos, JCTree.Tag optag, Symbol opSymbol, JCExpression lhs, JCExpression rhs) {
        JCBinary tree = factory.at(pos).Binary(optag, lhs, rhs);
        tree.operator = opSymbol;
        tree.type = tree.operator.type.getReturnType();
        //copyEndPosition(tree,rhs);
        return tree;
    }
    
    public JCExpression makeBinarySimp(DiagnosticPosition pos, JCTree.Tag optag, JCExpression lhs, JCExpression rhs) {
        if (optag == JCTree.Tag.OR) return makeOrSimp(pos.getStartPosition(), lhs, rhs);
        if (optag == JCTree.Tag.AND) return makeAndSimp(pos.getStartPosition(), lhs, rhs);
        return makeBinary(pos, optag,  lhs, rhs);
    }

    public JCExpression makeBinarySimp(int pos, JCTree.Tag optag, JCExpression lhs, JCExpression rhs) {
        if (optag == JCTree.Tag.OR) return makeOrSimp(pos, lhs, rhs);
        if (optag == JCTree.Tag.AND) return makeAndSimp(pos, lhs, rhs);
        return makeBinary(pos, optag,  lhs, rhs);
    }


    /** Makes an attributed Java binary operator node (with boolean result)
     * @param pos the pseudo source code location of the node
     * @param optag the binary operator (producing a boolean result), e.g. JCTree.EQ
     * @param lhs the left-hand expression
     * @param rhs the right-hand expression
     * @return the new node
     */
    public JCBinary makeBinary(DiagnosticPosition pos, JCTree.Tag optag, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,optag,findOpSymbol(optag,opType(lhs.type.baseType(),rhs.type.baseType())),lhs,rhs);
    }
    public JCBinary makeBinary(int pos, JCTree.Tag optag, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,optag,findOpSymbol(optag,opType(lhs.type.baseType(),rhs.type.baseType())),lhs,rhs);
    }
    
    public /*@ nullable */ String opname(Type t, JCTree.Tag tag) {
        JmlTypes jmltypes = JmlTypes.instance(context);
        String prefix = jmltypes.isJmlTypeOrRep(t, jmltypes.BIGINT) ? "bigint_" : jmltypes.isJmlTypeOrRep(t, jmltypes.REAL) ? "real_" : null;
        String suffix = null;
        switch (tag) {
            case LE: suffix = "le"; break;
            case LT: suffix = "lt"; break;
            case GE: suffix = "ge"; break;
            case GT: suffix = "gt"; break;
            case EQ: suffix = "eq"; break;
            case NE: suffix = "ne"; break;
        }
        if (prefix == null || suffix == null) {
            return null;
        } else {
            return prefix + suffix;
        }
    }


    /** Produces an Equality AST node; presumes that the lhs and rhs have the 
     * same type.
     * @param pos the position of the node
     * @param lhs the left argument
     * @param rhs the right argument
     * @return the AST
     */
    public JCBinary makeEquality(int pos, JCExpression lhs, JCExpression rhs) {
        JCBinary tree = factory.at(pos).Binary(JCTree.Tag.EQ, lhs, rhs);
        Type t = lhs.type;
        if (t.isPrimitive() && TypeTag.SHORT.ordinal() >= t.getTag().ordinal()) t = syms.intType;   // Perhaps should just presume the types are the same
        tree.operator = findOpSymbol(JCTree.Tag.EQ, t);
        tree.type = syms.booleanType;
        return tree;
    }

    /** Makes a JML binary operator node (with boolean result)
     * @param pos the pseudo source code location of the node
     * @param op the binary operator (producing a boolean result), e.g. JmlToken.IMPLIES
     * @param lhs the left-hand expression
     * @param rhs the right-hand expression
     * @return the new node
     */
    public JmlBinary makeJmlBinary(int pos, IJmlClauseKind op, JCExpression lhs, JCExpression rhs) {
        JmlBinary e = factory.at(pos).JmlBinary(op,lhs,rhs);
        e.type = syms.booleanType;
        copyEndPosition(e,rhs);
        return e;
    }

    public JCConditional makeConditional(int pos, JCExpression cond, JCExpression trueexpr, JCExpression falseexpr) {
        JCConditional e = factory.at(pos).Conditional(cond,trueexpr,falseexpr);
        e.type = trueexpr.type;
        copyEndPosition(e,falseexpr);
        return e;
    }

    /** Makes an attributed AST for a short-circuit boolean AND expression */
    public JCExpression makeAnd(DiagnosticPosition pos, JCExpression lhs, JCExpression ... rhs) {
        for (JCExpression r: rhs) {
            lhs = makeBinary(pos,JCTree.Tag.AND,andSymbol,lhs,r);
        }
        return lhs;
    }
    public JCExpression makeAnd(int pos, JCExpression lhs, JCExpression ... rhs) {
        for (JCExpression r: rhs) {
            lhs = makeBinary(pos,JCTree.Tag.AND,andSymbol,lhs,r);
        }
        return lhs;
    }

    /** Makes an attributed AST for a short-circuit boolean AND expression, simplifying literal true or false */
    public JCExpression makeAndSimp(int pos, JCExpression lhs, JCExpression rhs) {
        if (isTrueLit(rhs) || isFalseLit(lhs)) return lhs;
        if (isTrueLit(lhs) || isFalseLit(rhs)) return rhs;
        return makeBinary(pos,JCTree.Tag.AND,andSymbol,lhs,rhs);
    }

    /** Makes an attributed AST for a short-circuit boolean OR expression */
    public JCExpression makeOr(int pos, JCExpression lhs, JCExpression ... rhs) {
        for (JCExpression r: rhs) {
            lhs = makeBinary(pos,JCTree.Tag.OR,orSymbol,lhs,r);
        }
        return lhs;
    }

    /** Makes an attributed AST for a short-circuit boolean OR expression */
    public JCExpression makeOr(DiagnosticPosition pos, JCExpression lhs, JCExpression ... rhs) {
        for (JCExpression r: rhs) {
            lhs = makeBinary(pos,JCTree.Tag.OR,orSymbol,lhs,r);
        }
        return lhs;
    }

    /** Makes an attributed AST for a short-circuit boolean OR expression, simplifying literal true or false */
    public JCExpression makeOrSimp(int pos, JCExpression lhs, JCExpression rhs) {
        if (isFalseLit(rhs) || isTrueLit(lhs)) return lhs;
        if (isFalseLit(lhs) || isTrueLit(rhs)) return rhs;
        return makeBinary(pos,JCTree.Tag.OR,orSymbol,lhs,rhs);
    }

    /** Makes an attributed attributed AST for a non-short-circuit boolean AND expression */
    public JCExpression makeBitAnd(int pos, JCExpression lhs, JCExpression ... rhs) {
        for (JCExpression r: rhs) {
            lhs = makeBinary(pos,JCTree.Tag.BITAND,bitandSymbol,lhs,r);
        }
        return lhs;
    }

    /** Makes an attributed attributed AST for a non-short-circuit boolean OR expression */
    public JCExpression makeBitOr(int pos, JCExpression lhs, JCExpression ... rhs) {
        for (JCExpression r: rhs) {
            lhs = makeBinary(pos,JCTree.Tag.BITOR,bitorSymbol,lhs,r);
        }
        return lhs;
    }

    Boolean booleanLiteral(JCExpression e) {
        if (e instanceof JCLiteral) {
            JCLiteral lit = (JCLiteral)e;
            if (lit.value instanceof Boolean) return (Boolean)lit.value;
            if (e.type == syms.booleanType && lit.value instanceof Integer) return 0 != (Integer)lit.value;
        }
        return null;
    }

    /** Makes an attributed attributed AST for a non-short-circuit boolean OR expression */
    public JCExpression makeBitOrSimp(int pos, JCExpression lhs, JCExpression ... rhs) {
        for (JCExpression r: rhs) {
            Boolean bl = booleanLiteral(lhs);
            if (bl != null && bl) return lhs;
            if (bl != null && !bl) { lhs = r; continue; }
            Boolean b = booleanLiteral(r);
            if (b != null && b) return r;
            if (b != null && !b) continue;
            lhs = makeBinary(pos,JCTree.Tag.BITOR,bitorSymbol,lhs,r);
        }
        return lhs;
    }

    /** Makes an attributed AST for the Java equivalent of a JML IMPLIES expression */
    public JCExpression makeImplies(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.Tag.OR,orSymbol,
                makeNot(pos,lhs), rhs);
    }

    /** Makes an attributed AST for the Java equivalent of a JML IMPLIES expression */
    public JCExpression makeImpliesSimp(int pos, JCExpression lhs, JCExpression rhs) {
        if (isTrueLit(lhs) || isTrueLit(rhs)) return rhs;
        else if (isFalseLit(lhs)) return makeBooleanLiteral(pos,true);
        else if (isTrueLit(rhs)) return makeNot(pos,lhs);
        return makeBinary(pos,JCTree.Tag.OR,orSymbol,
                makeNot(pos,lhs), rhs);
    }

    /** Makes an attributed AST for a reference equality (==) expression */
    public JCBinary makeEqObject(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.Tag.EQ,objecteqSymbol,lhs, rhs);
    }

    /** Makes an attributed AST for a reference inequality (!=) expression */
    public JCBinary makeNeqObject(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.Tag.NE,objectneSymbol,lhs, rhs);
    }
    
    /** Makes an attributed AST for a reference inequality (!=) expression */
    public JCBinary makeNotNull(int pos, JCExpression lhs) {
        return makeBinary(pos,JCTree.Tag.NE,objectneSymbol,lhs, makeNullLiteral(pos));
    }
    
    /** Makes an attributed AST for a reference inequality (!=) expression */
    public JCBinary makeEqNull(int pos, JCExpression lhs) {
        return makeBinary(pos,JCTree.Tag.EQ,objecteqSymbol,lhs, makeNullLiteral(pos));
    }
    
    /** Makes an attributed AST for the length operation on an array. */
    public JCFieldAccess makeLength(DiagnosticPosition pos, JCExpression array) {
        JCFieldAccess fa = (JCFieldAccess)factory.at(pos).Select(array, syms.lengthVar);
        fa.type = syms.intType;
        return fa;
    }

//    /** Makes the AST for a catch block; the name of the exception variable is
//     * that of the 'caughtException' name defined in the constructor; the catch
//     * block itself is initialized with no statements; the type of the exception
//     * is java.lang.Exception.
//     * @param owner the symbol of the enclosing method
//     * @return the new AST
//     */
//    public JCCatch makeCatcher(Symbol owner) {
//        return makeCatcher(owner,syms.exceptionType);
//    }
    
    /** Makes the AST for a catch block; the name of the exception variable is
     * that of the 'caughtException' name defined in the constructor; the catch
     * block itself is initialized with no statements.
     * @param owner  TBD
     * @param exceptionType the type of the exception caught in the statement
     * @return the new AST
     */
    public JCCatch makeCatcher(Symbol owner, Type exceptionType) {
        JCVariableDecl v = makeVarDef(exceptionType,caughtException,owner,Position.NOPOS);
        return factory.at(Position.NOPOS).Catch(v,factory.Block(0,List.<JCStatement>nil()));
    }

    /** Makes an AST for an int variable declaration with initialization and no
     * modifiers and no position.
     * @param name the name of the new variable
     * @param initializer  the (possibly null) initializer expression
     * @param owner the owner of the declaration (e.g. a method or a class)
     * @return the new AST
     */
    public JCVariableDecl makeIntVarDef(Name name, JCExpression initializer, Symbol owner) {
        Type type = syms.intType;
        JCExpression tid = factory.Type(type); // sets tid.type
        tid.pos = Position.NOPOS;
        JCModifiers mods = factory.at(Position.NOPOS).Modifiers(0);
        JCVariableDecl d = factory.VarDef(mods,name,tid,initializer);
        VarSymbol v =
            new VarSymbol(0, d.name, type, owner);
        d.pos = Position.NOPOS;
        d.sym = v;
        d.type = type;
        return d;
    }
    
    // FIXME - might be a problem having no owner
    /** Creates a new VarSymbol with the given name and type and modifier flags 
     * (and no owner);
     * the declaration position is 'pos'. */
    public VarSymbol makeVarSymbol(long flags, @NonNull Name name, @NonNull Type type, int pos) {
        VarSymbol v = new VarSymbol(flags,name,type.baseType(),null); // FIXME - explain why baseType is needed
        v.pos = pos;
        return v;
    }
    


    /** Makes a new variable declaration for new helper variables in the AST translation;
     * a new VarSymbol is also created in conjunction with the variable; the variable
     * is created with no modifiers and no owner.
     * @param name the variable name, as it might be used in program text
     * @param type the variable type
     * @param init the initialization expression as it would appear in a declaration (null for no initialization)
     * @param pos the pseudo source code location for the new node
     * @return a new JCVariableDecl node
     */
    public JCVariableDecl makeVariableDecl(Name name, Type type, @Nullable JCExpression init, int pos) {
        VarSymbol vsym = new VarSymbol(0, name, type.baseType(), null);
        vsym.pos = pos;
        JCVariableDecl decl = factory.at(pos).VarDef(vsym,init);
        return decl;
    }

    /** Makes an attributed variable declaration along with a new VarSymbol (which is not 
     * put into the symbol table); the declaration has no modifiers; it is
     * initialized to a zero-equivalent value; no position set.
     * @param type  the type of the new variable (should be an attributed AST)
     * @param name  the name of the new variable
     * @param owner the owner of the new variable (e.g. a MethodSymbol or ClassSymbol)
     * @return the AST for the declaration
     */
    public JCVariableDecl makeVarDefZeroInit(JCExpression type, Name name, Symbol owner) {
        int flags = 0;
        JCModifiers mods = factory.at(Position.NOPOS).Modifiers(0);
        JCExpression zeroEquiv = makeZeroEquivalentLit(Position.NOPOS,type.type);
        JCVariableDecl d = factory.VarDef(mods,name,type,zeroEquiv);
        VarSymbol v =
            new VarSymbol(flags, d.name, d.vartype.type.baseType(), owner);
        v.pos = Position.NOPOS;
        d.pos = Position.NOPOS;
        d.sym = v;
        d.type = type.type;
        return d;
    }


    /** Makes an attributed variable declaration for the given VarSymbol; 
     * the declaration has no modifiers; position
     * is set to that of the init expression.
     */
    public JCVariableDecl makeVariableDecl(VarSymbol var, @Nullable JCExpression init) {
        JCVariableDecl d = factory.VarDef(var,init);
        if (init != null) d.pos = init.pos;
        return d;
    }

    /** Makes an attributed variable declaration along with a new VarSymbol (which is not 
     * put into the symbol table); the declaration has no modifiers; position
     * is set to that of the init expression.
     * @param type  the type of the new variable
     * @param name  the name of the new variable
     * @param owner the owner of the new variable (e.g. a MethodSymbol or ClassSymbol)
     * @param init  the initialization expression for the new AST
     * @return the AST for the declaration
     */
    public JCVariableDecl makeVarDef(Type type, Name name, Symbol owner, @NonNull JCExpression init) {
        int modifierFlags = 0;
        // We use type.baseType() here to remove any constType in case the 
        // expression the type came from is a literal. This made the difference 
        // in making the racnew2.testLblConst test work.
        // TODO - figure out why - something in code generation
        VarSymbol v = new VarSymbol(modifierFlags, name, type.baseType(), owner);
        v.pos = init.getStartPosition();
        JCVariableDecl d = factory.VarDef(v,init);
        d.pos = v.pos;
        return d;
    }

    public JCVariableDecl makeVarDefWithSym(VarSymbol v, @NonNull JCExpression init) {
        JCVariableDecl d = factory.VarDef(v,init);
        d.pos = v.pos;
        return d;
    }

    public JCVariableDecl makeStaticVarDef(Type type, Name name, Symbol owner, @NonNull JCExpression init) {
        int modifierFlags = Flags.STATIC;
        // We use type.baseType() here to remove any constType in case the 
        // expression the type came from is a literal. This made the difference 
        // in making the racnew2.testLblConst test work.
        // TODO - figure out why - something in code generation
        VarSymbol v = new VarSymbol(modifierFlags, name, type.baseType(), owner);
        v.pos = init.getStartPosition();
        JCVariableDecl d = factory.VarDef(v,init);
        d.pos = v.pos;
        return d;
    }

    /** Makes an attributed variable declaration along with a new VarSymbol (which is not 
     * put into the symbol table); the declaration has no modifiers and no initialization.
     * @param type  the type of the new variable
     * @param name  the name of the new variable
     * @param owner the owner of the new variable (e.g. a MethodSymbol or ClassSymbol)
     * @param pos   the position to set
     * @return the AST for the declaration
     */
    public JCVariableDecl makeVarDef(Type type, Name name, Symbol owner, int pos) {
        return makeVarDef(type, name, owner, 0, pos);
    }
    
    public JCVariableDecl makeVarDef(Type type, Name name, Symbol owner, long modifierFlags, int pos) {
        VarSymbol v = new VarSymbol(modifierFlags, name, type, owner);
        v.pos = pos;
        JCVariableDecl d = factory.VarDef(v,null);
        d.pos = pos;
        return d;
    }
    
    public JCVariableDecl makeDupDecl(JCVariableDecl decl, MethodSymbol owner, Name newname, int pos) {
        JCVariableDecl newdecl = makeVarDef(decl.type, newname, owner, decl.mods.flags, pos);
        newdecl.mods.annotations = decl.mods.annotations;
        newdecl.sym.setAttributes(decl.sym);
        return newdecl;
    }
    
   
    /** Makes an \old expression */
    public JCMethodInvocation makeOld(DiagnosticPosition pos, JCExpression arg) {
        JmlMethodInvocation m;
        m = factory.at(pos).JmlMethodInvocation(oldKind, List.<JCExpression>of(arg));
        m.type = arg.type;
        m.kind = oldKind;
        return m;
    }
    
    public JCMethodInvocation makeOld(DiagnosticPosition pos, JCExpression arg, JmlAssertionAdder.LabelProperties labelprop) {
        JmlMethodInvocation m;
        JCIdent id = makeIdent(pos.getStartPosition(), labelprop.name,null);
        m = factory.at(pos).JmlMethodInvocation(oldKind, List.<JCExpression>of(arg,id));
        m.labelProperties = labelprop;
        m.type = arg.type;
        m.kind = oldKind;
        return m;
    }
    
    public JCMethodInvocation makeOld(JCExpression arg) {
        return makeOld(arg,arg);
    }

   
    /** Makes a \past expression */
    public JCMethodInvocation makePast(int pos, JCExpression arg, JCIdent label) {
        JCMethodInvocation m;
        if (label.toString().isEmpty()) {
            m = factory.JmlMethodInvocation(pastKind, List.<JCExpression>of(arg));
        } else {
            JCIdent id = factory.at(pos).Ident(label.name);
            id.type = null; // Should never refer to the label's type
            id.sym = null; // Should never refer to the label's symbol
            m = factory.JmlMethodInvocation(pastKind, List.<JCExpression>of(arg, id));
        }
        m.type = arg.type;
        return m;
    }
    
    public JCExpression makeThrownPredicate(DiagnosticPosition pos, JCIdent exceptionId, JCMethodDecl methodDecl) {
        JCExpression rex = makeType(pos.getPreferredPosition(),syms.runtimeExceptionType);
        JCExpression condd = factory.at(pos).TypeTest(exceptionId, rex).setType(syms.booleanType);
        for (JCExpression ex: methodDecl.thrown) {
            if (pos == null) pos = ex.pos();
            JCExpression tc = factory.at(ex.pos()).TypeTest(exceptionId, ex).setType(syms.booleanType);
            condd = makeOr(ex.pos, condd, tc);
        }
        return condd;
    }
   
    /** This makes an expressions stating that the Java throws predicate is adhered to; that is,
     * the exceptionId is an instance of RuntimeException or one of the listed exception types.
     * @param pos
     * @param exceptionId
     * @param sym
     * @return
     */
    public JCExpression makeThrownPredicate(DiagnosticPosition pos, JCIdent exceptionId, MethodSymbol sym) {
        int p = pos.getPreferredPosition();
        JCExpression rex = makeType(p,syms.runtimeExceptionType);
//        JCExpression ex = makeType(p,syms.exceptionType);
        JCExpression condd = factory.at(pos).TypeTest(exceptionId, rex).setType(syms.booleanType);
//        JCExpression conde = factory.at(pos).TypeTest(exceptionId, ex).setType(syms.booleanType);
//        condd = makeAnd(p,condd,conde); // FIXME - why this redundancy?
        for (Type t: sym.getThrownTypes()) {
            JCExpression tc = factory.at(pos).TypeTest(exceptionId, makeType(p,t)).setType(syms.booleanType);
            condd = makeOr(p, condd, tc);
        }
        return condd;
    }
   
    /** Makes a Java method invocation using the given MethodSymbol, on the given receiver,
     * with the given arguments, at the given position; no varargs, no typeargs.
     */
    public JCMethodInvocation makeMethodInvocation(DiagnosticPosition pos, JCExpression receiver, MethodSymbol sym, JCExpression ... args) {
        JCExpression meth = factory.at(pos).Ident(sym);
        if (receiver != null) meth = makeSelect(pos.getPreferredPosition(), receiver, sym);
        List<JCExpression> nargs;
        if (args.length == 0) {
            nargs = List.<JCExpression>nil();
        } else {
            ListBuffer<JCExpression> a = new ListBuffer<JCExpression>();
            for (JCExpression arg: args) a.add(arg);
            nargs = a.toList();
        }
        JCMethodInvocation call = factory.at(pos).Apply(List.<JCExpression>nil(), meth, nargs);
        call.type = sym.type.getReturnType();
        call.varargsElement = null;
        return call;
    }
    
    public JCMethodInvocation makeMethodInvocation(DiagnosticPosition pos, JCExpression receiver, MethodSymbol sym, List<JCExpression> nargs) {
        JCExpression meth = factory.at(pos).Ident(sym);
        if (receiver != null) meth = makeSelect(pos.getPreferredPosition(), receiver, sym);
        JCMethodInvocation call = factory.at(pos).Apply(List.<JCExpression>nil(), meth, nargs);
        call.type = sym.type.getReturnType();
        call.varargsElement = null;
        return call;
    }
    
    public JCMethodInvocation makeMethodInvocation(DiagnosticPosition pos, JCExpression receiver, Name name, JCExpression ... nargs) {
        Scope sc = receiver.type.tsym.members();
        Symbol sym = sc.getElementsByName(name).iterator().next();
        return makeMethodInvocation(pos, receiver, (MethodSymbol)sym, nargs);
    }
    
    /** Makes a Java method invocation using the given MethodSymbol, on the given receiver,
     * with the given arguments, at the given position; no varargs, no typeargs.
     */
    public JmlMethodInvocation makeJmlMethodInvocation(DiagnosticPosition pos, JmlTokenKind token, Type type, JCExpression ... args) {
        ListBuffer<JCExpression> a = new ListBuffer<JCExpression>();
        a.appendArray(args);
        JmlMethodInvocation call = factory.at(pos).JmlMethodInvocation(token, a.toList());
        call.type = type;
        call.meth = null;
        call.typeargs = null;
        call.varargsElement = null;
        return call;
    }
    
    public JmlMethodInvocation makeJmlMethodInvocation(DiagnosticPosition pos, IJmlClauseKind token, Type type, JCExpression ... args) {
        ListBuffer<JCExpression> a = new ListBuffer<JCExpression>();
        a.appendArray(args);
        JmlMethodInvocation call = factory.at(pos).JmlMethodInvocation(token, a.toList());
        call.type = type;
        call.meth = null;
        call.typeargs = null;
        call.varargsElement = null;
        return call;
    }
    
    public JmlMethodInvocation makeJmlMethodInvocation(DiagnosticPosition pos, String token, Type type, JCExpression ... args) {
        ListBuffer<JCExpression> a = new ListBuffer<JCExpression>();
        a.appendArray(args);
        JmlMethodInvocation call = factory.at(pos).JmlMethodInvocation(token, a.toList());
        call.type = type;
        call.meth = null;
        call.typeargs = null;
        call.varargsElement = null;
        return call;
    }
    
    
    // FIXME _ document
    public JCMethodDecl makeMethodDefNoArg(JCModifiers mods, Name methodName, Type resultType, ClassSymbol ownerClass) {

        MethodType mtype = new MethodType(List.<Type>nil(),resultType,List.<Type>nil(),ownerClass);

        MethodSymbol msym = new MethodSymbol(
                mods.flags, 
                methodName, 
                mtype, 
                ownerClass);

        JCMethodDecl mdecl = factory.MethodDef(
                msym,
                factory.Block(0,List.<JCStatement>nil()));

        ownerClass.members_field.enter(msym);
        return mdecl;
    }
    
    /** Makes a new MethodSymbol, given its various properties */
    public MethodSymbol makeMethodSym(JCModifiers mods, Name methodName, Type resultType, TypeSymbol ownerClass, List<Type> argtypes) {

        MethodType mtype = new MethodType(List.<Type>nil(),resultType,argtypes,ownerClass);

        return new MethodSymbol(
                mods.flags, 
                methodName, 
                mtype, 
                ownerClass);

    }
    
    public JCExpression makeTypeCast(DiagnosticPosition pos, Type type, JCExpression expr) {
        return factory.at(pos).TypeCast(type, expr);
    }
    
    public JCTree.JCInstanceOf makeInstanceOf(int pos, JCExpression expr, JCExpression clazz) {
        if (clazz.toString().equals("\\bigint")) Utils.stop();
        JCTree.JCInstanceOf t = factory.at(pos).TypeTest(expr, clazz);
        t.type = syms.booleanType;
        return t;
    }

    public JCTree.JCInstanceOf makeInstanceOf(int pos, JCExpression expr, Type t) {
        return makeInstanceOf(pos,expr,makeType(pos,t));
    }

    /** Makes a JML \typeof expression, with the given expression as the argument */
    public JCExpression makeTypeof(JCExpression e) {
        JmlMethodInvocation typeof = factory.at(e.pos).JmlMethodInvocation(typeofKind,e);
        typeof.type = types.TYPE;
        typeof.kind = typeofKind;
        return typeof;
    }
    
    /** Makes a JML \type expression, with the given expression as the argument */
    public JCExpression makeTypelc(JCExpression e) {
        JmlMethodInvocation typeof = factory.at(e.pos).JmlMethodInvocation(typelcKind,e);
        typeof.type = types.TYPE;
        return typeof;
    }
    
    /** Makes an equivalent of \erasure(\typeof ) expression, with the given expression as the argument */
    public JCExpression makeJavaTypelc(JCExpression e) {
        JmlMethodInvocation type = factory.at(e.pos).JmlMethodInvocation(typelcKind,e);
        type.javaType = true;
        type.type = syms.classType;
        return type;
    }
    
    public JCExpression makeElemtype(JCExpression e) {
        JmlMethodInvocation elem = factory.at(e.pos).JmlMethodInvocation(elemtypeKind,e);
        elem.type = types.TYPE;
        elem.kind = elemtypeKind;
        return elem;
    }
    
    public JCExpression makeSubtype(DiagnosticPosition pos, JCExpression e1, JCExpression e2) {
        JmlMethodInvocation e = factory.at(pos).JmlMethodInvocation(JmlTokenKind.SUBTYPE_OF,e1,e2);
        e.type = syms.booleanType;
        return e;
    }
    
    /** Returns the AST for ( \typeof(id) == \type(type) && id instanceof 'erasure of type') */
    public JCExpression makeDynamicTypeEquality(DiagnosticPosition pos, JCExpression id, Type type) {
        int p = pos.getPreferredPosition();
        // FIXME - this does not handle intersection types
        if (type instanceof IntersectionClassType) {
//            log.warning(pos,  "jml.message", "Intersection type not handled: " + type.toString());
        }
        
        JCExpression lhs = makeTypeof(id);
        JmlMethodInvocation rhs = factory.at(p).JmlMethodInvocation(typelcKind,makeType(p,type));
        rhs.type = JmlTypes.instance(context).TYPE;
        JCExpression expr = makeEqObject(p,lhs,rhs);
        // FIXME - the check below just until unerased types are supported in boogie
        if (!JmlOption.isOption(context, JmlOption.BOOGIE)) {
            expr = makeAnd(p,expr,
                makeJmlMethodInvocation(pos,JmlTokenKind.SUBTYPE_OF,syms.booleanType,lhs,rhs));
            {
                Type t = types.erasure(type);
                if (!t.isPrimitive() && t.getKind() != TypeKind.ARRAY) {
                    JCTree.JCInstanceOf tt = makeInstanceOf(p,id,types.erasure(type));
                    expr = makeAnd(p,tt,expr);
                }
            }
            if (type.getTag() == TypeTag.ARRAY) {
                Type compType = ((Type.ArrayType)type).getComponentType();
                JmlMethodInvocation ct = factory.at(p).JmlMethodInvocation(typelcKind,makeType(p,compType));
                JCExpression e = makeTypeof(id);
                e = factory.at(p).JmlMethodInvocation(elemtypeKind,e);
                e.type = ct.type = types.TYPE;
                e = makeEqObject(p, e, ct);
                expr = makeAnd(p,expr,e);
            }
        }
        
        if (!type.isPrimitive() ) {
            JCExpression ex = makeEqNull(id.pos, id);
            expr = makeOr(p,ex,expr);
        }

        return expr;
    }

    // requires id to have a reference type
    /** Returns the AST for id == null || ( \typeof(id) <: \type(type) && id instanceof 'erasure of type') */
    public JCExpression makeDynamicTypeInEquality(DiagnosticPosition pos, JCExpression id, Type type) {
        int p = pos == null ? Position.NOPOS: pos.getPreferredPosition();
        JCExpression nn = makeEqObject(p,id,nullLit);
        
        return makeOr(p,nn,makeNonNullDynamicTypeInEquality(pos, id, type));
    }
    
    /** Returns the AST for \typeof(id) <: \type(type) && id instanceof 'erasure of type' */
    public JCExpression makeNonNullDynamicTypeInEquality(DiagnosticPosition pos, JCExpression id, Type type) {
        if (type instanceof IntersectionClassType) {
            IntersectionClassType itype = (IntersectionClassType)type;
            List<Type> ecomp = itype.getExplicitComponents();
            //List<Type> comp = itype.getComponents();// FIXME - not sure how this is different than the above
            JCExpression ee = trueLit;
            for (Type ictype: ecomp) {
                JCExpression e = makeNonNullDynamicTypeInEquality(pos, id, ictype);
                ee = makeAndSimp(pos.getPreferredPosition(), ee,e);
            }
            return ee;
        }
        int p = pos.getPreferredPosition();
        if (type.getKind().isPrimitive()) return trueLit;
        JCExpression lhs = makeTypeof(id); // FIXME - copy?
        JmlMethodInvocation rhs = factory.at(p).JmlMethodInvocation(typelcKind,makeType(p,type));
        rhs.type = JmlTypes.instance(context).TYPE;
        JCExpression expr = makeJmlMethodInvocation(pos,JmlTokenKind.SUBTYPE_OF,syms.booleanType,lhs,rhs);
        {
            if (type.getKind() != TypeKind.ARRAY) {
                JCTree.JCInstanceOf tt = makeInstanceOf(p,id,types.erasure(type));
                expr = makeAnd(p,tt,expr);
                if (JmlOption.isOption(context, JmlOption.BOOGIE)) expr = tt; // FIXME - just until Boogie handles unerased types
            } else {
                Type comptype = ((Type.ArrayType)type).elemtype;
                JCExpression e = makeTypeof(id);
                e = makeJmlMethodInvocation(pos,elemtypeKind,e.type,e);
                ((JmlMethodInvocation)e).kind = elemtypeKind;
                JmlMethodInvocation tt = factory.at(p).JmlMethodInvocation(typelcKind,makeType(p,comptype));
                tt.type = JmlTypes.instance(context).TYPE;
                if (comptype.isPrimitive()) e = makeEquality(p,e,tt);
                else e = makeJmlMethodInvocation(pos,JmlTokenKind.SUBTYPE_OF,syms.booleanType,e,tt);
                expr = makeAnd(p,expr,e);
            }
        }
        return expr;
    }
    
    /** Creates an AST for an invocation of a (static) method in org.jmlspecs.utils.Utils,
     * with the given name and arguments.
     * @param pos the node position of the new AST
     * @param methodName the name of the method to call
     * @param args the expressions that are the arguments of the call
     * @return the resulting AST
     */
    public JCMethodInvocation makeUtilsMethodCall(int pos, String methodName, List<JCExpression> args) {
        // presumes the arguments are all properly attributed
        JCFieldAccess meth = findUtilsMethod(pos,methodName);
        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
        list.addAll(args);
        JCMethodInvocation call = factory.at(pos).Apply(List.<JCExpression>nil(),meth,list.toList());
        call.type = ((MethodType)meth.type).getReturnType();
        return call;
    }

    /** Creates an AST for an invocation of a (static) method in org.jmlspecs.utils.Utils,
     * with the given name and arguments.
     * @param pos the node position of the new AST
     * @param methodName the name of the method to call
     * @param args the expressions that are the arguments of the call
     * @return the resulting AST
     */
    public JCMethodInvocation makeUtilsMethodCall(int pos, String methodName, JCExpression... args) {
        // presumes the arguments are all properly attributed
        factory.at(pos);
        JCFieldAccess meth = findUtilsMethod(pos,methodName);
        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
        list.appendArray(args);
        JCMethodInvocation call = factory.Apply(List.<JCExpression>nil(),meth,list.toList());
        if (meth.type instanceof Type.ErrorType) {
        	log.error("esc.incomplete.typechecking",meth.sym.toString());
        	throw new JmlInternalAbort();
        } else if (meth.type instanceof MethodType)
            call.type = ((MethodType)meth.type).getReturnType();
        else
            call.type = ((Type.ForAll)meth.type).getReturnType();
        return call;
    }

    public JCStatement makeUtilsMethodStat(int pos, String methodName, JCExpression... args) {
        JCMethodInvocation m = makeUtilsMethodCall(pos, methodName, args);
        return factory.at(pos).Exec(m);
    }

    public JCExpression copyArray(int pos, JCExpression ad) {
        Type t = ((Type.ArrayType)ad.type).getComponentType(); 
        JCExpression a = null;
        switch (t.getTag()) {
            case INT:
                a = makeUtilsMethodCall(pos,"copyIntArray",ad);
                break;
            case BOOLEAN:
                a = makeUtilsMethodCall(pos,"copyBooleanArray",ad);
                break;
            case CLASS:
                a = makeUtilsMethodCall(pos,"copyArray",ad);
                break;
            case SHORT:
                a = makeUtilsMethodCall(pos,"copyShortArray",ad);
                break;
            case CHAR:
                a = makeUtilsMethodCall(pos,"copyCharArray",ad);
                break;
            case BYTE:
                a = makeUtilsMethodCall(pos,"copyByteArray",ad);
                break;
            case FLOAT:
                a = makeUtilsMethodCall(pos,"copyFloatArray",ad);
                break;
            case DOUBLE:
                a = makeUtilsMethodCall(pos,"copyDoubleArray",ad);
                break;
            default:
                a = null; // FIXME - error
        }
        return a;
    }

    // FIXME - review & document - for ESC
    public JCExpression makeDotClass(int pos, Type type) {
        if (type.tsym instanceof ClassSymbol) type = ((ClassSymbol)type.tsym).erasure(Types.instance(context));
        JCExpression tt = makeType(pos,type);
        JCFieldAccess result = factory.Select(tt,names._class);
        result.pos = pos;
        Type t = syms.classType;
        List<Type> typeargs = List.of(type);
        t = new ClassType(t.getEnclosingType(), typeargs, t.tsym);
        result.sym = new VarSymbol(
            STATIC | PUBLIC | FINAL, names._class, t, type.tsym);
        result.type = result.sym.type;
        return result;
    }

    public JCFieldAccess makeArrayLength(int pos, JCExpression array) {
        JCFieldAccess fa = (JCFieldAccess)factory.Select(array, syms.lengthVar);
        fa.pos = pos;
        fa.type = syms.intType;
        return fa;
    }
    
    public JCExpression makeArrayElement(int pos, JCExpression array, JCExpression index) {
        JCExpression e = factory.Indexed(array,  index);
        e.pos = pos;
        e.type = ((Type.ArrayType)array.type).elemtype;
        return e;
    }
    
    // FIXME - review & document - translates a type into ESC logic
    public JCExpression trType(int pos, Type type) {
        JCTree tree = factory.at(pos).Type(type);
        return trType(pos,tree);
    }
    
    // FIXME - review & document
    public JCExpression trType(int pos, JCTree type) {
        JCExpression result = null;
        if (type instanceof JCTypeApply) {
            // Convert a literal generic type, e.g. Vector<String>
            // into a function that creates type objects:
            // Utils.makeType(Vector.class,\type(String));
            JCExpression headType = ((JCTypeApply)type).clazz; 
            // t.type is the actual Java type of the head (e.g. java.util.Vector)
            // What we want is a Java class literal
            headType = makeDotClass(type.pos,headType.type);
            ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
            args.append(headType);
            for (JCExpression tt: ((JCTypeApply)type).arguments) args.append(trType(tt.pos,tt));
            int n = args.size()-1;
            if (n <= 2) {
                result = makeUtilsMethodCall(pos,"makeTYPE"+n,args.toList());
            } else {
                // FIXME - we need to make an array argument here.
                result = makeUtilsMethodCall(pos,"makeTYPE",args.toList());
            }
        } else if (type instanceof JCIdent) {
            if (type.type instanceof TypeVar) {
                // This is a generic type variable
                result = (JCIdent)type;
                
            } else {
                JCExpression headType = (JCIdent)type; 
                // t.type is the actual Java type of the head (e.g. java.util.Vector)
                // What we want is a Java class literal
                headType = makeDotClass(type.pos,headType.type);
                result = makeUtilsMethodCall(pos,"makeTYPE0",headType);
            }
        } else if (type instanceof JCFieldAccess) {
            JCExpression headType = (JCFieldAccess)type; 
            // t.type is the actual Java type of the head (e.g. java.util.Vector)
            // What we want is a Java class literal
            headType = makeDotClass(type.pos,headType.type);
            result = makeUtilsMethodCall(pos,"makeTYPE0",headType);
        } else if (type instanceof JCArrayTypeTree) {
            JCExpression headType = (JCArrayTypeTree)type; 
            // t.type is the actual Java type of the head (e.g. java.util.Vector)
            // What we want is a Java class literal
            headType = makeDotClass(type.pos,headType.type);
            result = makeUtilsMethodCall(pos,"makeTYPE0",headType);
        } else if (type instanceof JCPrimitiveTypeTree) {
            // FIXME - this does not work
            JCExpression headType = (JCPrimitiveTypeTree)type;
            headType = makeDotClass(type.pos,headType.type);
            result = makeUtilsMethodCall(pos,"makeTYPE0",headType);
        } else if (type instanceof JCWildcard) {
            result = (JCWildcard)type; // FIXME - is this right?
        } else {
            log.getWriter(WriterKind.NOTICE).println("NOT IMPLEMENTED (JmlTreeUtils) - " + type.getClass());
            //result = type;
            // Unknown - FIXME - error
        }
        return result;
    }
    
    public JCExpression convertToString(JCExpression that) {
        String n;
        switch(that.type.getTag()) {
            case CLASS:    n = "toStringObject"; break;
            case INT:      n = "toStringInt"; break;
            case LONG:     n = "toStringLong"; break;
            case BOOLEAN:  n = "toStringBoolean"; break;
            case SHORT:    n = "toStringShort"; break;
            case BYTE:     n = "toStringByte"; break;
            case DOUBLE:   n = "toStringDouble"; break;
            case FLOAT:    n = "toStringFloat"; break;
            case CHAR:     n = "toStringChar"; break;
            default:
                log.warning("jml.internal", "Missing case in Utils.convertToType");
                return null;
        }
        JCExpression e = makeUtilsMethodCall(that.pos,n,that);
        e.type = syms.stringType;
        return e;
    }
    
    public Map<Symbol.TypeSymbol,Type> accumulateTypeInstantiations(List<Type> formals, List<JCExpression> exprs) {
        Map<Symbol.TypeSymbol,Type> map = new java.util.HashMap<>();
        while (formals.head != null && exprs.head != null) {
            accumulateTypeInstantiations(formals.head, exprs.head.type, map);
            formals = formals.tail;
            exprs = exprs.tail;
        }
        if (formals.head != null || exprs.head != null) {
            log.error("jml.internal","Mismatch in number of arguments in accumulateTypeInstantiations");
        }
        return map;
    }
    
    public void accumulateTypeInstantiations(Type formal, Type targetType, Map<Symbol.TypeSymbol,Type> map) {
        if (formal instanceof TypeVar) {
            map.put(((TypeVar)formal).tsym, targetType);
            return;
        }
        if (formal instanceof Type.WildcardType) {
            map.put(((Type.WildcardType)formal).tsym, targetType);
            return;
        }
        if (targetType.tsym.isSubClass(formal.tsym, types)) {
            accumulateTypeInstantiations(formal.allparams(), targetType.allparams(), map);
        }
        // FIXME - iterate to deepser levels as well.
    }

    public void accumulateTypeInstantiations(List<Type> formals, List<Type> targetTypes, Map<Symbol.TypeSymbol,Type> map) {
        while (formals.head != null && targetTypes.head != null) {
            accumulateTypeInstantiations(formals.head, targetTypes.head, map);
            formals = formals.tail;
            targetTypes = targetTypes.tail;
        }
        if (formals.head != null || targetTypes.head != null) {
            log.error("jml.internal","Mismatch in number of arguments in accumulateTypeInstantiations");
        }
    }
    
    // FIXME _ use a type visitor
    
    public Type mapTypeVars(Type t, Map<Symbol.TypeSymbol,Type> map) {
        if (t instanceof TypeVar) {
            Type r = map.get(t.tsym);
            if (r == null) r = t;
            return r;
        } else {
            List<Type> args = t.allparams();
            List<Type> newargs = mapTypeVars(args, map);
            if (newargs == args) return t;
            return new Type.ClassType(Type.noType, newargs, t.tsym);
        }
    }
    
    public List<Type> mapTypeVars(List<Type> tlist, Map<Symbol.TypeSymbol,Type> map) {
        ListBuffer<Type> buf = new ListBuffer<>();
        boolean changed = false;
        for (Type t: tlist) {
            Type tt = mapTypeVars(t,map);
            buf.add(tt);
            changed = changed || t != tt;
        }
        if (changed) return buf.toList();
        buf.clear();
        return tlist;
    }


    
}
