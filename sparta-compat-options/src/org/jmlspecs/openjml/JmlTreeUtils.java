package org.jmlspecs.openjml;

import static com.sun.tools.javac.code.Flags.FINAL;
import static com.sun.tools.javac.code.Flags.PUBLIC;
import static com.sun.tools.javac.code.Flags.STATIC;

import java.util.Arrays;
import java.util.Map;

import javax.lang.model.type.TypeKind;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.esc.Label;

import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.code.Type.TypeVar;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.JCArrayTypeTree;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCAssignOp;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCCatch;
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
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
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
    @NonNull final protected Types types;
    
//    /** The Env in which to do resolving */
//    @NonNull protected Env<AttrContext> attrEnv;
        
    /** The factory used to create AST nodes, initialized in the constructor */
    @NonNull final public JmlTree.Maker factory;

    // Cached values of all of these symbols
    final public ClassSymbol utilsClass;
    final public JCIdent utilsClassIdent;
    final public Symbol andSymbol;
    final public Symbol orSymbol;
    final public Symbol intbitandSymbol;
    final public Symbol longbitandSymbol;
    final public Symbol bitorSymbol;
    final public Symbol notSymbol;
    final public Symbol objecteqSymbol;
    final public Symbol objectneSymbol;
    final public Symbol booleqSymbol;
    final public Symbol boolneSymbol;
    final public Symbol intminusSymbol;
    final public Symbol intplusSymbol;
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
    final public JCLiteral trueLit;
    final public JCLiteral falseLit;
    final public JCLiteral zero;
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
        andSymbol = findOpSymbol(JCTree.AND,syms.booleanType);
        orSymbol = findOpSymbol(JCTree.OR,syms.booleanType);
        intbitandSymbol = findOpSymbol(JCTree.BITAND,syms.intType);
        longbitandSymbol = findOpSymbol(JCTree.BITAND,syms.longType);
        bitorSymbol = findOpSymbol(JCTree.BITOR,syms.booleanType);
        notSymbol = findOpSymbol(JCTree.NOT,syms.booleanType);
        objecteqSymbol = findOpSymbol(JCTree.EQ,syms.objectType);
        objectneSymbol = findOpSymbol(JCTree.NE,syms.objectType);
        booleqSymbol = findOpSymbol(JCTree.EQ,syms.booleanType);
        boolneSymbol = findOpSymbol(JCTree.NE,syms.booleanType);
        intminusSymbol = findOpSymbol(JCTree.MINUS,syms.intType);
        intplusSymbol = findOpSymbol(JCTree.PLUS,syms.intType);
        inteqSymbol = findOpSymbol(JCTree.EQ,syms.intType);
        intneqSymbol = findOpSymbol(JCTree.NE,syms.intType);
        intgtSymbol = findOpSymbol(JCTree.GT,syms.intType);
        intltSymbol = findOpSymbol(JCTree.LT,syms.intType);
        intleSymbol = findOpSymbol(JCTree.LE,syms.intType);
        longleSymbol = findOpSymbol(JCTree.LE,syms.longType);
        longltSymbol = findOpSymbol(JCTree.LT,syms.longType);
        longeqSymbol = findOpSymbol(JCTree.EQ,syms.longType);
        longminusSymbol = findOpSymbol(JCTree.MINUS,syms.longType);
        longplusSymbol = findOpSymbol(JCTree.PLUS,syms.longType);
        trueLit = makeLit(0,syms.booleanType,1);
        falseLit = makeLit(0,syms.booleanType,0);
        zero = makeLit(0,syms.intType,0);
        one = makeLit(0,syms.intType,1);
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
        Map<JCTree,Integer> z = log.currentSource().getEndPosTable();
        if (z != null) {
        	int end = srcnode.getEndPosition(z);
        	z.put(newnode, end);
        }
    }

    /** Finds the Symbol for the operator given an optag (e.g. JCTree.AND) and an
     * argument type.  Note that for object equality, the argument type must be
     * Object, not another reference class - better to use makeEqObject in that
     * case.
     * @param optag the optag of the builtin operator, e.g. JCTree.AND
     * @param argtype the argument type
     * @return the symbol of the operator
     */
    public Symbol findOpSymbol(int optag, Type argtype) {
        Name opName = TreeInfo.instance(context).operatorName(optag);
        Scope.Entry e = syms.predefClass.members().lookup(opName);
        while (e != null && e.sym != null) {
            if (types.isSameType(((MethodType)e.sym.type).argtypes.head,argtype)) return e.sym;
            e = e.next();
        }
        if (argtype != syms.objectType && !argtype.isPrimitive()) return findOpSymbol(optag,syms.objectType);
        throw new JmlInternalError("The operation symbol " + opName + " for type " + argtype + " could not be resolved");
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
    /** Returns true if the argument is a type name (e.g., A or tt.A)
     * rather than an identifier for a variable or field or other
     * kind of expression.
     */
    public boolean isATypeTree(JCExpression tree) {
        if (tree instanceof JCIdent) {
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
        return tree;
    }
    
    /** Make an attributed tree representing a literal - NOT FOR BOOLEAN or NULL or CHARACTER values.
     *  @param pos        The node position
     *  @param type       The literal's type.
     *  @param value      The literal's value; use 0 or 1 for Boolean; use an int for char literals.
     */
    public JCLiteral makeLit(int pos, Type type, Object value) {
        return factory.at(pos).Literal(type.tag, value).setType(type.constType(value));
    }

    /** Returns true if the argument is a boolean Literal with value true */
    public boolean isTrueLit(JCTree tree) {
        if (tree == trueLit) return true;
        if (!(tree instanceof JCLiteral)) return false;
        if (tree.type.tag != TypeTags.BOOLEAN) return false;
        return (Boolean)((JCLiteral)tree).getValue();
    }
    
    /** Returns true if the argument is a boolean Literal with value true */
    public boolean isFalseLit(JCTree tree) {
        if (tree == falseLit) return true;
        if (!(tree instanceof JCLiteral)) return false;
        if (tree.type.tag != TypeTags.BOOLEAN) return false;
        return !(Boolean)((JCLiteral)tree).getValue();
    }
    
    /** Makes an attributed AST that is a copy of a given literal AST,
     * but with the new position. */
    public JCLiteral makeDuplicateLiteral(int pos, JCLiteral lit) {
        // Note that lit.typetag can be different from lit.type.tag - e.g for null values
        return factory.at(pos).Literal(lit.typetag, lit.value).setType(lit.type.constType(lit.value));
    }
    
    /** Make an attributed tree representing an integer literal. */
    public JCLiteral makeIntLiteral(int pos, int value) {
        return factory.at(pos).Literal(TypeTags.INT, value).setType(syms.intType.constType(value));
    }

    /** Make an attributed tree representing an long literal. */
    public JCLiteral makeLongLiteral(int pos, long value) {
        return factory.at(pos).Literal(TypeTags.LONG, value).setType(syms.longType.constType(value));
    }

    /** Make an attributed tree representing a null literal. */
    public JCLiteral makeNullLiteral(int pos) {
        return makeDuplicateLiteral(pos,nullLit);
    }

    /** Makes a constant boolean literal AST node.
     * @param pos the position to use for the node
     * @param value the boolean value of the constant node
     * @return the AST node
     */
    public JCLiteral makeBooleanLiteral(int pos, boolean value) {
        int v = value?1:0;
        JCLiteral r = factory.at(pos).Literal(TypeTags.BOOLEAN,v);
        r.type = syms.booleanType.constType(v);
        return r;
    }

    /** Makes a constant String literal AST node.
     * @param pos the position to use for the node
     * @param value the String value of the constant node
     * @return the AST node
     */
    public JCLiteral makeStringLiteral(int pos, String value) {
        JCLiteral r = factory.at(pos).Literal(TypeTags.CLASS,value);
        r.type = syms.stringType.constType(value);
        return r;
    }

    /** Make a zero-equivalent constant node of the given type
     * @param type the type of the node, e.g. syms.intType
     * @return the AST node
     */ 
    public JCLiteral makeZeroEquivalentLit(int pos, Type type) {
        switch (type.tag) {
            case TypeTags.CHAR:
                return makeLit(pos,type,0); // Character literal requires an int value
            case TypeTags.LONG:
                return makeLit(pos,type,(long)0);
            case TypeTags.INT:
                return makeLit(pos,type,0);
            case TypeTags.SHORT:
                return makeLit(pos,type,(short)0);
            case TypeTags.BYTE:
                return makeLit(pos,type,(byte)0);
            case TypeTags.BOOLEAN:
                return makeLit(pos,type,0); // Boolean literal requires an int value
            case TypeTags.FLOAT:
                return makeLit(pos,type,0.0f);
            case TypeTags.DOUBLE:
                return makeLit(pos,type,0.0);
            case TypeTags.CLASS:
            case TypeTags.ARRAY:
            default:
                return makeNullLiteral(pos);
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
    public JCAssignOp makeAssignOp(int pos, int op, JCExpression lhs, JCExpression rhs) {
        JCAssignOp asn = factory.at(pos).Assignop(op, lhs, rhs);
        asn.setType(lhs.type);
        asn.operator = findOpSymbol(op - JCTree.ASGOffset,asn.lhs.type);
        return asn;
    }

    /** Makes a JML assume statement */
    public JmlStatementExpr makeAssume(DiagnosticPosition pos, Label label, JCExpression expr) {
        JmlStatementExpr e = factory.at(pos).JmlExpressionStatement(JmlToken.ASSUME, label, expr);
        e.associatedPos = Position.NOPOS;
        e.associatedSource = null;
        return e;
    }

    /** Makes a JML assert statement */
    public JmlStatementExpr makeAssert(DiagnosticPosition pos, Label label, JCExpression expr) {
        JmlStatementExpr e = factory.at(pos).JmlExpressionStatement(JmlToken.ASSERT, label, expr);
        e.associatedPos = Position.NOPOS;
        e.associatedSource = null;
        return e;
    }

    /** Returns the 'larger' of the two types as numeric types are compared;
     * not appropriate for Boolean types; floats test larger than long */
    private Type maxType(Type lhs, Type rhs) {
        Type t = lhs.tag >= rhs.tag || rhs.tag == TypeTags.BOT ? lhs : rhs;
        if (TypeTags.INT > t.tag) t = syms.intType;
        return t;
    }
    
    /** Makes a Java unary operator node; it may be constant-folded
     * @param pos the pseudo source code location of the node
     * @param optag the unary operator, e.g. JCTree.NOT, JCTree.NEG, JCTree.COMPL, ...
     * @param expr the argument expression
     * @return the new node
     */
    public JCExpression makeUnary(int pos, int optag, JCExpression expr) {
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
    public JCExpression makeUnary(int pos, int optag, Symbol opsymbol, JCExpression expr) {
        JCUnary e = factory.at(pos).Unary(optag,expr);
        e.operator = opsymbol;
        e.type = e.operator.type.getReturnType();
        copyEndPosition(e,expr);
        return e;
    }

    /** Make an attributed unary NOT(!) expression
     *  @param pos    The position at which to put the new AST.
     *  @param arg    The operator's argument.
     */
    public JCExpression makeNot(int pos, JCExpression arg) {
        return makeUnary(pos,JCTree.NOT,arg);
    }

    /** Make an attributed binary expression.
     *  @param pos      The pseudo-position at which to place the node
     *  @param optag    The operator's operation tag (e.g. JCTree.PLUS).
     *  @param opSymbol The symbol for the operation
     *  @param lhs      The operator's left argument.
     *  @param rhs      The operator's right argument.
     */
    public JCBinary makeBinary(int pos, int optag, Symbol opSymbol, JCExpression lhs, JCExpression rhs) {
        JCBinary tree = factory.at(pos).Binary(optag, lhs, rhs);
        tree.operator = opSymbol;
        tree.type = tree.operator.type.getReturnType();
        //copyEndPosition(tree,rhs);
        return tree;
    }

    /** Makes an attributed Java binary operator node (with boolean result)
     * @param pos the pseudo source code location of the node
     * @param optag the binary operator (producing a boolean result), e.g. JCTree.EQ
     * @param lhs the left-hand expression
     * @param rhs the right-hand expression
     * @return the new node
     */
    public JCBinary makeBinary(int pos, int optag, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,optag,findOpSymbol(optag,maxType(lhs.type.baseType(),rhs.type.baseType())),lhs,rhs);
    }

    /** Produces an Equality AST node; presumes that the lhs and rhs have the 
     * same type.
     * @param pos the position of the node
     * @param lhs the left argument
     * @param rhs the right argument
     * @return the AST
     */
    public JCBinary makeEquality(int pos, JCExpression lhs, JCExpression rhs) {
        JCBinary tree = factory.at(pos).Binary(JCTree.EQ, lhs, rhs);
        Type t = lhs.type;
        if (t.isPrimitive() && TypeTags.INT > t.tag) t = syms.intType;
        tree.operator = findOpSymbol(JCTree.EQ, t);
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
    public JmlBinary makeJmlBinary(int pos, JmlToken op, JCExpression lhs, JCExpression rhs) {
        JmlBinary e = factory.at(pos).JmlBinary(op,lhs,rhs);
        e.type = syms.booleanType;
        copyEndPosition(e,rhs);
        return e;
    }

    /** Makes an attributed AST for a short-circuit boolean AND expression */
    public JCExpression makeAnd(int pos, JCExpression lhs, JCExpression rhs) {
        if (lhs == null) {
            System.out.println("BAD AND");
        }
        return makeBinary(pos,JCTree.AND,andSymbol,lhs,rhs);
    }

    /** Makes an attributed AST for a short-circuit boolean OR expression */
    public JCExpression makeOr(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.OR,orSymbol,lhs,rhs);
    }

    /** Makes an attributed attributed AST for a non-short-circuit boolean OR expression */
    public JCExpression makeBitOr(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.BITOR,bitorSymbol,lhs,rhs);
    }

    /** Makes an attributed AST for the Java equivalent of a JML IMPLIES expression */
    public JCExpression makeImplies(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.OR,orSymbol,
                makeNot(pos,lhs), rhs);
    }

    /** Makes an attributed AST for a reference equality (==) expression */
    public JCBinary makeEqObject(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.EQ,objecteqSymbol,lhs, rhs);
    }

    /** Makes an attributed AST for a reference inequality (!=) expression */
    public JCBinary makeNeqObject(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.NE,objectneSymbol,lhs, rhs);
    }
    
    /** Makes an attributed AST for a reference inequality (!=) expression */
    public JCBinary makeNotNull(int pos, JCExpression lhs) {
        return makeBinary(pos,JCTree.NE,objectneSymbol,lhs, nullLit);
    }
    
    /** Makes an attributed AST for a reference inequality (!=) expression */
    public JCBinary makeEqNull(int pos, JCExpression lhs) {
        return makeBinary(pos,JCTree.EQ,objecteqSymbol,lhs, nullLit);
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
        VarSymbol v = new VarSymbol(flags,name,type.baseType(),null);
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

    /** Makes an attributed variable declaration along with a new VarSymbol (which is not 
     * put into the symbol table); the declaration has no modifiers and no initialization.
     * @param type  the type of the new variable
     * @param name  the name of the new variable
     * @param owner the owner of the new variable (e.g. a MethodSymbol or ClassSymbol)
     * @param pos   the position to set
     * @return the AST for the declaration
     */
    public JCVariableDecl makeVarDef(Type type, Name name, Symbol owner, int pos) {
        int modifierFlags = 0;
        VarSymbol v = new VarSymbol(modifierFlags, name, type, owner);
        v.pos = pos;
        JCVariableDecl d = factory.VarDef(v,null);
        d.pos = pos;
        return d;
    }
    
    /** Makes an \old expression */
    public JCMethodInvocation makeOld(int pos, JCExpression arg, JCIdent label) {
        JCMethodInvocation m;
        if (label == null || label.toString().isEmpty()) {
            m = factory.at(pos).JmlMethodInvocation(JmlToken.BSOLD, List.<JCExpression>of(arg));
        } else {
            JCIdent id = factory.at(pos).Ident(label.name);
            id.type = null; // Should never refer to the label's type
            id.sym = null; // Should never refer to the label's symbol
            m = factory.at(pos).JmlMethodInvocation(JmlToken.BSOLD, List.<JCExpression>of(arg, id));
        }
        m.type = arg.type;
        return m;
    }
   
    /** Makes an \old expression */
    public JCMethodInvocation makeOld(DiagnosticPosition pos, JCExpression arg) {
        JCMethodInvocation m;
        m = factory.at(pos).JmlMethodInvocation(JmlToken.BSOLD, List.<JCExpression>of(arg));
        m.type = arg.type;
        return m;
    }
   
    /** Makes a \past expression */
    public JCMethodInvocation makePast(int pos, JCExpression arg, JCIdent label) {
        JCMethodInvocation m;
        if (label.toString().isEmpty()) {
            m = factory.JmlMethodInvocation(JmlToken.BSPAST, List.<JCExpression>of(arg));
        } else {
            JCIdent id = factory.at(pos).Ident(label.name);
            id.type = null; // Should never refer to the label's type
            id.sym = null; // Should never refer to the label's symbol
            m = factory.JmlMethodInvocation(JmlToken.BSPAST, List.<JCExpression>of(arg, id));
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
   
    public JCExpression makeThrownPredicate(DiagnosticPosition pos, JCIdent exceptionId, MethodSymbol sym) {
        int p = pos.getPreferredPosition();
        JCExpression rex = makeType(p,syms.runtimeExceptionType);
        JCExpression ex = makeType(p,syms.exceptionType);
        JCExpression condd = factory.at(pos).TypeTest(exceptionId, rex).setType(syms.booleanType);
        JCExpression conde = factory.at(pos).TypeTest(exceptionId, ex).setType(syms.booleanType);
        condd = makeAnd(p,condd,conde); // FIXME - why this redundancy?
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
    
    /** Makes a Java method invocation using the given MethodSymbol, on the given receiver,
     * with the given arguments, at the given position; no varargs, no typeargs.
     */
    public JmlMethodInvocation makeJmlMethodInvocation(DiagnosticPosition pos, JmlToken token, Type type, JCExpression ... args) {
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
    
    public MethodSymbol makeMethodSym(JCModifiers mods, Name methodName, Type resultType, ClassSymbol ownerClass, List<Type> argtypes) {

        MethodType mtype = new MethodType(List.<Type>nil(),resultType,argtypes,ownerClass);

        return new MethodSymbol(
                mods.flags, 
                methodName, 
                mtype, 
                ownerClass);

    }
    
    public JCTree.JCInstanceOf makeInstanceOf(int pos, JCExpression expr, JCExpression clazz) {
        JCTree.JCInstanceOf t = factory.at(pos).TypeTest(expr, clazz);
        t.type = syms.booleanType;
        return t;
    }

    public JCTree.JCInstanceOf makeInstanceOf(int pos, JCExpression expr, Type t) {
        return makeInstanceOf(pos,expr,makeType(pos,t));
    }

    /** Makes a JML \typeof expression, with the given expression as the argument */
    public JCExpression makeTypeof(JCExpression e) {
        JmlMethodInvocation typeof = factory.at(e.pos).JmlMethodInvocation(JmlToken.BSTYPEOF,e);
        typeof.type = syms.classType;
        return typeof;
    }
    
    /** Returns the AST for ( \typeof(id) == \type(type) && id instanceof 'erasure of type') */
    public JCExpression makeDynamicTypeEquality(DiagnosticPosition pos, JCExpression id, Type type) {
        int p = pos.getPreferredPosition();
        
        JCExpression lhs = makeTypeof(id);
        JmlMethodInvocation rhs = factory.at(p).JmlMethodInvocation(JmlToken.BSTYPELC,makeType(p,type));
        rhs.type = JmlTypes.instance(context).TYPE;
        JCExpression expr = makeEqObject(p,lhs,rhs);
        expr = makeAnd(p,expr,
                makeJmlMethodInvocation(pos,JmlToken.SUBTYPE_OF,syms.booleanType,lhs,rhs));
        {
            Type t = types.erasure(type);
            if (!t.isPrimitive() && t.getKind() != TypeKind.ARRAY) {
                JCTree.JCInstanceOf tt = makeInstanceOf(p,id,types.erasure(type));
                expr = makeAnd(p,tt,expr);
            }
        }
        if (type.tag == TypeTags.ARRAY) {
            Type compType = ((Type.ArrayType)type).getComponentType();
            JmlMethodInvocation ct = factory.at(p).JmlMethodInvocation(JmlToken.BSTYPELC,makeType(p,compType));
            JCExpression e = makeTypeof(id);
            e = factory.at(p).JmlMethodInvocation(JmlToken.BSELEMTYPE,e);
            e = makeEqObject(p, e, ct);
            expr = makeAnd(p,expr,e);
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
        int p = pos.getPreferredPosition();
        JCExpression nn = makeEqObject(p,id,nullLit);
        JCExpression lhs = makeTypeof(id); // FIXME - copy?
        JmlMethodInvocation rhs = factory.at(p).JmlMethodInvocation(JmlToken.BSTYPELC,makeType(p,type));
        rhs.type = JmlTypes.instance(context).TYPE;
        JCExpression expr = makeJmlMethodInvocation(pos,JmlToken.SUBTYPE_OF,syms.booleanType,lhs,rhs);
        {
            if (type.getKind() != TypeKind.ARRAY) {
                JCTree.JCInstanceOf tt = makeInstanceOf(p,id,types.erasure(type));
                expr = makeAnd(p,tt,expr);
            } else {
                Type comptype = ((Type.ArrayType)type).elemtype;
                JCExpression e = makeTypeof(id);
                e = makeJmlMethodInvocation(pos,JmlToken.BSELEMTYPE,e.type,e);
                JmlMethodInvocation tt = factory.at(p).JmlMethodInvocation(JmlToken.BSTYPELC,makeType(p,comptype));
                tt.type = JmlTypes.instance(context).TYPE;
                if (comptype.isPrimitive()) e = makeEquality(p,e,tt);
                else e = makeJmlMethodInvocation(pos,JmlToken.SUBTYPE_OF,syms.booleanType,e,tt);
                expr = makeAnd(p,expr,e);
            }
        }
        return makeOr(p,nn,expr);
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
    
    public JCExpression copyArray(int pos, JCExpression ad) {
        Type t = ((Type.ArrayType)ad.type).getComponentType(); 
        JCExpression a = null;
        switch (t.tag) {
            case TypeTags.INT:
                a = makeUtilsMethodCall(pos,"copyIntArray",ad);
                break;
            case TypeTags.BOOLEAN:
                a = makeUtilsMethodCall(pos,"copyBooleanArray",ad);
                break;
            case TypeTags.CLASS:
                a = makeUtilsMethodCall(pos,"copyArray",ad);
                break;
            case TypeTags.SHORT:
                a = makeUtilsMethodCall(pos,"copyShortArray",ad);
                break;
            case TypeTags.CHAR:
                a = makeUtilsMethodCall(pos,"copyCharArray",ad);
                break;
            case TypeTags.BYTE:
                a = makeUtilsMethodCall(pos,"copyByteArray",ad);
                break;
            case TypeTags.FLOAT:
                a = makeUtilsMethodCall(pos,"copyFloatArray",ad);
                break;
            case TypeTags.DOUBLE:
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
            log.noticeWriter.println("NOT IMPLEMENTED (JmlTreeUtils) - " + type.getClass());
            //result = type;
            // Unknown - FIXME - error
        }
        return result;
    }
    
    public JCExpression convertToString(JCExpression that) {
        String n;
        switch(that.type.tag) {
            case TypeTags.CLASS:    n = "toStringObject"; break;
            case TypeTags.INT:      n = "toStringInt"; break;
            case TypeTags.LONG:     n = "toStringLong"; break;
            case TypeTags.BOOLEAN:  n = "toStringBoolean"; break;
            case TypeTags.SHORT:    n = "toStringShort"; break;
            case TypeTags.BYTE:     n = "toStringByte"; break;
            case TypeTags.DOUBLE:   n = "toStringDouble"; break;
            case TypeTags.FLOAT:    n = "toStringFloat"; break;
            case TypeTags.CHAR:     n = "toStringChar"; break;
            default:
                log.warning("jml.internal", "Missing case in Utils.convertToType");
                return null;
        }
        JCExpression e = makeUtilsMethodCall(that.pos,n,that);
        e.type = syms.stringType;
        return e;
    }
    
}
