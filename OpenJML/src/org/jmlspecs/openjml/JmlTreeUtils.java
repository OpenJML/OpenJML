package org.jmlspecs.openjml;

import static com.sun.tools.javac.code.Flags.FINAL;
import static com.sun.tools.javac.code.Flags.PUBLIC;
import static com.sun.tools.javac.code.Flags.STATIC;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.JmlTree.JmlBinary;

import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.code.Type.TypeVar;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCArrayTypeTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCCatch;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCNewClass;
import com.sun.tools.javac.tree.JCTree.JCPrimitiveTypeTree;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCThrow;
import com.sun.tools.javac.tree.JCTree.JCTypeApply;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

/** This class holds a number of utility functions that create fragments of AST trees
 * (using a factory); the created trees are fully type and symbol attributed and so
 * are to be used in tree transformations after type attribution is complete
 * and successful.  It is the user's responsibility to ensure that the resulting
 * tree is legal (including flow checks) since there will be no further checking.
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
    final public static String utilsClassQualifiedName = "org.jmlspecs.utils.Utils";

    /** The Context in which this object was constructed */ 
    //@ non_null
    final protected Context context;
    
    /** The Attr tool for this context */
    final protected JmlAttr attr;
    
    /** The Log tool for this context */
    final protected Log log;
    
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
    
    /** The Env in which to do resolving */
    @NonNull protected Env<AttrContext> attrEnv;
        
    /** The factory used to create AST nodes, initialized in the constructor */
    @NonNull final public JmlTree.Maker factory;

    /** The type of java.lang.Integer, initialized in the constructor */
    protected Type integerType;
    
    // Cached values of all of these symbols
    protected ClassSymbol utilsClass = null;
    protected JCIdent utilsClassIdent;
    protected Symbol andSymbol;
    protected Symbol orSymbol;
    protected Symbol notSymbol;
    protected Symbol objecteqSymbol;
    protected Symbol booleqSymbol;
    protected Symbol boolneSymbol;
    public JCLiteral trueLit;
    public JCLiteral falseLit;
    public JCLiteral zero;
    public JCLiteral nulllit;
    public JCLiteral maxIntLit;

    /** Indicates when we are within a spec expression */
    boolean inSpecExpression;
    
    DiagnosticPosition make_pos = null;  // Need this as a placeholder,
        // but it should never be used.  It would only be referenced if
        // an attempt to resolve an operator or name failed, and that would
        // be an openjml coding bug.
    ClassSymbol assertionFailureClass;
    final public Name resultName;
    final public Name exceptionName;
    final public Name caughtException;
    
    /** Creates an instance in association with the given Context; 
     * do not call the constructor 
     * directly.
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
        this.types = Types.instance(context);

        ClassReader reader = ClassReader.instance(context);

        Name utilsName = names.fromString(utilsClassQualifiedName);
        this.utilsClass = reader.enterClass(utilsName);
        utilsClassIdent = factory.Ident(utilsName);  // FIXME - should this be some sort of Qualified Ident - a simple Ident seems to work
        utilsClassIdent.type = utilsClass.type;
        utilsClassIdent.sym = utilsClassIdent.type.tsym;
        andSymbol = findOpSymbol("&&",syms.booleanType);
        orSymbol = findOpSymbol("||",syms.booleanType);
        notSymbol = findOpSymbol("!",syms.booleanType);
        objecteqSymbol = findOpSymbol("==",syms.objectType);
        booleqSymbol = findOpSymbol("==",syms.booleanType);
        boolneSymbol = findOpSymbol("!=",syms.booleanType);
        trueLit = makeLit(0,syms.booleanType,1);
        falseLit = makeLit(0,syms.booleanType,0);
        zero = makeLit(0,syms.intType,0);
        nulllit = makeLit(0,syms.botType, null);
        maxIntLit = makeLit(0,syms.intType,Integer.MAX_VALUE);


        assertionFailureClass = reader.enterClass(names.fromString(utilsClassQualifiedName+"$JmlAssertionFailure"));
        integerType = reader.enterClass(names.fromString("java.lang.Integer")).type;
        
        this.resultName = attr.resultName;
        this.exceptionName = attr.exceptionName;
        this.caughtException = names.fromString("_JML$$$caughtException");   // FIXME - do we need this?
        
    }
    
    public void setEnv(Env<AttrContext> env) {
        attrEnv = env;
    }
    
    /** Finds the symbol for the built-in operator with the given argument type
     * @param name the operation, e.g. ">="
     * @param argtype the argument type, e.g. syms.intType;
     * @return the associated symbol
     */
    public Symbol findOpSymbol(String name, Type argtype) {
        Scope.Entry e = syms.predefClass.members().lookup(names.fromString(name));
        while (e != null && e.sym != null) {
            if (types.isSameType(((MethodType)e.sym.type).argtypes.head,argtype)) return e.sym;
            e = e.next();
        }
        if (argtype != syms.objectType && !argtype.isPrimitive()) return findOpSymbol(name,syms.objectType);
        throw new JmlInternalError("The operation symbol " + name + " for type " + argtype + " could not be resolved");
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
    

    
    /** Makes an attributed JCTree for a class literal corresponding to the given type. */
    public JCExpression makeType(int pos, Type type) {
        // factory.Type does produce an attributed tree - after all we start knowing the type
        JCExpression tree = factory.at(pos).Type(type);
        return tree;
    }
    
    /** Make an attributed tree representing a literal - NOT FOR BOOLEAN VALUES.
     *  @param pos        The node position
     *  @param type       The literal's type.
     *  @param value      The literal's value.
     */
    public JCLiteral makeLit(int pos, Type type, Object value) { // FIXME  I don't think it is correct for char literals
        return factory.at(pos).Literal(type.tag, value).setType(type.constType(value));
    }
    
    /** Make an attributed tree representing an integer literal. */
    public JCLiteral makeIntLit(int pos, int value) {
        return factory.at(pos).Literal(TypeTags.INT, value).setType(syms.intType.constType(value));
    }

    protected JCLiteral makeTypeLiteral(Type type, int pos) {
        JCLiteral lit = factory.at(pos).Literal(TypeTags.CLASS,type);
        lit.type = syms.classType;
        return lit;
    }

    
    /** Makes a constant boolean literal AST node.
     * @param pos the position to use for the node
     * @param value the boolean value of the constant node
     * @return the AST node
     */
    public JCLiteral makeBooleanLiteral(int pos, boolean value) {
        JCLiteral r = factory.at(pos).Literal(TypeTags.BOOLEAN,value?1:0);
        r.type = syms.booleanType;  // FIXME - make constant - but do we use a booleann value or the 0 /1
        return r;
    }

    /** Makes a constant String literal AST node.
     * @param value the String value of the constant node
     * @param pos the position to use for the node
     * @return the AST node
     */
    public JCLiteral makeStringLiteral(String value, int pos) {
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
            case TypeTags.CLASS:
            case TypeTags.ARRAY:
                return nulllit;
            case TypeTags.BOOLEAN:
                return falseLit;
            case TypeTags.CHAR:
                return makeLit(pos,type,0x0000);
            default:
                return makeLit(pos,type,0);
        }
    }


    /** Makes an AST for a primitive type literal, e.g. "int"
     * @param s the text string corresponding to the type
     * @return the AST
     */ // FIXME - position
    public JCExpression makePrimitiveClassLiteralExpression(String s) {
        Name n = names.fromString(s);
        // The following only ever loads the class once, despite multiple calls
        Type type = ClassReader.instance(context).enterClass(n).type;
        JCIdent id = factory.Ident(n);
        id.type = type;
        id.sym = type.tsym;
        Name nTYPE = names.fromString("TYPE"); // TODO - no explicit strings
        JCFieldAccess f = factory.Select(id,nTYPE);
        f.type = syms.objectType;
        Scope.Entry e = type.tsym.members().lookup(nTYPE);
        f.sym = e.sym;
        return f;
    }


    /** Makes an AST for an identifier that references the given symbol
     * @param sym the symbol for which to make an identifier
     * @return the AST
     */ 
    public JCIdent makeIdent(int pos, Symbol sym) {
        JCIdent id = factory.Ident(sym.name);
        id.pos = pos;
        id.sym = sym;
        id.type = sym.type;
        return id;
    }


    /** Makes a Java unary operator node; it may be constant-folded
     * @param pos the pseudo source code location of the node
     * @param optag the unary operator, e.g. JCTree.NOT, JCTree.NEG, JCTree.COMPL, ...
     * @param expr the argument expression
     * @return the new node
     */
    public JCExpression makeUnary(int pos, int optag, JCExpression expr) {
        if (optag == JCTree.NOT){
            if (expr.equals(trueLit)) return falseLit;
            if (expr.equals(falseLit)) return trueLit;
        }
        // FIXME - other constant foldings?
        JCUnary e = factory.at(pos).Unary(optag,expr);
        e.operator = findOpSymbol(optag,expr.type);
        e.type = e.operator.type.getReturnType();
        return e;
    }

    /** Make an attributed unary NOT(!) expression.
     *  @param pos    The position at which to put the new AST.
     *  @param arg    The operator's argument.
     */
    public JCExpression makeNot(int pos, JCExpression arg) {
        return makeUnary(pos,JCTree.NOT,arg);
    }

    /** Make an attributed binary expression.
     *  @param pos      The pseudo-position at which to place the node
     *  @param optag    The operator's operation tag (e.g. JCTree.PLUS).
     *  @param opSymbol The symbol for the operation; if null, no symbol is given
     *                  (this is OK for ESC, but NOT for RAC).
     *  @param lhs      The operator's left argument.
     *  @param rhs      The operator's right argument.
     */
    public JCBinary makeBinary(int pos, int optag, @Nullable Symbol opSymbol, JCExpression lhs, JCExpression rhs) {
        JCBinary tree = factory.at(pos).Binary(optag, lhs, rhs);
        tree.operator = opSymbol;
        tree.type = optag == JCTree.EQ ? syms.booleanType : tree.operator.type.getReturnType();
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
        return e;
    }

    
    /** Produces an Equality AST node.  The symbol is null, so this cannot be 
     * used for RAC.
     * @param pos the position of the node
     * @param lhs the left argument
     * @param rhs the right argument
     * @return the AST
     */
    public JCBinary makeEquality(int pos, JCExpression lhs, JCExpression rhs) {
        JCBinary tree = factory.at(pos).Binary(JCTree.EQ, lhs, rhs);
        tree.operator = null;
        tree.type = syms.booleanType;
        return tree;
    }

    /** Returns the 'larger' of the two types as numeric types are compared */
        // FIXME - does this give the right type resolution for all pairs?
    private Type maxType(Type lhs, Type rhs) {
        return lhs.tag >= rhs.tag || rhs.tag == TypeTags.BOT ? lhs : rhs;
    }
    
    /** Makes a Java binary operator node (with boolean result)
     * @param pos the pseudo source code location of the node
     * @param optag the binary operator (producing a boolean result), e.g. JCTree.EQ
     * @param lhs the left-hand expression
     * @param rhs the right-hand expression
     * @return the new node
     */
    public JCBinary makeBinary(int pos, int optag, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,optag,findOpSymbol(optag,maxType(lhs.type.baseType(),rhs.type.baseType())),lhs,rhs);
    }

    /** Makes the AST for a short-circuit boolean AND expression */
    public JCExpression makeAnd(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.AND,andSymbol,lhs,rhs);
    }

    /** Makes the AST for a short-circuit boolean OR expression */
    public JCExpression makeOr(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.OR,orSymbol,lhs,rhs);
    }

    /** Makes the AST for the Java equivalent of a JML IMPLIES expression */
    public JCExpression makeImplies(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.OR,orSymbol,
                makeNot(pos,lhs), rhs);
    }

    /** Makes the AST for a reference equality (==) expression */
    public JCBinary makeEqObject(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.EQ,objecteqSymbol,lhs, rhs);
    }

    /** Makes the AST for a reference equality (==) expression */
    public JCBinary makeNeqObject(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.NE,objecteqSymbol,lhs, rhs);
    }

    /** Makes a new variable declaration for helper variables in the AST translation;
     * a new VarSymbol is also created in conjunction with the variable; the variable
     * is created with no modifiers and no owner.
     * @param name the variable name, as it might be used in program text
     * @param type the variable type
     * @param init the initialization expression as it would appear in a declaration (null for no initialization)
     * @param pos the pseudo source code location for the new node
     * @returns a new JCVariableDecl node
     */
    public JCVariableDecl makeVariableDecl(Name name, Type type, @Nullable JCExpression init, int pos) {
        VarSymbol vsym = new VarSymbol(0, name, type, null);
        vsym.pos = pos;
        JCVariableDecl decl = factory.at(pos).VarDef(vsym,init);
        return decl;
    }
    
    /** Makes the AST for a catch block; the name of the exception variable is
     * that of the 'caughtException' name defined in the constructor; the catch
     * block itself is initialized with no statements; the type of the exception
     * is java.lang.Exception.
     * @param owner  TBD
     * @param exceptionType the type of the exception caught in the statement
     * @return the new AST
     */ // FIXME - needs position
    public JCCatch makeCatcher(Symbol owner) {
        return makeCatcher(owner,syms.exceptionType);
    }
    
    /** Makes the AST for a catch block; the name of the exception variable is
     * that of the 'caughtException' name defined in the constructor; the catch
     * block itself is initialized with no statements.
     * @param owner  TBD
     * @param exceptionType the type of the exception caught in the statement
     * @return the new AST
     */  // FIXME - needs position
    public JCCatch makeCatcher(Symbol owner, Type exceptionType) {
        JCVariableDecl v = makeVarDef(exceptionType,caughtException,owner,null);
        return factory.Catch(v,factory.Block(0,List.<JCStatement>nil()));
    }
    
    // TBD FIXME document
    public JCCatch makeCatcherJML(Symbol owner) {
        JCVariableDecl v = makeVarDef(assertionFailureClass.type,caughtException,owner,null);
        JCIdent id = factory.Ident(caughtException);
        id.sym = v.sym;
        id.type = v.type;
        JCThrow t = factory.Throw(id);
        return factory.Catch(v,factory.Block(0,List.<JCStatement>of(t)));
    }
    
    /** Makes an ident that references 'this', in the given class 
     * @param csym the containing class
     * @return the new JCIdent
     */ // FIXME - makes a new VarSymbol for each instance - is that right? what visibility?
    // FIXME _ needs position
    public JCIdent factoryThis(ClassSymbol csym) {
        JCIdent id = factory.Ident(names._this);
        //Scope.Entry e = csym.members().lookup(names._this);
        id.type = csym.type;
        id.sym = new VarSymbol(0, id.name, csym.type, csym);
        return id;
    }

    /** Makes an AST for an int variable declaration with initialization and no
     * modifiers.
     * @param name the name of the new variable
     * @param initializer  the (possibly null) initializer expression
     * @param owner the owner of the declaration (e.g. a method or a class)
     * @return the new AST
     */ // FIXME - needs position 
    public JCVariableDecl makeIntVarDef(Name name, JCExpression initializer, Symbol owner) {
        Type type = syms.intType;
        JCExpression tid = factory.Type(type);
        tid.type = type;  // FIXME - not needed?
        JCVariableDecl d = factory.VarDef(factory.Modifiers(0),name,tid,initializer);
        VarSymbol v =
            new VarSymbol(0, d.name, type, owner);
        d.sym = v;
        d.type = type;
        return d;
    }

    /** Makes an attributed variable declaration along with a new VarSymbol (which is not 
     * put into the symbol table); the declaration has no modifiers; it is
     * initialized to a zero-equivalent value.
     * @param type  the type of the new variable (should be an attributed AST)
     * @param name  the name of the new variable
     * @param owner the owner of the new variable (e.g. a MethodSymbol or ClassSymbol)
     * @return the AST for the declaration
     */  // FIXME - what about position
    public JCVariableDecl makeVarDef(JCExpression type, Name name, Symbol owner) {
        int flags = 0;
        int pos = 0;
        factory.at(pos);
        JCModifiers mods = factory.Modifiers(0);
        JCExpression zeroEquiv = makeZeroEquivalentLit(pos,type.type);
        JCVariableDecl d = factory.VarDef(mods,name,type,zeroEquiv);
        VarSymbol v =
            new VarSymbol(flags, d.name, d.vartype.type, owner);
        d.sym = v;
        d.type = type.type;
        return d;
    }


    /** Makes an attributed variable declaration along with a new VarSymbol (which is not 
     * put into the symbol table); the declaration has no modifiers.
     * @param type  the type of the new variable
     * @param name  the name of the new variable
     * @param owner the owner of the new variable (e.g. a MethodSymbol or ClassSymbol)
     * @param init  the initialization expression for the new AST
     * @return the AST for the declaration
     */  // FIXME - what about position
    public JCVariableDecl makeVarDef(Type type, Name name, Symbol owner, JCExpression init) {
        int modifierFlags = 0;
        JCExpression tid = factory.Type(type);
        tid.type = type;  // FIXME - relevant?
        JCVariableDecl d = factory.VarDef(factory.Modifiers(0),name,tid,init);
        VarSymbol v = new VarSymbol(modifierFlags, d.name, type, owner);
        d.sym = v;
        d.type = type;
        return d;
    }

//    // FIXME - document
//    public JCMethodDecl makeMethodDef(Name methodName, List<JCStatement> stats, ClassSymbol ownerClass) {
//        Type restype = syms.voidType;
//
//        MethodType mtype = new MethodType(List.<Type>nil(),restype,List.<Type>nil(),ownerClass);
//
//        MethodSymbol msym = new MethodSymbol(
//                Flags.PUBLIC, 
//                methodName, 
//                mtype, 
//                ownerClass);
//
//        // Caution: This call does not use a factory; it uses the
//        // JCMethodDef constructor directly
//        JCMethodDecl mdecl = factory.MethodDef(
//                msym,
//                factory.Block(0,stats));
//        // FIXME ownerClass.members_field.enter(msym);
//        return mdecl;
//    }

    public JCMethodInvocation makeMethodInvocation(int pos, JCExpression object, Name methodName) {
        JCFieldAccess meth = factory.Select(object,methodName);
        meth.pos = pos;
        meth.sym = null; // FIXME
        meth.type = null; // FIXME
        JCMethodInvocation call = factory.Apply(List.<JCExpression>nil(), meth, List.<JCExpression>nil());
        call.pos = pos;
        call.type = syms.classType; // FIXME
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

//    public JCMethodDecl makeStaticMethodDef(Name methodName, List<JCStatement> stats, ClassSymbol ownerClass) {
//        Type restype = syms.voidType;
//
//        MethodType mtype = new MethodType(List.<Type>nil(),restype,List.<Type>nil(),ownerClass);
//
//        MethodSymbol msym = new MethodSymbol(
//                Flags.PUBLIC | Flags.STATIC, 
//                methodName, 
//                mtype, 
//                ownerClass);
//
//        // Caution: This call does not use a factory; it uses the
//        // JCMethodDef constructor directly
//        JCMethodDecl mdecl = factory.MethodDef(
//                msym,
//                factory.Block(0,stats));
//
//        //FIXME ownerClass.members_field.enter(msym);
//        return mdecl;
//    }

    /** Make an attributed class instance creation expression (with no type arguments).
     * Needs to have setEnv called to set the environment in which to lookup 
     * the constructor.
     *  @param ctype    The class type.
     *  @param args     The constructor arguments.
     */  // FIXME - needs position
    public JCNewClass makeNewClass(Type ctype, List<JCExpression> args) {
        int pos = 0;
        factory.at(pos);
        JCNewClass tree = factory.NewClass(null,
            null, factory.QualIdent(ctype.tsym), args, null);
        // FIXME - can we change this to find the constructor in the type's members directly?
        tree.constructor = rs.resolveConstructor(
            make_pos, attrEnv, ctype, TreeInfo.types(args), null, false, false);
        tree.type = ctype;
        return tree;
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
        factory.at(pos);
        JCFieldAccess meth = findUtilsMethod(pos,methodName);
        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
        for (JCExpression e: args) list.append(e);
        JCMethodInvocation call = factory.Apply(List.<JCExpression>nil(),meth,list.toList());
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
        for (JCExpression e: args) list.append(e);
        JCMethodInvocation call = factory.Apply(List.<JCExpression>nil(),meth,list.toList());
        return call;
    }

    // FIXME - document
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

    // FIXME - document
    public JCExpression trType(int pos, Type type) {
        JCTree tree = factory.at(pos).Type(type);
        return trType(pos,tree);
    }
    
    // FIXME - document
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
        } else {
            log.noticeWriter.println("NOT IMPLEMENTED (JmlTreeUtils) - " + type.getClass());
            //result = type;
            // Unknown - FIXME - error
        }
        return result;
    }

}
