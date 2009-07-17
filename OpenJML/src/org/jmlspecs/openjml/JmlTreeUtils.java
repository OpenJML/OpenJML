package org.jmlspecs.openjml;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.esc.Label;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.JmlResolve;
import com.sun.tools.javac.comp.Resolve;
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
import com.sun.tools.javac.util.Options;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

/** This class holds a number of utility functions that factory fragments of 
 * AST trees; the created trees are fully type and symbol attributed and so
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

    /** The Context in which this object was constructed */ 
    //@ non_null
    final protected Context context;
    
    /** The Attr tool for this context */
    final protected JmlAttr attr;
    
    /** The Log tool for this context */
    final protected Log log;
    
    /** The symbol table from the compilation context, initialized in the constructor */
    @NonNull protected Symtab syms;
    
    /** The Names table from the compilation context, initialized in the constructor */
    @NonNull protected Names names;
    
    /** The Utils tool for this context */
    @NonNull final protected Utils utils;
    
    /** The Resolve tool for this compilation context */
    @NonNull final protected JmlResolve rs;

    /** The Env in which to do resolving */
    @NonNull Env<AttrContext> attrEnv;
        
    /** The factory used to create AST nodes, initialized in the constructor */
    @NonNull protected JmlTree.Maker factory;

    ClassSymbol utilsClass = null;
    JCIdent utilsClassIdent;
    Type integerType;
    
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

    boolean dorac;
    boolean doesc;
    boolean inSpecExpression;
    
    DiagnosticPosition make_pos;
    ClassSymbol assertionFailureClass;
    Name resultName;
    Name exceptionName;
    Name exceptionCatchName;
    
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
        this.factory = (JmlTree.Maker)JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.rs = JmlResolve.instance(context);
        this.syms = Symtab.instance(context);
        this.utilsClass = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.utils.Utils"));
        utilsClassIdent = factory.Ident(names.fromString("org.jmlspecs.utils.Utils"));
        utilsClassIdent.type = utilsClass.type;
        utilsClassIdent.sym = utilsClassIdent.type.tsym;
        dorac = Options.instance(context).get("-rac") != null;  // FIXME - fix these - proper call and names
        doesc = Options.instance(context).get("-esc") != null;
        andSymbol = syms.predefClass.members().lookup(names.fromString("&&")).sym;
        orSymbol  = syms.predefClass.members().lookup(names.fromString("||")).sym;
        notSymbol = syms.predefClass.members().lookup(names.fromString("!")).sym;
        objecteqSymbol = findOpSymbol("==",syms.objectType);
        booleqSymbol = findOpSymbol("==",syms.booleanType);
        boolneSymbol = findOpSymbol("!=",syms.booleanType);
        trueLit = makeLit(syms.booleanType,1);
        falseLit = makeLit(syms.booleanType,0);
        zero = makeLit(syms.intType,0);
        nulllit = makeLit(syms.botType, null);
        maxIntLit = makeLit(syms.intType,Integer.MAX_VALUE);

        ClassReader reader = ClassReader.instance(context);

        assertionFailureClass = reader.enterClass(names.fromString("org.jmlspecs.utils.Utils$JmlAssertionFailure"));
        utilsClass = reader.enterClass(names.fromString("org.jmlspecs.utils.Utils"));
        utilsClassIdent = factory.Ident(names.fromString("org.jmlspecs.utils.Utils"));
        utilsClassIdent.type = utilsClass.type;
        utilsClassIdent.sym = utilsClassIdent.type.tsym;
        
        trueLit = makeLit(syms.booleanType,1);
        falseLit = makeLit(syms.booleanType,0);
        zero = makeLit(syms.intType,0);
        nulllit = makeLit(syms.botType, null);
        maxIntLit = makeLit(syms.intType,Integer.MAX_VALUE);

        this.resultName = Names.instance(context).fromString("_JML$$$result");
        this.exceptionName = Names.instance(context).fromString("_JML$$$exception");
        this.exceptionCatchName = Names.instance(context).fromString("_JML$$$exceptionCatch");

        integerType = reader.enterClass(names.fromString("java.lang.Integer")).type;
    }
    
    public void setEnv(Env<AttrContext> env) {
        attrEnv = env;
    }
    
    public Symbol findOpSymbol(String name, Type argtype) {
        Scope.Entry e = syms.predefClass.members().lookup(names.fromString(name));
        while (e != null && e.sym != null) {
            if (((MethodType)e.sym.type).argtypes.head.equals(argtype)) return e.sym;
            e = e.next();
        }
        // FIXME - throw error
        return null;
    }
    
    public JCFieldAccess findUtilsMethod(String methodName) {
        Name n = names.fromString(methodName);
        Scope.Entry e = utilsClass.members().lookup(n);
        Symbol ms = e.sym;
        if (ms == null) {
            throw new JmlInternalError("Method " + methodName + " not found in Utils");
        }
        JCFieldAccess m = factory.Select(utilsClassIdent,n);
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
    
    /** Make an attributed tree representing a literal. This will be an
     *  Ident node in the case of boolean literals, a Literal node in all
     *  other cases.
     *  @param type       The literal's type.
     *  @param value      The literal's value.
     */
    public JCLiteral makeLit(Type type, Object value) { // FIXME - needs pos
        return factory.Literal(type.tag, value).setType(type.constType(value));
    }

    
    public JCMethodInvocation makeUtilsMethodCall(int pos, String methodName, List<JCExpression> args) {
        // presumes the arguments are all properly attributed
        JCFieldAccess meth = findUtilsMethod(methodName);
        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
        for (JCExpression e: args) list.append(e);
        JCMethodInvocation call = factory.at(pos).Apply(List.<JCExpression>nil(),meth,list.toList());
        return call;
    }

    public JCMethodInvocation makeUtilsMethodCall(int pos, String methodName, JCExpression... args) {
        // presumes the arguments are all properly attributed
        JCFieldAccess meth = findUtilsMethod(methodName);
        ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
        for (JCExpression e: args) list.append(e);
        JCMethodInvocation call = factory.at(pos).Apply(List.<JCExpression>nil(),meth,list.toList());
        return call;
    }

    
    public JCLiteral makeLiteral(boolean v, int pos) {
        JCLiteral r = factory.at(pos).Literal(TypeTags.BOOLEAN,v?1:0);
        r.type = syms.booleanType;
        return r;
    }

    public JCLiteral makeStringLiteral(String s, int pos) {
        JCLiteral r = factory.at(pos).Literal(TypeTags.CLASS,s);
        r.type = syms.stringType;
        return r;
    }

    // FIXME - can we cache the && and || operators ?
    /** Make an attributed binary expression.
     *  @param optag    The operators tree tag.
     *  @param lhs      The operator's left argument.
     *  @param rhs      The operator's right argument.
     */
    public JCExpression makeBinary(int pos, int optag, Symbol opSymbol, JCExpression lhs, JCExpression rhs) {
//        if (optag == JCTree.OR && lhs == falseLit) return rhs;  // Lose position if we do this
//        if (optag == JCTree.AND && lhs == trueLit) return rhs;
        JCBinary tree = factory.at(pos).Binary(optag, lhs, rhs);
        tree.operator = opSymbol != null ? opSymbol : optag == JCTree.AND ? andSymbol : optag == JCTree.OR ? orSymbol : null; // FIXME - report error
        tree.type = tree.operator.type.getReturnType();
        return tree;
    }
    
    public JCExpression makeAnd(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.AND,andSymbol,lhs,rhs);
    }

    public JCExpression makeOr(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.OR,orSymbol,lhs,rhs);
    }

    public JCExpression makeImplies(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.OR,orSymbol,
                makeUnary(pos,JCTree.NOT,lhs), rhs);
    }

    public JCExpression makeEqObject(int pos, JCExpression lhs, JCExpression rhs) {
        return makeBinary(pos,JCTree.EQ,objecteqSymbol,lhs, rhs);
    }

    // FIXME - can we cache the ! operator?
    /** Make an attributed unary expression.
     *  @param optag    The operators tree tag.
     *  @param arg      The operator's argument.
     */
    public JCExpression makeUnary(int pos, int optag, JCExpression arg) {
        if (arg.equals(trueLit) && optag == JCTree.NOT) return falseLit;
        if (arg.equals(falseLit) && optag == JCTree.NOT) return trueLit;
        JCUnary tree = factory.at(pos).Unary(optag, arg);
        tree.operator = optag == JCTree.NOT ? notSymbol : null; // FIXME - report error
        tree.type = tree.operator.type.getReturnType();
        return tree;
    }
    
    public JCExpression makeNot(int pos, JCExpression arg) {
        return makeUnary(pos,JCTree.NOT,arg);
    }
    
    /** Makes a Java binary operator node (with boolean result)
     * @param op the binary operator (producing a boolean result), e.g. JCTree.EQ
     * @param lhs the left-hand expression
     * @param rhs the right-hand expression
     * @param pos the pseudo source code location of the node
     * @return the new node
     */
    public JCBinary makeBinary(int op, JCExpression lhs, JCExpression rhs, int pos) {
        JCBinary e = factory.at(pos).Binary(op,lhs,rhs);
        switch (op) {
            case JCTree.EQ:
            case JCTree.NE:
            case JCTree.GT:
            case JCTree.GE:
            case JCTree.LT:
            case JCTree.LE:
            case JCTree.OR:
            case JCTree.AND:
                e.type = syms.booleanType;
                break;

            case JCTree.PLUS:
            case JCTree.MINUS:
            case JCTree.MUL:
            case JCTree.DIV:
            case JCTree.MOD:
                if (lhs.type == syms.doubleType || rhs.type == syms.doubleType)
                    e.type = syms.doubleType;
                else if (lhs.type == syms.floatType || rhs.type == syms.floatType)
                    e.type = syms.floatType;
                else if (lhs.type == syms.longType || rhs.type == syms.longType)
                    e.type = syms.longType;
                else e.type = syms.intType;
                break;

            case JCTree.BITOR:
            case JCTree.BITAND:
            case JCTree.BITXOR:
            case JCTree.SR:
            case JCTree.USR:
            case JCTree.SL:
                // FIXME - check that this is correct
                if (lhs.type == syms.longType || rhs.type == syms.longType)
                    e.type = syms.longType;
                else e.type = syms.intType;
                break;
                
            default:
                Log.instance(context).error("esc.not.implemented","Unknown binary operator in BasicBlocker.makeBinary "+op);
        }
        return e;
    }
    
    /** Makes a Java unary operator node
     * @param op the unary operator, e.g. JCTree.NOT, JCTree.NEG, JCTree.COMPL, ...
     * @param lhs the left-hand expression
     * @param rhs the right-hand expression
     * @param pos the pseudo source code location of the node
     * @return the new node
     */
    public JCExpression makeUnary(int op, JCExpression expr, int pos) {
        JCUnary e = factory.at(pos).Unary(op,expr);
        if (op == JCTree.NOT) e.type = syms.booleanType;
        else if (expr.type == syms.doubleType) e.type = expr.type;
        else if (expr.type == syms.floatType) e.type = expr.type;
        else if (expr.type == syms.longType) e.type = expr.type;
        else e.type = syms.intType;  // NEG POS COMPL PREINC PREDEC POSTINC POSTDEC
        return e;
    }
    
    /** Makes a new variable declaration for helper variables in the AST translation;
     * a new VarSymbol is also created in conjunction with the variable
     * @param name the variable name, as it might be used in program text
     * @param type the variable type
     * @param init the initialization expression as it would appear in a declaration
     * @param pos the pseudo source code location for the new node
     * @returns a new JCVariableDecl node
     */
    public JCVariableDecl makeVariableDecl(Name name, Type type, JCExpression init, int pos) {
        VarSymbol vsym = new VarSymbol(0, name, type, null);
        vsym.pos = pos;
        JCVariableDecl decl = factory.at(pos).VarDef(vsym,init);
        return decl;
    }
    
    public JCVariableDecl makeVariableDecl(Name name, Type type, int pos) {
        VarSymbol vsym = new VarSymbol(0, name, type, null);
        vsym.pos = pos;
        JCVariableDecl decl = factory.at(pos).VarDef(vsym,null);
        return decl;
    }
    
    // FIXME - can we cache the && and || operators ?
    /** Make an attributed binary expression.
     *  @param optag    The operators tree tag.
     *  @param lhs      The operator's left argument.
     *  @param rhs      The operator's right argument.
     */
    public JCExpression makeBinary(int optag, JCExpression lhs, JCExpression rhs) {
        if (optag == JCTree.OR && lhs == falseLit) return rhs;
        if (optag == JCTree.AND && lhs == trueLit) return rhs;
        JCBinary tree = factory.Binary(optag, lhs, rhs);
        tree.operator = rs.resolveBinaryOperator(
            make_pos, optag, attrEnv, lhs.type, rhs.type);
        tree.type = tree.operator.type.getReturnType();
        return tree;
    }

    // FIXME - can we cache the ! operator?
    /** Make an attributed unary expression.
     *  @param optag    The operators tree tag.
     *  @param arg      The operator's argument.
     */
    public JCExpression makeUnary(int optag, JCExpression arg) {
        if (arg.equals(trueLit) && optag == JCTree.NOT) return falseLit;
        if (arg.equals(falseLit) && optag == JCTree.NOT) return trueLit;
        JCUnary tree = factory.Unary(optag, arg);
        tree.operator = rs.resolveUnaryOperator(
            make_pos, optag, attrEnv, arg.type);
        tree.type = tree.operator.type.getReturnType();
        return tree;
    }
    
    public JCCatch makeCatcher(Symbol owner) {
        return makeCatcher(owner,syms.exceptionType);
    }
    
    public JCCatch makeCatcher(Symbol owner, Type ex) {
        Name n = names.fromString("_JML$$$caughtException");
        JCVariableDecl v = makeVarDef(ex,n,owner,null);
        return factory.Catch(v,factory.Block(0,List.<JCStatement>nil()));
    }
    
    public JCCatch makeCatcherJML(Symbol owner) {
        Name n = names.fromString("_JML$$$caughtException");
        JCVariableDecl v = makeVarDef(assertionFailureClass.type,n,owner,null);
        JCIdent id = factory.Ident(n);
        id.sym = v.sym;
        id.type = v.type;
        JCThrow t = factory.Throw(id);
        return factory.Catch(v,factory.Block(0,List.<JCStatement>of(t)));
    }
    
    public JCIdent makeIdent(Symbol sym) {
        JCIdent id = factory.Ident(sym.name);
        id.sym = sym;
        id.type = sym.type;
        return id;
    }
    
    public JCIdent factoryThis(ClassSymbol csym) {
        JCIdent id = factory.Ident(names._this);
        //Scope.Entry e = csym.members().lookup(names._this);
        id.type = csym.type;
        id.sym = new VarSymbol(0, id.name, csym.type, csym);
        return id;
    }



    public JCVariableDecl makeIntVarDef(Name name, JCExpression e, Symbol owner) {
        Type type = syms.intType;
        JCExpression tid = factory.Type(type);
        tid.type = type;
        JCVariableDecl d = factory.VarDef(factory.Modifiers(0),name,tid,e);
        VarSymbol v =
            new VarSymbol(0, d.name, type, owner);
        d.sym = v;
        d.type = type;
        return d;
    }

    public JCMethodDecl makeMethodDef(Name methodName, List<JCStatement> stats, ClassSymbol ownerClass) {
        Type restype = syms.voidType;

        MethodType mtype = new MethodType(List.<Type>nil(),restype,List.<Type>nil(),ownerClass);

        MethodSymbol msym = new MethodSymbol(
                Flags.PUBLIC, 
                methodName, 
                mtype, 
                ownerClass);

        // Caution: This call does not use a factory; it uses the
        // JCMethodDef constructor directly
        JCMethodDecl mdecl = factory.MethodDef(
                msym,
                factory.Block(0,stats));
        // FIXME ownerClass.members_field.enter(msym);
        return mdecl;
    }

    public JCMethodDecl makeMethodDefNoArg(JCModifiers mods, Name methodName, Type resultType, ClassSymbol ownerClass) {

        MethodType mtype = new MethodType(List.<Type>nil(),resultType,List.<Type>nil(),ownerClass);

        MethodSymbol msym = new MethodSymbol(
                mods.flags, 
                methodName, 
                mtype, 
                ownerClass);

        // Caution: This call does not use a factory; it uses the
        // JCMethodDef constructor directly
        JCMethodDecl mdecl = factory.MethodDef(
                msym,
                factory.Block(0,List.<JCStatement>nil()));

        ownerClass.members_field.enter(msym);
        return mdecl;
    }

    public JCMethodDecl makeStaticMethodDef(Name methodName, List<JCStatement> stats, ClassSymbol ownerClass) {
        Type restype = syms.voidType;

        MethodType mtype = new MethodType(List.<Type>nil(),restype,List.<Type>nil(),ownerClass);

        MethodSymbol msym = new MethodSymbol(
                Flags.PUBLIC | Flags.STATIC, 
                methodName, 
                mtype, 
                ownerClass);

        // Caution: This call does not use a factory; it uses the
        // JCMethodDef constructor directly
        JCMethodDecl mdecl = factory.MethodDef(
                msym,
                factory.Block(0,stats));

        //FIXME ownerClass.members_field.enter(msym);
        return mdecl;
    }

    /** Make an attributed class instance creation expression.
     *  @param ctype    The class type.
     *  @param args     The constructor arguments.
     */
    public JCNewClass makeNewClass(Type ctype, List<JCExpression> args) {
        JCNewClass tree = factory.NewClass(null,
            null, factory.QualIdent(ctype.tsym), args, null);
        tree.constructor = rs.resolveConstructor(
            make_pos, attrEnv, ctype, TreeInfo.types(args), null, false, false);
        tree.type = ctype;
        return tree;
    }

//    /** Make an attributed tree representing a literal. This will be an
//     *  Ident node in the case of boolean literals, a Literal node in all
//     *  other cases.
//     *  @param type       The literal's type.
//     *  @param value      The literal's value.
//     */
//    JCLiteral makeLit(Type type, Object value) {
//        return factory.Literal(type.tag, value).setType(type.constType(value));
//    }

    public JCLiteral makeZeroEquivalentLit(Type type) {
        switch (type.tag) {
            case TypeTags.CLASS:
            case TypeTags.ARRAY:
                return nulllit;
            case TypeTags.BOOLEAN:
                return falseLit;
            case TypeTags.CHAR:
                return makeLit(type,' ');
            default:
                return makeLit(type,0);

        }
    }
    public JCExpression makePrimitiveClassLiteralExpression(String s) {
        Name n = names.fromString(s);
        // The following only ever loads the class once, despite multiple calls
        Type type = ClassReader.instance(context).enterClass(n).type;
        JCIdent id = factory.Ident(n);
        id.type = type;
        id.sym = type.tsym;
        Name nTYPE = names.fromString("TYPE");
        JCFieldAccess f = factory.Select(id,nTYPE);
        f.type = syms.objectType;
        Scope.Entry e = type.tsym.members().lookup(nTYPE);
        f.sym = e.sym;
        return f;
    }
    
    // Expect the type to be attributed
    public JCVariableDecl makeVarDef(JCExpression type, Name name, Symbol owner) {
        JCVariableDecl d = factory.VarDef(factory.Modifiers(0),name,type,makeZeroEquivalentLit(type.type));
        VarSymbol v =
            new VarSymbol(0, d.name, d.vartype.type, owner);
        d.sym = v;
        d.type = type.type;
        return d;
    }
    
    // Expect the type to be attributed
    public JCVariableDecl makeVarDef(Type type, Name name, Symbol owner,JCExpression init) {
        //JCIdent tid = factory.Ident(names.fromString("int"));
        JCExpression tid = factory.Type(type);
        tid.type = type;
        //tid.sym = type.tsym;
        JCVariableDecl d = factory.VarDef(factory.Modifiers(0),name,tid,init);
        VarSymbol v =
            new VarSymbol(0, d.name, type, owner);
        d.sym = v;
        d.type = type;
        return d;
    }


}
