package com.sun.tools.javac.comp;

import static com.sun.tools.javac.code.Flags.ABSTRACT;
import static com.sun.tools.javac.code.Flags.AccessFlags;
import static com.sun.tools.javac.code.Flags.INTERFACE;
import static com.sun.tools.javac.code.Flags.STATIC;
import static com.sun.tools.javac.code.Flags.SYNTHETIC;
import static com.sun.tools.javac.code.Kinds.AMBIGUOUS;
import static com.sun.tools.javac.code.Kinds.ERR;
import static com.sun.tools.javac.code.Kinds.MTH;
import static com.sun.tools.javac.code.Kinds.TYP;
import static com.sun.tools.javac.code.Kinds.VAR;
import static com.sun.tools.javac.code.Kinds.WRONG_MTHS;
import static com.sun.tools.javac.code.TypeTags.CLASS;
import static com.sun.tools.javac.code.TypeTags.TYPEVAR;

import org.jmlspecs.openjml.JmlCompiler;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.OperatorSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

/**
 * This class extends Resolve in order to implement lookup of JML names. In the
 * current design of OpenJML, we use just one symbol table for Java and JML
 * names. This is no restriction because JML declarations have to be legal Java
 * declarations and have to create a legal Java compilation unit if they were
 * actual Java declarations. However JML names must only be visible from within
 * JML annotations. To implement that, each JML declaration has its JMLBIT set
 * in the modifiers bit-vector and the field JmlResolve.allowJML determines
 * whether or not JML-flagged declarations are returned as the result of a name
 * lookup: if allowJML is true, any declaration is returned; if allowJML is
 * false, JML-flagged declarations are not returned.
 * <P>
 * MAINTENANCE ISSUE: Unfortunately, the methods that do the lookup had to be
 * copied wholesale from the superclass, in order to insert the JML checks. Thus
 * integration of changes will have to be performed by hand.
 * 
 * @author David Cok
 */
public class JmlResolve extends Resolve {

    /** This flag determines whether or not JML-flagged declarations are 
     * returned as the result of a name lookup.  It may be set by clients of
     * this class through the setJML method.  Note that contexts are nested, 
     * so you should remember and
     * restore the value of this flag when you are setting it.
     */
    protected boolean allowJML = false;
    
    /** The compilation context in which to do lookup. */
    public Context context;
    
    /** A constant symbol that represents the < operation on locks; it is 
     * initialized in the constructor.
     */
    public OperatorSymbol lockLT;

    /** A constant symbol that represents the <= operation on locks; it is 
     * initialized in the constructor.
     */
    public OperatorSymbol lockLE;
    
    private Type integerType;
    
    /** Returns the unique instance of this class for the given compilation context
     * @param context the compilation context whose instance of Resolve is desired
     * @return
     */
    public static Resolve instance(Context context) {
        Resolve instance = context.get(resolveKey);
        if (instance == null)
            instance = new JmlResolve(context);
        return instance;
    }

    /** Registers a factory for JmlResolve against the attrKey.  Once an instance
     * is created it registers itself, so there is a unique instance per context.
     * @param context the context in which to register the instance
     */
    public static void preRegister(final Context context) {
        context.put(Resolve.resolveKey, new Context.Factory<Resolve>() {
            public Resolve make() {
                return new JmlResolve(context);
            }
        });
    }
    
    /** Creates an instance of this class for the given context; clients should
     * use the instance() method rather than calling this constructor directly.
     * @param context the compilation context in which to construct this instance
     */
    //@ ensures context != null;
    //@ ensures lockLT != null;
    //@ ensures lockLE != null;
    //@ ensures !allowJML;
    protected JmlResolve(Context context) {
        super(context);
        this.context = context;
        
        Symtab syms = Symtab.instance(context);
        integerType = reader.enterClass(names.fromString("java.lang.Integer")).type;
        lockLT = new OperatorSymbol(
                names.fromString("<#"),
                new MethodType(List.of(syms.objectType, syms.objectType), syms.booleanType,
                        List.<Type>nil(), syms.methodClass),
                        1000,
                        syms.predefClass);
        lockLE = new OperatorSymbol(
                names.fromString("<#="),
                new MethodType(List.of(syms.objectType, syms.objectType), syms.booleanType,
                        List.<Type>nil(), syms.methodClass),
                        1001,
                        syms.predefClass);
        // We could enter these operators into the symbol table 
        // with the code below.  That works nicely for operator
        // lookup, but it is hard to control that they are looked 
        // up only when JML is active.  Also, these operators take
        // Objects as arguments.  With type boxing, that means that
        // they can take any argument.  However, boxed arguments
        // will not have locks anyway, so with direct control in
        // resolveBinaryOperator we avoid this.
//        syms.predefClass.members().enter(lockLT);
//        syms.predefClass.members().enter(lockLE);

    }
    
    /** This method is used to set the value of the allowJML flag.  It returns
     * the previous value.
     * @param context the compilation context in which to do the modification
     * @param allowJML the new value
     * @return the old value
     */
    static boolean setJML(Context context, boolean allowJML) {
        JmlResolve r = (JmlResolve)JmlResolve.instance(context);
        boolean b = r.allowJML;
        r.allowJML = allowJML;
        return b;
    }
    
    /** This method overrides the super class method in order to check for
     * resolutions against JML operators: in particular, the < and <= operators
     * on Objects that used to implement lock ordering comparisons.  The method
     * returns an error symbol (Symtab.instance(context).errSymbol) if there
     * is no matching operator.
     * 
     * Once < and <= are no longer used for lock ordering, this method can be
     * removed.
     */
    @Override
    protected Symbol resolveBinaryOperator(DiagnosticPosition pos,
            int optag,
            Env<AttrContext> env,
            Type left,
            Type right) {
        // TODO: Eventually disallow using < and <= for lock operations
        // Then this whole method can be removed
        if (allowJML && !left.isPrimitive() && !right.isPrimitive()) {
            if (!types.isSameType(left,integerType) && !types.isSameType(right,integerType)) {
                if (optag == JCTree.LT) {
                    log.warning(pos,"lock.ops");
                    return lockLT;
                }
                if (optag == JCTree.LE) {
                    log.warning(pos,"lock.ops");
                    return lockLE;
                }
            }
        }
        return super.resolveBinaryOperator(pos, optag, env, left, right);
    }
    
    

    /** Based on super.resolveMethod */
    Symbol findMatchingMethod(DiagnosticPosition pos,
            Env<AttrContext> env,
            Name name,
            List<Type> argtypes,
            List<Type> typeargtypes) {
        Symbol sym = findFun(env, name, argtypes, typeargtypes, false, env.info.varArgs=false);
        if (varargsEnabled && sym.kind >= WRONG_MTHS) {
            sym = findFun(env, name, argtypes, typeargtypes, true, false);
            if (sym.kind >= WRONG_MTHS)
                sym = findFun(env, name, argtypes, typeargtypes, true, env.info.varArgs=true);
        }
        if (sym.kind >= AMBIGUOUS) {
            return null;
//            sym = access(
//                    sym, pos, env.enclClass.sym.type, name, false, argtypes, typeargtypes);
        }
        return sym;
    }



    /** This overrides the superclass method in order to implement distinguishing
     * JML and Java name lookup
     * @param env the scope environment in which to find a type name
     * @param name the name to find
     * @return the found symbol, or errSymbol if none found
     */
    // MAINTENANCE ISSUE: This is copied verbatim from Resolve, 
    // with just a few inline changes for JML
    @Override
    Symbol findType(Env<AttrContext> env, Name name) {
        Symbol bestSoFar = typeNotFound;
        Symbol sym;
        boolean staticOnly = false;
        for (Env<AttrContext> env1 = env; env1.outer != null; env1 = env1.outer) {
            if (isStatic(env1)) staticOnly = true;
            for (Scope.Entry e = env1.info.scope.lookup(name);
                 e.scope != null;
                 e = e.next()) {
                if (e.sym.kind == TYP) {
                    if (!allowJML && Utils.isJML(e.sym.flags_field)) continue;
                    if (staticOnly &&
                        e.sym.type.tag == TYPEVAR &&
                        e.sym.owner.kind == TYP) return new StaticError(e.sym);
                    return e.sym;
                }
            }

            sym = findMemberType(env1, env1.enclClass.sym.type, name,
                                 env1.enclClass.sym);
            if (staticOnly && sym.kind == TYP &&
                sym.type.tag == CLASS &&
                sym.type.getEnclosingType().tag == CLASS &&
                env1.enclClass.sym.type.isParameterized() &&
                sym.type.getEnclosingType().isParameterized())
                return new StaticError(sym);
            else if (sym.exists()) return sym;
            else if (sym.kind < bestSoFar.kind) bestSoFar = sym;

            JCClassDecl encl = env1.baseClause ? (JCClassDecl)env1.tree : env1.enclClass;
            if ((encl.sym.flags() & STATIC) != 0)
                staticOnly = true;
        }

        if (env.tree.getTag() != JCTree.IMPORT) {
            sym = findGlobalType(env, env.toplevel.namedImportScope, name);
            if (sym.exists()) return sym;
            else if (sym.kind < bestSoFar.kind) bestSoFar = sym;

            sym = findGlobalType(env, env.toplevel.packge.members(), name);
            if (sym.exists()) return sym;
            else if (sym.kind < bestSoFar.kind) bestSoFar = sym;

            sym = findGlobalType(env, env.toplevel.starImportScope, name);
            if (sym.exists()) return sym;
            else if (sym.kind < bestSoFar.kind) bestSoFar = sym;
        }

        return bestSoFar;
    }

    /** This overrides the superclass method in order to implement distinguishing
     * JML and Java name lookup
     * Find qualified member type.
     *  @param env       The current environment.
     *  @param site      The original type from where the selection takes
     *                   place.
     *  @param name      The type's name.
     *  @param c         The class to search for the member type. This is
     *                   always a superclass or implemented interface of
     *                   site's class.
     */
    // MAINTENANCE ISSUE: This is copied verbatim from Resolve, 
    // with just a few inline changes for JML
    @Override
    Symbol findMemberType(Env<AttrContext> env,
                          Type site,
                          Name name,
                          TypeSymbol c) {
        Symbol bestSoFar = typeNotFound;
        Symbol sym;
        Scope.Entry e = c.members().lookup(name);
        while (e.scope != null) {
            if (e.sym.kind == TYP &&
                (allowJML || !Utils.isJML(e.sym.flags_field))) {
                return isAccessible(env, site, e.sym)
                    ? e.sym
                    : new AccessError(env, site, e.sym);
            }
            e = e.next();
        }
        Type st = types.supertype(c.type);
        if (st != null && st.tag == CLASS) {
            sym = findMemberType(env, site, name, st.tsym);
            if (sym.kind < bestSoFar.kind) bestSoFar = sym;
        }
        for (List<Type> l = types.interfaces(c.type);
             bestSoFar.kind != AMBIGUOUS && l.nonEmpty();
             l = l.tail) {
            sym = findMemberType(env, site, name, l.head.tsym);
            if (bestSoFar.kind < AMBIGUOUS && sym.kind < AMBIGUOUS &&
                sym.owner != bestSoFar.owner)
                bestSoFar = new AmbiguityError(bestSoFar, sym);
            else if (sym.kind < bestSoFar.kind)
                bestSoFar = sym;
        }
        return bestSoFar;
    }

    /** Find a global type in given scope and load corresponding class.
     * This overrides the superclass method in order to distinguish JML
     * and Java name lookup.
     *  @param env       The current environment.
     *  @param scope     The scope in which to look for the type.
     *  @param name      The type's name.
     */
    // MAINTENANCE ISSUE: This is copied verbatim from Resolve, 
    // with just a few inline changes for JML
    @Override
    public Symbol findGlobalType(Env<AttrContext> env, Scope scope, Name name) {
        Symbol bestSoFar = typeNotFound;
        for (Scope.Entry e = scope.lookup(name); e.scope != null; e = e.next()) {
            Symbol sym = loadClass(env, e.sym.flatName());
            if (!allowJML && Utils.isJML(e.sym.flags_field)) continue;
            if (bestSoFar.kind == TYP && sym.kind == TYP &&
                bestSoFar != sym)
                return new AmbiguityError(bestSoFar, sym);
            else if (sym.kind < bestSoFar.kind)
                bestSoFar = sym;
        }
        return bestSoFar;
    }

    /** This overrides the superclass method in order to distinguish JML
    * and Java name lookup.
    */
    // MAINTENANCE ISSUE: This is copied verbatim from Resolve, 
    // with just a few inline changes for JML
    @Override
    Symbol findVar(Env<AttrContext> env, Name name) {
        Symbol bestSoFar = varNotFound;
        Symbol sym;
        Env<AttrContext> env1 = env;
        boolean staticOnly = false;
        while (env1.outer != null) {
            if (isStatic(env1)) staticOnly = true;
            Scope.Entry e = env1.info.scope.lookup(name);
            while (e.scope != null &&
                   (e.sym.kind != VAR
                   || (!allowJML && Utils.isJML(e.sym.flags_field)) 
                   || (e.sym.flags_field & SYNTHETIC) != 0)) {
                e = e.next();
            }
            sym = (e.scope != null)
                ? e.sym
                : findField(
                    env1, env1.enclClass.sym.type, name, env1.enclClass.sym);
            if (sym.exists()) {
                if (staticOnly &&
                    sym.kind == VAR &&
                    sym.owner.kind == TYP &&
                    (sym.flags() & STATIC) == 0)
                    return new StaticError(sym);
                else
                    return sym;
            } else if (sym.kind < bestSoFar.kind) {
                bestSoFar = sym;
            }

            if ((env1.enclClass.sym.flags() & STATIC) != 0) staticOnly = true;
            env1 = env1.outer;
        }

        sym = findField(env, syms.predefClass.type, name, syms.predefClass);
        if (sym.exists())
            return sym;
        if (bestSoFar.exists())
            return bestSoFar;

        Scope.Entry e = env.toplevel.namedImportScope.lookup(name);
        for (; e.scope != null; e = e.next()) {
            sym = e.sym;
            Type origin = e.getOrigin().owner.type;
            if (sym.kind == VAR) {
                if (e.sym.owner.type != origin)
                    sym = sym.clone(e.getOrigin().owner);
                return isAccessible(env, origin, sym)
                    ? sym : new AccessError(env, origin, sym);
            }
        }

        Symbol origin = null;
        e = env.toplevel.starImportScope.lookup(name);
        for (; e.scope != null; e = e.next()) {
            sym = e.sym;
            if (sym.kind != VAR)
                continue;
            if (!allowJML && Utils.isJML(e.sym.flags_field)) continue;
            // invariant: sym.kind == VAR
            if (bestSoFar.kind < AMBIGUOUS && sym.owner != bestSoFar.owner)
                return new AmbiguityError(bestSoFar, sym);
            else if (bestSoFar.kind >= VAR) {
                origin = e.getOrigin().owner;
                bestSoFar = isAccessible(env, origin.type, sym)
                    ? sym : new AccessError(env, origin.type, sym);
            }
        }
        if (bestSoFar.kind == VAR && bestSoFar.owner.type != origin.type)
            return bestSoFar.clone(origin);
        else
            return bestSoFar;
    }

    /** This overrides the superclass method in order to distinguish JML
     * and Java name lookup.
     */
    // MAINTENANCE ISSUE: This is copied verbatim from Resolve, 
    // with just a few inline changes for JML
    @Override
    Symbol findField(Env<AttrContext> env,
            Type site,
            Name name,
            TypeSymbol c) {
        Symbol bestSoFar = varNotFound;
        Symbol sym;
        Scope.Entry e = c.members().lookup(name);
        while (e.scope != null) {
            if (e.sym.kind == VAR && (e.sym.flags_field & SYNTHETIC) == 0
                    && !(!allowJML && Utils.isJML(e.sym.flags_field))) {
                return isAccessible(env, site, e.sym)
                ? e.sym : new AccessError(env, site, e.sym);
            }
            e = e.next();
        }
        Type st = types.supertype(c.type);
        if (st != null && st.tag == CLASS) {
            sym = findField(env, site, name, st.tsym);
            if (sym.kind < bestSoFar.kind) bestSoFar = sym;
        }
        for (List<Type> l = types.interfaces(c.type);
        bestSoFar.kind != AMBIGUOUS && l.nonEmpty();
        l = l.tail) {
            sym = findField(env, site, name, l.head.tsym);
            if (bestSoFar.kind < AMBIGUOUS && sym.kind < AMBIGUOUS &&
                    sym.owner != bestSoFar.owner)
                bestSoFar = new AmbiguityError(bestSoFar, sym);
            else if (sym.kind < bestSoFar.kind)
                bestSoFar = sym;
        }
        return bestSoFar;
    }
    
    public boolean noSuper = false;
    
     /** This overrides the superclass method in order to distinguish JML
      * and Java name lookup.
      */
     // MAINTENANCE ISSUE: This is copied verbatim from Resolve, 
     // with just a few inline changes for JML
     @Override
     protected Symbol findMethod(Env<AttrContext> env, 
            Type site,
            Name name,
            List<Type> argtypes,
            List<Type> typeargtypes,
            Type intype,
            boolean abstractok,
            Symbol bestSoFar,
            boolean allowBoxing,
            boolean useVarargs,
            boolean operator) {
        for (Type ct = intype; ct.tag == CLASS; ct = noSuper? Type.noType : types.supertype(ct)) {
            ClassSymbol c = (ClassSymbol)ct.tsym;
            if (!allowJML && (c.flags() & (ABSTRACT | INTERFACE)) == 0 && !noSuper)
                abstractok = false;
            for (Scope.Entry e = c.members().lookup(name);
                        e.scope != null;
                        e = e.next()) {
                if (e.sym.kind == MTH &&
                        (e.sym.flags_field & SYNTHETIC) == 0 &&
                        !(!allowJML && Utils.isJML(e.sym.flags_field))) {
                    bestSoFar = selectBest(env, site, argtypes, typeargtypes,
                            e.sym, bestSoFar,
                            allowBoxing,
                            useVarargs,
                            operator);
                }
            }
            if (abstractok) {
                Symbol concrete = methodNotFound;
                if ((bestSoFar.flags() & ABSTRACT) == 0)
                    concrete = bestSoFar;
                for (List<Type> l = types.interfaces(c.type);
                l.nonEmpty();
                l = l.tail) {
                    bestSoFar = findMethod(env, site, name, argtypes,
                            typeargtypes,
                            l.head, abstractok, bestSoFar,
                            allowBoxing, useVarargs, operator);
                }
                if (concrete != bestSoFar &&
                        concrete.kind < ERR  && bestSoFar.kind < ERR &&
                        types.isSubSignature(concrete.type, bestSoFar.type))
                    bestSoFar = concrete;
            }
        }
        // Added this in - when we are within JML we can look in interfaces for 
        // model methods
        // FIXME - does this do interfaces recursively?
//        if (allowJML) 
//            for (Type ct : types.interfaces(intype)) {
//            ClassSymbol c = (ClassSymbol)ct.tsym;
//            abstractok = true;
//            for (Scope.Entry e = c.members().lookup(name);
//                        e.scope != null;
//                        e = e.next()) {
////              - System.out.println(" e " + e.sym);
//                if (e.sym.kind == MTH &&
//                        (e.sym.flags_field & SYNTHETIC) == 0 &&
//                        !(!allowJML && Utils.isJML(e.sym.flags_field))) {
//                    bestSoFar = selectBest(env, site, argtypes, typeargtypes,
//                            e.sym, bestSoFar,
//                            allowBoxing,
//                            useVarargs,
//                            operator);
//                }
//            }
////          - System.out.println(" - " + bestSoFar);
//            if (abstractok) {
//                Symbol concrete = methodNotFound;
//                if ((bestSoFar.flags() & ABSTRACT) == 0)
//                    concrete = bestSoFar;
//                for (List<Type> l = types.interfaces(c.type);
//                l.nonEmpty();
//                l = l.tail) {
//                    bestSoFar = findMethod(env, site, name, argtypes,
//                            typeargtypes,
//                            l.head, abstractok, bestSoFar,
//                            allowBoxing, useVarargs, operator);
//                }
//                if (concrete != bestSoFar &&
//                        concrete.kind < ERR  && bestSoFar.kind < ERR &&
//                        types.isSubSignature(concrete.type, bestSoFar.type))
//                    bestSoFar = concrete;
//            }
//        }
        return bestSoFar;
     }

     /** This method overrides the superclass method in order to load spec files
      * when a class is loaded.  If the superclass loads a method from source, then
      * the specs are parsed at the same time that the source file is parsed.
      * However, if the specs are loaded from binary, then the code here is needed
      * to obtain and parse the specification files as well.
      * 
      * @param env the environment within which a class will be loaded (e.g. package or containing class)
      * @param name the qualified name of the class to load
      * @return the unique symbol corresponding to this class
      */
     @Override
     public Symbol loadClass(Env<AttrContext> env, Name name) {
         if (Utils.jmldebug) System.out.println("LOADING REQUESTED " + name + " " + ClassReader.isClassAlreadyRead(context,name));
         Symbol s = super.loadClass(env, name);
         if (!(s instanceof ClassSymbol)) return s; // loadClass can be called for a package
         JmlSpecs.TypeSpecs tsp = JmlSpecs.instance(context).get((ClassSymbol)s);
         if (tsp == null) {
             if (Utils.jmldebug) System.out.println("   LOADING SPECS FOR (BINARY) CLASS " + name);
             ((JmlCompiler)JmlCompiler.instance(context)).loadSpecsForBinary(env,(ClassSymbol)s);
             //if (Utils.jmldebug) System.out.println("   LOADED BINARY " + name + " HAS SCOPE WITH SPECS " + s.members());
             return s;
         } else {
             //if (Utils.jmldebug) System.out.println("   LOADED CLASS " + name + " ALREADY HAS SPECS LOADED");
         }
         return s;
     }
     
     /** A cache of the symbol for the spec_public annotation class, created on
      * demand.
      */
     private ClassSymbol specPublicSym = null;
     
     /** A cache of the symbol for the spec_protected annotation class, created on
      * demand.
      */
     private ClassSymbol specProtectedSym = null;
     
     /** This class is overridden in order to allow access according to the rules
      * for spec_public and spec_protected.
      */
     @Override
     public boolean isAccessible(Env<AttrContext> env, Type site, Symbol sym) {
         if (sym.name == names.init && sym.owner != site.tsym) return false;
         if (super.isAccessible(env,site,sym)) return true;
         
         if (!allowJML) return false;
         // If not accessible and we are in JML, see if spec_public or spec_protected helps
         
         JCTree.JCModifiers mods=null;
         if (sym instanceof Symbol.VarSymbol) {
             JmlSpecs.FieldSpecs f = JmlSpecs.instance(context).getSpecs((Symbol.VarSymbol)sym);
             if (f != null) mods = f.mods;
         }
         
         if (specPublicSym == null) {
             specPublicSym = ClassReader.instance(context).enterClass(JmlAttr.instance(context).tokenToAnnotationName.get(JmlToken.SPEC_PUBLIC));
         }
         if (specProtectedSym == null) {
             specProtectedSym = ClassReader.instance(context).enterClass(JmlAttr.instance(context).tokenToAnnotationName.get(JmlToken.SPEC_PROTECTED));
         }
         // FIXME - sort out what is really happening here - the second part seems at least needed when a java file is referencing a binary file with a spec
         // (Is this because the binary file will not have the attributes in it - they are add ad hoc when the spec file is parsed???)
         boolean isSpecPublic = sym.attributes_field == null ? false : (sym.attribute(specPublicSym) != null || JmlAttr.instance(context).findMod(mods,JmlToken.SPEC_PUBLIC)!=null);
         if (isSpecPublic) return true;
         boolean isSpecProtected = sym.attributes_field == null ? false : (sym.attribute(specProtectedSym) != null || JmlAttr.instance(context).findMod(mods,JmlToken.SPEC_PROTECTED)!=null);
         //int flag = (int)((sym.flags() & AccessFlags));
         //if (isSpecProtected && flag != Flags.PUBLIC) return true;
         if (isSpecProtected) { // The symbol being accessed should be treated as if it were protected.
                         // Copy code from overridden method
             return
             (env.toplevel.packge == sym.owner.owner // fast special case
              ||
              env.toplevel.packge == sym.packge()
              ||
              isProtectedAccessible(sym, env.enclClass.sym, site)
              ||
              // OK to select instance method or field from 'super' or type name
              // (but type names should be disallowed elsewhere!)
              env.info.selectSuper && (sym.flags() & STATIC) == 0 && sym.kind != TYP)
             &&
             isAccessible(env, site)
             &&
             // `sym' is accessible only if not overridden by
             // another symbol which is a member of `site'
             // (because, if it is overridden, `sym' is not strictly
             // speaking a member of `site'.)
             (sym.kind != MTH || sym.isConstructor() || sym.isStatic() ||
              ((MethodSymbol)sym).implementation(site.tsym, types, true) == sym);
             
         }
         return false;
     }
}
