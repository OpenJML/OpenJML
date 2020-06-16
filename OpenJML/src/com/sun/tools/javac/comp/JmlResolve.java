/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 * Reviewed: 2018-03-17
 */
package com.sun.tools.javac.comp;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.ext.Modifiers;

import com.sun.tools.javac.main.JmlCompiler;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;

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
 * 
 * @author David Cok
 */
public class JmlResolve extends Resolve {

    /** The compilation context in which to do lookup. */
    public Context context;
    
    /** This flag determines whether or not JML-flagged declarations are 
     * returned as the result of a name lookup.  It may be set by clients of
     * this class through the setJML method.  Note that contexts are nested, 
     * so you should remember and
     * restore the value of this flag when you are setting it.
     */
    protected boolean allowJML = false;
    
    /** Cached value of a org.jmlspecs.openjml.Utils object */
    final protected Utils utils;
    
    /** Cached value of JmlCompiler, used for loading classes */
    protected JmlCompiler jmlcompiler;
    
    /** Cached value of JmlAttr, used for resolving annotations */
    final protected JmlAttr attr;
    
    /** Returns the unique instance of this class for the given compilation context
     * @param context the compilation context whose instance of Resolve is desired
     * @return the unique instance of JmlResolve
     */
    public static JmlResolve instance(Context context) {
        JmlResolve instance = (JmlResolve)context.get(resolveKey);
        if (instance == null)
            instance = new JmlResolve(context);
        return instance;
    }

    /** Registers a factory for JmlResolve against the resolveKey.  Once an instance
     * is created it registers itself, so there is a unique instance per context.
     * @param context the context in which to register the instance
     */
    public static void preRegister(final Context context) {
        context.put(Resolve.resolveKey, new Context.Factory<Resolve>() {
            public Resolve make(Context context) {
                return new JmlResolve(context);
            }
        });
    }
    
    /** Creates an instance of this class for the given context; clients should
     * use the instance() method rather than calling this constructor directly.
     * @param context the compilation context in which to construct this instance
     */
    //@ ensures context != null;
    protected JmlResolve(Context context) {
        super(context);
        this.context = context;
        this.utils = Utils.instance(context);
        this.attr = JmlAttr.instance(context);
        
    }
    
    /** This method is used to set the value of the allowJML flag.  It returns
     * the previous value.
     * @param allowJML the new value
     * @return the old value
     */
    public boolean setAllowJML(boolean allowJML) {
        boolean b = this.allowJML;
        this.allowJML = allowJML;
        return b;
    }
    
    /** Returns the value of the allowJML flag. */
    public boolean allowJML() {
        return this.allowJML;
    }
    
    /** This check is inserted in the superclass methods: JML symbols are mixed in
     * with the Java symbols in the various scopes; we do this check to forbid using
     * JML symbols when we are not in a JML context.
     */
    @Override
    protected boolean symbolOK(Scope.Entry e) {
        return allowJML || !utils.isJML(e.sym.flags_field);
    }
    
    public Symbol resolveQualifiedMethod(DiagnosticPosition pos, Env<AttrContext> env,
            Symbol location, Type site, Name name, List<Type> argtypes,
            List<Type> typeargtypes) {
        boolean isJML = utils.isJML(site.tsym.flags());
        boolean prev = setAllowJML(isJML || allowJML());
        Symbol s =  super.resolveQualifiedMethod(pos, env, location, site, name, argtypes, typeargtypes);
        setAllowJML(prev);
        return s;
    }


     
//     // A hook method added into Resolve.findMethod to avoid replication of
//     // parent class code.
//     /** TODO: Not sure exactly what this controls in the superclass */
//     @Override
//     protected boolean abstractOK(ClassSymbol c) {
//         return allowJML || super.abstractOK(c);
//     }


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
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("BINARY LOADING STARTING " + name );
        Symbol s = super.loadClass(env, name);
        // Here s can be a type or a package or not exist 
        // s may not exist because it is being tested whether such a type exists
        // (rather than a package) and is a legitimate workflow in this
        // architecture.  Hence no warning or error is given.
        // This happens for example in the resolution of org.jmlspecs.annotation
        if (!s.exists()) {
            return s;
        }
        if (!(s instanceof ClassSymbol)) {
            if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("  Loaded a non-class " + name );
            return s; // loadClass can be called for a package
        }

        JmlMemberEnter memberEnter = (JmlMemberEnter)JmlMemberEnter.instance(context);
        boolean completion = memberEnter.completionEnabled;
        memberEnter.completionEnabled = true;
        // FIXME - explain why we need completion enabled

        try {
            JmlSpecs specs = JmlSpecs.instance(context);
            JmlSpecs.TypeSpecs tsp = specs.get((ClassSymbol)s);
            if (tsp == null) {

                if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("   LOADING SPECS FOR (BINARY) CLASS " + name);
                // Cannot set jmlcompiler in the constructor because we get a circular initialization problem.
                if (jmlcompiler == null) jmlcompiler = ((JmlCompiler)JmlCompiler.instance(context));
                jmlcompiler.loadSpecsForBinary(env,(ClassSymbol)s);
                if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("   LOADED BINARY " + name + " HAS SCOPE WITH SPECS " + s.members());
// FIXME - the following happens routinely - it is not an error apparenetly, but some explanation or understanding is needed
//                if (specs.get((ClassSymbol)s) == null) 
//                    log.getWriter(WriterKind.NOTICE).println("(Internal error) POSTCONDITION PROBLEM - no typeSpecs stored for " + s);
            } else {
                if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("   LOADED CLASS " + name + " ALREADY HAS SPECS LOADED");
            }
            return s;
        } finally {
            memberEnter.completionEnabled = completion;
        }
    }

    // FIXME - I think these are cached elsewhere as well??
    /** A cache of the symbol for the spec_public annotation class, created on
     * demand.
     */
    public ClassSymbol specPublicSym = null;

    /** A cache of the symbol for the spec_protected annotation class, created on
     * demand.
     */
    public ClassSymbol specProtectedSym = null;

    /** This class is overridden in order to allow access according to the rules
     * for spec_public and spec_protected.
     */
    @Override
    public boolean isAccessible(Env<AttrContext> env, Type site, Symbol sym) {
        if (super.isAccessible(env,site,sym)) return true;
        if (!allowJML) return false;

        // If not accessible and we are in JML, see if spec_public or spec_protected helps

        JmlSpecs specs = JmlSpecs.instance(context);
        JCTree.JCModifiers mods = null;
        if (sym instanceof Symbol.VarSymbol) {
            JmlSpecs.FieldSpecs f = specs.getSpecs((Symbol.VarSymbol)sym);
            if (f != null) mods = f.mods;
        } else if (sym instanceof Symbol.MethodSymbol) {
            JmlSpecs.MethodSpecs f = specs.getSpecs((Symbol.MethodSymbol)sym);
            if (f != null) mods = f.mods;
        } else if (sym instanceof Symbol.ClassSymbol) {
            JmlSpecs.TypeSpecs f = specs.getSpecs((Symbol.ClassSymbol)sym);
            if (f != null) mods = f.modifiers;
        }

        if (specPublicSym == null) {
            specPublicSym = attr.modToAnnotationSymbol.get(Modifiers.SPEC_PUBLIC);
        }
        if (specProtectedSym == null) {
            specProtectedSym = attr.modToAnnotationSymbol.get(Modifiers.SPEC_PROTECTED);
        }

        boolean isSpecPublic = utils.findMod(mods,specPublicSym) != null;
        if (isSpecPublic) {
            long saved = sym.flags();
            sym.flags_field |= Flags.PUBLIC;
            boolean b = super.isAccessible(env,site,sym);
            sym.flags_field = saved;
            return b;
        }

        if ((sym.flags() & Flags.PROTECTED) != 0) return false;
        boolean isSpecProtected = utils.findMod(mods,specProtectedSym) != null;
        if (isSpecProtected) {
            long saved = sym.flags_field;
            sym.flags_field |= Flags.PROTECTED;
            boolean b = super.isAccessible(env,site,sym);
            sym.flags_field = saved;
            return b;
        }
        return false;
    }

    /** This is declared in order to provide public visibility */
    public Symbol resolveUnaryOperator(DiagnosticPosition pos, JCTree.Tag optag, Env<AttrContext> env, Type arg) {
        return super.resolveUnaryOperator(pos,optag,env,arg);
    }

    // TODO - explain while we need to silence errors
    boolean silentErrors = false;
//    boolean errorOccurred = false;

    protected void logResolveError(ResolveError error, 
            DiagnosticPosition pos,
            Symbol location,
            Type site,
            Name name,
            List<Type> argtypes,
            List<Type> typeargtypes) {
        if (!silentErrors) super.logResolveError(error,pos,location,site,name,argtypes,typeargtypes);
    }

    // Overridden purely to invoke JmlLookupFilter; otherwise a copy of Resolve.findMethodInScope
    @Override
    protected Symbol findMethodInScope(Env<AttrContext> env, 
            Type site,
            Name name,
            List<Type> argtypes,
            List<Type> typeargtypes,
            Scope sc,
            Symbol bestSoFar,
            boolean allowBoxing,
            boolean useVarargs,
            boolean operator,
            boolean abstractok) {
        for (Symbol s : sc.getElementsByName(name, new JmlLookupFilter(abstractok))) {
            bestSoFar = selectBest(env, site, argtypes, typeargtypes, s,
                    bestSoFar, allowBoxing, useVarargs, operator);
        }
        return bestSoFar;
    }

    /** This class extends Resolve.LookupFilter to disallow using variables declared in
     * JML within Java code
     */
    class JmlLookupFilter extends LookupFilter {

        boolean abstractOk;

        JmlLookupFilter(boolean abstractOk) {
            super(abstractOk);
        }

        public boolean accepts(Symbol s) {
            if (!super.accepts(s)) return false;
            if (utils.isJML(s.flags()) && !allowJML()) return false;
            return true;
        }
    };
}
