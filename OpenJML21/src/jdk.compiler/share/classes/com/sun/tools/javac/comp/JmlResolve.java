/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 * Reviewed: 2018-03-17
 */
package com.sun.tools.javac.comp;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.ext.Modifiers;

import com.sun.tools.javac.main.JmlCompiler;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.comp.Resolve.RecoveryLoadClass;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Kinds.KindSelector;
import com.sun.tools.javac.code.JmlType;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.Tag;
import com.sun.tools.javac.tree.Pretty;
import com.sun.tools.javac.tree.TreeInfo;
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
     * Setting this to true is for name resolution within a JML annotation.
     */
    protected boolean allowJML = false;
    
    /** This flag is set true when a name resolution is within a .jml file
     * and thus should use the import list in the .jml file; this is not the
     * same as being within a JML annotation (which is what allowJML is for).
     */
    protected boolean inJMLCU = false;
    
    /** Cached value of a org.jmlspecs.openjml.Utils object */
    final protected Utils utils;
    
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
    /** Sets the value of inJML, returning the old value */
    public boolean setInJMLCU(boolean inJMLCU) {
        boolean b = this.inJMLCU;
        this.inJMLCU = inJMLCU;
        return b;
    }
    
    /** This method is used to set the value of the allowJML flag.  It returns
     * the previous value.
     * @param allowJML the new value
     * @return the old value
     */
    public boolean setAllowJML(boolean allowJML) {
        //System.out.println("SETTING ALLOWJML TO " + allowJML); Utils.dumpStack();
        boolean b = this.allowJML;
        this.allowJML = allowJML;
        return b;
    }
    
    /** Turns on allowJML if the argument is true, but does not turn it off; returns the old setting */
    public boolean addAllowJML(boolean allowJML) {
        return setAllowJML(this.allowJML || allowJML);
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
    protected boolean symbolOK(Symbol e) {
        return allowJML || !utils.isJML(e.flags_field);
    }
    
    @Override
    Symbol findTypeGlobalDetails(Env<AttrContext> env, Name name, Symbol bestSoFar) {
        if (!env.tree.hasTag(Tag.IMPORT)) {
            Symbol sym;
            var cu = (org.jmlspecs.openjml.JmlTree.JmlCompilationUnit)env.toplevel;
            var speccu = cu.specsCompilationUnit;
            
            boolean deb2 = false; // name.toString().equals("X") || name.toString().equals("Q");
            if (deb2) System.out.println("SEARCHING FOR GLOBAL: " + name + "  allowJML=" + allowJML + "  inJMLCU=" + inJMLCU + " " + (speccu == null) + " " + (speccu == cu));

            if (inJMLCU) {
                sym = findGlobalType(env, speccu.namedImportScope, name, namedImportScopeRecovery);
            } else {
                sym = findGlobalType(env, cu.namedImportScope, name, namedImportScopeRecovery);
            }
            if (deb2 && sym.exists()) System.out.println("Name " + name + " is matched to a named import");
            if (sym.exists()) return sym;
            else bestSoFar = bestOf(bestSoFar, sym);

            sym = findGlobalType(env, cu.toplevelScope, name, noRecovery);
            if (deb2 && sym.exists()) System.out.println("Name " + name + " is matched to a top-level class");
            if (sym.exists()) return sym;
            else bestSoFar = bestOf(bestSoFar, sym);

            sym = findGlobalType(env, cu.packge.members(), name, noRecovery);
            if (deb2 && sym.exists()) System.out.println("Name " + name + " is matched to a package class");
            if (sym.exists()) return sym;
            else bestSoFar = bestOf(bestSoFar, sym);

            if (inJMLCU) {
                sym = findGlobalType(env, speccu.starImportScope, name, starImportScopeRecovery);
            } else {
                sym = findGlobalType(env, cu.starImportScope, name, starImportScopeRecovery);
            }
            if (deb2 && sym.exists()) System.out.println("Name " + name + " is matched to a star import");
            if (sym.exists()) return sym;
            else bestSoFar = bestOf(bestSoFar, sym);
            //if (deb2) { System.out.println("BEST " + bestSoFar); org.jmlspecs.openjml.Utils.dumpStack(); }
        }

        return bestSoFar;
    }
    
    Symbol findIdent(DiagnosticPosition pos, Env<AttrContext> env, Name name, KindSelector kind) {
        //if (name.toString().equals("Q")) System.out.println("FINDIDENT " + name + " " + allowJML);
        var s = super.findIdent(pos, env, name, kind);
        return s;
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


//    /** This method overrides the superclass method in order to load spec files
//     * when a class is loaded.  If the superclass loads a method from source, then
//     * the specs are parsed at the same time that the source file is parsed.
//     * However, if the specs are loaded from binary, then the code here is needed
//     * to obtain and parse the specification files as well.
//     * 
//     * @param env the environment within which a class will be loaded (e.g. package or containing class)
//     * @param name the qualified name of the class to load
//     * @return the unique symbol corresponding to this class
//     */
//    @Override
//    public Symbol loadClass(Env<AttrContext> env, Name name, RecoveryLoadClass recoveryLoadClass) {
//        Symbol s = super.loadClass(env, name, recoveryLoadClass);
//        // Here s can be a type or a package or not exist 
//        // s may not exist because it is being tested whether such a type exists
//        // (rather than a package) and is a legitimate workflow in this
//        // architecture.  Hence no warning or error is given.
//        // This happens for example in the resolution of org.jmlspecs.annotation
//        if (!s.exists()) {
//            //utils.note(true,"  Attempt to load " + name + " in module " + env.toplevel.modle + " but does not exist: " + s);
//            return s;
//        }
//        if (!(s instanceof ClassSymbol)) {
//            utils.note(true,"  Loaded a non-class " + name + " module " + env.toplevel.modle);
//            return s; // loadClass can be called for a package
//        }
//
//        utils.note(true,"  Loaded class without specs: " + s);
////        // Cannot set jmlcompiler in the constructor because we get a circular initialization problem.
////        JmlEnter.instance(context).requestSpecs((ClassSymbol)s);
//        return s;
//    }

    /** This class is overridden in order to allow access according to the rules
     * for spec_public and spec_protected.
     */
    protected long flags(Symbol sym) { // OPENJML
    	return attr.flags(sym);
    }
    
//    @Override
//    public boolean isAccessible(Env<AttrContext> env, TypeSymbol sym, boolean checkInner) {
//        if (super.isAccessible(env,sym,checkInner)) return true;
//        if (!allowJML) return false;
//
//        // If not accessible and we are in JML, see if spec_public or spec_protected helps
//
//        JmlSpecs specs = JmlSpecs.instance(context);
//        JCTree.JCModifiers mods = null;
//        if (sym instanceof Symbol.ClassSymbol) {
//        	JmlSpecs.TypeSpecs f = specs.getSpecs((Symbol.ClassSymbol)sym);
//        	if (f != null) mods = f.modifiers;
//        }
//
//        boolean isSpecPublic = utils.hasMod(mods,Modifiers.SPEC_PUBLIC);
//        if (isSpecPublic) {
//        	return true;
////        	long saved = sym.flags();
////        	sym.flags_field |= Flags.PUBLIC;
////        	boolean b = super.isAccessible(env,sym,checkInner);
////        	sym.flags_field = saved;
////        	return b;
//        }
//
//        if ((sym.flags() & Flags.PROTECTED) != 0) return false; // Already is protected
//        boolean isSpecProtected = utils.hasMod(mods,Modifiers.SPEC_PROTECTED);
//        if (isSpecProtected) {
//        	long saved = sym.flags_field;
//        	sym.flags_field |= Flags.PROTECTED;
//        	boolean b = super.isAccessible(env,sym,checkInner);
//        	sym.flags_field = saved;
//        	return b;
//        }
//        return false;
//    }
//
//
//    /** This class is overridden in order to allow access according to the rules
//     * for spec_public and spec_protected.
//     */
//    @Override
//    public boolean isAccessible(Env<AttrContext> env, Type site, Symbol sym, boolean checkInner) {
//        if (super.isAccessible(env,site,sym,checkInner)) return true;
//        if (!allowJML) return false;
//
//        // If not accessible and we are in JML, see if spec_public or spec_protected helps
//
//        JmlSpecs specs = JmlSpecs.instance(context);
//        JCTree.JCModifiers mods = null;
//        if (sym instanceof Symbol.VarSymbol) {
//            JmlSpecs.FieldSpecs f = specs.getSpecs((Symbol.VarSymbol)sym);
//            if (f != null) mods = f.mods;
//        } else if (sym instanceof Symbol.MethodSymbol) {
//            JmlSpecs.MethodSpecs f = specs.getSpecs((Symbol.MethodSymbol)sym);
//            if (f != null) mods = f.mods;
//        } else if (sym instanceof Symbol.ClassSymbol) {
//            JmlSpecs.TypeSpecs f = specs.getSpecs((Symbol.ClassSymbol)sym);
//            if (f != null) mods = f.modifiers;
//        }
//
//        boolean isSpecPublic = utils.hasMod(mods,Modifiers.SPEC_PUBLIC);
//        if (isSpecPublic) {
//        	return true;
////            long saved = sym.flags();
////            sym.flags_field |= Flags.PUBLIC;
////            boolean b = super.isAccessible(env,site,sym);
////            sym.flags_field = saved;
////            return b;
//        }
//
//        if ((sym.flags() & Flags.PROTECTED) != 0) return false; // Already is protected
//        boolean isSpecProtected = utils.hasMod(mods,Modifiers.SPEC_PROTECTED);
//        if (isSpecProtected) {
//            long saved = sym.flags_field;
//            sym.flags_field |= Flags.PROTECTED;
//            boolean b = super.isAccessible(env,site,sym);
//            sym.flags_field = saved;
//            return b;
//        }
//        return false;
//    }
    
    // FIXME - this is copied from old OpenJDK -- there must be a better way in the current framework
    // FIXME - and there must be a better way to get an operator name than using the Pretty printer
    Symbol.OperatorSymbol resolveOperator(DiagnosticPosition pos, JCTree.Tag optag,
    		Env<AttrContext> env, List<Type> argtypes) {
    	MethodResolutionContext prevResolutionContext = currentResolutionContext;
    	try {
    		currentResolutionContext = new MethodResolutionContext();
    		Name name = names.fromString(Pretty.operatorName(optag));
    		return (Symbol.OperatorSymbol)lookupMethod(env, pos, syms.predefClass, currentResolutionContext,
    				new BasicLookupHelper(name, syms.predefClass.type, argtypes, null, MethodResolutionPhase.BOX) {
    			@Override
    			Symbol doLookup(Env<AttrContext> env, MethodResolutionPhase phase) {
    				return findMethod(env, site, name, argtypes, typeargtypes,
    						phase.isBoxingRequired(),
    						phase.isVarargsRequired());
    			}
    			@Override
    			Symbol access(Env<AttrContext> env, DiagnosticPosition pos, Symbol location, Symbol sym) {
    				return accessMethod(sym, pos, env.enclClass.sym.type, name,
    						false, argtypes, null);
    			}
    		});
    	} finally {
    		currentResolutionContext = prevResolutionContext;
    	}
    }

    public Symbol.OperatorSymbol resolveUnaryOperator(DiagnosticPosition pos, JCTree.Tag optag, Env<AttrContext> env, Type arg) {
        return resolveOperator(pos,optag,env,List.of(arg));
    }

    public Symbol.OperatorSymbol resolveBinaryOperator(DiagnosticPosition pos, JCTree.Tag optag, Env<AttrContext> env, Type arg, Type arg2) {
        return resolveOperator(pos,optag,env,List.of(arg,arg2));
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
            boolean useVarargs,
            boolean operator,
            boolean abstractok) {
    	try {
    		for (Symbol s : sc.getSymbolsByName(name, new JmlLookupFilter(abstractok))) {
    			bestSoFar = selectBest(env, site, argtypes, typeargtypes, s,
    					bestSoFar, useVarargs, operator);
    		}
    		return bestSoFar;
    	} catch (Exception e) {
    		utils.error("jml.internal", "Exception in findMethodInScope: " + site + " " + name + " " + argtypes + " <" + typeargtypes +">");
    		e.printStackTrace(System.out);
    		throw e;
    	}
    }
    
    /** This class extends Resolve.LookupFilter to disallow using variables declared in
     * JML within Java code
     */
    class JmlLookupFilter extends LookupFilter {

        boolean abstractOk;

        JmlLookupFilter(boolean abstractOk) {
            super(abstractOk);
        }

        public boolean test(Symbol s) {
            if (!super.test(s)) return false;
            if (utils.isJML(s.flags()) && !allowJML()) return false;
            return true;
        }
    };
}
