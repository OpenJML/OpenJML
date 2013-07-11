/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.smtlib.ICommand;
import org.smtlib.ICommand.IScript;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IBinding;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser;
import org.smtlib.ISort;
import org.smtlib.SMT;
import org.smtlib.command.C_assert;
import org.smtlib.command.C_check_sat;
import org.smtlib.command.C_declare_fun;
import org.smtlib.command.C_declare_sort;
import org.smtlib.command.C_define_fun;
import org.smtlib.command.C_push;
import org.smtlib.command.C_set_logic;
import org.smtlib.command.C_set_option;
import org.smtlib.impl.Factory;
import org.smtlib.impl.Script;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.Type.ClassType;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.model.JavacTypes;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

/** This class translates a BasicBlock program into SMTLIB. 
 * The input program is a BasicBlock program, which may consist of the
 * following kinds of statements:
 * <UL>
 * <LI>declaration statements with or without initializers (FIXME - what kinds of types)
 * <LI>JML assume statements
 * <LI>JML assert statements
 * <LI>JML comment statements
 * </UL>
 * Expressions may include the following:
 * <UL>
 * <LI>Java operators: + - * / % comparisons bit-operations logic-operators
 * <LI>field access - FIXME?
 * <LI>array access - FIXME?
 * <LI>STORE and SELECT functions using Java method class (JCMethodInvocation)
 * <LI>method calls (FIXME - any restrictions?)
 * </UL>
 */
public class SMTTranslator extends JmlTreeScanner {

    /** The compilation context */
    protected Context context;
    
    /** The error log */
    protected Log log;
    
    /** The symbol table for this compilation context */
    protected Symtab syms;
    
    /** The Names table for this compilation context */
    protected Names names;
    
    /** Cached value of the types tool */
    protected javax.lang.model.util.Types types;
    
    /** Cached instance of the JmlTreeUtils tool for the context. */
    protected JmlTreeUtils treeutils;
    
    /** The factory for creating SMTLIB expressions */
    protected Factory F;
    
    /** SMTLIB subexpressions - the result of each visit call */
    protected IExpr result;
    
    /** Commonly used SMTLIB expressions - using these shares structure */
    protected ISort refSort;
    protected ISort stringSort;
    protected ISort javaTypeSort;
    protected ISort jmlTypeSort;
    protected ISort intSort;
    protected ISort boolSort;
    protected ISort realSort;
    protected IExpr.ISymbol nullSym;
    protected IExpr.ISymbol lengthSym;
    protected IExpr.ISymbol arraySym;
    protected IExpr.ISymbol thisSym;
    protected IExpr.ISymbol eqSym;
    protected IExpr.ISymbol impliesSym;
    protected IExpr.ISymbol selectSym;
    
    
    /** The SMTLIB script as it is being constructed */
    protected IScript script;
    
    /** An alias to script.commands() */
    protected List<ICommand> commands;
    
    /** A list that accumulates all the Java type constants used */
    protected Set<Type> javaTypes = new HashSet<Type>();
    protected Set<String> javaTypeSymbols = new HashSet<String>();
    
    int stringCount = 0;
    int doubleCount = 0;
    int uniqueCount = 0;
    boolean inQuant = false;

    // Strings used in our use of SMT. Strings that are part of SMTLIB itself
    // are used verbatim in the code.
    public static final String store = "store";
    public static final String select = "select";
    public static final String NULL = "NULL";
    public static final String this_ = "THIS"; // Must be the same as the id used in JmlAssertionAdder
    public static final String REF = "REF";
    public static final String STRINGSORT = "_STRING_";
    public static final String JAVATYPESORT = "JavaTypeSort";
    public static final String JMLTYPESORT = "JMLTypeSort";
    public static final String length = "__JMLlength"; // array length
    public static final String arrays_ = "arrays_";
    public static final String Array = "Array"; // Name of SMT Array sort
    
    public BiMap<JCExpression,IExpr> bimap = new BiMap<JCExpression,IExpr>();
    
    public SMTTranslator(Context context) {
        this.context = context;
        log = Log.instance(context);
        syms = Symtab.instance(context);
        names = Names.instance(context);
        types = JavacTypes.instance(context);
        treeutils = JmlTreeUtils.instance(context);
        
        F = new org.smtlib.impl.Factory();
        nullSym = F.symbol(NULL);
        thisSym = F.symbol(this_);
        refSort = F.createSortExpression(F.symbol(REF));
        boolSort = F.createSortExpression(F.symbol("Bool"));
        intSort = F.createSortExpression(F.symbol("Int"));
        realSort = F.createSortExpression(F.symbol("Real"));
        stringSort = F.createSortExpression(F.symbol(STRINGSORT));
        javaTypeSort = F.createSortExpression(F.symbol(JAVATYPESORT));
        jmlTypeSort = F.createSortExpression(F.symbol(JMLTYPESORT));
        lengthSym = F.symbol(length);
        arraySym = F.symbol(Array);
        eqSym = F.symbol("="); // Name determined by SMT Core theory
        impliesSym = F.symbol("=>"); // Name determined by SMT Core theory
        selectSym = F.symbol("select"); // Name determined by SMT Array Theory
        
    }
    
    @Override
    public void scan(JCTree t) {
        result = null;
        if (t != null) {
            super.scan(t);
            if (result != null && t instanceof JCExpression) bimap.put((JCExpression)t, result);
            if (result != null && t instanceof JmlVariableDecl) {
                JCIdent id = ((JmlVariableDecl)t).ident;
                bimap.put(id, result);
            }
        }
    }
    
    public final List<ISort> emptyList = new LinkedList<ISort>();
    
    // FIXME - want to be able to produce AUFBV programs as well
    // FIXME - this converts the whole program into one big SMT program
    //  - might want the option to produce many individual programs, i.e.
    //  one for each assertion, or a form that accommodates push/pop/coreids etc.
    
    public ICommand.IScript convert(BasicProgram program, SMT smt) {
        script = new Script();
        ICommand c;
        commands = script.commands();
        
        // FIXME - use factory for the commands?
        // set the logic
        c = new C_set_option(F.keyword(":produce-models"),F.symbol("true"));
        commands.add(c);
        
        String s = JmlOption.value(context, JmlOption.LOGIC);
        c = new C_set_logic(F.symbol(s));
        commands.add(c);
        
        // add background statements
        c = new C_declare_sort(F.symbol(REF),F.numeral(0));
        commands.add(c);
        c = new C_declare_sort(F.symbol(STRINGSORT),F.numeral(0));
        commands.add(c);
        c = new C_declare_sort(F.symbol(JAVATYPESORT),F.numeral(0));
        commands.add(c);
        c = new C_declare_sort(F.symbol(JMLTYPESORT),F.numeral(0));
        commands.add(c);
        c = new C_declare_fun(nullSym,emptyList, refSort);
        commands.add(c);
        c = new C_declare_fun(thisSym,emptyList, refSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("equals"),Arrays.asList(refSort,refSort), boolSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("stringConcat"),Arrays.asList(refSort,refSort), refSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("stringLength"),Arrays.asList(refSort), intSort);
        commands.add(c);
        c = new C_assert(F.fcn(F.symbol("distinct"), thisSym, nullSym));
        commands.add(c);
        c = new C_declare_fun(lengthSym,
                emptyList, 
                F.createSortExpression(arraySym,refSort,intSort)
                );
        commands.add(c);
        try {
            c = smt.smtConfig.smtFactory.createParser(smt.smtConfig,smt.smtConfig.smtFactory.createSource("(assert (forall ((o REF)) (>= (select "+length+" o) 0)))",null)).parseCommand();
            commands.add(c);
            c = smt.smtConfig.smtFactory.createParser(smt.smtConfig,smt.smtConfig.smtFactory.createSource("(assert (forall ((s1 REF)(s2 REF)) (distinct (stringConcat s1 s2) NULL)))",null)).parseCommand();
            commands.add(c);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
        List<ISort> args = Arrays.asList(refSort);
        c = new C_declare_fun(F.symbol("asIntArray"),args, F.createSortExpression(arraySym,intSort,intSort));
        commands.add(c);
        c = new C_declare_fun(F.symbol("asREFArray"),args, F.createSortExpression(arraySym,intSort,refSort));
        commands.add(c);
        c = new C_declare_fun(F.symbol("intValue"),args, intSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("boolValue"),args, boolSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("javaTypeOf"),args, javaTypeSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("jmlTypeOf"),args, jmlTypeSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("javaSubType"),
                Arrays.asList(new ISort[]{javaTypeSort,javaTypeSort}), 
                boolSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("jmlSubType"),
                Arrays.asList(new ISort[]{jmlTypeSort,jmlTypeSort}), 
                boolSort);
        commands.add(c);
        c = new C_declare_fun(F.symbol("erasure"),
                Arrays.asList(new ISort[]{jmlTypeSort}), 
                javaTypeSort);
        commands.add(c);
        c = new C_declare_fun(lengthSym,
                Arrays.asList(new ISort[]{refSort}), 
                intSort);
        // The declaration + assertion form is nominally equivalent to the define_fcn form, but works better
        // for SMT solvers with modest (or no) support for quantifiers (like yices2)
        if (false) {
            // (define_fcn nonnullelements ((a REF)(arrays (Array REF (Array Int REF)))) 
            //                             Bool
            //                             (forall ((i Int)) (=> (and (<= 0 i) (< i (length a))) (distinct NULL (select (select arrays a) i)))))
            c = new C_define_fun(F.symbol("nonnullelements"),
                    Arrays.asList(new IDeclaration[]{F.declaration(F.symbol("a"),refSort),
                            F.declaration(F.symbol("arrays"),
                                    F.createSortExpression(arraySym,
                                            refSort,
                                            F.createSortExpression(arraySym,intSort,refSort)))}), 
                    boolSort,
                    F.forall(Arrays.asList(new IDeclaration[]{F.declaration(F.symbol("i"),intSort)}),
                            F.fcn(impliesSym,
                                    F.fcn(F.symbol("and"),
                                            F.fcn(F.symbol("<="),F.numeral("0"),F.symbol("i")),
                                            F.fcn(F.symbol("<"), F.symbol("i"), F.fcn(selectSym,lengthSym,F.symbol("a")))
                                            ),
                                    F.fcn(F.symbol("distinct"),
                                            nullSym,
                                            F.fcn(selectSym,
                                                    F.fcn(selectSym,F.symbol("arrays"),F.symbol("a")),
                                                    F.symbol("i"))))));
            commands.add(c);
        } else {
            // (declare_fcn nonnullelements ((a REF)(arrays (Array REF (Array Int REF)))) Bool)
            // (assert (forall ((a REF)(arrays (Array REF (Array Int REF)))) (= (nonnullelements a arrays)
            //                             (forall ((i Int)) (=> (and (<= 0 i) (< i (length a))) (distinct NULL (select (select arrays a) i)))))
            c = new C_declare_fun(F.symbol("nonnullelements"),
                    Arrays.asList(new ISort[]{refSort,
                            F.createSortExpression(arraySym,
                                    refSort,
                                    F.createSortExpression(arraySym,intSort,refSort))}), 
                    boolSort);
            commands.add(c);
            c = new C_assert(
                    F.forall(Arrays.asList(new IDeclaration[]{F.declaration(F.symbol("a"),refSort),
                                                              F.declaration(F.symbol("arrays"),
                                                                      F.createSortExpression(arraySym,
                                                                              refSort,
                                                                              F.createSortExpression(arraySym,intSort,refSort)))
                                                             }),
                            F.fcn(eqSym,
                                    F.fcn(F.symbol("nonnullelements"), F.symbol("a"), F.symbol("arrays")),
                                    F.forall(Arrays.asList(new IDeclaration[]{F.declaration(F.symbol("i"),intSort)}),
                                            F.fcn(impliesSym,
                                                    F.fcn(F.symbol("and"),
                                                            F.fcn(F.symbol("<="),F.numeral("0"),F.symbol("i")),
                                                            F.fcn(F.symbol("<"), F.symbol("i"), F.fcn(selectSym,lengthSym,F.symbol("a")))
                                                            ),
                                                    F.fcn(F.symbol("distinct"),
                                                            F.symbol(NULL),
                                                            F.fcn(selectSym,F.fcn(selectSym,F.symbol("arrays"),F.symbol("a")),F.symbol("i"))
                                                            )
                                                    )
                                             )
                                    )));
            commands.add(c);
        }
        
        int loc = commands.size();
        
        addType(syms.objectType);
        addType(syms.exceptionType);
        addType(syms.runtimeExceptionType);
        
        
        for (JCExpression e: program.background()) {
            try {
                scan(e);
                IExpr ex = result;
                c = new C_assert(ex);
                commands.add(c);
            } catch (RuntimeException ee) {
                // skip - error already issued // FIXME - better error recovery?
            }
        }
        
        // add declarations
        
        defined.add(names.fromString(this_));
        defined.add(names.fromString(length));
        for (JCIdent id: program.declarations) {
            if (defined.add(id.name)) {
                try {
                    ISort sort = convertSort(id.type);
                    String nm = id.name.toString();
                    if (id.sym.owner instanceof Symbol.ClassSymbol && !Utils.instance(context).isJMLStatic(id.sym) && !id.sym.name.toString().equals("this")) {
                        sort = F.createSortExpression(arraySym,refSort,sort);
                    } else if (nm.startsWith(arrays_)) { // FIXME - use the constant string
                        sort = convertSort(((Type.ArrayType)id.type).getComponentType());
                        ISort intSort = convertSort(syms.intType); // FIXME: Make this a constant like Bool?
                        sort = F.createSortExpression(arraySym,intSort,sort); 
                        sort = F.createSortExpression(arraySym,refSort,sort);
                    }
                    ISymbol sym = F.symbol(nm);
                    c = new C_declare_fun(sym,
                            emptyList,
                            sort);
                    commands.add(c);
                    bimap.put(id,sym);
                } catch (RuntimeException ee) {
                    // skip - error already issued// FIXME - better error recovery?
                }
            }
        }
        
        // add definitions
        for (BasicProgram.Definition e: program.definitions()) {
            try {
                scan(e.value);
                ISymbol sym = F.symbol(e.id.toString());
                c = new C_define_fun(sym,
                        new LinkedList<IDeclaration>(),
                        convertSort(e.id.type),
                        result);
                commands.add(c);
                bimap.put(e.id,sym);
            } catch (RuntimeException ee) {
                // skip - error already issued // FIXME - better error recovery?
            }
        }
        
        // Because blocks have forward references to later blocks, but
        // backward references to variables in earlier blocks, we declare
        // all the block variables first
        for (BasicProgram.BasicBlock b: program.blocks()) {
            ICommand cc = new C_declare_fun(F.symbol(b.id.toString()), emptyList, F.Bool());
            commands.add(cc);
        }
        
        // add blocks
        for (BasicProgram.BasicBlock b: program.blocks()) {
            convertBasicBlock(b);
        }
        
        LinkedList<IExpr> argss = new LinkedList<IExpr>();
        argss.add(F.symbol(program.startId().name.toString()));
        IExpr negStartID = F.fcn(F.symbol("not"), argss);
        ICommand cc = new C_assert(negStartID);
        commands.add(cc);
        
        cc = new C_push(F.numeral(1));
        commands.add(cc);
        cc = new C_assert(F.fcn(eqSym,F.symbol(JmlAssertionAdder.assumeCheckVar),F.numeral(0)));
        commands.add(cc);
        cc = new C_push(F.numeral(1));
        commands.add(cc);
        cc = new C_check_sat();
        commands.add(cc);
        
        // Insert type relationships
        int len = javaTypes.size();
        List<ICommand> tcommands = new ArrayList<ICommand>(len*len);
        for (Type ti: javaTypes) {
            tcommands.add(new C_declare_fun(
                    javaTypeSymbol(ti),
                    emptyList,
                    javaTypeSort));
            tcommands.add(new C_declare_fun(
                    jmlTypeSymbol(ti),
                    emptyList,
                    jmlTypeSort));
            tcommands.add(new C_assert(F.fcn(
                    eqSym, 
                    F.fcn(F.symbol("erasure"),jmlTypeSymbol(ti)),
                    javaTypeSymbol(ti))));

        }
        for (Type ti: javaTypes) {
            for (Type tj: javaTypes) {
                IExpr.ISymbol si = javaTypeSymbol(ti);
                IExpr.ISymbol sj = javaTypeSymbol(tj);
                boolean b = types.isSubtype(types.erasure(ti),types.erasure(tj));
                IExpr comp = F.fcn(F.symbol("javaSubType"), si, sj);
                if (!b) comp = F.fcn(F.symbol("not"),comp);
                tcommands.add(new C_assert(comp));
                b = types.isSubtype(ti,tj);
                comp = F.fcn(F.symbol("jmlSubType"), jmlTypeSymbol(ti), jmlTypeSymbol(tj));
                if (!b) comp = F.fcn(F.symbol("not"),comp);
                tcommands.add(new C_assert(comp));
            }
        }
        {
            List<IDeclaration> params = new LinkedList<IDeclaration>();
            params.add(F.declaration(F.symbol("t1"),javaTypeSort));
            params.add(F.declaration(F.symbol("t2"),javaTypeSort));
            params.add(F.declaration(F.symbol("t3"),javaTypeSort));
            IExpr e = F.forall(params, 
                    F.fcn(F.symbol("=>"), 
                          F.fcn(F.symbol("and"), 
                                  F.fcn(F.symbol("javaSubType"),F.symbol("t1"),F.symbol("t2")),
                                  F.fcn(F.symbol("javaSubType"),F.symbol("t2"),F.symbol("t3"))
                                  ),
                          F.fcn(F.symbol("javaSubType"),F.symbol("t1"),F.symbol("t3"))
                          ));
            tcommands.add(new C_assert(e));
        }
        commands.addAll(loc,tcommands);
        
        return script;
    }
    
    public String typeString(Type t) {
        if (t.tag == TypeTags.ARRAY){
            return typeString(((ArrayType)t).elemtype) + "_A_";
        }
        return t.toString().replace(".", "_");
    }
    
    public IExpr.ISymbol javaTypeSymbol(Type t) {
        //String s = "|T_" + t.toString() + "|";
        if (t.tag == TypeTags.BOT) t = syms.objectType;
        String s = "T_" + typeString(t);
        return F.symbol(s);
    }
    
    public IExpr.ISymbol jmlTypeSymbol(Type t) {
        if (t.tag == TypeTags.BOT) t = syms.objectType;
        //String s = "|JMLT_" + t.toString() + "|" ;
        String s = "JMLT_" + typeString(t);
        return F.symbol(s);
    }
    
    public void addType(Type t) {
        // FIXME - what if t is the type of an explicit null?
        if (javaTypeSymbols.add(t.toString())) javaTypes.add(t);
    }
    
    /** Converts a BasicBlock into SMTLIB, adding commands into the
     * current 'commands' list.
     */
    public void convertBasicBlock(BasicProgram.BasicBlock block) {
        Iterator<JCStatement> iter = block.statements.iterator();
        IExpr tail; 
        if (block.followers.isEmpty()) {
            tail = F.symbol("true");
        } else if (block.followers.size() == 1) {
            tail = F.symbol(block.followers.get(0).id.name.toString());
        } else {
            ArrayList<IExpr> args = new ArrayList<IExpr>();
            for (BasicProgram.BasicBlock bb: block.followers) {
                args.add(F.symbol(bb.id.name.toString()));
            }
            tail = F.fcn(F.symbol("and"),args);
        }
        IExpr ex = convert(iter,tail);
        LinkedList<IExpr> args = new LinkedList<IExpr>();
        args.add(F.symbol(block.id.toString()));
        args.add(ex);
        ex = F.fcn(eqSym,args);
        commands.add(new C_assert(ex));
    }
    
    /** A helper method for convertBasicBlock. We need to construct the
     * expression representing a basicBlock from the end back to the 
     * beginning; we use recursive calls on this method to do that.
     */
    public IExpr convert(Iterator<JCStatement> iter, IExpr tail) {
        if (!iter.hasNext()) {
            return tail;
        }
        JCStatement stat = iter.next();
        try {
            if (stat instanceof JmlVariableDecl) {
                JmlVariableDecl decl = (JmlVariableDecl)stat;
                // convert to a declaration or definition
                IExpr init = decl.init == null ? null : convertExpr(decl.init);
                
                ISymbol sym = F.symbol(decl.name.toString());
                ICommand c = init == null ?
                        new C_declare_fun(
                                sym,
                                emptyList,
                                convertSort(decl.type))
                : new C_define_fun(
                        sym,
                        new LinkedList<IDeclaration>(),
                        convertSort(decl.type),
                        init);
                 commands.add(c);
                 if (decl.ident != null) bimap.put(decl.ident, sym);
                 return convert(iter,tail);
            } else if (stat instanceof JmlStatementExpr) {
                IExpr ex = convert(iter,tail); // FIXME - this make a big stack for a long list of commands
                JmlStatementExpr s = (JmlStatementExpr)stat;
                if (s.token == JmlToken.ASSUME) {
                    IExpr exx = convertExpr(s.expression);
                    LinkedList<IExpr> args = new LinkedList<IExpr>();
                    args.add(exx);
                    args.add(ex);
                    return F.fcn(impliesSym, args);
                } else if (s.token == JmlToken.ASSERT) {
                    IExpr exx = convertExpr(s.expression);
                    LinkedList<IExpr> args = new LinkedList<IExpr>();
                    args.add(exx);
                    args.add(ex);
                    return F.fcn(F.symbol("and"), args);
                } else if (s.token == JmlToken.COMMENT) {
                    // skip - add script comment ? TODO
                    return ex;
                } else {
                    log.error("jml.internal", "Incorrect kind of token encountered when converting a BasicProgram to SMTLIB: " + s.token);
                    return ex;
                }
            } else {
                log.error("jml.internal", "Incorrect kind of statement encountered when converting a BasicProgram to SMTLIB: " + stat.getClass());
            }
        } catch (RuntimeException ee) {
            // skip - error already issued // FIXME - better recovery
        }
        return F.symbol("false");
        
    }
    
    // FIXME - review this - need to choose between java and jml
    /** Converts a Java/JML type into an SMT Sort */
    public ISort convertSort(Type t) {
        if ( t == null) {
            log.error("jml.internal", "No type translation implemented when converting a BasicProgram to SMTLIB: " + t);
            throw new RuntimeException();
        } else if (t.tag == TypeTags.BOOLEAN) {
            return F.Bool();
        } else if (t.tag == TypeTags.INT) { 
            return intSort;
        } else if (t.tag == syms.objectType.tag) {
            return refSort;
        } else if (t.tag == TypeTags.SHORT) { 
            return intSort;
        } else if (t.tag == TypeTags.CHAR) { 
            return intSort;
        } else if (t.tag == TypeTags.BYTE) { 
            return intSort;
        } else if (t.tag == TypeTags.LONG) { 
            return intSort;
        } else if (t.tag == TypeTags.FLOAT) { 
            return F.createSortExpression(F.symbol("Real"));
        } else if (t.tag == TypeTags.DOUBLE) { 
            return F.createSortExpression(F.symbol("Real"));
        } else if (t.tag == TypeTags.ARRAY) {
            return refSort;
        } else if (t.tag == TypeTags.BOT) {
            return refSort;
        } else if (t instanceof Type.TypeVar) {
            return refSort;
//            ArrayType atype = (ArrayType)t;
//            Type elemtype = atype.getComponentType();
//            return F.createSortExpression(arraySym, intSort, convertSort(elemtype));
        } else {
            return F.createSortExpression(javaTypeSymbol(t)); // FIXME - use the common method for translating to type names?
//            log.error("jml.internal", "No type translation implemented when converting a BasicProgram to SMTLIB: " + t);
//            throw new RuntimeException();
        }
    }
    
    /** Converts an AST expression into SMT form. */
    public IExpr convertExpr(JCExpression expr) {
        scan(expr);
        return result;
    }
    
    // We need to be able to translate expressions
    
    public void notImpl(JCTree tree) {
        log.error("jml.internal","Not yet supported expression node in converting BasicPrograms to SMTLIB: " + tree.getClass());
    }
    
    public void shouldNotBeCalled(JCTree tree) {
        log.error("jml.internal","This node should not be present in converting BasicPrograms to SMTLIB: " + tree.getClass());
    }
    
    Set<String> fcnsDefined = new HashSet<String>();
    
    protected void addFcn(String newname, JCMethodInvocation tree) {
        if (fcnsDefined.add(newname)) {
            // Was not already present
            ISymbol n = F.symbol(newname);
            ISort resultSort = convertSort(tree.type);
            List<ISort> argSorts = new LinkedList<ISort>();
            if (!Utils.instance(context).isJMLStatic(treeutils.getSym(tree))) {
                argSorts.add(refSort);
            }
            for (JCExpression e: tree.args) {
                argSorts.add(convertSort(e.type));
            }
            C_declare_fun c = new C_declare_fun(n,argSorts,resultSort);
            commands.add(c);
        }
        
    }
    
    @Override
    public void visitApply(JCMethodInvocation tree) {
        JCExpression m = tree.meth;
        if (m instanceof JCIdent) {
            String name = ((JCIdent)m).name.toString();
            String newname;
            if (name.equals(BasicBlocker2.SELECTString)) {
                newname = "select";
            } else if (!JmlAssertionAdder.useMethodAxioms && name.equals("equals")) {
                newname = "equals";
            } else if (!JmlAssertionAdder.useMethodAxioms && name.equals("equal")) {
                newname = "equals";
            } else {
                newname = name;
                addFcn(newname,tree);
            }
            List<IExpr> newargs = new LinkedList<IExpr>();
            if (JmlAssertionAdder.useMethodAxioms && !Utils.instance(context).isJMLStatic(treeutils.getSym(tree))) {
                JCExpression e = ((JCFieldAccess)tree.meth).selected;
                scan(e);
                newargs.add(convertExpr(e));
            }
            for (JCExpression arg: tree.args) {
                scan(arg);
                newargs.add(convertExpr(arg));
            }
            result = F.fcn(F.symbol(newname),newargs);
            return;

        } else if (m == null) {
            if (tree instanceof JmlBBFieldAssignment) {
                IExpr.IFcnExpr right = F.fcn(F.symbol("store"),
                        convertExpr(tree.args.get(1)),
                        convertExpr(tree.args.get(2)),
                        convertExpr(tree.args.get(3))
                        );
                result = F.fcn(eqSym, convertExpr(tree.args.get(0)),right);
                return;
            }
            else if (tree instanceof JmlBBArrayAssignment) {
                if (tree.args.length() > 3) {
                    // [0] = store([1],[2], store(select([1],[2]),[3],[4]))
                    IExpr.IFcnExpr sel = F.fcn(selectSym,
                            convertExpr(tree.args.get(1)),
                            convertExpr(tree.args.get(2))
                            );
                    IExpr.IFcnExpr newarray = F.fcn(F.symbol("store"),
                            sel,
                            convertExpr(tree.args.get(3)),
                            convertExpr(tree.args.get(4))
                            );

                    IExpr.IFcnExpr right = F.fcn(F.symbol("store"),
                            convertExpr(tree.args.get(1)),
                            convertExpr(tree.args.get(2)),
                            newarray
                            );
                    result = F.fcn(eqSym, convertExpr(tree.args.get(0)),right);
                } else {
                    // [0] = store([1],[2], select([0],[2]))
                    IExpr arg0 = convertExpr(tree.args.get(0));
                    IExpr arg2 = convertExpr(tree.args.get(2));
                    IExpr.IFcnExpr sel = F.fcn(selectSym,
                            arg0,
                            arg2
                            );

                    IExpr.IFcnExpr newarray = F.fcn(F.symbol("store"),
                            convertExpr(tree.args.get(1)),
                            arg2,
                            sel
                            );
                    result = F.fcn(eqSym, arg0,newarray);                    
                }
                return;
            }
        } else if (m instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)m;
            String name = fa.name.toString();
            String newname = null;
            if (name.equals(BasicBlocker2.SELECTString)) {
                newname = "select";
            } else {
                newname = name;
                //if (name.equals("equal")) newname = "equals";
                addFcn(newname,tree);
            }
            List<IExpr> newargs = new LinkedList<IExpr>();
            if (!Utils.instance(context).isJMLStatic(fa.sym)) newargs.add(convertExpr(fa.selected));
            for (JCExpression arg: tree.args) {
                newargs.add(convertExpr(arg));
            }
            result = F.fcn(F.symbol(newname),newargs);
            
        }
    }
    
    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        if (that.token == JmlToken.BSTYPELC) {
            Type t = that.args.get(0).type;
            addType(t);
            result = that.javaType ? javaTypeSymbol(t) : jmlTypeSymbol(t);
            return;
        }
        List<IExpr> newargs = new LinkedList<IExpr>();
        for (JCExpression e: that.args) {
            scan(e);
            newargs.add(result);
        }
        if (that.token == JmlToken.SUBTYPE_OF) {
            result = F.fcn(F.symbol("jmlSubType"), newargs);
        } else if (that.token == JmlToken.BSTYPEOF) {
            ISymbol s = that.javaType ? F.symbol("javaTypeOf") : F.symbol("jmlTypeOf");
            result = F.fcn(s, newargs);
        } else if (that.token == JmlToken.BSNONNULLELEMENTS) {
            result = F.fcn(F.symbol("nonnullelements"), newargs);
        } else if (that.meth != null) result = F.fcn(F.symbol(that.meth.toString()),newargs);
        else result = newargs.get(0); // FIXME - this is needed for \old and \pre but a better solution should be found (cf. testLabeled)
    }

    @Override
    public void visitNewClass(JCNewClass tree) {
        shouldNotBeCalled(tree);
        super.visitNewClass(tree);
    }

    @Override
    public void visitNewArray(JCNewArray tree) {
        shouldNotBeCalled(tree);
        super.visitNewArray(tree);
    }

    @Override
    public void visitAssign(JCAssign tree) {
        shouldNotBeCalled(tree);
        super.visitAssign(tree);
    }

    @Override
    public void visitAssignop(JCAssignOp tree) {
        shouldNotBeCalled(tree);
        super.visitAssignop(tree);
    }

    @Override
    public void visitUnary(JCUnary tree) {
        int op = tree.getTag();
        scan(tree.arg);
        IExpr arg = result;
        LinkedList<IExpr> args = new LinkedList<IExpr>();
        args.add(arg);
        switch (op) {
            case JCTree.NOT:
                result = F.fcn(F.symbol("not"), args);
                break;
            case JCTree.NEG:
                result = F.fcn(F.symbol("-"), args);
                break;
            default:
                log.error("jml.internal","Don't know how to translate expression to SMTLIB: " + JmlPretty.write(tree));
                throw new RuntimeException();
        }
    }
    
    @Override public void visitParens(JCParens that) {
        // Since SMT-LIB consists of S-expressions, we do not need to 
        // add additional parentheses for resolving precedence
        super.visitParens(that);
    }


    @Override
    public void visitBinary(JCBinary tree) {
        int op = tree.getTag();
        scan(tree.lhs);
        IExpr lhs = result;
        scan(tree.rhs);
        IExpr rhs = result;
        LinkedList<IExpr> args = new LinkedList<IExpr>();
        args.add(lhs);
        args.add(rhs);
        switch (op) {
            case JCTree.EQ:
                result = F.fcn(eqSym, args);
                break;
            case JCTree.NE:
                result = F.fcn(F.symbol("distinct"), args);
                break;
            case JCTree.AND:
                result = F.fcn(F.symbol("and"), args);
                break;
            case JCTree.OR:
                result = F.fcn(F.symbol("or"), args);
                break;
            case JCTree.LT:
                result = F.fcn(F.symbol("<"), args);
                break;
            case JCTree.LE:
                result = F.fcn(F.symbol("<="), args);
                break;
            case JCTree.GT:
                result = F.fcn(F.symbol(">"), args);
                break;
            case JCTree.GE:
                result = F.fcn(F.symbol(">="), args);
                break;
            case JCTree.PLUS:
                if (tree.lhs.type.tag == TypeTags.CLASS) {
                    result = F.fcn(F.symbol("stringConcat"), args);
                } else {
                    result = F.fcn(F.symbol("+"), args);
                }
                break;
            case JCTree.MINUS:
                result = F.fcn(F.symbol("-"), args);
                break;
            case JCTree.MUL:
                result = F.fcn(F.symbol("*"), args);
                break;
            case JCTree.DIV:
                // FIXME - what kinds of primitive types should be expected
                if (tree.type.tag == TypeTags.FLOAT)
                    result = F.fcn(F.symbol("/"), args);
                else if (tree.type.tag == TypeTags.DOUBLE)
                    result = F.fcn(F.symbol("/"), args);
                else
                    result = F.fcn(F.symbol("div"), args);
                break;
            case JCTree.MOD:
                result = F.fcn(F.symbol("mod"), args);
                break;
                // FIXME - implement these
//            case JCTree.SL:
//                result = F.fcn(F.symbol("or"), args);
//                break;
//            case JCTree.SR:
//                result = F.fcn(F.symbol("or"), args);
//                break;
//            case JCTree.USR:
//                result = F.fcn(F.symbol("or"), args);
//                break;
//            case JCTree.BITAND:
//                result = F.fcn(F.symbol("or"), args);
//                break;
//            case JCTree.BITOR:
//                result = F.fcn(F.symbol("or"), args);
//                break;
//            case JCTree.BITXOR:
//                result = F.fcn(F.symbol("or"), args);
//                break;
            default:
                log.error("jml.internal","Don't know how to translate expression to SMTLIB: " + JmlPretty.write(tree));
                throw new RuntimeException();
        }
    }

    @Override
    public void visitTypeCast(JCTypeCast tree) {
        // For reference types, ignore the cast; we presume any check about the
        // validity of the cast is already performed.
        result = convertExpr(tree.expr);
    }

    @Override
    public void visitTypeTest(JCInstanceOf tree) {
//        notImpl(tree); // TODO
//        super.visitTypeTest(tree);
        
        addType((ClassType)tree.clazz.type);
        IExpr e = convertExpr(tree.expr);
        // instanceof is always false if the argument is null
        // and javaTypeOf is not defined for null arguments
        IExpr r1 = F.fcn(F.symbol("distinct"), e, nullSym);
        IExpr r2 = F.fcn(F.symbol("javaSubType"),
                F.fcn(F.symbol("javaTypeOf"), e),
                javaTypeSymbol(tree.clazz.type));
        result = F.fcn(F.symbol("and"), r1, r2);
    }

    @Override
    public void visitIndexed(JCArrayAccess tree) {
        if (tree instanceof JmlBBArrayAccess) {
            JmlBBArrayAccess aa = (JmlBBArrayAccess)tree;
            // select(select(arraysId,a).i)
            IExpr.IFcnExpr sel = F.fcn(selectSym,
                    convertExpr(aa.arraysId),
                    convertExpr(aa.indexed)
                    );
            sel = F.fcn(selectSym,
                    sel,
                    convertExpr(aa.index)
                    );
            result = sel;
            return;
        }

        // FIXME: This should never be called!
        scan(tree.indexed);
        IExpr array = result;
        scan(tree.index);
        IExpr index = result;
        result = F.fcn(selectSym,result,array);
        result = F.fcn(selectSym,result,index);

//        if (tree.type.tag == syms.intType.tag) {
//            result = F.fcn(F.symbol("asIntArray"), array);
//            result = F.fcn(selectSym,result,index);
//        } else if (!tree.type.isPrimitive()) {
//            result = F.fcn(F.symbol("asREFArray"), array);
//            result = F.fcn(selectSym,result,index);
//        } else {
//            notImpl(tree);
//            result = null;
//        }
    }
    
    @Override 
    public void visitConditional(JCConditional that) { 
        result = F.fcn(F.symbol("ite"), convertExpr(that.cond), convertExpr(that.truepart), convertExpr(that.falsepart));
    }


    @Override
    public void visitSelect(JCFieldAccess tree) {
        // FIXME - review
        // o.f becomes f[o] where f has sort (Array REF type)
        if (tree.selected != null) doFieldAccess(tree,tree.selected,tree.name,tree.sym);
    }
    
    java.util.Set<Name> defined = new java.util.HashSet<Name>();
    
    // FIXME - review
    protected void doFieldAccess(JCFieldAccess tree, JCExpression object, Name name, Symbol field) {
        if (field != syms.lengthVar) {
            if (defined.add(name)) {
                ISort arrsort = F.createSortExpression(arraySym,refSort,convertSort(field.type));
                ICommand c = new C_declare_fun(F.symbol(name.toString()),
                        emptyList,arrsort);
                commands.add(c);
            }
            if (Utils.instance(context).isJMLStatic(field)) { // FIXME - isJMLStatic?
                result = F.symbol(name.toString());
            } else {
                result = F.fcn(selectSym,F.symbol(name.toString()),
                        object == null ? thisSym: convertExpr(object));
            }
        } else {
            //Type t = ((ArrayType)object.type).getComponentType();
            IExpr sel = convertExpr(object);
            result = F.fcn(selectSym,F.symbol(length),sel);
            return;
        }
        
    }

    @Override
    public void visitIdent(JCIdent tree) {
//        if (tree.sym != null && tree.sym.owner instanceof ClassSymbol && tree.sym.name != names._this && !Utils.instance(context).isJMLStatic(tree.sym)) {
//            // a select from this
//            // This is defensive programming - all implicit uses of this are
//            // supposed to have been made explicit
        // NOPE - adds extra field accesses
//            doFieldAccess(null,tree.name,tree.sym);
//        } else {
        String n = tree.name.toString();
        if (n.equals("length")) {
            result = F.symbol(length);
        } else {
            result = F.symbol(n);
        }
//        } 
    }
    
    @Override
    public void visitLiteral(JCLiteral tree) {
        if (tree.typetag == TypeTags.BOOLEAN) {
           result = F.symbol(((Boolean)tree.getValue()) ?"true":"false"); 
        } else if (tree.typetag == TypeTags.INT || tree.typetag == TypeTags.LONG || tree.typetag == TypeTags.SHORT || tree.typetag == TypeTags.BYTE) {
            long k = Long.parseLong(tree.value.toString());
            result = k >= 0 ? F.numeral(k) : F.fcn(F.symbol("-"), F.numeral(-k));
        } else if (tree.typetag == TypeTags.CHAR) {
            long k = Long.parseLong(tree.value.toString());
            result = k >= 0 ? F.numeral(k) : F.fcn(F.symbol("-"), F.numeral(-k));
        } else if (tree.typetag == TypeTags.BOT) {
            result = nullSym;
        } else if (tree.typetag == TypeTags.CLASS) {
            // FIXME - every literal is different and we don't remember the value
            ISymbol sym = F.symbol("STRINGLIT"+(++stringCount)); 
            ICommand c = new C_declare_fun(sym,emptyList, refSort);
            commands.add(c);
            result = sym;
        } else if (tree.typetag == TypeTags.FLOAT || tree.typetag == TypeTags.DOUBLE) {
            // FIXME - every literal is different and we don't remember the value
            ISymbol sym = F.symbol("REALLIT"+(++doubleCount)); 
            ICommand c = new C_declare_fun(sym,emptyList, 
                    F.createSortExpression(F.symbol("Real")));
            commands.add(c);
            result = sym;
        } else {
            notImpl(tree);
            super.visitLiteral(tree);
        }
    }

    @Override public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) { notImpl(that); } // FIXME - maybe
    @Override public void visitJmlSetComprehension(JmlSetComprehension that) { notImpl(that); }
    @Override public void visitJmlSingleton(JmlSingleton that)               { notImpl(that); }

    @Override public void visitLetExpr(LetExpr that) { 
        
        Iterator<JCVariableDecl> iter = that.defs.iterator();
        result = doLet(iter,(JCExpression)that.expr);
    }
    
    // We need to create nested let expressions because the SMT let expression
    // does parallel bindings of initializers to variables, while Java does
    // sequential bindings.
    private IExpr doLet(Iterator<JCVariableDecl> iter, JCExpression expr) {
        if (iter.hasNext()) {
            JCVariableDecl decl = iter.next();
            IExpr.ISymbol sym = F.symbol(decl.name.toString());
            IExpr e = convertExpr(decl.init);
            List<IBinding> bindings = new LinkedList<IBinding>();
            bindings.add(F.binding(sym,e));
            return F.let(bindings, doLet(iter,expr));
        } else {
            return convertExpr(expr);
        }
    }

    @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        boolean prev = inQuant;
        try {
            inQuant = true;
            List<IDeclaration> params = new LinkedList<IDeclaration>();
            for (JCVariableDecl decl: that.decls) {
                IExpr.ISymbol sym = F.symbol(decl.name.toString());
                ISort sort = convertSort(decl.type);
                params.add(F.declaration(sym, sort));
            }
            scan(that.range);
            IExpr range = result;
            scan(that.value);
            IExpr value = result;
            if (that.op == JmlToken.BSFORALL) {
                if (range != null) value = F.fcn(impliesSym,range,value);
                result = F.forall(params,value);
            } else if (that.op == JmlToken.BSEXISTS) {
                if (range != null) value = F.fcn(impliesSym,range,value);
                result = F.forall(params,value);
            } else {
                notImpl(that);
            }
            if (!prev) {
//              // Because SMTLIB does not allow getValue to have arguments containing
//              // quantifiers, we do the following trick. We could use named 
//              // SMTLIB expressions, but I'm not sure how widespread support
//              // for that feature is.
                ISymbol tmp = F.symbol("_JMLSMT_tmp_" + (++uniqueCount));
                ICommand c = new C_declare_fun(tmp,emptyList,boolSort);
                commands.add(c);
                c = new C_assert(F.fcn(eqSym,  tmp, result));
                commands.add(c);
                //ICommand c = new C_define_fun(tmp,new LinkedList<IDeclaration>(),boolSort,result);
                //commands.add(c);
                result = tmp;
            }
        } finally {
            inQuant = prev;
        }
    }
//
//    public void visitJmlSetComprehension(JmlSetComprehension that) {
//        scan(that.newtype);
//        scan(that.variable);
//        scan(that.predicate);
//    }
//
//    public void visitJmlLblExpression(JmlLblExpression that) {
//        scan(that.expression);
//    }
//


    @Override
    public void visitTypeIdent(JCPrimitiveTypeTree tree) {
        notImpl(tree);
        super.visitTypeIdent(tree);
    }

    @Override
    public void visitTypeArray(JCArrayTypeTree tree) {
        notImpl(tree);
        super.visitTypeArray(tree);
    }

    @Override
    public void visitTypeApply(JCTypeApply tree) {
        notImpl(tree);
        super.visitTypeApply(tree);
    }

    @Override
    public void visitTypeUnion(JCTypeUnion tree) {
        notImpl(tree);
        super.visitTypeUnion(tree);
    }

    @Override
    public void visitTypeParameter(JCTypeParameter tree) {
        notImpl(tree);
        super.visitTypeParameter(tree);
    }

    @Override
    public void visitWildcard(JCWildcard tree) {
        notImpl(tree);
        super.visitWildcard(tree);
    }

    @Override
    public void visitTypeBoundKind(TypeBoundKind tree) {
        notImpl(tree);
        super.visitTypeBoundKind(tree);
    }
    
    // These should all be translated away prior to calling the basic blocker,
    // or should never be called in the first place, because they are not
    // expressions
    // FIXME - what about calls of anonymous classes
    @Override public void visitTopLevel(JCCompilationUnit that)    { shouldNotBeCalled(that); }
    @Override public void visitImport(JCImport that)               { shouldNotBeCalled(that); }
    @Override public void visitJmlCompilationUnit(JmlCompilationUnit that)   { shouldNotBeCalled(that); }
    @Override public void visitJmlImport(JmlImport that)                     { shouldNotBeCalled(that); }
    @Override public void visitMethodDef(JCMethodDecl that)        { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodDecl(JmlMethodDecl that)  { shouldNotBeCalled(that); }
    @Override public void visitJmlBinary(JmlBinary that)           { shouldNotBeCalled(that); }
    @Override public void visitJmlChoose(JmlChoose that)           { shouldNotBeCalled(that); }
    @Override public void visitJmlClassDecl(JmlClassDecl that)           { shouldNotBeCalled(that); }
    @Override public void visitJmlConstraintMethodSig(JmlConstraintMethodSig that) { shouldNotBeCalled(that); }
    @Override public void visitJmlDoWhileLoop(JmlDoWhileLoop that)  { shouldNotBeCalled(that); }
    @Override public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) { shouldNotBeCalled(that); }
    @Override public void visitJmlForLoop(JmlForLoop that) { shouldNotBeCalled(that); }
    @Override public void visitJmlGroupName(JmlGroupName that) { shouldNotBeCalled(that); }
    @Override public void visitJmlLblExpression(JmlLblExpression that) { shouldNotBeCalled(that); }    
    @Override public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodSpecs(JmlMethodSpecs that)           { shouldNotBeCalled(that); }
    @Override public void visitJmlModelProgramStatement(JmlModelProgramStatement that) { shouldNotBeCalled(that); }
    @Override public void visitJmlSpecificationCase(JmlSpecificationCase that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementDecls(JmlStatementDecls that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementExpr(JmlStatementExpr that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementLoop(JmlStatementLoop that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementSpec(JmlStatementSpec that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseIn(JmlTypeClauseIn that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) { shouldNotBeCalled(that); }
    @Override public void visitJmlVariableDecl(JmlVariableDecl that) { shouldNotBeCalled(that); }
    @Override public void visitJmlWhileLoop(JmlWhileLoop that) { shouldNotBeCalled(that); }

    @Override public void visitClassDef(JCClassDecl that) { shouldNotBeCalled(that); }
    @Override public void visitVarDef(JCVariableDecl that)  { shouldNotBeCalled(that); }
    @Override public void visitSkip(JCSkip that) { shouldNotBeCalled(that); }
    @Override public void visitBlock(JCBlock that) { shouldNotBeCalled(that); }
    @Override public void visitDoLoop(JCDoWhileLoop that) { shouldNotBeCalled(that); }
    @Override public void visitWhileLoop(JCWhileLoop that) { shouldNotBeCalled(that); }
    @Override public void visitForLoop(JCForLoop that) { shouldNotBeCalled(that); }
    @Override public void visitForeachLoop(JCEnhancedForLoop that) { shouldNotBeCalled(that); }
    @Override public void visitLabelled(JCLabeledStatement that) { shouldNotBeCalled(that); }
    @Override public void visitSwitch(JCSwitch that) { shouldNotBeCalled(that); }
    @Override public void visitCase(JCCase that) { shouldNotBeCalled(that); }
    @Override public void visitSynchronized(JCSynchronized that) { shouldNotBeCalled(that); }
    @Override public void visitTry(JCTry that) { shouldNotBeCalled(that); }
    @Override public void visitCatch(JCCatch that) { shouldNotBeCalled(that); }
    @Override public void visitIf(JCIf that) { shouldNotBeCalled(that); }
    @Override public void visitExec(JCExpressionStatement that) { shouldNotBeCalled(that); }
    @Override public void visitBreak(JCBreak that) { shouldNotBeCalled(that); }
    @Override public void visitContinue(JCContinue that) { shouldNotBeCalled(that); }
    @Override public void visitReturn(JCReturn that) { shouldNotBeCalled(that); }
    @Override public void visitThrow(JCThrow that) { shouldNotBeCalled(that); }
    @Override public void visitAssert(JCAssert that) { shouldNotBeCalled(that); }
 
    // Some of these could be notImpl
    @Override public void visitAnnotation(JCAnnotation that) { shouldNotBeCalled(that); }
    @Override public void visitModifiers(JCModifiers that) { shouldNotBeCalled(that); }
    @Override public void visitErroneous(JCErroneous that) { shouldNotBeCalled(that); }

}

class QuantCheck extends JmlTreeScanner {
    
    boolean result;
    
    public boolean check(JCTree that) {
        result = false;
        scan(that);
        return result;
    }
        
    @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        result = true;
    }
}
