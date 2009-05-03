package com.sun.tools.javac.comp;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.IJmlVisitor;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.tree.TreeTranslator;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

public class JmlRac extends TreeTranslator implements IJmlVisitor {

    Context context;
    
    Env<AttrContext> env;
    Env<AttrContext> attrEnv;
    Resolve rs;
    Symtab syms;
    Names names;
    JmlTree.Maker make;
    JmlSpecs specs;
    DiagnosticPosition make_pos;
    ClassSymbol assertionFailureClass;
    ClassSymbol utilsClass;
    JCIdent utilsClassIdent;
    JmlAttr attr;
    Name resultName;
    Name exceptionName;
    Name exceptionCatchName;
    Log log;
    
    JCLiteral trueLit;
    JCLiteral falseLit;
    JCLiteral zero;
    JCLiteral nulllit;
    JCLiteral maxIntLit;
    
    static final public String invariantMethodString = "_JML$$$checkInvariant";
    Name invariantMethodName;
    static final public String staticinvariantMethodString = "_JML$$$checkStaticInvariant";
    Name staticinvariantMethodName;
    
    Type integerType;
    
    public JmlRac(Context context, Env<AttrContext> env) {
        this.context = context;
        this.env = env;
        this.attrEnv = env;
        this.syms = Symtab.instance(context);
        this.rs = Resolve.instance(context);
        this.names = Names.instance(context);
        this.make = (JmlTree.Maker)JmlTree.Maker.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.attr = (JmlAttr)JmlAttr.instance(context);
        this.log = Log.instance(context);
        
        ClassReader reader = ClassReader.instance(context);

        assertionFailureClass = reader.enterClass(names.fromString("org.jmlspecs.utils.Utils$JmlAssertionFailure"));
        utilsClass = reader.enterClass(names.fromString("org.jmlspecs.utils.Utils"));
        utilsClassIdent = make.Ident(names.fromString("org.jmlspecs.utils.Utils"));
        utilsClassIdent.type = utilsClass.type;
        utilsClassIdent.sym = utilsClassIdent.type.tsym;
        
        trueLit = attr.trueLit;
        falseLit = makeLit(syms.booleanType,0);
        zero = makeLit(syms.intType,0);
        nulllit = makeLit(syms.botType, null);
        maxIntLit = makeLit(syms.intType,Integer.MAX_VALUE);

        this.resultName = Names.instance(context).fromString("_JML$$$result");
        this.exceptionName = Names.instance(context).fromString("_JML$$$exception");
        this.exceptionCatchName = Names.instance(context).fromString("_JML$$$exceptionCatch");

        integerType = reader.enterClass(names.fromString("java.lang.Integer")).type;
        
        invariantMethodName = names.fromString(invariantMethodString);
        staticinvariantMethodName = names.fromString(staticinvariantMethodString);
    }
    
    /** Make an attributed class instance creation expression.
     *  @param ctype    The class type.
     *  @param args     The constructor arguments.
     */
    JCNewClass makeNewClass(Type ctype, List<JCExpression> args) {
        JCNewClass tree = make.NewClass(null,
            null, make.QualIdent(ctype.tsym), args, null);
        tree.constructor = rs.resolveConstructor(
            make_pos, attrEnv, ctype, TreeInfo.types(args), null, false, false);
        tree.type = ctype;
        return tree;
    }

    public void visitJmlMethodInvocation(JmlMethodInvocation tree) {
        JmlToken t = tree.token;
        JCExpression arg;
        switch (t) {
            case BSOLD:
            case BSPRE:
                arg = translate(tree.args.get(0));
                int n = methodInfo.olds.size();
                String s = "_JML$$$old_" + n;
                Name nm = names.fromString(s);
                JCVariableDecl v = makeVarDef(arg.type,nm,methodInfo.owner,arg);
                methodInfo.olds.append(v);
                JCIdent r = make.Ident(nm);
                r.sym = v.sym;
                r.type = v.sym.type;
                result = r;
                break;

            case BSTYPEOF:
                translateTypeOf(tree);
                break;

            case BSNONNULLELEMENTS :
                translateNonnullelements(tree);
                break;

            case BSTYPELC:
                translateTypelc(tree);
                break;
            
            case BSELEMTYPE:
                translateElemtype(tree);
                break;
                
            case BSMAX:
            case BSNOTMODIFIED:
            case BSNOTASSIGNED :
            case BSONLYASSIGNED :
            case BSONLYACCESSED :
            case BSONLYCAPTURED :
            case BSISINITIALIZED :
            case BSFRESH:
            case BSREACH:
            case BSINVARIANTFOR :
            case BSDURATION :
            case BSWORKINGSPACE :

            case BSSPACE:
            case BSNOWARN:
            case BSNOWARNOP:
            case BSWARN:
            case BSWARNOP:
            case BSBIGINT_MATH:
            case BSSAFEMATH:
            case BSJAVAMATH:
            case BSONLYCALLED:
                Log.instance(context).error(tree.pos, "jml.unimplemented.construct",t.internedName(),"JmlRac.visitApply");
                // FIXME - recovery possible?
                break;

            default:
                Log.instance(context).error(tree.pos, "jml.unknown.construct",t.internedName(),"JmlRac.visitApply");
            // FIXME - recovery possible?
                break;
        }
        return;
    }

    public void translateNonnullelements(JCMethodInvocation tree) {
        JCExpression r = trueLit;
        for (int i = 0; i<tree.args.size(); i++) {
            JCExpression arg = translate(tree.args.get(i));
            JCExpression e = methodCallUtilsExpression("nonnullElementCheck",arg);
            r = makeBinary(JCTree.AND,r,e);
        }
        result = r;
    }

    public void translateTypelc(JCMethodInvocation tree) {
        // Argument is a type, not an expression, so we
        // replace it with a type literal
        JCExpression arg = tree.args.get(0);
        JCTree.JCFieldAccess f = make.Select(arg,names._class);
        f.type = syms.classType;
        f.sym = f.type.tsym;
        result = translate(f);
    }
    
    // FIXME - what about generic types
    // FIXME - what about arrays of arrays
    public void translateTypeOf(JCMethodInvocation tree) {
        JCExpression arg = tree.args.get(0);
        int tag = arg.type.tag;
        switch (tag) {
            case TypeTags.ARRAY:
            case TypeTags.CLASS:
                result = methodCallgetClass(translate(arg));
                break;
            case TypeTags.BOOLEAN:
                result = makePrimitiveClassLiteralExpression("java.lang.Boolean");
                break;
            case TypeTags.INT:
                result = makePrimitiveClassLiteralExpression("java.lang.Integer");
                break;
            case TypeTags.LONG:
                result = makePrimitiveClassLiteralExpression("java.lang.Long");
                break;
            case TypeTags.SHORT:
                result = makePrimitiveClassLiteralExpression("java.lang.Short");
                break;
            case TypeTags.BYTE:
                result = makePrimitiveClassLiteralExpression("java.lang.Byte");
                break;
            case TypeTags.FLOAT:
                result = makePrimitiveClassLiteralExpression("java.lang.Float");
                break;
            case TypeTags.DOUBLE:
                result = makePrimitiveClassLiteralExpression("java.lang.Double");
                break;
            case TypeTags.CHAR:
                result = makePrimitiveClassLiteralExpression("java.lang.Character");
                break;
            default:
                log.error(arg.pos,"jml.unknown.construct","typeof for " + arg.type,"JmlRac.translateTypeOf");
                // We give it an arbitrary value // FIXME - or do we call it undefined
                result = makePrimitiveClassLiteralExpression("java.lang.Boolean");
                break;
        }
    }
    
    public void translateElemtype(JCMethodInvocation tree) {
        Name n = names.fromString("getComponentType");
        Scope.Entry e = syms.classType.tsym.members().lookup(n);
        Symbol ms = e.sym;
        JCFieldAccess m = make.Select(translate(tree.args.head),n);
        m.sym = ms;
        m.type = m.sym.type;

        JCExpression c = make.Apply(null,m,List.<JCExpression>nil());
        c.setType(syms.classType);
        result = c;
    }
    
    public static class ClassInfo {
        public ClassInfo(JCClassDecl d) { this.decl = d; }
        JCClassDecl decl;
        JmlSpecs.TypeSpecs typeSpecs = null;
        JCMethodDecl invariantDecl = null;
        JCMethodDecl staticinvariantDecl = null;
        ListBuffer<JmlTypeClauseConstraint> constraints = new ListBuffer<JmlTypeClauseConstraint>();
        ListBuffer<JmlTypeClauseExpr> initiallys = new ListBuffer<JmlTypeClauseExpr>();
    }

    public ClassInfo classInfo = null;

    @Override
    public void visitClassDef(JCClassDecl tree) {
//        if (tree.sym != null && 
//                ((JmlClassDecl)tree).sourcefile.getKind() != JavaFileObject.Kind.SOURCE) {
//            return;
//        } // Model classes can have a sourcefile that is in an OTHER file
        result = tree;
        if (tree.sym == null) return;
        if (tree.sym.className().startsWith("org.jmlspecs")) return;  // FIXME - don't instrument runtime files (can get infinite loops)
        if (Utils.isInstrumented(tree.mods.flags)) {
            // The file is already instrumented.
            // This can happen if desugarLater is called on a file, so that it
            // is put back on the todo list.  If we are in the mode of BY_FILE
            // in JavaCompiler, that means that it is run through the 
            // attribute/flow/desugar sequence again.  Thus we need to check
            // for and skip this case.
            return;
        }
        Utils.setInstrumented(tree.mods);
        
        ClassInfo prevClassInfo = classInfo;
        classInfo = new ClassInfo(tree);
        classInfo.typeSpecs = specs.get(tree.sym);
        JmlSpecs.TypeSpecs typeSpecs = classInfo.typeSpecs;
        if (typeSpecs == null) {
            System.out.println("UNEXPECTEDLY NULL TYPESPECS");
            return;
        }
        
//        JCMethodDecl invariantDecl = makeMethodDef(invariantMethodName,List.<JCStatement>nil(),tree.sym);
//        classInfo.invariantDecl = invariantDecl;
//        JCMethodDecl staticinvariantDecl = makeStaticMethodDef(staticinvariantMethodName,List.<JCStatement>nil(),tree.sym);
//        classInfo.staticinvariantDecl = staticinvariantDecl;
        JCMethodDecl invariantDecl = classInfo.invariantDecl = classInfo.typeSpecs.checkInvariantDecl;
        JCMethodDecl staticinvariantDecl = classInfo.staticinvariantDecl = classInfo.typeSpecs.checkStaticInvariantDecl;
        
        // Remove any non-Java declarations from the Java AST before we do translation
        // After the superclass translation, we will add back in all the JML stuff.
        ListBuffer<JCTree> newlist = new ListBuffer<JCTree>();
        for (JCTree t: tree.defs) {
            if (t == null || t.getTag() >= JmlTree.JMLFUNCTION) {
                // skip it
            } else {
                newlist.append(t);
            }
        }

        // Divide up the various type specification clauses into the various types
        ListBuffer<JmlTypeClauseExpr> invariants = new ListBuffer<JmlTypeClauseExpr>();
        ListBuffer<JmlTypeClauseRepresents> represents = new ListBuffer<JmlTypeClauseRepresents>();
        ListBuffer<JCVariableDecl> modelFields = new ListBuffer<JCVariableDecl>();
        for (JmlTypeClause c: typeSpecs.clauses) {
            if (c instanceof JmlTypeClauseDecl) {
                JCTree t = ((JmlTypeClauseDecl)c).decl;
                if (t instanceof JCVariableDecl && attr.isModel(((JCVariableDecl)t).mods)) {
                    // model field - find represents or make into abstract method
                    modelFields.append((JCVariableDecl)t);
                } else {
                    // ghost fields, model methods, model classes are used as is
                    //t = translate(t);
                    newlist.append(t);
                }
            } else {
                JmlToken token = c.token;
                if (token == JmlToken.INVARIANT) {
                    invariants.append((JmlTypeClauseExpr)c);
                } else if (token == JmlToken.REPRESENTS) {
                    JmlTypeClauseRepresents r = (JmlTypeClauseRepresents)c;
                    if (r.suchThat) log.warning(r.pos,"jml.not.implemented.rac","relational represents clauses (\\such_that)");
                    else represents.append(r);
                } else if (token == JmlToken.CONSTRAINT) {
                    classInfo.constraints.append((JmlTypeClauseConstraint)c);
                } else if (token == JmlToken.INITIALLY) {
                    classInfo.initiallys.append((JmlTypeClauseExpr)c);
                } else {
                    // We ignore axioms
                }
            }
        }
        
        tree.defs = newlist.toList();
        newlist = new ListBuffer<JCTree>();
        newlist.appendList(tree.defs);

        for (JmlTypeClauseRepresents r : represents) {
            JCExpression e = r.ident;
            Symbol sym = null;
            if (e instanceof JCIdent) sym = ((JCIdent)e).sym;
            else if (e instanceof JCFieldAccess) sym = ((JCFieldAccess)e).sym;
            else {
                // FIXME -error
            }
            if (sym != null) {
                Name name = names.fromString("_JML$model$" + sym.name);
                JmlMethodDecl mdecl = null;
                for (JmlTypeClauseDecl m: typeSpecs.modelFieldMethods) {
                    mdecl = (JmlMethodDecl)m.decl;
                    if (! mdecl.name.equals(name)) continue;
                    JCReturn st = make.Return(translate(r.expression));
                    if (mdecl.body.stats.isEmpty()) {
                        mdecl.body.stats = List.<JCStatement>of(st);
                    } else {
                        log.error(r.pos,"jml.duplicate.represents");
                    }
                    break;
                }
                if (mdecl == null) {
                    // We can get here if there is no model field at all, but then
                    // there would have been an error on resolving the target of
                    // the represents clause.  The usual route to this code is
                    // when a subclass has a represents clause for a super class's
                    // model field.
                    
                    long flags = Flags.PUBLIC | Flags.SYNTHETIC;
                    flags |= (r.modifiers.flags & Flags.STATIC);
                    JCModifiers mods = make.Modifiers(flags);
                    JCMethodDecl msdecl = makeMethodDefNoArg(mods,name,r.ident.type,tree.sym);
                    JCReturn st = make.Return(translate(r.expression));
                    msdecl.body.stats = List.<JCStatement>of(st);
                    newlist.append(msdecl);
                    JmlTypeClauseDecl tcd = make.JmlTypeClauseDecl(msdecl);
                    tcd.modifiers = msdecl.mods;
                    typeSpecs.modelFieldMethods.append(tcd);
                }
            }
        }
        for (JmlTypeClauseDecl m: typeSpecs.modelFieldMethods) {
            JmlMethodDecl mdecl = (JmlMethodDecl)m.decl;
            if (mdecl.body.stats.isEmpty()) {
                //System.out.println("NO IMPLEMENTATION " + mdecl.name);
                String position = position(m.source,m.pos);
                String s = mdecl.name.toString();
                int p = s.lastIndexOf('$');
                JCStatement st = assertFailure(position + "model field is not implemented: " + s.substring(p+1));
                JCStatement stt = make.Return(makeZeroEquivalentLit(mdecl.getReturnType().type));
                mdecl.body.stats = List.<JCStatement>of(st,stt);
            }
        }
        

        super.visitClassDef(tree);
        if (env.tree == tree) env.tree = result;
        //if (typeSpecs == null) return; - would get a NPE before this
        if (tree.name.toString().equals("org.jmlspecs.utils.Utils")) return;
        
        // All ghost fields, model methods, model fields should have
        // been attributed.  So we append them to the class definitions.
        

        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> staticstats = new ListBuffer<JCStatement>();
        for (JmlTypeClause inv: invariants) {
            JCExpression e = translate(((JmlTypeClauseExpr)inv).expression);
            String position = position(inv.source(),inv.pos);
            if ((inv.modifiers.flags & Flags.STATIC) != 0) {
                JCStatement s = undefinedCheck(staticinvariantDecl.sym,
                        position+"static invariant",
                        make.If(makeUnary(JCTree.NOT,e),assertFailure(position+"static invariant is false"),null));
                staticstats.append(s);
            } else {
                JCStatement s = undefinedCheck(invariantDecl.sym,
                        position+"invariant",
                        make.If(makeUnary(JCTree.NOT,e),assertFailure(position+"invariant is false"),null));
                stats.append(s);
            }
        }

//        stats.append(findSuperMethod(tree.sym,names.fromString("_JML$$$checkInvariant")));

        //JCExpression exp = methodCallUtilsExpression("callSuperInvariantCheck",nulllit);
        //stats.append(make.Exec(methodCallUtilsExpression("callSuperInvariantCheck",makeThis(tree.sym))));
        invariantDecl.body = make.Block(0,stats.toList());
        staticinvariantDecl.body = make.Block(0,staticstats.toList());


        tree.defs = newlist.toList();
        result = tree;
        //System.out.println("REWRITTEN " + result);
        classInfo = prevClassInfo;
    }
    

    static public class MethodInfo {
        public MethodInfo(JCMethodDecl d) { 
            this.decl = d; 
            this.owner = d.sym; 
            this.source = ((JmlMethodDecl)d).sourcefile;
        }
        MethodSymbol owner;
        JCMethodDecl decl;
        JavaFileObject source;
        JCVariableDecl resultDecl;
        boolean resultUsed = false;
        JCExpression exceptionDecl;
        VarSymbol exceptionLocal;
        ListBuffer<JCVariableDecl> olds = new ListBuffer<JCVariableDecl>();
        JCStatement preCheck;
        JCStatement postCheck;
        int variableDefs = 0;
    }
    
    public void visitIdent(JCIdent tree) {
        if (tree.sym != null && tree.sym.kind == Kinds.VAR && attr.isModel(tree.sym)) {
            Name name = names.fromString("_JML$model$" + tree.name);
            ClassSymbol sym = classInfo.decl.sym;
            Scope.Entry e = sym.members().lookup(name);
            while (e.sym == null) {// FIXME - do we need to look in interfaces?
                Type t = sym.getSuperclass();
                if (t == null) break;
                sym = (ClassSymbol)t.tsym;
                e = sym.members().lookup(name);
            }
            if (e.sym instanceof MethodSymbol) {
                MethodSymbol ms = (MethodSymbol)e.sym;
                JCIdent m = make.Ident(name);
                m.sym = ms;
                m.type = m.sym.type;
                JCExpression c = make.Apply(null,m,List.<JCExpression>nil());
                c.setType(tree.type);
                result = c;
                return;
            } else {
                System.out.println("COULD NOT FIND METHOD FOR MODEL FIELD " + tree.sym);
                // FIXME - problem?
            }
        }
        if (methodInfo != null && tree.sym == methodInfo.exceptionLocal) {
            result = methodInfo.exceptionDecl;
            return;
        }
        super.visitIdent(tree);
    }
    
    public void visitSelect(JCFieldAccess tree) {
        if (tree.sym != null && tree.sym.kind == Kinds.VAR && attr.isModel(tree.sym)) {
            Name name = names.fromString("_JML$model$" + tree.name);
            ClassSymbol sym = classInfo.decl.sym;
            Scope.Entry e = sym.members().lookup(name);
            while (e.sym == null) {  // FIXME - do we need to look in interfaces?
                Type t = sym.getSuperclass();
                if (t == null) break;
                sym = (ClassSymbol)t.tsym;
                e = sym.members().lookup(name);
            }
            if (e.sym instanceof MethodSymbol) {
                MethodSymbol ms = (MethodSymbol)e.sym;
                JCFieldAccess m = make.Select(translate(tree.selected),name);
                m.sym = ms;
                m.type = m.sym.type;
                JCExpression c = make.Apply(null,m,List.<JCExpression>nil());
                c.setType(tree.type);
                result = c;
                return;
            } else {
                System.out.println("COULD NOT FIND METHOD FOR MODEL FIELD " + tree.sym);
                // FIXME - problem?
            }
        }
        super.visitSelect(tree);
    }
    
    MethodInfo methodInfo = null;
    
    public void visitMethodDef(JCMethodDecl tree) {
        JmlMethodSpecs s = null;
        JavaFileObject source = ((JmlMethodDecl)tree).sourcefile;
        boolean doRac = tree.sym != null && ((s=specs.getDenestedSpecs(tree.sym)) != null || classInfo.invariantDecl != null || classInfo.staticinvariantDecl != null);
        doRac = doRac && ((tree.mods.flags & (Flags.SYNTHETIC|Flags.ABSTRACT|Flags.NATIVE)) == 0);
        boolean isConstructor = tree.restype == null;
        if (classInfo.decl.sym == syms.objectType.tsym && isConstructor) doRac = false;
     // FIXME - why might tree.sym be null - aren't things attributed? but annotations have null symbol, constructors?
        MethodInfo prevMethodInfo = methodInfo;
        methodInfo = null;
        if (doRac) {
            methodInfo = new MethodInfo(tree);
            JCExpression resultType = tree.restype;
            if (!isConstructor && resultType.type.tag != TypeTags.VOID)
                methodInfo.resultDecl = makeVarDef(resultType,resultName,tree.sym);
            //methodInfo.exceptionDecl = makeVarDef(resultType,exceptionName,tree.sym);
        }
        
        super.visitMethodDef(tree);
        tree = (JCMethodDecl)result;
        
        if (doRac) {
            boolean isHelper = isHelper(tree.sym);
            if (s != null && !isConstructor) {
                JCExpression pre = s.cases.size() == 0 ? trueLit : falseLit;
                int num = 0;
                String position = null;
                for (JmlSpecificationCase spc: s.cases) {
                    JCExpression spre = trueLit;
                    for (JmlMethodClause c: spc.clauses) {
                        if (c.token == JmlToken.REQUIRES) {
                            num++;
                            position = position(spc.sourcefile,c.pos);
                            spre = makeBinary(JCTree.AND,spre,translate(((JmlMethodClauseExpr)c).expression));
                        }
                    }
                    pre = makeBinary(JCTree.OR,pre,spre);
                }
                if (num > 1) position = position(source,tree.pos);
                if (pre != trueLit)
                    methodInfo.preCheck = undefinedCheck(methodInfo.owner,
                        position+"precondition",
                        make.If(makeUnary(JCTree.NOT,pre),methodCallPre(position,pre),null));
            }
            
            Name n = names.fromString("_JML$$$signalsException");
            JCVariableDecl signalsEx = makeVarDef(make.QualIdent(syms.exceptionType.tsym),n,tree.sym);
            
            ListBuffer<JCStatement> postChecks = new ListBuffer<JCStatement>();
            if (s != null) {
                for (JmlSpecificationCase spc: s.cases) {
                    JCExpression spre = trueLit;
                    for (JmlMethodClause c: spc.clauses) {
                        if (c.token == JmlToken.REQUIRES) spre = makeBinary(JCTree.AND,spre,translate(((JmlMethodClauseExpr)c).expression));
                    }
                    for (JmlMethodClause c: spc.clauses) {
                        if (c.token == JmlToken.ENSURES) {
                            JCExpression post = makeBinary(JCTree.AND,spre,makeUnary(JCTree.NOT,translate(((JmlMethodClauseExpr)c).expression)));
                            String sp = position(spc.sourcefile,c.pos);
                            JCStatement st = undefinedCheck(methodInfo.owner,
                                    sp+"postcondition",
                                    make.If(post,methodCallPost(sp,post),null));
                            postChecks.append(st);
                        }
                    }
                }
            }
            
            ListBuffer<JCStatement> signalsChecks = new ListBuffer<JCStatement>();
            if (s != null) {
                for (JmlSpecificationCase spc: s.cases) {
                    JCExpression spre = trueLit;
                    for (JmlMethodClause c: spc.clauses) {
                        if (c.token == JmlToken.REQUIRES) spre = makeBinary(JCTree.AND,spre,translate(((JmlMethodClauseExpr)c).expression));
                    }
                    boolean hasSignalsOnly = false;
                    for (JmlMethodClause c: spc.clauses) {
                        if (c.token == JmlToken.SIGNALS) {
                            JmlMethodClauseSignals sig = (JmlMethodClauseSignals)c;
                            JCIdent id = makeIdent(signalsEx.sym);
                            JCExpression test = null; 
                            if (sig.vardef == null) {
                                // If there is no vardef, there cannot be uses of the local variable to replace
                                test = make.TypeTest(id,make.Type(syms.exceptionType));
                                test.type = syms.booleanType;
                                methodInfo.exceptionDecl = null;
                                methodInfo.exceptionLocal = null;
                            } else {
                                // During the walking of the tree, instances of exceptionLocal are replaced by the JCExpression exceptionDecl
                                test = make.TypeTest(id,sig.vardef.getType());
                                test.type = syms.booleanType;
                                methodInfo.exceptionDecl = make.TypeCast(sig.vardef.vartype,id).setType(sig.vardef.vartype.type);
                                methodInfo.exceptionLocal = sig.vardef.sym;
                            }
                            JCExpression post = makeBinary(JCTree.AND,spre,makeBinary(JCTree.AND,test,makeUnary(JCTree.NOT,translate(sig.expression))));
                            methodInfo.exceptionLocal = null;
                            String sp = position(spc.sourcefile,c.pos);
                            JCStatement st = undefinedCheck(methodInfo.owner,
                                    sp+"signals condition",
                                    make.If(post,assertFailure(sp+"signals condition is false"),null));
                            signalsChecks.append(st);
                        } else if (c.token == JmlToken.SIGNALS_ONLY) {
                            hasSignalsOnly = true;
                            JmlMethodClauseSigOnly sig = (JmlMethodClauseSigOnly)c;
                            JCExpression e = falseLit;
                            for (JCExpression t: sig.list) {
                                JCIdent id = makeIdent(signalsEx.sym);
                                JCInstanceOf test = make.TypeTest(id,translate(t));
                                test.type = syms.booleanType;
                                e = makeBinary(JCTree.OR,e,test);
                            }
                            methodInfo.exceptionLocal = null;
                            String sp = position(spc.sourcefile,c.pos);
                            JCStatement st = undefinedCheck(methodInfo.owner,
                                    sp+"signals_only condition",
                                    make.If(makeUnary(JCTree.NOT,e),assertFailure(sp+"signals_only condition is false"),null));
                            signalsChecks.append(st);
                        }
                    }
                    if (!hasSignalsOnly) {
                        JCExpression e = falseLit;
                        for (JCExpression t: methodInfo.decl.getThrows()) {
                            JCIdent id = makeIdent(signalsEx.sym);
                            JCInstanceOf test = make.TypeTest(id,translate(t)); // Caution: these get translated multiple times - is that oK?
                            test.type = syms.booleanType;
                            e = makeBinary(JCTree.OR,e,test);
                        }
                        methodInfo.exceptionLocal = null;
                        String sp = position(spc.sourcefile,methodInfo.decl.pos);
                        JCStatement st = undefinedCheck(methodInfo.owner,
                                sp+"default signals_only condition",
                                make.If(makeUnary(JCTree.NOT,e),assertFailure(sp+"unexpected exception"),null));
                        signalsChecks.append(st);
                    }
                }
            }
            
            
            if (!isConstructor) {
                for (JmlTypeClauseConstraint constraint : classInfo.constraints) {
                    if ((constraint.modifiers.flags & Flags.STATIC) == 0 &&
                        (methodInfo.decl.mods.flags & Flags.STATIC) != 0) continue;
                    // FIXME - check that method signature is present
                    String sp = position(constraint.source(),constraint.pos);
                    JCExpression e = translate(makeUnary(JCTree.NOT,JmlTreeCopier.copy(make,constraint.expression)));
                    JCStatement st = undefinedCheck(methodInfo.owner,
                            sp+"constraint",
                            make.If(e,assertFailure(sp+"constraint is false"),null));
                    postChecks.append(st);
                }
            }
            if (isConstructor) {
                for (JmlTypeClauseExpr initially : classInfo.initiallys) {
                    String sp = position(initially.source(),initially.pos);
                    JCExpression e = translate(makeUnary(JCTree.NOT,initially.expression));
                    JCStatement st = undefinedCheck(methodInfo.owner,
                            sp+"initially",
                            make.If(e,assertFailure(sp+"initially is false"),null));
                    postChecks.append(st);
                }
            }
            
            JCIdent m = make.Ident(invariantMethodName);
            m.sym = classInfo.invariantDecl.sym;
            m.type = m.sym.type;
            m = make.Ident(staticinvariantMethodName);
            m.sym = classInfo.staticinvariantDecl.sym;
            m.type = m.sym.type;

            ListBuffer<JCStatement> finalChecks = new ListBuffer<JCStatement>();
            if (!isHelper) {
                if ((tree.mods.flags & Flags.STATIC) == 0) {
                    finalChecks.append(methodCallThis(classInfo.invariantDecl));
                }
                finalChecks.append(methodCallThis(classInfo.staticinvariantDecl));
            }
            finalChecks.append(methodCallUtils("printValues"));
            
            // Make the catchers for testing signal assertions
            boolean includeRuntime = true;
            ListBuffer<JCCatch> catchers = new ListBuffer<JCCatch>();
            ListBuffer<JCExpression> exceptions = new ListBuffer<JCExpression>();
            exceptions.appendList(tree.getThrows());
            while (!exceptions.isEmpty()) {
                JCExpression ex;
                loop: do {
                    ex = exceptions.next(); // removes from list
                    for (JCExpression exx: exceptions) {
                        // if ex is a superclass of exx then we can't do ex yet
                        if (Types.instance(context).isSuperType(ex.type,exx.type)) {
                            exceptions.append(ex);
                            continue loop;
                        }
                    }
                    break; // continue on with ex
                } while (true);
                if (Types.instance(context).isSuperType(ex.type,syms.runtimeExceptionType)) includeRuntime = false;
                JCCatch catcher = makeCatcher(methodInfo.owner,ex.type);
                JCAssign assign = make.Assign(makeIdent(signalsEx.sym),makeIdent(catcher.param.sym));
                assign.type = signalsEx.type;
                catcher.body.stats = catcher.body.stats.append(make.Exec(assign));
                JCThrow throwex = make.Throw(makeIdent(catcher.param.sym));
                catcher.body.stats = catcher.body.stats.append(throwex);
                catchers.append(catcher);
            }
            if (includeRuntime) {
                JCCatch catcher = makeCatcher(methodInfo.owner,syms.runtimeExceptionType);
                JCAssign assign = make.Assign(makeIdent(signalsEx.sym),makeIdent(catcher.param.sym));
                assign.type = signalsEx.type;
                catcher.body.stats = catcher.body.stats.append(make.Exec(assign));
                JCThrow throwex = make.Throw(makeIdent(catcher.param.sym));
                catcher.body.stats = catcher.body.stats.append(throwex);
                catchers.append(catcher);
            }
            finalChecks.prepend(make.If(makeBinary(JCTree.EQ,makeIdent(signalsEx.sym),nulllit),make.Block(0,postChecks.toList()),make.Block(0,signalsChecks.toList())));
            JCBlock finalBlock = make.Block(0,finalChecks.toList());
            finalBlock.type = Type.noType;
            JCBlock bl = tree.body;
            if (bl == null) {
                String mge = position(methodInfo.source,tree.pos) + "model method is not implemented: " + tree.name;  // FIXME - need the source of the model method
                JCStatement sta = assertFailure(mge);
                bl = make.Block(0,List.<JCStatement>of(sta));
            }
            JCTry tryBlock = make.Try(bl,catchers.toList(),finalBlock);
            tryBlock.type = Type.noType;
            
            ListBuffer<JCStatement> newbody = new ListBuffer<JCStatement>();
            if (!isConstructor) {
                newbody.append(methodCallUtils("clearValues"));
                if (methodInfo.preCheck != null) newbody.append(methodInfo.preCheck);
                if (!isHelper) {
                    newbody.append(methodCallThis(classInfo.staticinvariantDecl));
                    if ((tree.mods.flags & Flags.STATIC) == 0) {
                        newbody.append(methodCallThis(classInfo.invariantDecl));
                    }
                }
                if (methodInfo.resultDecl != null) newbody.append(methodInfo.resultDecl);
                if (signalsEx != null) newbody.append(signalsEx);
            } else if (classInfo.decl.sym == syms.objectType.tsym) {
                newbody.append(methodCallUtils("clearValues"));
                if (signalsEx != null) newbody.append(signalsEx);
            } else {
                newbody.append(tree.body.stats.head);
                newbody.append(methodCallUtils("clearValues"));
                if (signalsEx != null) newbody.append(signalsEx);
                tryBlock.body.stats = tree.body.stats.tail;
            }

            for (JCVariableDecl v: methodInfo.olds) {
                newbody.append(v);
            }
            newbody.append(tryBlock);

            tree.body = make.Block(0,newbody.toList());
            
            //System.out.println("REWRITTEN " + tree);

        }
        methodInfo = prevMethodInfo;
        result = tree;
    }
    
//    public JCStatement condThrow(int p, JCExpression translatedExpr, JCExpression translatedArg) {
//        JCExpression nc = makeNewClass(syms.runtimeExceptionType,
//                translatedArg == null ? List.<JCExpression>nil() : List.<JCExpression>of(translatedArg));
//        JCStatement thr = make.Throw(nc);
//        JCStatement result = make.If(translatedExpr,make.Skip(),thr);
//        result.pos = thr.pos = nc.pos = p;
//        return result;
//    }
    
    ClassSymbol helperAnnotationSymbol = null;
    public boolean isHelper(Symbol symbol) {
        if (helperAnnotationSymbol == null) {
            helperAnnotationSymbol = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.annotations.Helper"));
        }
        return symbol.attribute(helperAnnotationSymbol)!=null;

    }
    
    ClassSymbol modelAnnotationSymbol = null;
    public boolean isModel(Symbol symbol) {
        if (modelAnnotationSymbol == null) {
            modelAnnotationSymbol = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.annotations.Model"));
        }
        return symbol.attribute(modelAnnotationSymbol)!=null;

    }
    
//    ClassSymbol nonnullAnnotationSymbol = null;
//    ClassSymbol nullableAnnotationSymbol = null;
//    public boolean isNonNull(Symbol symbol) {
//        if (nonnullAnnotationSymbol == null) {
//            nonnullAnnotationSymbol = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.annotations.NonNull"));
//        }
//        if (symbol.attribute(nonnullAnnotationSymbol)!=null) return true;
//        if (nullableAnnotationSymbol == null) {
//            nullableAnnotationSymbol = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.annotations.Nullable"));
//        }
//        if (symbol.attribute(nullableAnnotationSymbol)!=null) return false;
//        return specs.defaultNullity(classInfo.typeSpecs.csymbol) == JmlToken.NONNULL;
//
//    }
    

    
    public JCFieldAccess findUtilsMethod(String methodName) {
        Name n = names.fromString(methodName);
        Scope.Entry e = utilsClass.members().lookup(n);
        Symbol ms = e.sym;
        JCFieldAccess m = make.Select(utilsClassIdent,n);
        m.sym = ms;
        m.type = m.sym.type;
        return m;
    }
    
    public JCStatement findSuperMethod(ClassSymbol csym, Name methodName) {
        Symbol ms;
        do {
            Type t = csym.getSuperclass();
            if (t == null) return make.Skip();
            csym = (ClassSymbol)t.tsym;
            Scope.Entry e = csym.members().lookup(methodName);
            ms = e.sym;
            if (ms != null) break;
        } while (true) ;
        JCIdent m = make.Ident(methodName);
        m.sym = ms;
        m.type = m.sym.type;
        JCMethodInvocation a = make.Apply(null,m,List.<JCExpression>nil());
        a.type = syms.voidType;
        return make.Exec(a);
    }
    
    // Expect the type to be attributed
    JCVariableDecl makeVarDef(JCExpression type, Name name, Symbol owner) {
        JCVariableDecl d = make.VarDef(make.Modifiers(0),name,type,makeZeroEquivalentLit(type.type));
        VarSymbol v =
            new VarSymbol(0, d.name, d.vartype.type, owner);
        d.sym = v;
        d.type = type.type;
        return d;
    }
    
    // Expect the type to be attributed
    JCVariableDecl makeVarDef(Type type, Name name, Symbol owner,JCExpression init) {
        //JCIdent tid = make.Ident(names.fromString("int"));
        JCExpression tid = make.Type(type);
        tid.type = type;
        //tid.sym = type.tsym;
        JCVariableDecl d = make.VarDef(make.Modifiers(0),name,tid,init);
        VarSymbol v =
            new VarSymbol(0, d.name, type, owner);
        d.sym = v;
        d.type = type;
        return d;
    }

    JCVariableDecl makeIntVarDef(Name name, JCExpression e) {
        Type type = syms.intType;
        JCExpression tid = make.Type(type);
        tid.type = type;
        JCVariableDecl d = make.VarDef(make.Modifiers(0),name,tid,e);
        VarSymbol v =
            new VarSymbol(0, d.name, type, methodInfo.owner);
        d.sym = v;
        d.type = type;
        return d;
    }
    
    JCMethodDecl makeMethodDef(Name methodName, List<JCStatement> stats, ClassSymbol ownerClass) {
        Type restype = syms.voidType;
        
        MethodType mtype = new MethodType(List.<Type>nil(),restype,List.<Type>nil(),ownerClass);

        MethodSymbol msym = new MethodSymbol(
                Flags.PUBLIC, 
                methodName, 
                mtype, 
                ownerClass);
        
        // Caution: This call does not use a factory; it uses the
        // JCMethodDef constructor directly
        JCMethodDecl mdecl = make.MethodDef(
                msym,
                make.Block(0,stats));
        // FIXME ownerClass.members_field.enter(msym);
        return mdecl;
    }
   
    JCMethodDecl makeMethodDefNoArg(JCModifiers mods, Name methodName, Type resultType, ClassSymbol ownerClass) {
        
        MethodType mtype = new MethodType(List.<Type>nil(),resultType,List.<Type>nil(),ownerClass);

        MethodSymbol msym = new MethodSymbol(
                mods.flags, 
                methodName, 
                mtype, 
                ownerClass);
        
        // Caution: This call does not use a factory; it uses the
        // JCMethodDef constructor directly
        JCMethodDecl mdecl = make.MethodDef(
                msym,
                make.Block(0,List.<JCStatement>nil()));
   
        ownerClass.members_field.enter(msym);
        return mdecl;
    }
   
    JCMethodDecl makeStaticMethodDef(Name methodName, List<JCStatement> stats, ClassSymbol ownerClass) {
        Type restype = syms.voidType;
        
        MethodType mtype = new MethodType(List.<Type>nil(),restype,List.<Type>nil(),ownerClass);

        MethodSymbol msym = new MethodSymbol(
                Flags.PUBLIC | Flags.STATIC, 
                methodName, 
                mtype, 
                ownerClass);
        
        // Caution: This call does not use a factory; it uses the
        // JCMethodDef constructor directly
        JCMethodDecl mdecl = make.MethodDef(
                msym,
                make.Block(0,stats));
        
        //FIXME ownerClass.members_field.enter(msym);
        return mdecl;
    }
    
    /** Overridden so as not to try to do any RACing in annotations */
    public void visitAnnotation(JCAnnotation tree) {
        //tree.annotationType = translate(tree.annotationType);
        //tree.args = translate(tree.args);
        result = tree;
    }


    
    public void visitAssign(JCAssign tree) {
        super.visitAssign(tree);
        int tag = tree.type.tag;
        if (tag == TypeTags.CLASS || tag == TypeTags.ARRAY) {
            Symbol sym = null;
            if (tree.lhs instanceof JCIdent) sym = ((JCIdent)tree.lhs).sym;
            else if (tree.lhs instanceof JCFieldAccess) sym = ((JCFieldAccess)tree.lhs).sym;
            if (sym != null) {
                if (specs.isNonNull(sym,classInfo.typeSpecs.csymbol)) {
                    String s = "assignment of null to non_null";
                    tree.rhs = nullCheck(s,tree.pos,tree.rhs);
                    result = tree;
                }
            }
        }
    }

    public void visitVarDef(JCVariableDecl tree) {
        super.visitVarDef(tree);
        if (tree.init != null && specs.isNonNull(tree.sym,classInfo.typeSpecs.csymbol)) {
            String s = "null initialization of non_null variable";
            tree.init = nullCheck(s,tree.pos,tree.init);
        }
    }


    // FIXME - can we cache the && and || operators ?
    /** Make an attributed binary expression.
     *  @param optag    The operators tree tag.
     *  @param lhs      The operator's left argument.
     *  @param rhs      The operator's right argument.
     */
    JCExpression makeBinary(int optag, JCExpression lhs, JCExpression rhs) {
        if (optag == JCTree.OR && lhs == falseLit) return rhs;
        if (optag == JCTree.AND && lhs == trueLit) return rhs;
        JCBinary tree = make.Binary(optag, lhs, rhs);
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
    JCExpression makeUnary(int optag, JCExpression arg) {
        if (arg.equals(trueLit) && optag == JCTree.NOT) return falseLit;
        if (arg.equals(falseLit) && optag == JCTree.NOT) return trueLit;
        JCUnary tree = make.Unary(optag, arg);
        tree.operator = rs.resolveUnaryOperator(
            make_pos, optag, attrEnv, arg.type);
        tree.type = tree.operator.type.getReturnType();
        return tree;
    }
    
    JCCatch makeCatcher(Symbol owner) {
        return makeCatcher(owner,syms.exceptionType);
    }
    
    JCCatch makeCatcher(Symbol owner, Type ex) {
        Name n = names.fromString("_JML$$$caughtException");
        JCVariableDecl v = makeVarDef(ex,n,owner,null);
        return make.Catch(v,make.Block(0,List.<JCStatement>nil()));
    }
    
    protected JCCatch makeCatcherJML(Symbol owner) {
        Name n = names.fromString("_JML$$$caughtException");
        JCVariableDecl v = makeVarDef(assertionFailureClass.type,n,owner,null);
        JCIdent id = make.Ident(n);
        id.sym = v.sym;
        id.type = v.type;
        JCThrow t = make.Throw(id);
        return make.Catch(v,make.Block(0,List.<JCStatement>of(t)));
    }
    
    protected JCIdent makeIdent(Symbol sym) {
        JCIdent id = make.Ident(sym.name);
        id.sym = sym;
        id.type = sym.type;
        return id;
    }
    
    protected JCIdent makeThis(ClassSymbol csym) {
        JCIdent id = make.Ident(names._this);
        //Scope.Entry e = csym.members().lookup(names._this);
        id.type = csym.type;
        id.sym = new VarSymbol(0, id.name, csym.type, csym);
        return id;
    }
    
    JCStatement undefinedCheck(Symbol owner, String prefix, JCStatement stat) {
        return undefinedCheck(owner,prefix,List.<JCStatement>of(stat));
    }
    
    JCStatement undefinedCheck(Symbol owner, String prefix, List<JCStatement> stats) {
        JCCatch ct = makeCatcher(owner);
        ct.body.stats = List.<JCStatement>of(methodCallUndefined(prefix));
        JCStatement s = make.Try(make.Block(0,stats), 
                List.<JCCatch>of(ct),
                null
                );
        return s;
    }

    /** Make an attributed tree representing a literal. This will be an
     *  Ident node in the case of boolean literals, a Literal node in all
     *  other cases.
     *  @param type       The literal's type.
     *  @param value      The literal's value.
     */
    JCLiteral makeLit(Type type, Object value) {
        return make.Literal(type.tag, value).setType(type.constType(value));
    }
    
    JCLiteral makeZeroEquivalentLit(Type type) {
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

   
    public JCStatement assertFailure(String sp) {
        JCExpression lit = makeLit(syms.stringType,sp);
        JCFieldAccess m = findUtilsMethod("assertionFailure");
        JCExpression c = make.Apply(null,m,List.<JCExpression>of(lit));
        c.setType(syms.voidType);
        return make.Exec(c);
    }
    
    public JCExpression nullCheck(String message, int pos, JCExpression value) {
        if (value.type.isPrimitive()) return value;
        String s = "";
        if (methodInfo != null) s = position(methodInfo.source,pos);
        else if (classInfo.decl instanceof JmlClassDecl) s = position(((JmlClassDecl)classInfo.decl).sourcefile,pos);
        else {
            // FIXME - print out a warning
        }
        JCExpression lit = makeLit(syms.stringType,s+message);
        JCFieldAccess m = findUtilsMethod("nonNullCheck");
        JCExpression c = make.Apply(null,m,List.<JCExpression>of(lit,value));
        c.setType(value.type);
        return c;
    }
    
    public JCStatement methodCallPre(String sp, JCExpression tree) {
        String s = sp + "precondition is false";
        return assertFailure(s);
    }
    
    public JCStatement methodCallUndefined(String prefix) {
        String s = prefix + " is undefined - exception thrown";
        JCExpression lit = makeLit(syms.stringType,s);
        JCFieldAccess m = findUtilsMethod("assertionFailure");
        JCExpression c = make.Apply(null,m,List.<JCExpression>of(lit));
        c.setType(syms.voidType);
        return make.Exec(c);
    }
    

    
    public JCStatement methodCallPost(String sp, JCExpression tree) {
        // org.jmlspecs.utils.Utils.assertionFailure();
        
        String s = sp + "postcondition is false";
        return assertFailure(s);
    }
    
    public JCStatement methodCallUtils(String methodName) {
        JCFieldAccess m = findUtilsMethod(methodName);
        JCExpression c = make.Apply(null,m,List.<JCExpression>nil());
        c.setType(syms.voidType);
        JCStatement p = make.Exec(c);
        p.setType(syms.voidType);
        return p;
    }
    
    public JCExpression methodCallUtilsExpression(String methodName, JCExpression translatedArg) {
        JCFieldAccess m = findUtilsMethod(methodName);
        JCExpression c = make.Apply(null,m,List.<JCExpression>of(translatedArg));
        c.setType(((Type.MethodType)m.type).restype);
        return c;
    }
    
//    public JCStatement methodCallThis(Name methodName) {
//        JCIdent m = findThisMethod(methodName);
//        JCExpression c = make.Apply(null,m,List.<JCExpression>nil());
//        c.setType(syms.voidType);
//        JCStatement p = make.Exec(c);
//        p.setType(syms.voidType);
//        return p;
//    }
    
    public JCExpression methodCallThisExpression(JCMethodDecl methodDecl) {
        JCIdent m = make.Ident(methodDecl.name);
        m.sym = methodDecl.sym;
        m.type = m.sym.type;
        JCExpression c = make.Apply(null,m,List.<JCExpression>nil());
        c.setType(syms.voidType);
        return c;
    }
    
    public JCStatement methodCallThis(JCMethodDecl methodDecl) {
        JCExpression c = methodCallThisExpression(methodDecl);
        JCStatement p = make.Exec(c);
        p.setType(syms.voidType);
        return p;
    }
    
//    public JCStatement methodInvoke(JCExpression exp, ClassSymbol csym) {
//        try {
//            Method invoke = java.lang.reflect.Method.class.getMethod("invoke",new Class<?>[]{Object.class, Object[].class});
//            invoke.invoke
//        } catch (Exception e) {
//            System.out.println("FAILED");
//        }
//    }
    
    public JCExpression methodCallgetClass(JCExpression expr) {
        Name n = names.fromString("getClass");
        Scope.Entry e = syms.objectType.tsym.members().lookup(n);
        Symbol ms = e.sym;
        JCFieldAccess m = make.Select(expr,n);
        m.sym = ms;
        m.type = m.sym.type;

        JCExpression c = make.Apply(null,m,List.<JCExpression>nil());
        c.setType(syms.classType);
        return c;
    }
    
    public JCExpression makePrimitiveClassLiteralExpression(String s) {
        Name n = names.fromString(s);
        // The following only ever loads the class once, despite multiple calls
        Type type = ClassReader.instance(context).enterClass(n).type;
        JCIdent id = make.Ident(n);
        id.type = type;
        id.sym = type.tsym;
        Name nTYPE = names.fromString("TYPE");
        JCFieldAccess f = make.Select(id,nTYPE);
        f.type = syms.objectType;
        Scope.Entry e = type.tsym.members().lookup(nTYPE);
        f.sym = e.sym;
        return f;
    }
    
    public JCStatement methodCall(JmlStatementExpr tree) {
        // org.jmlspecs.utils.Utils.assertionFailure();
        
        JmlToken t = tree.token;
        String s = t == JmlToken.ASSERT ? "assertion is false" : t == JmlToken.ASSUME ? "assumption is false" : "unreachable statement reached";
        s = tree.source.getName() + ":" + tree.line + ": JML " + s;
        JCExpression lit = makeLit(syms.stringType,s);
        JCFieldAccess m = findUtilsMethod("assertionFailure");
        JCExpression c = make.Apply(null,m,List.<JCExpression>of(lit));
        c.setType(syms.voidType);
        return make.Exec(c);
    }
    
    public JCStatement methodCall(JmlStatementExpr tree, JCExpression translatedOptionalExpr) {
        // org.jmlspecs.utils.Utils.assertionFailure();
        
        JmlToken t = tree.token;
        String s = t == JmlToken.ASSERT ? "assertion is false" : t == JmlToken.ASSUME ? "assumption is false" : "unreachable statement reached";
        s = tree.source.getName() + ":" + tree.line + ": JML " + s;
        JCExpression lit = makeLit(syms.stringType,s);
        JCFieldAccess m = findUtilsMethod("assertionFailure2");
        JCExpression c = make.Apply(null,m,List.<JCExpression>of(lit,translatedOptionalExpr));
        c.setType(syms.voidType);
        return make.Exec(c);
    }
    
    public void visitJmlStatementExpr(JmlStatementExpr tree) {
        int p = tree.pos;
        make_pos = tree;
        switch (tree.token) {
            case ASSERT:
            case ASSUME:
            {
                if (tree.optionalExpression == null) {
                    result = make.If(translate(tree.expression),make.Skip(),methodCall(tree));
                } else {
                    result = make.If(translate(tree.expression),make.Skip(),methodCall(tree,translate(tree.optionalExpression)));
                }
                result.pos = p;
                break;
            }

            case UNREACHABLE:
            {
                result = methodCall(tree);
                result.pos = p;
                break;
            }
                
            case HENCE_BY:
                // FIXME - not implemented
                result = tree;
                break;
                
            default:
                // FIXME - unknown
                result = tree;
                break;
        }
    }

    public void visitJmlBinary(JmlBinary that) {  // FIXME - how do we handle unboxing, casting
        JCExpression lhs = translate(that.lhs);
        JCExpression rhs = translate(that.rhs);
        switch (that.op) {
            case EQUIVALENCE:
                result = makeBinary(JCTree.EQ,lhs,rhs);
                break;
                
            case INEQUIVALENCE:
                result = makeBinary(JCTree.NE,lhs,rhs);
                break;

            case IMPLIES:
                result = makeBinary(JCTree.OR,makeUnary(JCTree.NOT,lhs),rhs);
                break;

            case REVERSE_IMPLIES: // FIXME - comment on order of evaluation
                result = makeBinary(JCTree.OR,makeUnary(JCTree.NOT,rhs),lhs);
                break;
                
            case SUBTYPE_OF:
                Name n = names.fromString("isAssignableFrom");
                Scope.Entry e = that.rhs.type.tsym.members().lookup(n);
                Symbol ms = e.sym;
                JCFieldAccess m = make.Select(rhs,n);
                m.sym = ms;
                m.type = m.sym.type;

                JCExpression c = make.Apply(null,m,List.<JCExpression>of(lhs));
                c.setType(syms.booleanType);
                result = c;
                // FIXME - do we intend that <: is always false among pairs of primitive types (even the same)
                break;
                
            default:
                log.error(that.pos(),"jml.unknown.operator",that.op.internedName(),"JmlRac");
                break;
}
    }

    public void visitJmlGroupName(JmlGroupName that) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlGroupName");
    }

    public void visitJmlImport(JmlImport that) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlImport");
    }

    public void visitJmlLblExpression(JmlLblExpression that) {
        JCExpression lit = makeLit(syms.stringType,that.label.toString());
        JCFieldAccess m = null;
        // FIXME - other types?
        if (that.expression.type.tag == TypeTags.INT) {
            m = findUtilsMethod("saveInt");
        } else if (that.expression.type.tag == TypeTags.BOOLEAN) {
            m = findUtilsMethod("saveBoolean");
        } else if (that.expression.type.tag == TypeTags.CLASS) {
            m = findUtilsMethod("saveObject");
        }
        JCExpression c = make.Apply(null,m,List.<JCExpression>of(lit,translate(that.expression)));
        c.setType(that.type);
        result = c;
    }

    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        // FIXME - implement
        
    }

    public void visitJmlRefines(JmlRefines that) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlRefines");
    }

    public void visitJmlSetComprehension(JmlSetComprehension that) {
        // FIXME - implement
        
    }

    public void visitJmlSingleton(JmlSingleton that) {
        result = that;
        switch (that.token) {
            case BSRESULT:
                JCIdent id = make.Ident(attr.resultName);
                id.sym = methodInfo.resultDecl.sym;
                id.type = methodInfo.resultDecl.type;
                result = id;
                break;

            case INFORMAL_COMMENT:
                result = trueLit;
                break;
                
            case BSLOCKSET:
            case BSINDEX:
            case BSVALUES:
            case BSSAME:
            case BSNOTSPECIFIED:
            case BSNOTHING:
            case BSEVERYTHING:
                Log.instance(context).error(that.pos, "jml.unimplemented.construct",that.token.internedName(),"JmlRac.visitJmlSingleton");
                // FIXME - recovery possible?
                break;

            default:
                Log.instance(context).error(that.pos, "jml.unknown.construct",that.token.internedName(),"JmlRac.visitJmlSingleton");
            // FIXME - recovery possible?
                break;
        }
    }
    
    @Override
    public void visitReturn(JCReturn tree) {
        super.visitReturn(tree);
        if (methodInfo != null) {
            if (methodInfo.resultDecl == null) {
                // FIXME - minternal error
            } else {
                tree = (JCReturn)result;
                // FIXME - what if conversions are needed?
                JCIdent id = make.Ident(attr.resultName);
                id.sym = methodInfo.resultDecl.sym;
                id.type = methodInfo.resultDecl.type;
                tree.expr = make.Assign(id,tree.expr);
                tree.expr.type = id.type;
            }
        }
        result = tree;
    }


    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlSpecificationCase");
    }

    public void visitJmlStatement(JmlStatement that) {
        switch (that.token) {
            case SET:
            case DEBUG: // FIXME - if turned on by options
                result = translate(that.statement);
                break;
                
            default:
                // FIXME - unimplemented
                result = that;
        }
    }

    public void visitJmlStatementDecls(JmlStatementDecls that) {
        // FIXME - only handles the first one
        result = translate(that.list.first());
    }

    public void visitJmlStatementLoop(JmlStatementLoop that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlStatementSpec(JmlStatementSpec that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlTypeClauseConditional");
    }

    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlTypeClauseConstraint");
    }

    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlTypeClauseDecl");
    }

    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlTypeClauseExpr");
    }

    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        // TODO Auto-generated method stub
        
    }

    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        // TODO Auto-generated method stub
        
    }
    
    public String position(JavaFileObject source, int pos) {
        JavaFileObject pr = log.currentSourceFile();
        log.useSource(source);
        String s = (source==null?"":source.getName()) + ":" + log.currentSource().getLineNumber(pos) + ": JML ";
        log.useSource(pr);
        return s;
    }

    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        if (that.loopSpecs.isEmpty()) {
            super.visitDoLoop(that);
            return;
        }
        ListBuffer<JCStatement> checks = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> vars = new ListBuffer<JCStatement>();
        makeLoopChecks(that.loopSpecs,checks,vars);
        
        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
        stats.appendList(checks);
        stats.append(that.body);
        that.body = make.Block(0,stats.toList());
        vars.append(that);
        vars.appendList(checks);
        result = make.Block(0,vars.toList());
        //System.out.println("REWRITTEN " + result);
    }

    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        if (that.loopSpecs.isEmpty()) {
            super.visitForeachLoop(that);
            return;
        }
        ListBuffer<JCStatement> checks = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> vars = new ListBuffer<JCStatement>();
        makeLoopChecks(that.loopSpecs,checks,vars);
        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
        stats.appendList(vars);
        ListBuffer<JCStatement> bodystats = new ListBuffer<JCStatement>();
        bodystats.appendList(checks);
        bodystats.append(translate(that.body));
        JCEnhancedForLoop loop = make.ForeachLoop(translate(that.var), translate(that.expr), make.Block(0,bodystats.toList()));
        stats.append(loop);
        stats.appendList(checks);
        result = make.Block(0,stats.toList());
    }

    public void visitJmlForLoop(JmlForLoop that) {
        if (that.loopSpecs.isEmpty()) {
            super.visitForLoop(that);
            return;
        }
        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
        stats.appendList(translate(that.init));
        ListBuffer<JCStatement> checks = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> vars = new ListBuffer<JCStatement>();
        makeLoopChecks(that.loopSpecs,checks,vars);
        stats.appendList(vars);
        ListBuffer<JCStatement> bodystats = new ListBuffer<JCStatement>();
        bodystats.appendList(checks);
        bodystats.append(translate(that.body));
        stats.append(make.ForLoop(List.<JCStatement>nil(),translate(that.cond),translate(that.step),make.Block(0,bodystats.toList())));
        stats.appendList(checks);
        result = make.Block(0,stats.toList());
    }

    public void visitJmlWhileLoop(JmlWhileLoop that) {
        if (that.loopSpecs.isEmpty()) {
            super.visitWhileLoop(that);
            return;
        }
        ListBuffer<JCStatement> checks = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> vars = new ListBuffer<JCStatement>();
        makeLoopChecks(that.loopSpecs,checks,vars);
        
        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
        stats.appendList(checks);
        stats.append(that.body);
        that.body = make.Block(0,stats.toList());
        vars.append(that);
        vars.appendList(checks);
        result = make.Block(0,vars.toList());
        //System.out.println("REWRITTEN " + result);
    }
    
    public void makeLoopChecks(List<JmlStatementLoop> specs, ListBuffer<JCStatement> checks, ListBuffer<JCStatement> vars) {
        for (JmlStatementLoop s: specs) {
            if (s.token == JmlToken.LOOP_INVARIANT) {
                String sp = position(methodInfo.source,s.pos);
                JCStatement ss = undefinedCheck(methodInfo.owner,
                        sp + "loop invariant",
                        make.If(makeUnary(JCTree.NOT,translate(s.expression)),
                                assertFailure(sp + "loop invariant is false"),null));
                checks.append(ss);
            } else if (s.token == JmlToken.DECREASES) {
                int n = ++methodInfo.variableDefs;
                Name name1 = names.fromString("_JML$$$loop"+n);
                Name name2 = names.fromString("_JML$$$loopTemp"+n);
                JCVariableDecl d = makeIntVarDef(name1,maxIntLit);
                JCIdent id1 = make.Ident(name1);
                id1.type = d.type;
                id1.sym = d.sym;
                vars.append(d);
                JCExpression e = translate(s.expression);
                JCVariableDecl dd = makeIntVarDef(name2,e);
                JCIdent id2 = make.Ident(name2);
                id2.type = dd.type;
                id2.sym = dd.sym;
                String sp = position(methodInfo.source,s.pos);
                JCStatement ss = make.If(
                        makeBinary(JCTree.GE,id2,id1),
                        assertFailure(sp + "loop variant did not decrease"),null);
                JCStatement sss = make.If(
                        makeBinary(JCTree.LT,id2,zero),
                        assertFailure(sp + "loop variant is less than 0"),null);
                e = make.Assign(id1,id2);
                e.type = id1.type;
                JCStatement sa = make.Exec(e);
                ss = undefinedCheck(methodInfo.owner,sp + "loop variant",
                        List.<JCStatement>of(dd,ss,sss,sa));
                checks.append(ss);
            } else {
                // FIXME - unk nownd
            }
        }
    }
    
    public void visitJmlClassDecl(JmlClassDecl that) {
        if ((that.sym.flags() & Flags.INTERFACE) != 0) {
            result = that;
            return;
        }
        visitClassDef(that);  // FIXME
    }

    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        visitTopLevel(that);  // FIXME
    }

    public void visitJmlMethodDecl(JmlMethodDecl that) {
        visitMethodDef(that);  // FIXME
    }

    public void visitJmlVariableDecl(JmlVariableDecl that) {
        visitVarDef(that);  // FIXME
    }

//    public void visitAuxVarDSA(AuxVarDSA that) {
//        // TODO Auto-generated method stub
//        
//    }
//
//    public void visitProgVarDSA(ProgVarDSA that) {
//        // TODO Auto-generated method stub
//        
//    }
}
