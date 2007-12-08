package com.sun.tools.javac.comp;

import java.io.OutputStreamWriter;
import java.io.Writer;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.IJmlVisitor;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeCopier;
import org.jmlspecs.openjml.JmlTreeVisitor;
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
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.source.tree.*;
import com.sun.source.tree.Tree.Kind;
import com.sun.source.tree.TreeVisitor;
import com.sun.source.util.TreeScanner;

import freeboogie.ast.AssertAssumeCmd;
import freeboogie.ast.Ast;
import freeboogie.ast.AstLocation;
import freeboogie.ast.AtomId;
import freeboogie.ast.AtomLit;
import freeboogie.ast.BinaryOp;
import freeboogie.ast.Block;
import freeboogie.ast.Blocks;
import freeboogie.ast.Body;
import freeboogie.ast.Command;
import freeboogie.ast.Commands;
import freeboogie.ast.Declaration;
import freeboogie.ast.Expr;
import freeboogie.ast.Implementation;
import freeboogie.ast.PrimitiveType;
import freeboogie.ast.Signature;
import freeboogie.ast.Specification;
import freeboogie.ast.UnaryOp;
import freeboogie.ast.VariableDecl;
import freeboogie.ast.AtomLit.AtomType;
import freeboogie.ast.utils.PrettyPrinter;

public class JmlBoogie extends TreeScanner<Ast,Object> 
                       implements TreeVisitor<Ast,Object>, JmlTreeVisitor<Ast,Object> {

    Context context;
    
    Env<AttrContext> env;
    Env<AttrContext> attrEnv;
    Resolve rs;
    Symtab syms;
    Name.Table names;
    JmlSpecs specs;
    DiagnosticPosition make_pos;
    ClassSymbol assertionFailureClass;
    ClassSymbol utilsClass;
    JCIdent utilsClassIdent;
    JmlAttr attr;
    IBoogie M;
    Name resultName;
    Name exceptionName;
    Name exceptionCatchName;
    Log log;
    JmlTree.Maker make; // FIXME - get rid of
    
    Expr trueLit;
    Expr falseLit;
    JCLiteral zero;
    Expr nulllit;
    JCLiteral maxIntLit;
    
    static public String invariantMethodString = "_JML$$$checkInvariant";
    Name invariantMethodName;
    static public String staticinvariantMethodString = "_JML$$$checkStaticInvariant";
    Name staticinvariantMethodName;
    
    Type integerType;
    
    public JmlBoogie(Context context, Env<AttrContext> env) {
        this.context = context;
        this.env = env;
        this.attrEnv = env;
        this.syms = Symtab.instance(context);
        this.rs = Resolve.instance(context);
        this.names = Name.Table.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.attr = (JmlAttr)JmlAttr.instance(context);
        this.log = Log.instance(context);
        this.make = (JmlTree.Maker)JmlTree.Maker.instance(context); // FIXME - get rid of
        this.M = new JmlBoogieFactory();
        
        ClassReader reader = ClassReader.instance(context);

        assertionFailureClass = reader.enterClass(names.fromString("org.jmlspecs.utils.Utils$JmlAssertionFailure"));
        utilsClass = reader.enterClass(names.fromString("org.jmlspecs.utils.Utils"));
        utilsClassIdent = make.Ident(names.fromString("org.jmlspecs.utils.Utils"));
        utilsClassIdent.type = utilsClass.type;
        utilsClassIdent.sym = utilsClassIdent.type.tsym;
        
        trueLit = M.AtomLit(AtomType.TRUE,null);
        falseLit = M.AtomLit(AtomType.FALSE,null);
        // FIXME zero = makeLit(syms.intType,0);
        nulllit = M.AtomLit(AtomType.NULL,null);
        // FIXME maxIntLit = makeLit(syms.intType,Integer.MAX_VALUE);

        this.resultName = Name.Table.instance(context).fromString("_JML$$$result");
        this.exceptionName = Name.Table.instance(context).fromString("_JML$$$exception");
        this.exceptionCatchName = Name.Table.instance(context).fromString("_JML$$$exceptionCatch");

        integerType = reader.enterClass(names.fromString("java.lang.Integer")).type;
        
        invariantMethodName = names.fromString(invariantMethodString);
        staticinvariantMethodName = names.fromString(staticinvariantMethodString);
    }
    
    Ast translate(JCTree tree) {
        return tree.accept(this,null);
    }
    
    Expr translate(ExpressionTree tree) {
        return (Expr)tree.accept(this,null);
    }
    
    Expr translate(JCExpression tree) {
        return (Expr)tree.accept(this,null);
    }
    
//    /** Make an attributed class instance creation expression.
//     *  @param ctype    The class type.
//     *  @param args     The constructor arguments.
//     */
//    JCNewClass makeNewClass(Type ctype, List<JCExpression> args) {
//        JCNewClass tree = make.NewClass(null,
//            null, make.QualIdent(ctype.tsym), args, null);
//        tree.constructor = rs.resolveConstructor(
//            make_pos, attrEnv, ctype, TreeInfo.types(args), null, false, false);
//        tree.type = ctype;
//        return tree;
//    }
    
    @Override
    public Ast visitMethodInvocation(MethodInvocationTree node, Object p) {
        ExpressionTree m = node.getMethodSelect();
        int pos = ((JCTree)node).pos;
        Expr arg = null;
        Expr ast = null;
        if (m instanceof JmlFunction) {
            JmlToken t = ((JmlFunction)m).token;
            switch (t) {
                case BSOLD:
                case BSPRE:
                    arg = translate((JCExpression)node.getArguments().get(0));
                    ast = M.AtomOld(arg,createLocation(pos));
//                    int n = methodInfo.olds.size();
//                    String s = "_JML$$$old_" + n;
//                    Name nm = names.fromString(s);
//                    JCVariableDecl v = makeVarDef(arg.type,nm,methodInfo.owner,arg);
//                    methodInfo.olds.append(v);
//                    JCIdent r = make.Ident(nm);
//                    r.sym = v.sym;
//                    r.type = v.sym.type;
//                    result = r;
                    break;

//                case BSTYPEOF:
//                    translateTypeOf(tree);
//                    break;
//
//                case BSNONNULLELEMENTS :
//                    translateNonnullelements(tree);
//                    break;
//
//                case BSTYPELC:
//                    translateTypelc(tree);
//                    break;
//                
//                case BSELEMTYPE:
//                    translateElemtype(tree);
//                    break;
                    
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
                    Log.instance(context).error(pos, "jml.unimplemented.construct",t.internedName(),"JmlRac.visitApply");
                    // FIXME - recovery possible?
                    break;

                default:
                    Log.instance(context).error(pos, "jml.unknown.construct",t.internedName(),"JmlRac.visitApply");
                // FIXME - recovery possible?
                    break;
            }
            return ast;
        } else {
            // FIXME Java method
            return null;
        }
    }
    
//    public void translateNonnullelements(JCMethodInvocation tree) {
//        JCExpression r = trueLit;
//        for (int i = 0; i<tree.args.size(); i++) {
//            JCExpression arg = translate(tree.args.get(i));
//            JCExpression e = methodCallUtilsExpression("nonnullElementCheck",arg);
//            r = makeBinary(JCTree.AND,r,e);
//        }
//        result = r;
//    }

//    public void translateTypelc(JCMethodInvocation tree) {
//        // Argument is a type, not an expression, so we
//        // replace it with a type literal
//        JCExpression arg = tree.args.get(0);
//        JCTree.JCFieldAccess f = make.Select(arg,names._class);
//        f.type = syms.classType;
//        f.sym = f.type.tsym;
//        result = translate(f);
//    }
    
//    // FIXME - what about generic types
//    // FIXME - what about arrays of arrays
//    public void translateTypeOf(JCMethodInvocation tree) {
//        JCExpression arg = tree.args.get(0);
//        int tag = arg.type.tag;
//        switch (tag) {
//            case TypeTags.ARRAY:
//            case TypeTags.CLASS:
//                result = methodCallgetClass(translate(arg));
//                break;
//            case TypeTags.BOOLEAN:
//                result = makePrimitiveClassLiteralExpression("java.lang.Boolean");
//                break;
//            case TypeTags.INT:
//                result = makePrimitiveClassLiteralExpression("java.lang.Integer");
//                break;
//            case TypeTags.LONG:
//                result = makePrimitiveClassLiteralExpression("java.lang.Long");
//                break;
//            case TypeTags.SHORT:
//                result = makePrimitiveClassLiteralExpression("java.lang.Short");
//                break;
//            case TypeTags.BYTE:
//                result = makePrimitiveClassLiteralExpression("java.lang.Byte");
//                break;
//            case TypeTags.FLOAT:
//                result = makePrimitiveClassLiteralExpression("java.lang.Float");
//                break;
//            case TypeTags.DOUBLE:
//                result = makePrimitiveClassLiteralExpression("java.lang.Double");
//                break;
//            case TypeTags.CHAR:
//                result = makePrimitiveClassLiteralExpression("java.lang.Character");
//                break;
//            default:
//                log.error(arg.pos,"jml.unknown.construct","typeof for " + arg.type,"JmlRac.translateTypeOf");
//                // We give it an arbitrary value // FIXME - or do we call it undefined
//                result = makePrimitiveClassLiteralExpression("java.lang.Boolean");
//                break;
//        }
//    }
    
//    public void translateElemtype(JCMethodInvocation tree) {
//        Name n = names.fromString("getComponentType");
//        Scope.Entry e = syms.classType.tsym.members().lookup(n);
//        Symbol ms = e.sym;
//        JCFieldAccess m = make.Select(translate(tree.args.head),n);
//        m.sym = ms;
//        m.type = m.sym.type;
//
//        JCExpression c = make.Apply(null,m,List.<JCExpression>nil());
//        c.setType(syms.classType);
//        result = c;
//    }
    
    public static class ClassInfo {
        public ClassInfo(JCClassDecl d) { this.decl = d; }
        JCClassDecl decl;
        JmlSpecs.TypeSpecs typeSpecs = null;
        JCMethodDecl invariantDecl = null;
        JCMethodDecl staticinvariantDecl = null;
        ListBuffer<Expr> constraints = new ListBuffer<Expr>();
        ListBuffer<Expr> staticconstraints = new ListBuffer<Expr>();
        ListBuffer<Expr> initiallys = new ListBuffer<Expr>();
        ListBuffer<Expr> invariants = new ListBuffer<Expr>();
        ListBuffer<Expr> staticinvariants = new ListBuffer<Expr>();
        ListBuffer<Expr> axioms = new ListBuffer<Expr>();
        Declaration decls = null;
    }

    public ClassInfo classInfo = null;

    @Override
    public Ast visitClass(ClassTree node, Object p) {
        JCClassDecl tree = (JCClassDecl)node;
//        if (tree.sym != null && 
//                ((JmlClassDecl)tree).sourcefile.getKind() != JavaFileObject.Kind.SOURCE) {
//            return;
//        } // Model classes can have a sourcefile that is in an OTHER file
        if (tree.sym == null) return null;
        
        ClassInfo prevClassInfo = classInfo;
        classInfo = new ClassInfo(tree);
        classInfo.typeSpecs = specs.get(tree.sym);
        
//        JCMethodDecl invariantDecl = makeMethodDef(invariantMethodName,List.<JCStatement>nil(),tree.sym);
//        classInfo.invariantDecl = invariantDecl;
//        JCMethodDecl staticinvariantDecl = makeStaticMethodDef(staticinvariantMethodName,List.<JCStatement>nil(),tree.sym);
//        classInfo.staticinvariantDecl = staticinvariantDecl;
//        JCMethodDecl invariantDecl = classInfo.invariantDecl = classInfo.typeSpecs.checkInvariantDecl;
//        JCMethodDecl staticinvariantDecl = classInfo.staticinvariantDecl = classInfo.typeSpecs.checkStaticInvariantDecl;
//        
        // Remove any non-Java declarations from the Java AST before we do translation
        // After the superclass translation, we will add back in all the JML stuff.
        ListBuffer<JCTree> newlist = new ListBuffer<JCTree>();
        for (JCTree tt: tree.defs) {
            if (tt == null || tt.getTag() >= JmlTree.JMLFUNCTION) {
                // skip it
            } else {
                newlist.append(tt);
            }
        }

        // Divide up the various type specification clauses into the various types
        JmlSpecs.TypeSpecs typeSpecs = classInfo.typeSpecs;
        ListBuffer<JmlTypeClauseRepresents> represents = new ListBuffer<JmlTypeClauseRepresents>();
        ListBuffer<JCVariableDecl> modelFields = new ListBuffer<JCVariableDecl>();
        if (typeSpecs != null) for (JmlTypeClause c: typeSpecs.clauses) {
            boolean isStatic = (c.modifiers.flags & Flags.STATIC) != 0;
            if (c instanceof JmlTypeClauseDecl) {
                JCTree tt = ((JmlTypeClauseDecl)c).decl;
                if (tt instanceof JCVariableDecl && attr.isModel(((JCVariableDecl)tt).mods)) {
                    // model field - find represents or make into abstract method
                    modelFields.append((JCVariableDecl)tt);
                } else {
                    // ghost fields, model methods, model classes are used as is
                    //t = translate(t);
                    newlist.append(tt);
                }
            } else {
                JmlToken token = c.token;
                if (token == JmlToken.INVARIANT) {
                    if (isStatic) classInfo.staticinvariants.append(translate(((JmlTypeClauseExpr)c).expression));
                    else          classInfo.invariants.append(translate(((JmlTypeClauseExpr)c).expression));
                } else if (token == JmlToken.REPRESENTS) {
                    JmlTypeClauseRepresents r = (JmlTypeClauseRepresents)c;
                    if (r.suchThat) log.warning(r.pos,"jml.not.implemented.rac","relational represents clauses (\\such_that)");
                    else represents.append(r);
                } else if (token == JmlToken.CONSTRAINT) {
                    if (isStatic) classInfo.staticconstraints.append(translate(((JmlTypeClauseConstraint)c).expression));
                    else          classInfo.constraints.append(translate(((JmlTypeClauseConstraint)c).expression));
                } else if (token == JmlToken.INITIALLY) {
                    classInfo.initiallys.append(translate(((JmlTypeClauseExpr)c).expression));
                } else {
                    classInfo.axioms.append(translate(((JmlTypeClauseExpr)c).expression));
                }
            }
        }
        
        tree.defs = newlist.toList();
        newlist = new ListBuffer<JCTree>();
        newlist.appendList(tree.defs);

//        for (JmlTypeClauseRepresents r : represents) {
//            JCExpression e = r.ident;
//            Symbol sym = null;
//            if (e instanceof JCIdent) sym = ((JCIdent)e).sym;
//            else if (e instanceof JCFieldAccess) sym = ((JCFieldAccess)e).sym;
//            else {
//                // FIXME -error
//            }
//            if (sym != null) {
//                Name name = names.fromString("_JML$model$" + sym.name);
//                JmlMethodDecl mdecl = null;
//                for (JmlTypeClauseDecl m: typeSpecs.modelFieldMethods) {
//                    mdecl = (JmlMethodDecl)m.decl;
//                    if (! mdecl.name.equals(name)) continue;
//                    JCReturn st = make.Return(translate(r.expression));
//                    if (mdecl.body.stats.isEmpty()) {
//                        mdecl.body.stats = List.<JCStatement>of(st);
//                    } else {
//                        log.error(r.pos,"jml.duplicate.represents");
//                    }
//                    break;
//                }
////                if (mdecl == null) {
////                    // We can get here if there is no model field at all, but then
////                    // there would have been an error on resolving the target of
////                    // the represents clause.  The usual route to this code is
////                    // when a subclass has a represents clause for a super class's
////                    // model field.
////                    
////                    long flags = Flags.PUBLIC | Flags.SYNTHETIC;
////                    flags |= (r.modifiers.flags & Flags.STATIC);
////                    JCModifiers mods = make.Modifiers(flags);
////                    JCMethodDecl msdecl = makeMethodDefNoArg(mods,name,r.ident.type,tree.sym);
////                    JCReturn st = make.Return(translate(r.expression));
////                    msdecl.body.stats = List.<JCStatement>of(st);
////                    newlist.append(msdecl);
////                    JmlTypeClauseDecl tcd = make.JmlTypeClauseDecl(msdecl);
////                    tcd.modifiers = msdecl.mods;
////                    typeSpecs.modelFieldMethods.append(tcd);
////                }
//            }
//        }
//        for (JmlTypeClauseDecl m: typeSpecs.modelFieldMethods) {
//            JmlMethodDecl mdecl = (JmlMethodDecl)m.decl;
//            if (mdecl.body.stats.isEmpty()) {
//                //System.out.println("NO IMPLEMENTATION " + mdecl.name);
//                String position = position(m.source,m.pos);
//                String s = mdecl.name.toString();
//                int p = s.lastIndexOf('$');
//                JCStatement st = assertFailure(position + "model field is not implemented: " + s.substring(p+1));
//                JCStatement stt = make.Return(makeZeroEquivalentLit(mdecl.getReturnType().type));
//                mdecl.body.stats = List.<JCStatement>of(st,stt);
//            }
//        }
        
        super.visitClass(tree,null);
//        if (env.tree == tree) env.tree = result;
//        if (typeSpecs == null) return;
//        if (tree.name.equals("org.jmlspecs.utils.Utils")) return;
//        
//        // All ghost fields, model methods, model fields should have
//        // been attributed.  So we append them to the class definitions.
//        
//
//        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
//        ListBuffer<JCStatement> staticstats = new ListBuffer<JCStatement>();
//        for (JmlTypeClause inv: invariants) {
//            JCExpression e = translate(((JmlTypeClauseExpr)inv).expression);
//            String position = position(inv.source(),inv.pos);
//            if ((inv.modifiers.flags & Flags.STATIC) != 0) {
//                JCStatement s = undefinedCheck(staticinvariantDecl.sym,
//                        position+"static invariant",
//                        make.If(makeUnary(JCTree.NOT,e),assertFailure(position+"static invariant is false"),null));
//                staticstats.append(s);
//            } else {
//                JCStatement s = undefinedCheck(invariantDecl.sym,
//                        position+"invariant",
//                        make.If(makeUnary(JCTree.NOT,e),assertFailure(position+"invariant is false"),null));
//                stats.append(s);
//            }
//        }
//
////        stats.append(findSuperMethod(tree.sym,names.fromString("_JML$$$checkInvariant")));
//
//        //JCExpression exp = methodCallUtilsExpression("callSuperInvariantCheck",nulllit);
//        //stats.append(make.Exec(methodCallUtilsExpression("callSuperInvariantCheck",makeThis(tree.sym))));
//        invariantDecl.body = make.Block(0,stats.toList());
//        staticinvariantDecl.body = make.Block(0,staticstats.toList());
//
//
//        tree.defs = newlist.toList();
//        result = tree;
//        System.out.println("REWRITTEN " + result);
        classInfo = prevClassInfo;
        return null;
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
        String resultName;
        boolean resultUsed = false;
        JCExpression exceptionDecl;
        VarSymbol exceptionLocal;
        ListBuffer<JCVariableDecl> olds = new ListBuffer<JCVariableDecl>();
        JCStatement preCheck;
        JCStatement postCheck;
        ListBuffer<Expr> requiresPredicates = new ListBuffer<Expr>();
        ListBuffer<Expr> ensuresPredicates = new ListBuffer<Expr>();
        int variableDefs = 0;
        ListBuffer<Command> commands = new ListBuffer<Command>();
        ListBuffer<Block> blocks = new ListBuffer<Block>();
        ListBuffer<VariableDecl> vars = new ListBuffer<VariableDecl>();
    }
    
    
    @Override
    public Ast visitLiteral(LiteralTree tree, Object p) {
        int tag = ((JCLiteral)tree).typetag; // FIXME _ use getKind()?
        Object value = tree.getValue();
        int pos = ((JCTree)tree).pos;
        Ast ast = null;
        switch (tag) {
            case TypeTags.BOOLEAN:
                if (value.equals(Boolean.TRUE)) {
                    ast = M.AtomLit(AtomLit.AtomType.TRUE,createLocation(pos));
                } else {
                    ast = M.AtomLit(AtomLit.AtomType.FALSE,createLocation(pos));
                }
                break;
                
            case TypeTags.BOT:
                ast = M.AtomLit(AtomLit.AtomType.NULL,createLocation(pos));
                break;
                
            case TypeTags.INT:
                Integer i = (Integer)value;  // FIXME - is it always an Integer?
                ast = M.AtomNum(java.math.BigInteger.valueOf(i.intValue()),createLocation(pos));
                break;
                
            case TypeTags.LONG:
                Long lg = (Long)value;  // FIXME - is it always an Long?
                ast = M.AtomNum(java.math.BigInteger.valueOf(lg.longValue()),createLocation(pos));
                break;
                
            case TypeTags.FLOAT:
            case TypeTags.DOUBLE:
            case TypeTags.CHAR:
            case TypeTags.CLASS:
                System.out.println("UNIMPLEMENTED AST LITERAL");
                break;
                
                
            default:
                System.out.println("UNKNOWN AST LITERAL");
                    
            
        }
        return ast;
    }
    
    public void visitSelect(JCFieldAccess tree) {
//        if (tree.sym != null && tree.sym.kind == Kinds.VAR && attr.isModel(tree.sym)) {
//            Name name = names.fromString("_JML$model$" + tree.name);
//            ClassSymbol sym = classInfo.decl.sym;
//            Scope.Entry e = sym.members().lookup(name);
//            while (e.sym == null) {  // FIXME - do we need to look in interfaces?
//                Type t = sym.getSuperclass();
//                if (t == null) break;
//                sym = (ClassSymbol)t.tsym;
//                e = sym.members().lookup(name);
//            }
//            if (e.sym instanceof MethodSymbol) {
//                MethodSymbol ms = (MethodSymbol)e.sym;
//                JCFieldAccess m = make.Select(translate(tree.selected),name);
//                m.sym = ms;
//                m.type = m.sym.type;
//                JCExpression c = make.Apply(null,m,List.<JCExpression>nil());
//                c.setType(tree.type);
//                result = c;
//                return;
//            } else {
//                System.out.println("COULD NOT FIND METHOD FOR MODEL FIELD " + tree.sym);
//                // FIXME - problem?
//            }
//        }
//        super.visitSelect(tree);
    }
    
    MethodInfo methodInfo = null;
    
    @Override
    public Ast visitMethod(MethodTree node, Object p) {
        JCMethodDecl tree = (JCMethodDecl)node;
        int pos = tree.pos;
        JmlMethodSpecs s = tree.sym == null ? null : specs.getDenestedSpecs(tree.sym);
        JavaFileObject source = ((JmlMethodDecl)tree).sourcefile;
        JavaFileObject prev = log.useSource(source);
        boolean doEsc = ((((JCMethodDecl)tree).mods.flags & (Flags.SYNTHETIC|Flags.ABSTRACT|Flags.NATIVE)) == 0);
        boolean isConstructor = tree.getReturnType() == null;
        boolean isStatic = tree.sym.isStatic();
        if (classInfo.decl.sym == syms.objectType.tsym && isConstructor) doEsc = false;
        if (!doEsc) return null;

        // FIXME - why might tree.sym be null - aren't things attributed? but annotations have null symbol, constructors?

        MethodInfo prevMethodInfo = methodInfo;
        methodInfo = null;
        methodInfo = new MethodInfo((JCMethodDecl)tree);

        String resultName  = methodInfo.resultName = "_JML$$$result";
        String signalsName = "_JML$$$signalsException";

        JCExpression resultType = (JCExpression)tree.getReturnType();
        if (isConstructor || resultType.type.tag == TypeTags.VOID)
            resultName = null;

        boolean isHelper = isHelper(tree.sym);

        Specification sps = null;

        if (s != null) {
            for (JmlSpecificationCase spc: s.cases) {
                Expr spre = trueLit;
                for (JmlMethodClause c: spc.clauses) {
                    if (c.token == JmlToken.REQUIRES) spre = M.BinaryOp(BinaryOp.Op.AND,spre,translate(((JmlMethodClauseExpr)c).expression));
                }
                for (JmlMethodClause c: spc.clauses) {
                    if (c.token == JmlToken.ENSURES) {
                        Expr post = M.BinaryOp(BinaryOp.Op.AND,spre,M.UnaryOp(UnaryOp.Op.NOT,translate(((JmlMethodClauseExpr)c).expression)));
                        methodInfo.ensuresPredicates.append(post);
                        // FIXME - need definedness checks ??
                        sps = M.Specification(Specification.SpecType.ENSURES,post,true,sps,createLocation(spc.source(),c.pos));
                    }
                }
            }
            if (!isHelper) {
                for (Expr c: classInfo.staticinvariants) {
                    sps = M.Specification(Specification.SpecType.ENSURES,c,true,sps,c.loc());
                }
                if (!isStatic) for (Expr c: classInfo.invariants) {
                    sps = M.Specification(Specification.SpecType.ENSURES,c,true,sps,c.loc());
                }
                if (isConstructor) for (Expr c: classInfo.initiallys) {
                    sps = M.Specification(Specification.SpecType.ENSURES,c,true,sps,c.loc());
                } else {
                    // FIXME - check the for clause method list
                    for (Expr c: classInfo.staticconstraints) {
                        sps = M.Specification(Specification.SpecType.ENSURES,c,true,sps,c.loc());
                    }
                    if (!isStatic) for (Expr c: classInfo.constraints) {
                        sps = M.Specification(Specification.SpecType.ENSURES,c,true,sps,c.loc());
                    }
                }
            }
        }

        if (s != null) {
            Expr pre = s.cases.size() == 0 ? trueLit : falseLit;
            int num = 0;
            for (JmlSpecificationCase spc: s.cases) {
                Expr spre = trueLit;
                for (JmlMethodClause c: spc.clauses) {
                    if (c.token == JmlToken.REQUIRES) {
                        num++;
                        spre = M.BinaryOp(BinaryOp.Op.AND,spre,translate(((JmlMethodClauseExpr)c).expression));
                    }
                }
                pre = M.BinaryOp(BinaryOp.Op.OR,pre,spre);
            }
            if (pre != trueLit) {
                methodInfo.requiresPredicates.append(pre);
                sps = M.Specification(Specification.SpecType.REQUIRES,pre,true,sps,AstLocation.unknown()); // FIXME - better location; split up requires when possible
            }
            // Need definedness checks?  FIXME
            if (!isConstructor && !isHelper) {
                if (!isStatic) for (Expr c: classInfo.invariants) {
                    sps = M.Specification(Specification.SpecType.REQUIRES,c,true,sps,c.loc());
                }
                for (Expr c: classInfo.staticinvariants) {
                    sps = M.Specification(Specification.SpecType.REQUIRES,c,true,sps,c.loc());
                }
            }
        }
        
        Declaration vars = null;
        for (JCVariableDecl param: tree.getParameters()) {
            freeboogie.ast.Type t;
            if (!param.type.isPrimitive()) {
                t = M.PrimitiveType(PrimitiveType.Ptype.REF,AstLocation.unknown());
            } else if (param.type.tag == TypeTags.BOOLEAN) {
                t = M.PrimitiveType(PrimitiveType.Ptype.BOOL,AstLocation.unknown());
            } else {
                t = M.PrimitiveType(PrimitiveType.Ptype.INT,AstLocation.unknown());
            }
            vars = M.VariableDecl(param.getName().toString(),t,vars,createLocation(param.pos));
        }
        
        Declaration out = null;
        out = M.VariableDecl(signalsName,M.PrimitiveType(PrimitiveType.Ptype.REF,AstLocation.unknown()),out,AstLocation.unknown());
        if (resultName != null) {
            freeboogie.ast.Type t;
            if (!resultType.type.isPrimitive()) {
                t = M.PrimitiveType(PrimitiveType.Ptype.REF,AstLocation.unknown());
            } else if (resultType.type.tag == TypeTags.BOOLEAN) {
                t = M.PrimitiveType(PrimitiveType.Ptype.BOOL,AstLocation.unknown());
            } else {
                t = M.PrimitiveType(PrimitiveType.Ptype.INT,AstLocation.unknown());
            }
            out = M.VariableDecl(resultName,t,out,AstLocation.unknown());
        }

        AstLocation loc = createLocation(((JCTree)tree).pos);
        Signature sig = M.Signature(tree.getName().toString(),vars,out,loc);
        Ast ast = M.Procedure(sig,sps,null,loc);
        //Ast ast = super.visitMethod(tree,null);
        Writer w = new OutputStreamWriter(System.out);
        ast.eval(new PrettyPrinter(w));
        try { w.flush(); } catch (java.io.IOException e) {}

        // create Implementation
        
        methodInfo.vars.append(M.VariableDecl("_JML$$$nullCheck",M.PrimitiveType(PrimitiveType.Ptype.REF,AstLocation.unknown()),null,AstLocation.unknown()));
        
        node.getBody().accept(this,null);
        
        if (!methodInfo.commands.isEmpty()) {
            Commands cmds = makeCommands(methodInfo.commands.toList());
            Block block = M.Block("last",cmds,null,AstLocation.unknown());
            methodInfo.blocks.append(block);
        }
        Body body = M.Body(vars,makeBlocks(methodInfo.blocks.toList()),null);
        Implementation impl = M.Implementation(sig,body,null,createLocation(pos));
        
        impl.eval(new PrettyPrinter(w));
        try { w.flush(); } catch (java.io.IOException e) {}

//            
//            Name n = names.fromString("_JML$$$signalsException");
//            JCVariableDecl signalsEx = makeVarDef(make.QualIdent(syms.exceptionType.tsym),n,tree.sym);
//            
//            
//            ListBuffer<JCStatement> signalsChecks = new ListBuffer<JCStatement>();
//            if (s != null) {
//                for (JmlSpecificationCase spc: s.cases) {
//                    JCExpression spre = trueLit;
//                    for (JmlMethodClause c: spc.clauses) {
//                        if (c.token == JmlToken.REQUIRES) spre = makeBinary(JCTree.AND,spre,translate(((JmlMethodClauseExpr)c).expression));
//                    }
//                    boolean hasSignalsOnly = false;
//                    for (JmlMethodClause c: spc.clauses) {
//                        if (c.token == JmlToken.SIGNALS) {
//                            JmlMethodClauseSignals sig = (JmlMethodClauseSignals)c;
//                            JCIdent id = makeIdent(signalsEx.sym);
//                            JCExpression test = null; 
//                            if (sig.vardef == null) {
//                                // If there is no vardef, there cannot be uses of the local variable to replace
//                                test = make.TypeTest(id,make.Type(syms.exceptionType));
//                                test.type = syms.booleanType;
//                                methodInfo.exceptionDecl = null;
//                                methodInfo.exceptionLocal = null;
//                            } else {
//                                // During the walking of the tree, instances of exceptionLocal are replaced by the JCExpression exceptionDecl
//                                test = make.TypeTest(id,sig.vardef.getType());
//                                test.type = syms.booleanType;
//                                methodInfo.exceptionDecl = make.TypeCast(sig.vardef.vartype,id).setType(sig.vardef.vartype.type);
//                                methodInfo.exceptionLocal = sig.vardef.sym;
//                            }
//                            JCExpression post = makeBinary(JCTree.AND,spre,makeBinary(JCTree.AND,test,makeUnary(JCTree.NOT,translate(sig.expression))));
//                            methodInfo.exceptionLocal = null;
//                            String sp = position(spc.sourcefile,c.pos);
//                            JCStatement st = undefinedCheck(methodInfo.owner,
//                                    sp+"signals condition",
//                                    make.If(post,assertFailure(sp+"signals condition is false"),null));
//                            signalsChecks.append(st);
//                        } else if (c.token == JmlToken.SIGNALS_ONLY) {
//                            hasSignalsOnly = true;
//                            JmlMethodClauseSigOnly sig = (JmlMethodClauseSigOnly)c;
//                            JCExpression e = falseLit;
//                            for (JCExpression t: sig.list) {
//                                JCIdent id = makeIdent(signalsEx.sym);
//                                JCInstanceOf test = make.TypeTest(id,translate(t));
//                                test.type = syms.booleanType;
//                                e = makeBinary(JCTree.OR,e,test);
//                            }
//                            methodInfo.exceptionLocal = null;
//                            String sp = position(spc.sourcefile,c.pos);
//                            JCStatement st = undefinedCheck(methodInfo.owner,
//                                    sp+"signals_only condition",
//                                    make.If(makeUnary(JCTree.NOT,e),assertFailure(sp+"signals_only condition is false"),null));
//                            signalsChecks.append(st);
//                        }
//                    }
//                    if (!hasSignalsOnly) {
//                        JCExpression e = falseLit;
//                        for (JCExpression t: methodInfo.decl.getThrows()) {
//                            JCIdent id = makeIdent(signalsEx.sym);
//                            JCInstanceOf test = make.TypeTest(id,translate(t)); // Caution: these get translated multiple times - is that oK?
//                            test.type = syms.booleanType;
//                            e = makeBinary(JCTree.OR,e,test);
//                        }
//                        methodInfo.exceptionLocal = null;
//                        String sp = position(spc.sourcefile,methodInfo.decl.pos);
//                        JCStatement st = undefinedCheck(methodInfo.owner,
//                                sp+"default signals_only condition",
//                                make.If(makeUnary(JCTree.NOT,e),assertFailure(sp+"unexpected exception"),null));
//                        signalsChecks.append(st);
//                    }
//                }
//            }
//            
//            
//            if (!isConstructor) {
//                for (JmlTypeClauseConstraint constraint : classInfo.constraints) {
//                    if ((constraint.modifiers.flags & Flags.STATIC) == 0 &&
//                        (methodInfo.decl.mods.flags & Flags.STATIC) != 0) continue;
//                    // FIXME - check that method signature is present
//                    String sp = position(constraint.source(),constraint.pos);
//                    JCExpression e = translate(makeUnary(JCTree.NOT,JmlTreeCopier.copy(make,constraint.expression)));
//                    JCStatement st = undefinedCheck(methodInfo.owner,
//                            sp+"constraint",
//                            make.If(e,assertFailure(sp+"constraint is false"),null));
//                    postChecks.append(st);
//                }
//            }
//            if (isConstructor) {
//                for (JmlTypeClauseExpr initially : classInfo.initiallys) {
//                    String sp = position(initially.source(),initially.pos);
//                    JCExpression e = translate(makeUnary(JCTree.NOT,initially.expression));
//                    JCStatement st = undefinedCheck(methodInfo.owner,
//                            sp+"initially",
//                            make.If(e,assertFailure(sp+"initially is false"),null));
//                    postChecks.append(st);
//                }
//            }
//            
//            JCIdent m = make.Ident(invariantMethodName);
//            m.sym = classInfo.invariantDecl.sym;
//            m.type = m.sym.type;
//            m = make.Ident(staticinvariantMethodName);
//            m.sym = classInfo.staticinvariantDecl.sym;
//            m.type = m.sym.type;
//
//            ListBuffer<JCStatement> finalChecks = new ListBuffer<JCStatement>();
//            if (!isHelper) {
//                if ((tree.mods.flags & Flags.STATIC) == 0) {
//                    finalChecks.append(methodCallThis(classInfo.invariantDecl));
//                }
//                finalChecks.append(methodCallThis(classInfo.staticinvariantDecl));
//            }
//            finalChecks.append(methodCallUtils("printValues"));
//            
//            // Make the catchers for testing signal assertions
//            boolean includeRuntime = true;
//            ListBuffer<JCCatch> catchers = new ListBuffer<JCCatch>();
//            ListBuffer<JCExpression> exceptions = new ListBuffer<JCExpression>();
//            exceptions.appendList(tree.getThrows());
//            while (!exceptions.isEmpty()) {
//                JCExpression ex;
//                loop: do {
//                    ex = exceptions.next(); // removes from list
//                    for (JCExpression exx: exceptions) {
//                        // if ex is a superclass of exx then we can't do ex yet
//                        if (Types.instance(context).isSuperType(ex.type,exx.type)) {
//                            exceptions.append(ex);
//                            continue loop;
//                        }
//                    }
//                    break; // continue on with ex
//                } while (true);
//                if (Types.instance(context).isSuperType(ex.type,syms.runtimeExceptionType)) includeRuntime = false;
//                JCCatch catcher = makeCatcher(methodInfo.owner,ex.type);
//                JCAssign assign = make.Assign(makeIdent(signalsEx.sym),makeIdent(catcher.param.sym));
//                assign.type = signalsEx.type;
//                catcher.body.stats = catcher.body.stats.append(make.Exec(assign));
//                JCThrow throwex = make.Throw(makeIdent(catcher.param.sym));
//                catcher.body.stats = catcher.body.stats.append(throwex);
//                catchers.append(catcher);
//            }
//            if (includeRuntime) {
//                JCCatch catcher = makeCatcher(methodInfo.owner,syms.runtimeExceptionType);
//                JCAssign assign = make.Assign(makeIdent(signalsEx.sym),makeIdent(catcher.param.sym));
//                assign.type = signalsEx.type;
//                catcher.body.stats = catcher.body.stats.append(make.Exec(assign));
//                JCThrow throwex = make.Throw(makeIdent(catcher.param.sym));
//                catcher.body.stats = catcher.body.stats.append(throwex);
//                catchers.append(catcher);
//            }
//            finalChecks.prepend(make.If(makeBinary(JCTree.EQ,makeIdent(signalsEx.sym),nulllit),make.Block(0,postChecks.toList()),make.Block(0,signalsChecks.toList())));
//            JCBlock finalBlock = make.Block(0,finalChecks.toList());
//            finalBlock.type = Type.noType;
//            JCBlock bl = tree.body;
//            if (bl == null) {
//                String mge = position(methodInfo.source,tree.pos) + "model method is not implemented: " + tree.name;  // FIXME - need the source of the model method
//                JCStatement sta = assertFailure(mge);
//                bl = make.Block(0,List.<JCStatement>of(sta));
//            }
//            JCTry tryBlock = make.Try(bl,catchers.toList(),finalBlock);
//            tryBlock.type = Type.noType;
//            
//            ListBuffer<JCStatement> newbody = new ListBuffer<JCStatement>();
//            if (!isConstructor) {
//                newbody.append(methodCallUtils("clearValues"));
//                if (methodInfo.preCheck != null) newbody.append(methodInfo.preCheck);
//                if (!isHelper) {
//                    newbody.append(methodCallThis(classInfo.staticinvariantDecl));
//                    if ((tree.mods.flags & Flags.STATIC) == 0) {
//                        newbody.append(methodCallThis(classInfo.invariantDecl));
//                    }
//                }
//                if (methodInfo.resultDecl != null) newbody.append(methodInfo.resultDecl);
//                if (signalsEx != null) newbody.append(signalsEx);
//            } else if (classInfo.decl.sym == syms.objectType.tsym) {
//                newbody.append(methodCallUtils("clearValues"));
//                if (signalsEx != null) newbody.append(signalsEx);
//            } else {
//                newbody.append(tree.body.stats.head);
//                newbody.append(methodCallUtils("clearValues"));
//                if (signalsEx != null) newbody.append(signalsEx);
//                tryBlock.body.stats = tree.body.stats.tail;
//            }
//
//            for (JCVariableDecl v: methodInfo.olds) {
//                newbody.append(v);
//            }
//            newbody.append(tryBlock);
//
//            tree.body = make.Block(0,newbody.toList());
//            
//            //System.out.println("REWRITTEN " + tree);
//
//        }
      methodInfo = prevMethodInfo;
      log.useSource(prev);
      return ast;
    }
    
    Commands makeCommands(List<Command> list) {
        if (list.tail == null) {
            return null;
        } else {
            return M.Commands(list.head,makeCommands(list.tail));
        }
    }
    
    Blocks makeBlocks(List<Block> list) {
        if (list.tail == null) {
            return null;
        } else {
            return M.Blocks(list.head,makeBlocks(list.tail));
        }
    }
    
    AstLocation createLocation(int pos) {
        AstLocation loc = M.Location(log.currentSource().getName(),log.getLineNumber(pos),log.getColumnNumber(pos));
        return loc;

    }
    
    AstLocation createLocation(JavaFileObject j, int pos) {
        JavaFileObject prev = log.useSource(j);
        AstLocation loc = M.Location(log.currentSource().getName(),log.getLineNumber(pos),log.getColumnNumber(pos));
        log.useSource(prev);
        return loc;

    }
    
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
    
    ClassSymbol nonnullAnnotationSymbol = null;
    ClassSymbol nullableAnnotationSymbol = null;
    public boolean isNonNull(Symbol symbol) {
        if (nonnullAnnotationSymbol == null) {
            nonnullAnnotationSymbol = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.annotations.NonNull"));
        }
        if (symbol.attribute(nonnullAnnotationSymbol)!=null) return true;
        if (nullableAnnotationSymbol == null) {
            nullableAnnotationSymbol = ClassReader.instance(context).enterClass(names.fromString("org.jmlspecs.annotations.Nullable"));
        }
        if (symbol.attribute(nullableAnnotationSymbol)!=null) return false;
        return specs.defaultNullity(classInfo.typeSpecs.csymbol) == JmlToken.NONNULL;

    }
    

    
     
    @Override
    public Ast visitAssignment(AssignmentTree node, Object p) {
        JCAssign tree = (JCAssign)node;
        Command ast = null;

        Expr lhs = translate(tree.lhs);
        Expr rhs = translate(tree.rhs);

        boolean doNullCheck = false;
        int tag = tree.type.tag;
        if (tag == TypeTags.CLASS || tag == TypeTags.ARRAY) {
            Symbol sym = null;
            if (tree.lhs instanceof JCIdent) {
                sym = ((JCIdent)tree.lhs).sym;
            } else if (tree.lhs instanceof JCFieldAccess) {
                sym = ((JCFieldAccess)tree.lhs).sym;
            }
            // FIXME - nonnull check
            if (sym != null) {
                if (isNonNull(sym)) {
                    doNullCheck = true;
//                    ast = M.AssertAssumeCmd();
//                    String s = "assignment of null to non_null";
//                    tree.rhs = nullCheck(s,tree.pos,tree.rhs);
//                    result = tree;
                }
            }
        }
        if (doNullCheck) {
            AtomId id = M.AtomId("_JML$$$nullCheck",AstLocation.unknown());
            ast = M.AssignmentCmd(id,rhs);
            methodInfo.commands.append(ast);
            ast = M.AssertAssumeCmd(AssertAssumeCmd.CmdType.ASSERT,M.BinaryOp(BinaryOp.Op.NEQ,id,nulllit),createLocation(((JCTree)node).pos));
            methodInfo.commands.append(ast);
            ast = M.AssignmentCmd(lhs,id);
            methodInfo.commands.append(ast);
            
        } else {
            ast = M.AssignmentCmd(lhs,rhs);
            methodInfo.commands.append(ast);
        }
        // FIXME - put in writable if check
        // FIXME - put in assignable check
        // FIXME - monitored check?
        return null;
    }

    public void visitVarDef(JCVariableDecl tree) {
//        super.visitVarDef(tree);
//        if (tree.init != null && isNonNull(tree.sym)) {
//            String s = "null initialization of non_null variable";
//            tree.init = nullCheck(s,tree.pos,tree.init);
//        }
    }


    @Override
    public Ast visitJmlStatementExpr(JmlStatementExpr tree, Object p) {
//        int p = tree.pos;
//        make_pos = tree;
//        switch (tree.token) {
//            case ASSERT:
//            case ASSUME:
//            {
//                if (tree.optionalExpression == null) {
//                    result = make.If(translate(tree.expression),make.Skip(),methodCall(tree));
//                } else {
//                    result = make.If(translate(tree.expression),make.Skip(),methodCall(tree,translate(tree.optionalExpression)));
//                }
//                result.pos = p;
//                break;
//            }
//
//            case UNREACHABLE:
//            {
//                result = methodCall(tree);
//                result.pos = p;
//                break;
//            }
//                
//            case HENCE_BY:
//                // FIXME - not implemented
//                result = tree;
//                break;
//                
//            default:
//                // FIXME - unknown
//                result = tree;
//                break;
//        }
        // FIXME
        return null;
    }

    @Override
    public Ast visitUnary(UnaryTree node, Object p) {
        Expr operand = translate(node.getExpression());
        int pos = ((JCTree)node).pos;
        int tag = ((JCUnary)node).getTag();
        switch (tag) {
            case JCTree.NOT:
                return M.UnaryOp(UnaryOp.Op.NOT,operand);
            case JCTree.NEG:
                return M.UnaryOp(UnaryOp.Op.MINUS,operand);
            case JCTree.POS:
                return operand;
            case JCTree.COMPL:
            case JCTree.PREINC:  //>>
            case JCTree.POSTINC: //>>>
            case JCTree.PREDEC:
            case JCTree.POSTDEC:  // FIXME
            default:
                System.out.println("UNKNOWN UNARY OPERATOR " + ((JCUnary)node).getOperator());
        }
        return null;
    }
    
    @Override
    public Ast visitBinary(BinaryTree node, Object p) {
        Expr lhs = translate(node.getLeftOperand());
        Expr rhs = translate(node.getRightOperand());
        int pos = ((JCTree)node).pos;
        int tag = ((JCBinary)node).getTag();
        switch (tag) {
            case JCTree.EQ:
                return M.BinaryOp(BinaryOp.Op.EQ,lhs,rhs);
            case JCTree.NE:
                return M.BinaryOp(BinaryOp.Op.NEQ,lhs,rhs);
            case JCTree.AND:
                return M.BinaryOp(BinaryOp.Op.AND,lhs,rhs);
            case JCTree.OR:
                return M.BinaryOp(BinaryOp.Op.OR,lhs,rhs);
            case JCTree.LE:
                return M.BinaryOp(BinaryOp.Op.LE,lhs,rhs);
            case JCTree.LT:
                return M.BinaryOp(BinaryOp.Op.LT,lhs,rhs);
            case JCTree.GE:
                return M.BinaryOp(BinaryOp.Op.GE,lhs,rhs);
            case JCTree.GT:
                return M.BinaryOp(BinaryOp.Op.GT,lhs,rhs);
            case JCTree.PLUS:
                return M.BinaryOp(BinaryOp.Op.PLUS,lhs,rhs);
            case JCTree.MINUS:
                return M.BinaryOp(BinaryOp.Op.MINUS,lhs,rhs);
            case JCTree.MUL:
                return M.BinaryOp(BinaryOp.Op.MUL,lhs,rhs);
            case JCTree.DIV:
                return M.BinaryOp(BinaryOp.Op.DIV,lhs,rhs);
            case JCTree.MOD:
                return M.BinaryOp(BinaryOp.Op.MOD,lhs,rhs);
            case JCTree.SL:  //<<
            case JCTree.SR:  //>>
            case JCTree.USR: //>>>
            case JCTree.BITOR:
            case JCTree.BITXOR:
            case JCTree.BITAND:  // FIXME
            default:
                System.out.println("UNKNOWN BINARY OPERATOR " + ((JCBinary)node).getOperator());
        }
        return null;
    }
    
    
    @Override
    public Ast visitJmlBinary(JmlBinary node, Object p) {  // FIXME - how do we handle unboxing, casting
        Expr lhs = translate(node.getLeftOperand());
        Expr rhs = translate(node.getRightOperand());
        int pos = node.pos;
        Ast result = null;
        switch (node.op) {
            case EQUIVALENCE:
                result = M.BinaryOp(BinaryOp.Op.EQ,lhs,rhs);
                break;
                
            case INEQUIVALENCE:
                result = M.BinaryOp(BinaryOp.Op.NEQ,lhs,rhs);
                break;

            case IMPLIES:
                result = M.BinaryOp(BinaryOp.Op.OR,M.UnaryOp(UnaryOp.Op.NOT,lhs),rhs);
                break;

            case REVERSE_IMPLIES: // FIXME - comment on order of evaluation
                result = M.BinaryOp(BinaryOp.Op.OR,lhs,M.UnaryOp(UnaryOp.Op.NOT,rhs));
                break;
 
                // FIXME
//            case SUBTYPE_OF:
//                Name n = names.fromString("isAssignableFrom");
//                Scope.Entry e = that.rhs.type.tsym.members().lookup(n);
//                Symbol ms = e.sym;
//                JCFieldAccess m = make.Select(rhs,n);
//                m.sym = ms;
//                m.type = m.sym.type;
//
//                JCExpression c = make.Apply(null,m,List.<JCExpression>of(lhs));
//                c.setType(syms.booleanType);
//                result = c;
                // FIXME - do we intend that <: is always false among pairs of primitive types (even the same)
//                break;
                
            default:
                log.error(pos,"jml.unknown.operator",node.op.internedName(),"JmlRac");
                break;
        }
        return result;
    }

    @Override
    public Ast visitJmlFunction(JmlFunction that, Object p) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlFunction");
        return null;
    }

    @Override
    public Ast visitJmlGroupName(JmlGroupName that, Object p) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlGroupName");
        return null;
    }

    @Override
    public Ast visitJmlImport(JmlImport that, Object p) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlImport");
        return null;
    }

    @Override
    public Ast visitJmlLblExpression(JmlLblExpression that, Object p) {
//        JCExpression lit = makeLit(syms.stringType,that.label.toString());
//        JCFieldAccess m = null;
//        // FIXME - other types?
//        if (that.expression.type.tag == TypeTags.INT) {
//            m = findUtilsMethod("saveInt");
//        } else if (that.expression.type.tag == TypeTags.BOOLEAN) {
//            m = findUtilsMethod("saveBoolean");
//        } else if (that.expression.type.tag == TypeTags.CLASS) {
//            m = findUtilsMethod("saveObject");
//        }
//        JCExpression c = make.Apply(null,m,List.<JCExpression>of(lit,translate(that.expression)));
//        c.setType(that.type);
//        result = c;
        // FIXME
        return null;
    }

    @Override
    public Ast visitJmlMethodClauseAssignable(JmlMethodClauseAssignable that, Object p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Ast visitJmlMethodClauseConditional(JmlMethodClauseConditional that, Object p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Ast visitJmlMethodClauseDecl(JmlMethodClauseDecl that, Object p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Ast visitJmlMethodClauseExpr(JmlMethodClauseExpr that, Object p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Ast visitJmlMethodClauseGroup(JmlMethodClauseGroup that, Object p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Ast visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly that, Object p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Ast visitJmlMethodClauseSignals(JmlMethodClauseSignals that, Object p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Ast visitJmlMethodSpecs(JmlMethodSpecs that, Object p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Ast visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that, Object p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Ast visitJmlQuantifiedExpr(JmlQuantifiedExpr that, Object p) {
        // FIXME - implement
        return null;
    }

    @Override
    public Ast visitJmlRefines(JmlRefines that, Object p) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlRefines");
        return null;
    }

    @Override
    public Ast visitJmlSetComprehension(JmlSetComprehension that, Object p) {
        // FIXME - implement
        return null;
    }

    public Ast visitJmlSingleton(JmlSingleton that, Object o) {
        Ast result = null;
        switch (that.token) {
            case BSRESULT:
                methodInfo.resultUsed = true;
                result = M.AtomId(methodInfo.resultName,createLocation(that.pos));
                break;

            case INFORMAL_COMMENT:
                result = trueLit;
                break;
                
            case BSLOCKSET:
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
        return result;
    }
    
    @Override
    public Ast visitReturn(ReturnTree tree, Object p) {
//        super.visitReturn(tree);
//        if (methodInfo != null) {
//            if (methodInfo.resultDecl == null) {
//                // FIXME - minternal error
//            } else {
//                tree = (JCReturn)result;
//                // FIXME - what if conversions are needed?
//                JCIdent id = make.Ident(attr.resultName);
//                id.sym = methodInfo.resultDecl.sym;
//                id.type = methodInfo.resultDecl.type;
//                tree.expr = make.Assign(id,tree.expr);
//                tree.expr.type = id.type;
//            }
//        }
//        result = tree;
        // FIXME
        return null;
    }


    @Override
    public Ast visitJmlSpecificationCase(JmlSpecificationCase that, Object p) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlSpecificationCase");
        return null;
    }

    @Override
    public Ast visitJmlStatement(JmlStatement that, Object p) {
//        switch (that.token) {
//            case SET:
//            case DEBUG: // FIXME - if turned on by options
//                result = translate(that.statement);
//                break;
//                
//            default:
//                // FIXME - unimplemented
//                result = that;
//        }
        // FIXME
        return null;
    }

    @Override
    public Ast visitJmlStatementDecls(JmlStatementDecls that, Object p) {
        // FIXME - only handles the first one
        //result = translate(that.list.first());
        return null;
    }

    @Override
    public Ast visitJmlStatementLoop(JmlStatementLoop that, Object p) {
        // TODO Auto-generated method stub
        return null;

    }

    @Override
    public Ast visitJmlStatementSpec(JmlStatementSpec that, Object p) {
        // TODO Auto-generated method stub
        return null;
        
    }

    @Override
    public Ast visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that, Object p) {
        // TODO Auto-generated method stub
        return null;
       
    }

    @Override
    public Ast visitJmlStoreRefKeyword(JmlStoreRefKeyword that, Object p) {
        // TODO Auto-generated method stub
        return null;
        
    }

    @Override
    public Ast visitJmlStoreRefListExpression(JmlStoreRefListExpression that, Object p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Ast visitJmlTypeClauseConditional(JmlTypeClauseConditional that, Object p) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlTypeClauseConditional");
        return null;
    }

    @Override
    public Ast visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that, Object p) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlTypeClauseConstraint");
        return null;
    }

    @Override
    public Ast visitJmlTypeClauseDecl(JmlTypeClauseDecl that, Object p) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlTypeClauseDecl");
        return null;
    }

    @Override
    public Ast visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that, Object p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Ast visitJmlTypeClauseExpr(JmlTypeClauseExpr that, Object p) {
        log.error("jml.internal","Do not expect to ever reach this point - JmlRac.visitJmlTypeClauseExpr");
        return null;
    }

    @Override
    public Ast visitJmlTypeClauseIn(JmlTypeClauseIn that, Object p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Ast visitJmlTypeClauseMaps(JmlTypeClauseMaps that, Object p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Ast visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that, Object p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Ast visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that, Object p) {
        // TODO Auto-generated method stub
        return null;
    }
    
    @Override
    public Ast visitJmlDoWhileLoop(JmlDoWhileLoop that, Object p) {
//        if (that.loopSpecs.isEmpty()) {
//            super.visitDoLoop(that);
//            return;
//        }
//        ListBuffer<JCStatement> checks = new ListBuffer<JCStatement>();
//        ListBuffer<JCStatement> vars = new ListBuffer<JCStatement>();
//        makeLoopChecks(that.loopSpecs,checks,vars);
//        
//        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
//        stats.appendList(checks);
//        stats.append(that.body);
//        that.body = make.Block(0,stats.toList());
//        vars.append(that);
//        vars.appendList(checks);
//        result = make.Block(0,vars.toList());
//        //System.out.println("REWRITTEN " + result);
        return null;
    }

    public Ast visitJmlEnhancedForLoop(JmlEnhancedForLoop that, Object p) {
//        if (that.loopSpecs.isEmpty()) {
//            super.visitForeachLoop(that);
//            return;
//        }
//        ListBuffer<JCStatement> checks = new ListBuffer<JCStatement>();
//        ListBuffer<JCStatement> vars = new ListBuffer<JCStatement>();
//        makeLoopChecks(that.loopSpecs,checks,vars);
//        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
//        stats.appendList(vars);
//        ListBuffer<JCStatement> bodystats = new ListBuffer<JCStatement>();
//        bodystats.appendList(checks);
//        bodystats.append(translate(that.body));
//        JCEnhancedForLoop loop = make.ForeachLoop(translate(that.var), translate(that.expr), make.Block(0,bodystats.toList()));
//        stats.append(loop);
//        stats.appendList(checks);
//        result = make.Block(0,stats.toList());
        return null;
    }

    public Ast visitJmlForLoop(JmlForLoop that, Object p) {
//        if (that.loopSpecs.isEmpty()) {
//            super.visitForLoop(that);
//            return;
//        }
//        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
//        stats.appendList(translate(that.init));
//        ListBuffer<JCStatement> checks = new ListBuffer<JCStatement>();
//        ListBuffer<JCStatement> vars = new ListBuffer<JCStatement>();
//        makeLoopChecks(that.loopSpecs,checks,vars);
//        stats.appendList(vars);
//        ListBuffer<JCStatement> bodystats = new ListBuffer<JCStatement>();
//        bodystats.appendList(checks);
//        bodystats.append(translate(that.body));
//        stats.append(make.ForLoop(List.<JCStatement>nil(),translate(that.cond),translate(that.step),make.Block(0,bodystats.toList())));
//        stats.appendList(checks);
//        result = make.Block(0,stats.toList());
        return null;
    }

    @Override
    public Ast visitJmlWhileLoop(JmlWhileLoop that, Object p) {
//        if (that.loopSpecs.isEmpty()) {
//            super.visitWhileLoop(that);
//            return;
//        }
//        ListBuffer<JCStatement> checks = new ListBuffer<JCStatement>();
//        ListBuffer<JCStatement> vars = new ListBuffer<JCStatement>();
//        makeLoopChecks(that.loopSpecs,checks,vars);
//        
//        ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
//        stats.appendList(checks);
//        stats.append(that.body);
//        that.body = make.Block(0,stats.toList());
//        vars.append(that);
//        vars.appendList(checks);
//        result = make.Block(0,vars.toList());
//        //System.out.println("REWRITTEN " + result);
        return null;
    }
    
    public void makeLoopChecks(List<JmlStatementLoop> specs, ListBuffer<JCStatement> checks, ListBuffer<JCStatement> vars) {
//        for (JmlStatementLoop s: specs) {
//            if (s.token == JmlToken.LOOP_INVARIANT) {
//                String sp = position(methodInfo.source,s.pos);
//                JCStatement ss = undefinedCheck(methodInfo.owner,
//                        sp + "loop invariant",
//                        make.If(makeUnary(JCTree.NOT,translate(s.expression)),
//                                assertFailure(sp + "loop invariant is false"),null));
//                checks.append(ss);
//            } else if (s.token == JmlToken.DECREASES) {
//                int n = ++methodInfo.variableDefs;
//                Name name1 = names.fromString("_JML$$$loop"+n);
//                Name name2 = names.fromString("_JML$$$loopTemp"+n);
//                JCVariableDecl d = makeIntVarDef(name1,maxIntLit);
//                JCIdent id1 = make.Ident(name1);
//                id1.type = d.type;
//                id1.sym = d.sym;
//                vars.append(d);
//                JCExpression e = translate(s.expression);
//                JCVariableDecl dd = makeIntVarDef(name2,e);
//                JCIdent id2 = make.Ident(name2);
//                id2.type = dd.type;
//                id2.sym = dd.sym;
//                String sp = position(methodInfo.source,s.pos);
//                JCStatement ss = make.If(
//                        makeBinary(JCTree.GE,id2,id1),
//                        assertFailure(sp + "loop variant did not decrease"),null);
//                JCStatement sss = make.If(
//                        makeBinary(JCTree.LT,id2,zero),
//                        assertFailure(sp + "loop variant is less than 0"),null);
//                e = make.Assign(id1,id2);
//                e.type = id1.type;
//                JCStatement sa = make.Exec(e);
//                ss = undefinedCheck(methodInfo.owner,sp + "loop variant",
//                        List.<JCStatement>of(dd,ss,sss,sa));
//                checks.append(ss);
//            } else {
//                // FIXME - unk nownd
//            }
//        }
    }
    
    public Ast visitJmlClassDecl(JmlClassDecl that, Object p) {
        return visitClass(that,p);  // FIXME
    }

    public Ast visitJmlCompilationUnit(JmlCompilationUnit that, Object p) {
        return visitCompilationUnit(that,p);
    }

    public Ast visitJmlMethodDecl(JmlMethodDecl that, Object p) {
        return visitMethod(that,p);  // FIXME
    }

    public Ast visitJmlVariableDecl(JmlVariableDecl that, Object p) {
        return visitVariable(that,p);  // FIXME
    }

    @Override
    public Ast visitAnnotation(AnnotationTree node, Object p) {
        // Do nothing
        return null;
    }
//
//    public Ast visitArrayAccess(ArrayAccessTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitArrayType(ArrayTypeTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitAssert(AssertTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitAssignment(AssignmentTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//
//    public Ast visitBlock(BlockTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitBreak(BreakTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitCase(CaseTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitCatch(CatchTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
    @Override
    public Ast visitCompilationUnit(CompilationUnitTree node, Object p) {
        // Just scan the type declarations // FIXME - does this include the model class declarations?
        scan(node.getTypeDecls(), p);
        return null;
    }
//
//    public Ast visitCompoundAssignment(CompoundAssignmentTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitConditionalExpression(ConditionalExpressionTree node,
//            Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitContinue(ContinueTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitDoWhileLoop(DoWhileLoopTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitEmptyStatement(EmptyStatementTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitEnhancedForLoop(EnhancedForLoopTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitErroneous(ErroneousTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitExpressionStatement(ExpressionStatementTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitForLoop(ForLoopTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }

    @Override
    public Ast visitIdentifier(IdentifierTree node, Object p) {
        JCIdent tree = (JCIdent)node;
        int pos = tree.pos;
        // FIXME
//        if (tree.sym != null && tree.sym.kind == Kinds.VAR && attr.isModel(tree.sym)) {
//            Name name = names.fromString("_JML$model$" + tree.name);
//            ClassSymbol sym = classInfo.decl.sym;
//            Scope.Entry e = sym.members().lookup(name);
//            while (e.sym == null) {// FIXME - do we need to look in interfaces?
//                Type t = sym.getSuperclass();
//                if (t == null) break;
//                sym = (ClassSymbol)t.tsym;
//                e = sym.members().lookup(name);
//            }
//            if (e.sym instanceof MethodSymbol) {
//                MethodSymbol ms = (MethodSymbol)e.sym;
//                JCIdent m = make.Ident(name);
//                m.sym = ms;
//                m.type = m.sym.type;
//                JCExpression c = make.Apply(null,m,List.<JCExpression>nil());
//                c.setType(tree.type);
//                return;
//            } else {
//                System.out.println("COULD NOT FIND METHOD FOR MODEL FIELD " + tree.sym);
//                // FIXME - problem?
//            }
//        }
//        if (methodInfo != null && tree.sym == methodInfo.exceptionLocal) {
//            result = methodInfo.exceptionDecl;
//            return;
//        }
        return M.AtomId(node.getName().toString(),createLocation(pos));
    }

//    public Ast visitIf(IfTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
    @Override
    public Ast visitImport(ImportTree node, Object p) {
        // Do nothing
        return null;
    }
//
//    public Ast visitInstanceOf(InstanceOfTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitLabeledStatement(LabeledStatementTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitMemberSelect(MemberSelectTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitMethodInvocation(MethodInvocationTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
    @Override
    public Ast visitModifiers(ModifiersTree node, Object p) {
        // Do nothing
        return null;
    }
//
//    public Ast visitNewArray(NewArrayTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitNewClass(NewClassTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitOther(Tree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitParameterizedType(ParameterizedTypeTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitParenthesized(ParenthesizedTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitPrimitiveType(PrimitiveTypeTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitReturn(ReturnTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitSwitch(SwitchTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitSynchronized(SynchronizedTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitThrow(ThrowTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitTry(TryTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitTypeCast(TypeCastTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitTypeParameter(TypeParameterTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitVariable(VariableTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitWhileLoop(WhileLoopTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
//
//    public Ast visitWildcard(WildcardTree node, Object p) {
//        // TODO Auto-generated method stub
//        return null;
//    }
}
