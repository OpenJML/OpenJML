package org.jmlspecs.openjml;

import java.io.IOException;
import java.io.StringWriter;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.esc.Label;

import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.TreeVisitor;
import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeMaker;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;

// FIXME - the start and end positions are gotten from TreeInfo, which does not work for JML nodes
/** This class simply holds the classes which are JML-specific nodes of parse trees. */
public class JmlTree {

    /** Convert a tree to a pretty-printed string using the JmlPrettyPrinter; note that
     * this is not inherited by anyone, it is here as a utility method and needs
     * to be called by nodes of JmlTree. */
    static public String toString(JCTree node) {
//        StringWriter s = new StringWriter();
//        new JmlPretty(s, false).write(node);
//        return s.toString();

        StringWriter sw = new StringWriter();
        JmlPretty p = new JmlPretty(sw,true);
        p.width = 2;
        node.accept(p);
        return sw.toString();
    }


    /** This interface extends the node factory for Java parse tree nodes by adding factory
     * methods for all of the JML nodes.
     */
    public interface JmlFactory extends JCTree.Factory {
        JmlPrimitiveTypeTree JmlPrimitiveTypeTree(JmlToken jt);
        JmlSingleton JmlSingleton(JmlToken jt);
        //JmlFunction JmlFunction(JmlToken jt);
        JmlImport JmlImport(JCTree qualid, boolean staticImport);
        JmlImport JmlImport(JCTree qualid, boolean staticImport, boolean isModel);
        JmlRefines JmlRefines(String filename);
        JmlBinary JmlBinary(JmlToken t, JCTree.JCExpression left, JCTree.JCExpression right);
        JmlMethodInvocation JmlMethodInvocation(JmlToken token, List<JCExpression> args);
        JmlStatementExpr JmlExpressionStatement(JmlToken t, Label label, JCTree.JCExpression e);
        JmlStatementDecls JmlStatementDecls(ListBuffer<JCTree.JCStatement> list);
        JmlStatementSpec JmlStatementSpec(JmlMethodSpecs specs);
        JmlStatementLoop JmlStatementLoop(JmlToken t, JCTree.JCExpression e);
        JmlForLoop JmlForLoop(JCForLoop loop, List<JmlStatementLoop> loopSpecs);
        JmlEnhancedForLoop JmlEnhancedForLoop(JCEnhancedForLoop loop, List<JmlStatementLoop> loopSpecs);
        JmlWhileLoop JmlWhileLoop(JCWhileLoop loop, List<JmlStatementLoop> loopSpecs);
        JmlDoWhileLoop JmlDoWhileLoop(JCDoWhileLoop loop, List<JmlStatementLoop> loopSpecs);
        JmlStatement JmlStatement(JmlToken t, JCTree.JCStatement e);
        JmlMethodClauseGroup JmlMethodClauseGroup(List<JmlSpecificationCase> cases);
        JmlMethodClauseDecl JmlMethodClauseDecl(JmlToken t, JCTree.JCExpression type, ListBuffer<JCTree.JCStatement> stats);
        JmlMethodClauseExpr JmlMethodClauseExpr(JmlToken t, JCTree.JCExpression e);
        JmlMethodClauseConditional JmlMethodClauseConditional(JmlToken t, JCTree.JCExpression e, JCTree.JCExpression predicate);
        JmlMethodClauseSignals JmlMethodClauseSignals(JmlToken t, JCTree.JCVariableDecl var, JCTree.JCExpression e);
        JmlMethodClauseSigOnly JmlMethodClauseSignalsOnly(JmlToken t, List<JCTree.JCExpression> e);
        JmlMethodClause JmlMethodClauseStoreRef(JmlToken t, List<JCExpression> list);
        JmlModelProgramStatement JmlModelProgramStatement(JCTree item);
        JmlConstraintMethodSig JmlConstraintMethodSig(JCExpression expr, List<JCExpression> argtypes);
        JmlSpecificationCase JmlSpecificationCase(JCModifiers mods, boolean code, JmlToken t, JmlToken also, JCBlock block);
        JmlSpecificationCase JmlSpecificationCase(JCModifiers mods, boolean code, JmlToken t, JmlToken also, List<JmlMethodClause> clauses);
        JmlSpecificationCase JmlSpecificationCase(JmlSpecificationCase sc, List<JmlMethodClause> clauses);
        JmlMethodSpecs JmlMethodSpecs(List<JmlSpecificationCase> cases);
        JmlTypeClauseExpr JmlTypeClauseExpr(JCModifiers mods, JmlToken token, JCTree.JCExpression e);
        JmlTypeClauseDecl JmlTypeClauseDecl(JCTree decl);
        JmlTypeClauseInitializer JmlTypeClauseInitializer(JmlToken token);
        JmlTypeClauseConstraint JmlTypeClauseConstraint(JCModifiers mods, JCExpression e, List<JmlConstraintMethodSig> sigs);
        JmlTypeClauseRepresents JmlTypeClauseRepresents(JCModifiers mods, JCTree.JCExpression ident, boolean suchThat, JCTree.JCExpression e);
        JmlTypeClauseConditional JmlTypeClauseConditional(JCModifiers mods, JmlToken token, JCTree.JCIdent ident, JCTree.JCExpression p);
        JmlTypeClauseMonitorsFor JmlTypeClauseMonitorsFor(JCModifiers mods, JCTree.JCIdent ident, ListBuffer<JCTree.JCExpression> list);
        JmlTypeClauseIn JmlTypeClauseIn(List<JmlGroupName> list);
        JmlTypeClauseMaps JmlTypeClauseMaps(JCExpression e, List<JmlGroupName> list);
        JmlQuantifiedExpr JmlQuantifiedExpr(JmlToken token, ListBuffer<JCVariableDecl> decls, JCTree.JCExpression range, JCTree.JCExpression predicate);
        JmlSetComprehension JmlSetComprehension(JCTree.JCExpression type, JCTree.JCVariableDecl v, JCTree.JCExpression predicate);
        JmlLblExpression JmlLblExpression(JmlToken token, Name label, JCTree.JCExpression expr);
        JmlGroupName JmlGroupName(JCExpression selection);
        JmlStoreRefListExpression JmlStoreRefListExpression(JmlToken t, ListBuffer<JCExpression> list);
        JmlStoreRefArrayRange JmlStoreRefArrayRange(JCExpression expr, JCExpression lo, JCExpression hi);
        JmlStoreRefKeyword JmlStoreRefKeyword(JmlToken t);
    }
    
    /** This class is a factory for JML parse tree nodes, and by extension, all 
     * the Java parse tree nodes as well.
     */
    public static class Maker extends TreeMaker implements JmlFactory {
        
        /** The factory keeps a reference to the context in which it was
         * created, for handy use later on.
         */
        protected Context context;
        
        /** A constructor for the factory
         * @param context the compilation context with which to associate this factory
         */
        public Maker(Context context) {
            super(context);
            this.context = context;
        }
        
        /** A method with which to register this factory with the compilation 
         * unit context
         * @param context the compilation context to be associated with
         */
        public static void preRegister(final Context context) {
            context.put(treeMakerKey, new Context.Factory<TreeMaker>() {
                public TreeMaker make() {
                    return new Maker(context);
                }
            });
        }
        
        public static JmlTree.Maker instance(Context context) {
            return (JmlTree.Maker)TreeMaker.instance(context);
        }
        /** Sets the preferred token position to be used for subsequent
         * factory produced nodes, typically used like this, for example:
         * maker.at(pos).JmlPrimitiveTypeTree(token)
         * @param pos the 0-based character position from the beginning of the input file
         */
        public Maker at(int pos) {
            this.pos = pos;
            return this;
        }
        
        @Override
        public JmlCompilationUnit TopLevel(List<JCAnnotation> packageAnnotations,
                JCExpression pid,
                List<JCTree> defs) {
            JmlCompilationUnit t = new JmlCompilationUnit(packageAnnotations,
                    pid,
                    defs,
                    null,null,null,null);
            t.pos = this.pos;
            return t;
        }
        
        /** Overridden because super.Literal(value) appears to have forgotten
         * the boolean case.
         */
        @Override 
        public JCLiteral Literal(Object value) {
            if (value instanceof Boolean) {
                return super.Literal(TypeTags.BOOLEAN,(Boolean)value ? 1 : 0)
                    .setType(Symtab.instance(context).stringType.constType(value));
            } else {
                return super.Literal(value);
            }
        }
        
        public JCExpression QualIdent(Name... names) {
            JCExpression t = Ident(names[0]);
            for (int i = 1; i < names.length; i++) {
                t = Select(t,names[i]);
            }
            return t;
        }
        
        public JCExpression QualIdent(String... names) {
            Names n = Names.instance(context);
            JCExpression t = Ident(n.fromString(names[0]));
            for (int i = 1; i < names.length; i++) {
                t = Select(t,n.fromString(names[i]));
            }
            return t;
        }
        
        public JCIdent Ident(String name) {
            Names n = Names.instance(context);
            return Ident(n.fromString(name));
        }
        
        public Name Name(String name) {
            Names n = Names.instance(context);
            return n.fromString(name);
        }
        
        @Override
        public JCClassDecl ClassDef(JCModifiers mods,
                Name name,
                List<JCTypeParameter> typarams,
                JCTree extending,
                List<JCExpression> implementing,
                List<JCTree> defs) {
            JmlClassDecl tree = new JmlClassDecl(mods,name,typarams,extending,implementing,defs,null);
            tree.pos = pos;
            // In the normal course of things, context is never null, but there is a circular dependency of
            // instantiating tools that occurs in the constructors of the various tools.  In particular
            // TreeMaker -> Symtab -> ClassReader -> Annotate -> Attr -> MemberEnter -> Enter which calls
            // TreeMaker.ClassDef before TreeMaker has completed construction
            // where A -> B means A constructs B during A's construction.  This results in TreeMaker.ClassDef
            // begin called with a null context during TreeMaker's construction
            if (context != null) 
                tree.sourcefile = Log.instance(context).currentSourceFile();
            else {
                System.err.println("INTERNAL ERROR: JmlTree.ClassDef called with a null context, indicating a problem with circular dependencies in constructors.");
                new Exception().printStackTrace(System.err);
                throw new JmlInternalError();
            }
            return tree;
        }
        
        @Override
        public JCMethodDecl MethodDef(JCModifiers mods,
                Name name,
                JCExpression restype,
                List<JCTypeParameter> typarams,
                List<JCVariableDecl> params,
                List<JCExpression> thrown,
                JCBlock body,
                JCExpression defaultValue) {
            JmlMethodDecl tree = new JmlMethodDecl(mods,name,restype,typarams,params,thrown,body,defaultValue,null);
            tree.pos = pos;
            tree.sourcefile = Log.instance(context).currentSourceFile();
            return tree;
        }
        
        @Override
        public JCMethodDecl MethodDef(MethodSymbol m, Type mtype, JCBlock body) {
            return (JCMethodDecl)
                new JmlMethodDecl(
                    Modifiers(m.flags(), Annotations(m.getAnnotationMirrors())),
                    m.name,
                    Type(mtype.getReturnType()),
                    TypeParams(mtype.getTypeArguments()),
                    Params(mtype.getParameterTypes(), m),
                    Types(mtype.getThrownTypes()),
                    body,
                    null,
                    m).setPos(pos).setType(mtype);
        }

        @Override
        public JCVariableDecl VarDef(VarSymbol v, JCExpression init) {
            return 
                (JCVariableDecl) new JmlVariableDecl(
                Modifiers(v.flags(), Annotations(v.getAnnotationMirrors())),
                v.name,
                Type(v.type),
                init,
                v).setPos(pos).setType(v.type);
        }

        
        @Override
        public JCVariableDecl VarDef(JCModifiers mods,
                Name name,
                JCExpression vartype,
                JCExpression init) {
            JmlVariableDecl tree =  new JmlVariableDecl(mods,name,vartype,init,null);
            tree.pos = pos;
            tree.type = vartype.type; // attribute if the type is known
            tree.sourcefile = Log.instance(context).currentSourceFile();
            return tree;
        }

        
        public JmlPrimitiveTypeTree JmlPrimitiveTypeTree(JmlToken jt) {
            return new JmlPrimitiveTypeTree(pos,jt);
        }
        
        public JmlSingleton JmlSingleton(JmlToken jt) {
            return new JmlSingleton(pos,jt);
        }
        
        public JmlRefines JmlRefines(String filename) {
            return new JmlRefines(pos,filename);
        }
        
        // Caution: you need to set the isModel field by hand
        public JmlImport JmlImport(JCTree qualid, boolean staticImport) {
            return new JmlImport(qualid, staticImport,false);
        }
        
        public JmlImport JmlImport(JCTree qualid, boolean staticImport, boolean isModel) {
            return new JmlImport(qualid, staticImport,isModel);
        }
        
        public JmlTree.JmlImport Import(JCTree qualid, boolean staticImport) {
            return JmlImport(qualid,staticImport,false);
        }

//        public JmlFunction JmlFunction(JmlToken jt) {
//            return new JmlFunction(pos,jt);
//        }
        
        public JmlBinary JmlBinary(JmlToken t, JCTree.JCExpression left, JCTree.JCExpression right) {
            return new JmlBinary(pos,t,left,right);
        }
        public JmlMethodInvocation JmlMethodInvocation(JmlToken token,List<JCExpression> args) {
            return new JmlMethodInvocation(pos,token,args);
        }
        
        public JmlMethodInvocation JmlMethodInvocation(JCExpression method,List<JCExpression> args) {
            return new JmlMethodInvocation(pos,method,args);
        }
        
        public JmlMethodInvocation JmlMethodInvocation(JmlToken token,JCExpression arg) {
            return new JmlMethodInvocation(pos,token,List.<JCExpression>of(arg));
        }
        
        public JmlMethodInvocation JmlMethodInvocation(JmlToken token,JCExpression arg, JCExpression arg2) {
            return new JmlMethodInvocation(pos,token,List.<JCExpression>of(arg,arg2));
        }
        
//        public JmlQuantifiedExpr JmlQuantifiedExpr(JmlToken t, JCModifiers mods, JCTree.JCExpression ty, ListBuffer<Name> names, JCTree.JCExpression range, JCTree.JCExpression predicate) {
//            return new JmlQuantifiedExpr(pos,t,mods,ty,names,range,predicate);
//        }
//        
//        public JmlQuantifiedExpr JmlQuantifiedExpr(JmlToken t, JCModifiers mods, ListBuffer<JCTree.JCExpression> types, ListBuffer<Name> names, JCTree.JCExpression range, JCTree.JCExpression predicate) {
//            return new JmlQuantifiedExpr(pos,t,mods,types,names,range,predicate);
//        }
        
        public JmlQuantifiedExpr JmlQuantifiedExpr(JmlToken t, ListBuffer<JCTree.JCVariableDecl> decls, JCTree.JCExpression range, JCTree.JCExpression predicate) {
            return new JmlQuantifiedExpr(pos,t,decls,range,predicate);
        }
        
        public JmlSetComprehension JmlSetComprehension(JCTree.JCExpression type, JCTree.JCVariableDecl v, JCTree.JCExpression predicate) {
            return new JmlSetComprehension(pos,type,v,predicate);
        }
        
        public JmlLblExpression JmlLblExpression(JmlToken token, Name label, JCTree.JCExpression expr) {
            return new JmlLblExpression(pos,token,label,expr);
        }

        public JmlStatementExpr JmlExpressionStatement(JmlToken t, Label label, JCTree.JCExpression e) {
            return new JmlStatementExpr(pos,t,label,e);
        }
        
        public JmlStatementSpec JmlStatementSpec(JmlMethodSpecs specs) {
            return new JmlStatementSpec(pos,specs);
        }
        
        public JmlStatementLoop JmlStatementLoop(JmlToken t, JCTree.JCExpression e) {
            return new JmlStatementLoop(pos,t,e);
        }

        public JmlDoWhileLoop JmlDoWhileLoop(JCDoWhileLoop loop, List<JmlStatementLoop> loopSpecs) {
            return new JmlDoWhileLoop(loop,loopSpecs);
        }
        
        @Override
        public JCForLoop ForLoop(List<JCStatement> init,
                JCExpression cond,
                List<JCExpressionStatement> step,
                JCStatement body)
        {
            JCForLoop tree = super.ForLoop(init, cond, step, body);
            tree.pos = pos;
            return JmlForLoop(tree,null);
        }
        
        @Override
        public JCEnhancedForLoop ForeachLoop(JCVariableDecl var, JCExpression expr, JCStatement body) {
            JCEnhancedForLoop tree = super.ForeachLoop(var, expr, body);
            tree.pos = pos;
            return JmlEnhancedForLoop(tree,null);
        }
        
        public JCDoWhileLoop DoLoop(JCStatement body, JCExpression cond) {
            JCDoWhileLoop tree = super.DoLoop(body, cond);
            tree.pos = pos;
            return JmlDoWhileLoop(tree,null);
        }

        @Override
        public JCWhileLoop WhileLoop(JCExpression cond, JCStatement body) {
            JCWhileLoop tree = super.WhileLoop(cond, body);
            tree.pos = pos;
            return JmlWhileLoop(tree,null);
        }



        public JmlForLoop JmlForLoop(JCForLoop loop, List<JmlStatementLoop> loopSpecs) {
            return new JmlForLoop(loop,loopSpecs);
        }
        
        public JmlEnhancedForLoop JmlEnhancedForLoop(JCEnhancedForLoop loop, List<JmlStatementLoop> loopSpecs) {
            return new JmlEnhancedForLoop(loop,loopSpecs);
        }
        
        public JmlWhileLoop JmlWhileLoop(JCWhileLoop loop, List<JmlStatementLoop> loopSpecs) {
            return new JmlWhileLoop(loop,loopSpecs);
        }

        public JmlStatementDecls JmlStatementDecls(ListBuffer<JCTree.JCStatement> list) {
            return new JmlStatementDecls(pos,list);
        }
        
        public JmlStatement JmlStatement(JmlToken t, JCTree.JCStatement e) {
            return new JmlStatement(pos,t,e);
        }

        public JmlStoreRefListExpression JmlStoreRefListExpression(JmlToken t, ListBuffer<JCExpression> list) {
            return new JmlStoreRefListExpression(pos,t,list);
        }

        public JmlStoreRefKeyword JmlStoreRefKeyword(JmlToken t) {
            return new JmlStoreRefKeyword(pos,t);
        }

        public JmlStoreRefArrayRange JmlStoreRefArrayRange(JCExpression expr, JCExpression lo, JCExpression hi) {
            return new JmlStoreRefArrayRange(pos,expr,lo,hi);
        }

        public JmlTypeClauseExpr JmlTypeClauseExpr(JCModifiers mods, JmlToken token, JCTree.JCExpression e) {
            JmlTypeClauseExpr t = new JmlTypeClauseExpr(pos,mods,token,e);
            t.source = Log.instance(context).currentSourceFile();
            return t;
        }
        
//        @Override
//        public JmlTypeClauseDecl JmlTypeClauseDecl(List<JCTree> list) {
//            JmlTypeClauseDecl t = new JmlTypeClauseDecl(pos,list);
//            t.source = Log.instance(context).currentSource();
//            return t;
//        }
        
        public JmlTypeClauseDecl JmlTypeClauseDecl(JCTree tt) {
            JmlTypeClauseDecl t = new JmlTypeClauseDecl(pos,tt);
            t.source = Log.instance(context).currentSourceFile();
            return t;
        }
        
        public JmlTypeClauseInitializer JmlTypeClauseInitializer(JmlToken token) {
            JmlTypeClauseInitializer t = new JmlTypeClauseInitializer(pos, token);
            t.source = Log.instance(context).currentSourceFile();
            return t;
        }
        
        public JmlTypeClauseConstraint JmlTypeClauseConstraint(JCModifiers mods, JCTree.JCExpression e, List<JmlConstraintMethodSig> sigs) {
            JmlTypeClauseConstraint t = new JmlTypeClauseConstraint(pos,mods,e,sigs);
            t.source = Log.instance(context).currentSourceFile();
            return t;
        }
        
        public JmlConstraintMethodSig JmlConstraintMethodSig(JCExpression expr, List<JCExpression> argtypes) {
            return new JmlConstraintMethodSig(pos,expr,argtypes);
        }

        
        public JmlTypeClauseRepresents JmlTypeClauseRepresents(JCModifiers mods, JCTree.JCExpression ident, boolean suchThat, JCTree.JCExpression e) {
            JmlTypeClauseRepresents t = new JmlTypeClauseRepresents(pos, mods, ident,suchThat,e);
            t.source = Log.instance(context).currentSourceFile();
            return t;
        }

        public JmlTypeClauseConditional JmlTypeClauseConditional(JCModifiers mods, JmlToken token, JCTree.JCIdent ident, JCTree.JCExpression p) {
            JmlTypeClauseConditional t = new JmlTypeClauseConditional(pos, mods, token,ident,p);
            t.source = Log.instance(context).currentSourceFile();
            return t;
        }

        public JmlTypeClauseMonitorsFor JmlTypeClauseMonitorsFor(JCModifiers mods, JCTree.JCIdent ident, ListBuffer<JCTree.JCExpression> list) {
            JmlTypeClauseMonitorsFor t = new JmlTypeClauseMonitorsFor(pos, mods, ident, list);
            t.source = Log.instance(context).currentSourceFile();
            return t;
        }

        public JmlMethodClauseGroup JmlMethodClauseGroup(List<JmlSpecificationCase> list) {
            return new JmlMethodClauseGroup(pos,list);
        }
        
        public JmlMethodClauseDecl JmlMethodClauseDecl(JmlToken t, JCTree.JCExpression type, ListBuffer<JCTree.JCStatement> stats) {
            return new JmlMethodClauseDecl(pos,t,type,stats);
        }
        
        public JmlMethodClauseExpr JmlMethodClauseExpr(JmlToken t, JCTree.JCExpression e) {
            return new JmlMethodClauseExpr(pos,t,e);
        }
        
        public JmlMethodClauseConditional JmlMethodClauseConditional(JmlToken t, JCTree.JCExpression e, JCTree.JCExpression p) {
            return new JmlMethodClauseConditional(pos,t,e,p);
        }
        
        public JmlMethodClauseSignals JmlMethodClauseSignals(JmlToken t, JCTree.JCVariableDecl var, JCTree.JCExpression e) {
            return new JmlMethodClauseSignals(pos,t,var,e);
        }
        
        public JmlMethodClauseSigOnly JmlMethodClauseSignalsOnly(JmlToken t, List<JCTree.JCExpression> e) {
            return new JmlMethodClauseSigOnly(pos,t,e);
        }

        public JmlMethodClauseStoreRef JmlMethodClauseStoreRef(JmlToken t, List<JCExpression> list) {
            return new JmlMethodClauseStoreRef(pos, t, list);
        }

        public JmlModelProgramStatement JmlModelProgramStatement(JCTree item) {
            return new JmlModelProgramStatement(pos, item);
        }

        public JmlSpecificationCase JmlSpecificationCase(JCModifiers mods, boolean code, JmlToken t, JmlToken also, List<JmlMethodClause> clauses) {
            JmlSpecificationCase jcase = new JmlSpecificationCase(pos,mods,code,t,also,clauses);
            jcase.sourcefile = Log.instance(context).currentSourceFile();
            return jcase;
        }
        
        public JmlSpecificationCase JmlSpecificationCase(JCModifiers mods, boolean code, JmlToken t, JmlToken also, JCBlock block) {
            JmlSpecificationCase jcase = new JmlSpecificationCase(pos,mods,code,t,also,block);
            jcase.sourcefile = Log.instance(context).currentSourceFile();
            return jcase;
        }
        
        public JmlSpecificationCase JmlSpecificationCase(JmlSpecificationCase sc, List<JmlMethodClause> clauses) {
            return new JmlSpecificationCase(sc,clauses);
        }
        
        public JmlMethodSpecs JmlMethodSpecs(List<JmlSpecificationCase> cases) {
            return new JmlMethodSpecs(pos,cases);
        }
        
        public JmlGroupName JmlGroupName(JCExpression selection) {
            return new JmlGroupName(pos,selection);
        }
        
        public JmlTypeClauseIn JmlTypeClauseIn(List<JmlGroupName> list) {
            JmlTypeClauseIn r = new JmlTypeClauseIn(pos,list);
            r.source = Log.instance(context).currentSourceFile();
            return r;
        }
        
        public JmlTypeClauseMaps JmlTypeClauseMaps(JCExpression e, List<JmlGroupName> list) {
            JmlTypeClauseMaps r = new JmlTypeClauseMaps(pos,e,list);
            r.source = Log.instance(context).currentSourceFile();
            return r;
        }

    }
    
    // IMPLEMENTATION NOTES:
    // The getTag method returns an int value that identifies the sort of node.
    // It is supposed to be used in preference to instanceof to determine subtypes.
    // Here we just expand on the numbers used in JCTree.
    //
    // The getKind method appears to have the same purpose, except that it is 
    // an Enum, which cannot be expanded.  getKind is used only a few occasions.
    // Here,the getKind method is implemented to return Kind.OTHER.  This is because
    // this method returns a Kind of node, but Kind is an enum of Java node kinds
    // and cannot be extended.  We use OTHER, despite the warning in Tree.java,
    // because there is no other option, besides null.  For JML nodes we don't
    // use this anyway (because of this problem).  

    // FIXME - fix toString
    
    // These numbers used for getTag();
    
    public static final int JMLFUNCTION = JCTree.LETEXPR + 100;  // The 100 is just to give some space, just in case LETEXPR stops being the largest tag number
    public static final int JMLBINARY = JMLFUNCTION + 1;
    public static final int JMLSTATEMENT = JMLBINARY + 1;
    public static final int JMLSTATEMENTSPEC = JMLBINARY + 1;
    public static final int JMLSTATEMENTLOOP = JMLSTATEMENTSPEC + 1;
    public static final int JMLSTATEMENTEXPR = JMLSTATEMENTLOOP + 1;
    public static final int JMLSTATEMENTDECLS = JMLSTATEMENTEXPR + 1;
    public static final int JMLMETHODCLAUSEGROUP = JMLSTATEMENTDECLS + 1;
    public static final int JMLMETHODCLAUSEDECL = JMLMETHODCLAUSEGROUP + 1;
    public static final int JMLMETHODCLAUSEEXPR = JMLMETHODCLAUSEDECL + 1;
    public static final int JMLMETHODCLAUSECONDITIONAL = JMLMETHODCLAUSEEXPR + 1;
    public static final int JMLMETHODCLAUSESIGNALS = JMLMETHODCLAUSECONDITIONAL + 1;
    public static final int JMLMETHODCLAUSESIGNALSONLY = JMLMETHODCLAUSESIGNALS + 1;
    public static final int JMLMETHODCLAUSEASSIGNABLE = JMLMETHODCLAUSESIGNALSONLY + 1;
    public static final int JMLMETHODSPECS = JMLMETHODCLAUSEASSIGNABLE + 1;
    public static final int JMLSPECIFICATIONCASE = JMLMETHODSPECS + 1;
    public static final int JMLPRIMITIVETYPETREE = JMLSPECIFICATIONCASE + 1;
    public static final int JMLQUANTIFIEDEXPR = JMLPRIMITIVETYPETREE + 1;
    public static final int JMLSETCOMPREHENSION = JMLQUANTIFIEDEXPR + 1;
    public static final int JMLLBLEXPR = JMLSETCOMPREHENSION + 1;
    public static final int JMLSINGLETON = JMLLBLEXPR + 1;
    public static final int JMLREFINES = JMLSINGLETON + 1;
    public static final int JMLTYPECLAUSEEXPR = JMLREFINES + 1;
    public static final int JMLTYPECLAUSEDECL = JMLTYPECLAUSEEXPR + 1;
    public static final int JMLTYPECLAUSEREPRESENTS = JMLTYPECLAUSEDECL + 1;
    public static final int JMLTYPECLAUSECONSTRAINT = JMLTYPECLAUSEREPRESENTS + 1;
    public static final int JMLCONSTRAINTMETHODSIG = JMLTYPECLAUSECONSTRAINT + 1;
    public static final int JMLTYPECLAUSEINITIALIZER = JMLCONSTRAINTMETHODSIG + 1;
    public static final int JMLTYPECLAUSECONDITIONAL = JMLTYPECLAUSEINITIALIZER + 1;
    public static final int JMLTYPECLAUSEMONITORSFOR = JMLTYPECLAUSECONDITIONAL + 1;
    public static final int JMLGROUPNAME = JMLTYPECLAUSEMONITORSFOR + 1;
    public static final int JMLTYPECLAUSEIN = JMLGROUPNAME + 1;
    public static final int JMLTYPECLAUSEMAPS = JMLTYPECLAUSEIN + 1;
    public static final int JMLSTOREREFKEYWORD = JMLTYPECLAUSEMAPS + 1;
    public static final int JMLSTOREREFLISTEXPR = JMLSTOREREFKEYWORD + 1;
    public static final int JMLSTOREREFIDENT = JMLSTOREREFLISTEXPR + 1;
    public static final int JMLSTOREREFFIELD = JMLSTOREREFIDENT + 1;
    public static final int JMLSTOREREFARRAYRANGE = JMLSTOREREFFIELD + 1;
    public static final int JMLLASTTAG = JMLSTOREREFARRAYRANGE;

    public interface JmlSource {
        JavaFileObject source();
    }
    
    /** This class adds some JML specific information to the JCCompilationUnit toplevel node. */
    public static class JmlCompilationUnit extends JCTree.JCCompilationUnit {
        /** This field contains the AST of the refines clause, or null if there is none for this compilation unit. */
        public /*@ nullable */ JmlRefines refinesClause = null;
        
        /** This list contains the parse trees of the sequence of specification files, if any, for this compilation unit. */
        public /*@ nullable */ java.util.List<JmlCompilationUnit> specsSequence = null;
        
        /** This list contains the top-level model types declared in this compilation unit; this
         * is not necessarily all or even part of the top-level model types that the CUs specifications
         * specify, since (a) other spec files may contribute top-level model types 
         * and (b) this CU may not be part of its own spec sequence.
         */
        public java.util.List<JmlClassDecl> parsedTopLevelModelTypes = new java.util.LinkedList<JmlClassDecl>();
        
        /** This list is the set of top-level model types specified by the
         * CUs specifications.  It is assembled when types are entered in JmlEnter.
         */
        public java.util.List<JmlClassDecl> specsTopLevelModelTypes = new java.util.LinkedList<JmlClassDecl>();

        /** The use to be made of this parse tree - one of the int constants below. */
        public int mode = 0; // init to an unknown value
        
        /** An unspecified value. */
        public static final int UNKNOWN = 0; 
        
        // Properties are encoded as bits:
        // Note that a specification file can be .java or not .java
        //  1-bit  this is a file that can contain source code (i.e. has a .java suffix)
        //  2-bit  this is a specification file
        //  4-bit  the Java is in a binary file, not a source file
        //  8-bit  full typechecking is desired - FIXME - implement
        
        /** Process the java source fully, including method bodies and field initializers. */
        public static final int JAVA_SOURCE_FULL = 1; 
        
        /** Process the java source for signatures and specifications only. */
        public static final int JAVA_SOURCE_PARTIAL = 9;
        
        /** Process the java source for signatures and specifications only. */
        public static final int JAVA_AS_SPEC_FOR_SOURCE = 3;
        
        /** Process the java source for signatures and specifications only. */
        public static final int JAVA_AS_SPEC_FOR_BINARY = 7;
        
        /** This is a specification file for Java source */
        public static final int SPEC_FOR_SOURCE = 2;
        
        /** This is a specification file, belonging to a Java class file (no java source) */
        public static final int SPEC_FOR_BINARY = 6;

        /** This is a specification file but there is no Java source or binary file */
        //public static final int SPEC_ALONE = ?;
        
        static public boolean isJava(int mode) { return (mode & 1) != 0; }
        
        static public boolean isSpec(int mode) { return (mode & 2) != 0; }
        
        static public boolean isForSource(int mode) { return (mode & 4) == 0; }
        
        static public boolean isForBinary(int mode) { return (mode & 4) != 0; }
        
        static public boolean isFull(int mode) { return (mode & 8) == 0; }

        public JmlCompilationUnit(List<JCAnnotation> packageAnnotations,
                JCExpression pid,
                List<JCTree> defs,
                JavaFileObject sourcefile,
                PackageSymbol packge,
                Scope namedImportScope,
                Scope starImportScope) {
            super(packageAnnotations,pid,defs,sourcefile,packge,namedImportScope,starImportScope);
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlCompilationUnit(this); 
            } else {
                //System.out.println("A JmlCompilationUnit expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlCompilationUnit(this, d);
            } else {
                //System.out.println("A JmlCompilationUnit expects a JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
        @Override
        public String toString() {
            return JmlTree.toString(this);
        }
    }
        
    public static class JmlImport extends JCTree.JCImport {
        public boolean isModel = false;
        protected JmlImport(JCTree qualid, boolean importStatic, boolean isModel) {
            super(qualid,importStatic);
            this.isModel = isModel;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlImport(this); 
            } else {
                //System.out.println("A JmlImport expects an IJmlVisitor, not a " + v.getClass()); // FIXME;
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlImport(this, d);
            } else {
                //System.out.println("A JmlImport expects a JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
        public String toString() {
            return JmlTree.toString(this);
        }

    }
    
    public static class JmlRefines extends JCTree {
        public String filename;
        public JmlRefines(int pos, String filename) {
            this.pos = pos;
            this.filename = filename;
        }

        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLREFINES;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlRefines(this); 
            } else {
                System.out.println("A JmlRefines expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlRefines(this, d);
            } else {
                System.out.println("A JmlRefines expects a JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
        
        @Override
        public String toString() {
            return JmlTree.toString(this);
        }

   }
      
    /** This class adds some JML specific information to the JCClassDecl toplevel node. */
    public static class JmlClassDecl extends JCTree.JCClassDecl implements JmlSource {
        /** This is a list of type declarations from the specs files that refine
         * the owning class. The list is in reverse order from the specs
         * sequence. That is, the least-refined file (the tail of the specs
         * sequence) is the first in this list, if it refines this particular
         * class, and the most refined file (the beginning of the 'refines'
         * declaration chain) would be last. A null value is legal and
         * corresponds to an empty list.
         */
        public java.util.List<JmlClassDecl> specsDecls;

        /* This field is the combination of specifications from all
         * specification sources (valid for the Java declaration, or, for
         * binary files, for the most refined specs file)
         */        
        public JmlSpecs.TypeSpecs typeSpecsCombined; 
        
        /** This field holds the class-level specifications given in this 
         * particular class declaration; it may not be all the specs of the class.
         */
        public JmlSpecs.TypeSpecs typeSpecs;

        /** The Java or spec source file from which this class declaration was parsed. */
        public JavaFileObject sourcefile;

        /** The top-level tree that this class declaration (perhaps indirectly) belongs to. */
        public JmlCompilationUnit toplevel;
        
        /** The scope environment just inside this class (e.g. with type parameters
         * added.  Not set or used in parsing; set during the enter phase and
         * used there and during type attribution.
         */
        public Env<AttrContext> env;
        
        public JmlClassDecl(JCModifiers mods, Name name,
                List<JCTypeParameter> typarams, JCTree extending,
                List<JCExpression> implementing, List<JCTree> defs,
                ClassSymbol sym) {
            super(mods, name, typarams, extending, implementing, defs, sym);
            specsDecls = null;
            typeSpecs = null;
            sourcefile = null;
        }
        
        public String docComment = null;
        
        public JavaFileObject source() { return sourcefile; }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlClassDecl(this); 
            } else {
                //System.out.println("A JmlClassDecl expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlClassDecl(this, d);
            } else {
                //System.out.println("A JmlClassDecl expects a JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
        public String toString() {
            return JmlTree.toString(this);
        }
    }

    /** This class adds some JML specific information to the JCMethodDecl node. */
    public static class JmlMethodDecl extends JCTree.JCMethodDecl implements JmlSource {
        public JmlMethodDecl specsDecl;
        public JmlMethodSpecs cases;
        public JmlSpecs.MethodSpecs methodSpecsCombined;
        public JmlClassDecl owner;
        public JavaFileObject sourcefile;
        public String docComment = null;
        
        public JmlMethodDecl(JCModifiers mods, Name name, JCExpression restype,
                List<JCTypeParameter> typarams, List<JCVariableDecl> params,
                List<JCExpression> thrown, JCBlock body,
                JCExpression defaultValue, MethodSymbol sym) {
            super(mods, name, restype, typarams, params, thrown, body, defaultValue, sym);
            specsDecl = null;
            sourcefile = null;
        }
        
        public JavaFileObject source() { return sourcefile; }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodDecl(this); 
            } else {
                //System.out.println("A JmlMethodDecl expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodDecl(this, d);
            } else {
                //System.out.println("A JmlMethodDecl expects a JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
        public String toString() {
            return JmlTree.toString(this);
        }

    }
    
    /** This class represents JML function invocations (e.g. \typeof, \old, ...) */
    // FIXME - this is not really a proper subclass of its parent
    public static class JmlMethodInvocation extends JCMethodInvocation {
        public JmlToken token;
        public Label label = null;
        
        protected JmlMethodInvocation(int pos,
                JmlToken token,
                List<JCExpression> args)
        {
            super(List.<JCExpression>nil(),null,args);
            this.token = token;
            this.pos = pos;
        }
        
        protected JmlMethodInvocation(int pos,
                JCExpression method,
                List<JCExpression> args)
        {
            super(List.<JCExpression>nil(),method,args);
            this.token = null;
            this.pos = pos;
        }
        
        @Override
        public void accept(Visitor v) { 
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodInvocation(this); 
            } else {
                //System.out.println("A JmlVariableDecl expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodInvocation(this, d);
            } else {
                //System.out.println("A JmlVariableDecl expects a JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
        public int getTag() {
            return JMLFUNCTION;
        }

    }

    /** This class adds some JML specific information to the JCVariableDecl node. */
    public static class JmlVariableDecl extends JCTree.JCVariableDecl implements JmlSource {
        public JmlVariableDecl specsDecl;
        public JmlSpecs.FieldSpecs fieldSpecs;
        public JmlSpecs.FieldSpecs fieldSpecsCombined;
        public JavaFileObject sourcefile;
        public String docComment = null;
        
        public JmlVariableDecl(JCModifiers mods, Name name,
                JCExpression vartype, JCExpression init, VarSymbol sym) {
            super(mods, name, vartype, init, sym);
            specsDecl = null;
            fieldSpecs = null;
            fieldSpecsCombined = null;
            sourcefile = null;
        }
        
        public JavaFileObject source() { return sourcefile; }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlVariableDecl(this); 
            } else {
                //System.out.println("A JmlVariableDecl expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlVariableDecl(this, d);
            } else {
                //System.out.println("A JmlVariableDecl expects a JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
        public String toString() {
            return JmlTree.toString(this);
        }

    }

//    /** This class represents JML method name of constructs take arguments. */
//    public static class JmlFunction extends JmlExpression {
//        public JmlToken token;
//        
//        protected JmlFunction(int pos, JmlToken token) {
//            this.pos = pos;
//            this.token = token;
//        }
//
//        public Kind getKind() { 
//            return Kind.OTHER; // See note above
//        }
//        
//        @Override
//        public int getTag() {
//            return JMLFUNCTION;
//        }
//        
//        @Override
//        public String toString() {
//            return token.internedName();
//        }
//
//        @Override
//        public void accept(Visitor v) {
//            if (v instanceof IJmlVisitor) {
//                ((IJmlVisitor)v).visitJmlFunction(this); 
//            } else {
//                //System.out.println("A JmlFunction expects an IJmlVisitor, not a " + v.getClass());
//                //super.accept(v);
//            }
//        }
//
//        @Override
//        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
//            if (v instanceof JmlTreeVisitor) {
//                return ((JmlTreeVisitor<R,D>)v).visitJmlFunction(this, d);
//            } else {
//                //System.out.println("A JmlFunction expects a JmlTreeVisitor, not a " + v.getClass());
//                return null; //return super.accept(v,d);
//            }
//        }
//    }

    /** This class represents JML functions that take a list of store-refs as arguments. */
    public static class JmlStoreRefListExpression extends JmlExpression {
        public JmlToken token;
        public ListBuffer<JCExpression> list;
        
        protected JmlStoreRefListExpression(int pos, JmlToken token, ListBuffer<JCExpression> list) {
            this.pos = pos;
            this.token = token;
            this.list = list;
        }

        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLSTOREREFLISTEXPR;
        }
        
        @Override
        public String toString() {
            return token.internedName();
        }

        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlStoreRefListExpression(this); 
            } else {
                //System.out.println("A JmlStoreRefListExpression expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
                for (JCTree t: list) t.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlStoreRefListExpression(this, d);
            } else {
                //System.out.println("A JmlStoreRefListExpression expects a JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
    }

    /** This class represents JML expression constructs which do not have arguments (syntactically). */
    public static class JmlSingleton extends JmlExpression {
        public JmlToken token;
        public Symbol symbol;  // Convenience for some node types
        public Object info = null;
        
        protected JmlSingleton(int pos, JmlToken token) {
            this.pos = pos;
            this.token = token;
        }

        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLSINGLETON;
        }
        
        public String toString() {
            return token.internedName();
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlSingleton(this); 
            } else {
                //System.out.println("A JmlSingleton expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlSingleton(this,d); 
            } else {
                System.out.println("A JmlSingleton expects a JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
    }

    abstract public static class JmlExpression extends JCTree.JCExpression {
        public String toString() {
            return JmlTree.toString(this);
        }
    }
    
    /** This class represents binary expressions with JML operators */
    public static class JmlBinary extends JmlExpression implements BinaryTree {
        public JmlToken op;
        public JCExpression lhs;
        public JCExpression rhs;
        protected JmlBinary(int pos, JmlToken op,
                JCExpression lhs,
                JCExpression rhs) {
            this.pos = pos;
            this.op = op;
            this.lhs = lhs;
            this.rhs = rhs;
        }
        
        /** A shallow copy constructor */
        protected JmlBinary(JmlBinary that) {
            this.op = that.op;
            this.lhs = that.lhs;
            this.rhs = that.rhs;
            this.pos = that.pos;
            this.type = that.type;
        }

        public JCExpression getLeftOperand() { return lhs; }
        public JCExpression getRightOperand() { return rhs; }

//        public Symbol getOperator() {
//            return null; // FIXME
//        }

        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLBINARY;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlBinary(this); 
            } else {
                System.out.println("A JmlBinary expects an IJmlVisitor, not a " + v.getClass());
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlBinary(this, d);
            } else {
                System.out.println("A JmlBinary expects a JmlTreeVisitor, not a " + v.getClass());
                return null;
            }
        }
        
    }

    /** This class represents JML LBL expressions */
    public static class JmlLblExpression extends JmlExpression {
        public JmlToken token;
        public Name label;
        public JCExpression expression;
        protected JmlLblExpression(int pos, JmlToken token, Name label, JCTree.JCExpression expr) {
            this.pos = pos;
            this.token = token;
            this.label = label;
            this.expression = expr;
        }

        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLLBLEXPR;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlLblExpression(this); 
            } else {
                //System.out.println("A JmlLblExpression expects an IJmlVisitor, not a " + v.getClass());
                expression.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlLblExpression(this, d);
            } else {
                System.out.println("A JmlLblExpression expects an JmlTreeVisitor, not a " + v.getClass());
                return null; // return super.accept(v,d);
            }
        }
    }

    /** This class represents JML quantified expressions */
    public static class JmlQuantifiedExpr extends JmlExpression {
        // Current JML allows multiple bound variables in a quantified expression,
        // but requires them all to have the same type.  However, in anticipation of
        // relaxing this requirement and for use elsewhere (i.e. in ESC) this
        // class permits different types.
        public JmlToken op;
//        public ListBuffer<Name> names;
//        public JCModifiers modifiers;
//        public ListBuffer<JCExpression> localtypes;
        public JCExpression range;
        public ListBuffer<JCVariableDecl> decls;
        public JCExpression predicate;
        protected JmlQuantifiedExpr(int pos, JmlToken op,
                ListBuffer<JCVariableDecl> decls,
                JCExpression range, JCExpression predicate) {
            this.pos = pos;
            this.op = op;
            this.decls = decls;
            this.range = range;
            this.predicate = predicate;
        }

//        protected JmlQuantifiedExpr(int pos, JmlToken op, JCModifiers mods,
//                JCExpression localtype, ListBuffer<Name> names,
//                JCExpression range, JCExpression predicate) {
//            this.pos = pos;
//            this.op = op;
//            this.modifiers = mods;
//            this.names = names;
//            this.localtypes = new ListBuffer<JCExpression>();
//            int i = names.size();
//            while (--i >= 0) this.localtypes.append(localtype);
//            this.range = range;
//            this.predicate = predicate;
//        }

//        protected JmlQuantifiedExpr(int pos, JmlToken op, JCModifiers mods,
//                ListBuffer<JCExpression> localtypes, ListBuffer<Name> names,
//                JCExpression range, JCExpression predicate) {
//            this.pos = pos;
//            this.op = op;
//            this.modifiers = mods;
//            this.names = names;
//            this.localtypes = localtypes;
//            this.range = range;
//            this.predicate = predicate;
//        }

        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLQUANTIFIEDEXPR;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlQuantifiedExpr(this); 
            } else {
                //System.out.println("A JmlQuantifiedExpr expects an IJmlVisitor, not a " + v.getClass());
                // super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlQuantifiedExpr(this, d);
            } else {
                System.out.println("A JmlQuantifiedExpr expects an JmlTreeVisitor, not a " + v.getClass());
                return null; // return super.accept(v,d);
            }
        }
    }
    
    /** This class represents JML quantified expressions */
    public static class JmlSetComprehension extends JmlExpression {
        public JCExpression newtype;
        public JCVariableDecl variable;
        public JCExpression predicate;
        protected JmlSetComprehension(int pos, JCExpression type, JCVariableDecl var, JCExpression predicate) {
            this.pos = pos;
            this.newtype = type;
            this.variable = var;
            this.predicate = predicate;
        }

        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLSETCOMPREHENSION;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlSetComprehension(this); 
            } else {
                //System.out.println("A JmlSetComprehension expects an IJmlVisitor, not a " + v.getClass());
                // super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlSetComprehension(this, d);
            } else {
                System.out.println("A JmlSetComprehension expects an JmlTreeVisitor, not a " + v.getClass());
                return null; // return super.accept(v,d);
            }
        }
    }
    
    /** This class is simply a superclass for all AST classes representing 
     * statements within the body of a method.  From a Java perspective, these
     * need to behave like Skip statements.
     */
    public static abstract class JmlAbstractStatement extends JCTree.JCSkip {
        public String toString() {
            return JmlTree.toString(this);
        }
    }

    /** This class represents JML statements within the body of a method
     * that take a statement, such as set and debug
     */
    public static class JmlStatement extends JmlAbstractStatement {
        public JmlStatement(int pos, JmlToken token, JCTree.JCStatement statement) {
            this.pos = pos;
            this.token = token;
            this.statement = statement;
        }
        public JmlToken token;
        public JCTree.JCStatement statement;
        
        @Override
        public int getTag() {
            return JMLSTATEMENT;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlStatement(this); 
            } else {
                //System.out.println("A JmlStatement expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlStatement(this, d);
            } else {
                //System.out.println("A JmlStatement expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    
    /** This class represents JML method specifications within the body of a method
     * that then apply to the next statement (FIXME - this is not implemented in JML yet)
     */
    public static class JmlStatementSpec extends JmlAbstractStatement {
        public JmlStatementSpec(int pos, JmlMethodSpecs statementSpecs) {
            this.pos = pos;
            this.statementSpecs = statementSpecs;
        }
        public JmlMethodSpecs statementSpecs;

        @Override
        public int getTag() {
            return JMLSTATEMENTSPEC;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlStatementSpec(this); 
            } else {
                //System.out.println("A JmlStatementSpec expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlStatementSpec(this, d);
            } else {
                //System.out.println("A JmlStatementSpec expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    
    /** This class represents JML statements within the body of a method
     * that apply to a following loop statement (decreases, loop_invariant)
     */    // FIXME - should this really keep source - it is the same as the enclosing method
    public static class JmlStatementLoop extends JmlAbstractStatement implements JmlSource {
        public JmlStatementLoop(int pos, JmlToken token, JCTree.JCExpression expression) {
            this.pos = pos;
            this.token = token;
            this.expression = expression;
        }
        public JmlToken token;
        public JCTree.JCExpression expression;
        public int line;
        public JavaFileObject source;

        public JavaFileObject source() {
            return source;
        }
        
        @Override
        public int getTag() {
            return JMLSTATEMENTLOOP;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlStatementLoop(this); 
            } else {
                //System.out.println("A JmlStatementLoop expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlStatementLoop(this, d);
            } else {
                //System.out.println("A JmlStatementLoop expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }

    
    /** This class wraps a Java while loop just so it can attach some specs
     * to it.
     */
    public static class JmlWhileLoop extends JCWhileLoop {
        public JmlWhileLoop(JCWhileLoop loop, List<JmlStatementLoop> loopSpecs) {
            super(loop.cond,loop.body);
            this.pos = loop.pos;
            this.type = loop.type;
            this.loopSpecs = loopSpecs;
        }
        public List<JmlStatementLoop> loopSpecs;

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlWhileLoop(this); 
            } else {
                //System.out.println("A JmlWhileLoop expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlWhileLoop(this, d);
            } else {
                //System.out.println("A JmlWhileLoop expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
        public String toString() {
            return JmlTree.toString(this);
        }

    }

    /** This class wraps a Java for loop just so it can attach some specs
     * to it.
     */
    public static class JmlForLoop extends JCForLoop {
        public JmlForLoop(JCForLoop loop, List<JmlStatementLoop> loopSpecs) {
            super(loop.init,loop.cond,loop.step,loop.body);
            this.pos = loop.pos;
            this.type = loop.type;
            this.loopSpecs = loopSpecs;
        }
        public List<JmlStatementLoop> loopSpecs;

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlForLoop(this); 
            } else {
                //System.out.println("A JmlForLoop expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlForLoop(this, d);
            } else {
                //System.out.println("A JmlForLoop expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
        public String toString() {
            return JmlTree.toString(this);
        }

    }

    /** This class wraps a Java enhanced loop just so it can attach some specs
     * to it.
     */
    public static class JmlEnhancedForLoop extends JCEnhancedForLoop {
        public JmlEnhancedForLoop(JCEnhancedForLoop loop, List<JmlStatementLoop> loopSpecs) {
            super(loop.var, loop.expr, loop.body);
            this.pos = loop.pos;
            this.type = loop.type;
            this.loopSpecs = loopSpecs;
        }
        public List<JmlStatementLoop> loopSpecs;
        
        // These are used for rewriting the loop in JmlAttr
        public JCVariableDecl indexDecl;
        public JCVariableDecl valuesDecl;
        public JCVariableDecl iterDecl;
        public JCBlock implementation;

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlEnhancedForLoop(this); 
            } else {
                //System.out.println("A JmlEnhancedForLoop expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlEnhancedForLoop(this, d);
            } else {
                //System.out.println("A JmlEnhancedForLoop expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
        public String toString() {
            return JmlTree.toString(this);
        }

    }

    /** This class wraps a Java do while loop just so it can attach some specs
     * to it.
     */
    public static class JmlDoWhileLoop extends JCDoWhileLoop {
        public JmlDoWhileLoop(JCDoWhileLoop loop, List<JmlStatementLoop> loopSpecs) {
            super(loop.body,loop.cond);
            this.pos = loop.pos;
            this.type = loop.type;
            this.loopSpecs = loopSpecs;
        }
        public List<JmlStatementLoop> loopSpecs;

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlDoWhileLoop(this); 
            } else {
                //System.out.println("A JmlDoWhileLoop expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlDoWhileLoop(this, d);
            } else {
                //System.out.println("A JmlDoWhileLoop expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
        public String toString() {
            return JmlTree.toString(this);
        }

    }

    /** This class represents JML statements within the body of a method
     * that take an expression, such as assert, assume, unreachable
     */
    public static class JmlStatementExpr extends JmlAbstractStatement {
        public JmlStatementExpr(int pos, JmlToken token, Label label, JCTree.JCExpression expression) {
            this.pos = pos;
            this.token = token;
            this.expression = expression;
            this.label = label;
            this.declPos = pos;
        }
        public JmlToken token;
        public JCTree.JCExpression expression;
        public JCTree.JCExpression optionalExpression = null;
        public int line; // FIXME - I don't think this is used
        public JavaFileObject source;
        public Label label;
        public int declPos; // the source position that generated the assert
                            // (for an explicit assert or assume, this should
                            // be the same as this.pos)

        @Override
        public int getTag() {
            return JMLSTATEMENTEXPR;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlStatementExpr(this); 
            } else {
                //System.out.println("A JmlStatementExpr expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlStatementExpr(this, d);
            } else {
                //System.out.println("A JmlStatementExpr expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    
    /** This class represents JML statements within the body of a model
     * program that are not statements themselves, such as 
     * invariants, specification cases
     */
    public static class JmlModelProgramStatement extends JmlAbstractStatement {
        public JmlModelProgramStatement(int pos, JCTree item) {
            this.pos = pos;
            this.item = item;
        }
        public JCTree item;

        @Override
        public int getTag() {
            return item.getTag();
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }

        @Override
        public void accept(Visitor v) {
            item.accept(v);
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            return item.accept(v,d);
        }
    }
    
    /** This class represents JML ghost declarations and model local class
     * declarations (FIXME _ local class?)
     */
    public static class JmlStatementDecls extends JmlAbstractStatement {
        public JmlStatementDecls(int pos, ListBuffer<JCTree.JCStatement> list) {
            this.pos = pos;
            this.token = JmlToken.GHOST;
            this.list = list;
        }
        public JmlToken token;
        public ListBuffer<JCTree.JCStatement> list;

        @Override
        public int getTag() {
            return JMLSTATEMENTDECLS;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlStatementDecls(this); 
            } else {
                //System.out.println("A JmlStatementDecls expects an IJmlVisitor, not a " + v.getClass());
                for (JCStatement s: list) s.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlStatementDecls(this, d);
            } else {
                System.out.println("A JmlStatementDecls expects an JmlTreeVisitor, not a " + v.getClass());
                //for (JCStatement s: list) s.accept(v,d);
                return super.accept(v,d);
            }
        }
    }
    
    /** This is an abstract class that is a parent to any type of clause in
     * a method specification.
     */
    abstract public static class JmlMethodClause extends JmlAbstractStatement implements JmlSource {
        public JmlToken token;
        public JavaFileObject sourcefile;
        abstract public StringBuilder toString(String indent);
        public JavaFileObject source() { return sourcefile; }
    }
    
    /** This class represents a method specification clause that has just an
     * expression.
     */
    public static class JmlMethodClauseDecl extends JmlMethodClause {
        public JmlMethodClauseDecl(int pos, JmlToken token, JCTree.JCExpression type, ListBuffer<JCTree.JCStatement> stats) {
            this.pos = pos;
            this.token = token;
            this.type = type;  // FIXME - this hidcs super type decl
            this.stats = stats;
        }
        public JCTree.JCExpression type;
        public ListBuffer<JCTree.JCStatement> stats;

        @Override
        public int getTag() {
            return JMLMETHODCLAUSEDECL;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        public String toString() {
            return super.toString();  // FIXME
        }
        
        public StringBuilder toString(String indent) {
            StringBuilder s = new StringBuilder();
            s.append(indent).append(token.internedName()).append(" ").append(type.toString()).append(" ").append(stats).append(eol);
            return s;
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodClauseDecl(this); 
            } else {
                //System.out.println("A JmlMethodClauseDecl expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodClauseDecl(this, d);
            } else {
                System.out.println("A JmlMethodClauseDecl expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    
    /** This class represents a method specification clause that has just an
     * expression.
     */
    public static class JmlMethodClauseExpr extends JmlMethodClause {
        public JmlMethodClauseExpr(int pos, JmlToken token, JCTree.JCExpression expression) {
            this.pos = pos;
            this.token = token;
            this.expression = expression;
        }
        public JCTree.JCExpression expression;

        @Override
        public int getTag() {
            return JMLMETHODCLAUSEEXPR;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        public String toString() {
            return super.toString();  // FIXME
        }
        
        public StringBuilder toString(String indent) {
            StringBuilder s = new StringBuilder();
            if (expression != null) s.append(indent).append(token.internedName()).append(" ").append(expression.toString()).append(eol);
            else s.append(indent).append(token.internedName()).append(eol);
            return s;
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodClauseExpr(this); 
            } else {
                //System.out.println("A JmlMethodClauseExpr expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodClauseExpr(this, d);
            } else {
                System.out.println("A JmlMethodClauseExpr expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    
    /** This class represents a method specification clause that has just an
     * expression.
     */
    public static class JmlMethodClauseConditional extends JmlMethodClause {
        public JmlMethodClauseConditional(int pos, JmlToken token, JCTree.JCExpression expression, /*@ nullable*/ JCTree.JCExpression predicate) {
            this.pos = pos;
            this.token = token;
            this.expression = expression;
            this.predicate = predicate;
        }
        public JCTree.JCExpression expression;
        /*@ nullable */ public JCTree.JCExpression predicate;

        @Override
        public int getTag() {
            return JMLMETHODCLAUSECONDITIONAL;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        public String toString() {
            return super.toString();  // FIXME
        }
        
        public StringBuilder toString(String indent) {
            StringBuilder s = new StringBuilder();
            if (expression != null) s.append(indent).append(token.internedName()).append(" ").append(expression.toString()).append(eol);
            else s.append(indent).append(token.internedName()).append(eol);
            return s;
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodClauseConditional(this); 
            } else {
                //System.out.println("A JmlMethodClauseConditional expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodClauseConditional(this, d);
            } else {
                System.out.println("A JmlMethodClauseCOnditional expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    
    /** This class represents a signals clause in a method specification. */
    public static class JmlMethodClauseSignals extends JmlMethodClause {
        // NOTE: the ident in the variable declaration may be null
        public JmlMethodClauseSignals(int pos, JmlToken token, JCTree.JCVariableDecl var, JCTree.JCExpression expression) {
            this.pos = pos;
            this.token = token;
            this.vardef = var;
            this.expression = expression;
        }
        
        public JCTree.JCExpression expression;
        public JCTree.JCVariableDecl vardef;

        @Override
        public int getTag() {
            return JMLMETHODCLAUSESIGNALS;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        public StringBuilder toString(String indent) {  // FIXME - incomplete
            StringBuilder s = new StringBuilder();
            if (expression != null) s.append(indent).append(token.internedName()).append(expression.toString()).append(eol);
            else s.append(indent).append(token.internedName()).append(eol);
            return s;
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodClauseSignals(this); 
            } else {
                //System.out.println("A JmlMethodClauseSignals expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodClauseSignals(this, d);
            } else {
                System.out.println("A JmlMethodClauseSignals expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    
    /** This class represents a signals_only clause in a method specification */
    public static class JmlMethodClauseSigOnly extends JmlMethodClause {
        public JmlMethodClauseSigOnly(int pos, JmlToken token, List<JCTree.JCExpression> list) {
            this.pos = pos;
            this.token = token;
            this.list = list;
        }
        public List<JCTree.JCExpression> list;

        @Override
        public int getTag() {
            return JMLMETHODCLAUSESIGNALSONLY;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }

        public StringBuilder toString(String indent) {  // FIXME - incomplete
            StringBuilder s = new StringBuilder();
            s.append(indent).append(token.internedName()).append(eol);
            return s;
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodClauseSigOnly(this); 
            } else {
                //System.out.println("A JmlMethodClauseSigOnly expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodClauseSigOnly(this, d);
            } else {
                System.out.println("A JmlMethodClauseSigOnly expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }

    /** This class represents an assignable clause in a method specification */
    public static class JmlMethodClauseStoreRef extends JmlMethodClause {
        public JmlMethodClauseStoreRef(int pos, JmlToken token, List<JCExpression> list) {
            this.pos = pos;
            this.token = token;
            this.list = list;
        }
        public List<JCExpression> list;

        @Override
        public int getTag() {
            return JMLMETHODCLAUSEASSIGNABLE;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }

        public StringBuilder toString(String indent) {  // FIXME - incomplete
            StringBuilder s = new StringBuilder();
            s.append(indent).append(token.internedName()).append(eol);
            return s;
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodClauseStoreRef(this); 
            } else {
                //System.out.println("A JmlMethodClauseAssignable expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodClauseAssignable(this, d);
            } else {
                System.out.println("A JmlMethodClauseAssignable expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    
    /** Represents a nothing, everything or informal comment token */
    public static class JmlStoreRefKeyword extends JCExpression {
        public JmlToken token; // nothing or everything or informal comment

        public JmlStoreRefKeyword(int pos, JmlToken token) {
            this.pos = pos;
            this.token = token;
        }

        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLSTOREREFKEYWORD;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlStoreRefKeyword(this); 
            } else {
                System.out.println("A JmlStoreRefKeyword expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlStoreRefKeyword(this, d);
            } else {
                System.out.println("A JmlStoreRefKeyword expects an JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
        public String toString() {
            return JmlTree.toString(this);
        }

    }

    public static class JmlStoreRefArrayRange extends JmlExpression {
        public JCExpression expression;
        public JCExpression lo;
        public JCExpression hi;

        public JmlStoreRefArrayRange(int pos, JCExpression expr, JCExpression lo, JCExpression hi) {
            this.pos = pos;
            this.expression = expr;
            this.lo = lo;
            this.hi = hi;
        }

        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLSTOREREFARRAYRANGE;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlStoreRefArrayRange(this); 
            } else {
                System.out.println("A JmlStoreRefArrayRange expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlStoreRefArrayRange(this, d);
            } else {
                System.out.println("A JmlStoreRefArrayRange expects an JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
    }

    /** This class represents type clauses (e.g. invariant, constraint,...) in a class specification */
    abstract public static class JmlTypeClause extends JCTree implements JmlSource {
        
        public JmlToken token;
        public JavaFileObject source;
        public JCModifiers modifiers;

        public JavaFileObject source() { return source; }
        
        public String toString() {
            return JmlTree.toString(this);
        }
    }
    
    /** This class represents a group in an "in" or "maps" type clause in a class specification */
    public static class JmlGroupName extends JCTree {

        public JmlGroupName(int pos, JCExpression selection) {
            this.pos = pos;
            this.selection = selection;
        }
        
        public JCExpression selection;
        public VarSymbol sym;
        
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLGROUPNAME;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlGroupName(this); 
            } else {
                System.out.println("A JmlGroupName expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlGroupName(this, d);
            } else {
                System.out.println("A JmlGroupName expects an JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
        
        public String toString() {
            return JmlTree.toString(this);
        }
    }
    
    /** This class represents an "in" type clause in a class specification */
    public static class JmlTypeClauseIn extends JmlTypeClause {

        public JmlTypeClauseIn(int pos, List<JmlGroupName> list) {
            this.pos = pos;
            this.token = JmlToken.IN;
            this.list = list;
            this.parentVar = null;
        }
        
        public List<JmlGroupName> list;
        public JmlVariableDecl parentVar;
        
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLTYPECLAUSEIN;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlTypeClauseIn(this); 
            } else {
                //System.out.println("A JmlTypeClauseIn expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlTypeClauseIn(this, d);
            } else {
                System.out.println("A JmlTypeClauseIn expects an JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
    }

    /** This class represents type clauses (e.g. invariant, constraint,...) in a class specification */
    public static class JmlTypeClauseMaps extends JmlTypeClause {

        public JmlTypeClauseMaps(int pos, JCExpression e, List<JmlGroupName> list) {
            this.pos = pos;
            this.expression = e;
            this.modifiers = null;
            this.token = JmlToken.MAPS;
            this.list = list;
        }
        
        public JCExpression expression;
        public List<JmlGroupName> list;
        
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLTYPECLAUSEMAPS;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlTypeClauseMaps(this); 
            } else {
                //System.out.println("A JmlTypeClauseMaps expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlTypeClauseMaps(this, d);
            } else {
                System.out.println("A JmlTypeClauseMaps expects an JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
    }

    /** This class represents 'represents' type clauses  in a class specification */
    public static class JmlTypeClauseInitializer extends JmlTypeClause {

        public JmlTypeClauseInitializer(int pos, JmlToken token) {
            this.pos = pos;
            this.token = token;
            // FIXME - needs to set source and modifiers
        }
        
        public JmlMethodSpecs specs;
        
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLTYPECLAUSEINITIALIZER;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlTypeClauseInitializer(this); 
            } else {
                //System.out.println("A JmlTypeClauseInitializer expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlTypeClauseInitializer(this, d);
            } else {
                System.out.println("A JmlTypeClauseInitializer expects an JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
    }
    
    /** This class represents 'represents' type clauses  in a class specification */
    public static class JmlTypeClauseConstraint extends JmlTypeClause {

        public JmlTypeClauseConstraint(int pos, JCModifiers mods, JCExpression expression, List<JmlConstraintMethodSig> sigs) {
            this.pos = pos;
            this.modifiers = mods;
            this.token = JmlToken.CONSTRAINT;
            this.expression = expression;
            this.sigs = sigs; // Method signatures
        }
        
        public JCTree.JCExpression expression;
        public List<JmlConstraintMethodSig> sigs;
        
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLTYPECLAUSECONSTRAINT;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlTypeClauseConstraint(this); 
            } else {
                //System.out.println("A JmlTypeClauseConstraint expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlTypeClauseConstraint(this, d);
            } else {
                System.out.println("A JmlTypeClauseConstraint expects an JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
    }
    
    public static class JmlConstraintMethodSig extends JCTree {
        public JCExpression expression;
        public List<JCExpression> argtypes;
        
        public JmlConstraintMethodSig(int pos, JCExpression expr, List<JCExpression> argtypes) {
            this.pos = pos;
            this.expression = expr;
            this.argtypes = argtypes;
        }

        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLCONSTRAINTMETHODSIG;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
 // FIXME               ((IJmlVisitor)v).visitJmlConstraintMethodSig(this); 
            } else {
                //System.out.println("A JmlConstraintMethodSig expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return null; // FIXME((JmlTreeVisitor<R,D>)v).visitJmlConstraintMethodSig(this, d);
            } else {
                System.out.println("A JmlConstraintMethodSig expects an JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
        
        public String toString() {
            return JmlTree.toString(this);
        }
    }
    
    /** This class represents 'represents' type clauses  in a class specification */
    public static class JmlTypeClauseRepresents extends JmlTypeClause {

        public JmlTypeClauseRepresents(int pos, JCModifiers mods, JCTree.JCExpression ident, boolean suchThat, JCTree.JCExpression expression) {
            this.pos = pos;
            this.modifiers = mods;
            this.token = JmlToken.REPRESENTS;
            this.ident = ident;
            this.expression = expression;
            this.suchThat = suchThat;
        }
        
        public JCTree.JCExpression ident; // a store-ref expression  // FIXME - doesn't this need to be a simple name?
        public boolean suchThat;
        public JCTree.JCExpression expression;
        
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLTYPECLAUSEREPRESENTS;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlTypeClauseRepresents(this); 
            } else {
                //System.out.println("A JmlTypeClauseRepresents expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlTypeClauseRepresents(this, d);
            } else {
                System.out.println("A JmlTypeClauseRepresents expects an JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
    }

    /** This class represents type clauses (e.g. invariant, constraint,...) in a class specification */
    public static class JmlTypeClauseExpr extends JmlTypeClause implements JmlSource {

        public JmlTypeClauseExpr(int pos, JCModifiers mods, JmlToken token, JCTree.JCExpression expression) {
            this.pos = pos;
            this.modifiers = mods;
            this.token = token;
            this.expression = expression;
        }
        
        public JCTree.JCExpression expression;
        
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLTYPECLAUSEEXPR;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlTypeClauseExpr(this); 
            } else {
                //System.out.println("A JmlTypeClauseExpr expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlTypeClauseExpr(this, d);
            } else {
                System.out.println("A JmlTypeClauseExpr expects an JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
    }
    
    /** This class represents readable_if and writable_if type clauses */
    public static class JmlTypeClauseConditional extends JmlTypeClause {

        public JmlTypeClauseConditional(int pos, JCModifiers mods, JmlToken token, JCTree.JCIdent ident, JCTree.JCExpression expression) {
            this.pos = pos;
            this.modifiers = mods;
            this.token = token;
            this.identifier = ident;
            this.expression = expression;
        }
        
        public JCTree.JCIdent identifier;
        public JCTree.JCExpression expression;
        
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLTYPECLAUSECONDITIONAL;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlTypeClauseConditional(this); 
            } else {
                //System.out.println("A JmlTypeClauseConditional expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlTypeClauseConditional(this, d);
            } else {
                System.out.println("A JmlTypeClauseConditional expects an JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
    }
    
    /** This class represents monitors_for type clauses */
    public static class JmlTypeClauseMonitorsFor extends JmlTypeClause {

        public JmlTypeClauseMonitorsFor(int pos, JCModifiers mods, JCIdent ident, ListBuffer<JCTree.JCExpression> list) {
            this.pos = pos;
            this.modifiers = mods;
            this.identifier = ident;
            this.token = JmlToken.MONITORS_FOR;
            this.list = list;
        }
        
        public JCTree.JCIdent identifier;
        public ListBuffer<JCTree.JCExpression> list;
        
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLTYPECLAUSEMONITORSFOR;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlTypeClauseMonitorsFor(this); 
            } else {
                //System.out.println("A JmlTypeClauseMonitorsFor expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlTypeClauseMonitorsFor(this, d);
            } else {
                System.out.println("A JmlTypeClauseMonitorsFor expects an JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
    }
    
    /** This class represents type clauses that are declarations (ghost and model) */
    public static class JmlTypeClauseDecl extends JmlTypeClause {
        
        public JmlTypeClauseDecl(int pos, JCTree decl) {
            this.pos = pos;
            this.token = JmlToken.JMLDECL;
            this.decl = decl;
        }
        
        public JCTree decl;
        
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLTYPECLAUSEDECL;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlTypeClauseDecl(this); 
            } else {
                //System.out.println("A JmlTypeClauseDecl expects an IJmlVisitor, not a " + v.getClass());
                //decl.accept(v); // FIXME - if this is in then JML decls that are part of the AST get processed when they should not
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlTypeClauseDecl(this, d);
            } else {
                //System.out.println("A JmlTypeClauseDecl expects an JmlTreeVisitor, not a " + v.getClass());
                return decl.accept(v,d);
            }
        }
    }

    /** This class represents a specification case in a method specification */
    public static class JmlSpecificationCase extends JmlAbstractStatement implements JmlSource {
        public JCModifiers modifiers;
        public JmlToken token;
        public JmlToken also;
        public boolean code;
        public List<JmlMethodClause> clauses; // A behavior spec case has clauses but no block of statements
        public JCBlock block;  // A model program has a block (of statements) but no clauses
        public JavaFileObject sourcefile;
        
        public JmlSpecificationCase(int pos, JCModifiers mods, boolean code, JmlToken token, JmlToken also, List<JmlMethodClause> clauses) {
            this.pos = pos;
            this.modifiers = mods;
            this.code = code;
            this.token = token;
            this.also = also;
            this.clauses = clauses;
            this.block = null;
        }
        
        public JmlSpecificationCase(int pos, JCModifiers mods, boolean code, JmlToken token, JmlToken also, JCBlock block) {
            this.pos = pos;
            this.modifiers = mods;
            this.code = code;
            this.token = token;
            this.also = also;
            this.clauses = null;
            this.block = block;
        }
        
        public JmlSpecificationCase(JmlSpecificationCase old, List<JmlMethodClause> clauses) {
            this.pos = old.pos;
            this.modifiers = old.modifiers;
            this.code = old.code;
            this.token = old.token;
            this.also = old.also;
            this.sourcefile = old.sourcefile;
            this.clauses = clauses;
        }
        
        public JavaFileObject source() { return sourcefile; }


        @Override
        public int getTag() {
            return JMLSPECIFICATIONCASE;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }

        public StringBuilder toString(String indent) {
            StringBuilder s = new StringBuilder();
            String indent2 = indent + "  ";
            s.append(indent).append(token == null ? "<lightweight>" : token.internedName()).append(eol);
            for (JmlMethodClause c: clauses) {
                s.append(c.toString(indent2));
            }
            return s;
        }


        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlSpecificationCase(this); 
            } else {
                //System.out.println("A JmlSpecificationCase expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlSpecificationCase(this, d);
            } else {
                //System.out.println("A JmlSpecificationCase expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    
    /** This represents the sequence of method specs lists that are the sequence
     * of nested specs
     */
    public static class JmlMethodClauseGroup extends JmlMethodClause {
        
        public List<JmlSpecificationCase> cases;
        
        public JmlMethodClauseGroup(int pos, List<JmlSpecificationCase> cases) {
            this.pos = pos;
            this.token = JmlToken.SPEC_GROUP_START;
            this.cases = cases;
        }

        @Override
        public int getTag() {
            return JMLMETHODCLAUSEGROUP;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        public String toString() {
            return super.toString();  // FIXME
        }
        
        // FIXME
        public StringBuilder toString(String indent) {
            StringBuilder s = new StringBuilder();
//            if (expression != null) s.append(indent).append(token.internedName()).append(" ").append(expression.toString()).append(eol);
//            else s.append(indent).append(token.internedName()).append(eol);
            return s;
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodClauseGroup(this); 
            } else {
                //System.out.println("A JmlMethodClauseGroup expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodClauseGroup(this, d);
            } else {
                //System.out.println("A JmlMethodClauseGroup expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    
    /** This class represents the specifications of a method (a list of 
     * specification cases).
     */
    public static class JmlMethodSpecs extends JmlAbstractStatement {
        public JmlMethodDecl decl = null; // A declaration that has the result and parameter modifiers
        public List<JmlSpecificationCase> cases;
        public List<JmlSpecificationCase> impliesThatCases;
        public List<JmlSpecificationCase> forExampleCases;
        public JmlMethodSpecs deSugared = null;
        
        public JmlMethodSpecs(int pos, List<JmlSpecificationCase> cases) {
            this.pos = pos;
            this.cases = cases;
            this.impliesThatCases = List.<JmlSpecificationCase>nil();
            this.forExampleCases = List.<JmlSpecificationCase>nil();
        }
        
        public JmlMethodSpecs() {
            this.pos = Position.NOPOS;
            this.cases = List.<JmlSpecificationCase>nil();;
            this.impliesThatCases = List.<JmlSpecificationCase>nil();
            this.forExampleCases = List.<JmlSpecificationCase>nil();
        }
        
        @Override
        public int getTag() {
            return JMLMETHODSPECS;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }

        public String toString(String indent) {
            StringBuilder s = new StringBuilder();
            for (JmlSpecificationCase c: cases) {
                s.append(c.toString(indent));
            }
            return s.toString();
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodSpecs(this); 
            } else {
                //System.out.println("A JmlMethodSpecs expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodSpecs(this, d);
            } else {
                //System.out.println("A JmlMethodSpecs expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    
    /** This class represents JML primitive types */
    static public class JmlPrimitiveTypeTree extends JmlExpression {
        
        public JmlToken token;
        
        public JmlPrimitiveTypeTree(int pos, JmlToken token) {
            this.pos = pos;
            this.token = token;
        }
        
        public String toString() {
            return token.internedName();
        }

        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            return JMLPRIMITIVETYPETREE;
        }

        @Override
        public void accept(Visitor v) { 
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlPrimitiveTypeTree(this); 
            } else {
                //System.out.println("A JmlPrimitiveTypeTree expects an IJmlVisitor, not a " + v.getClass());
                // super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlPrimitiveTypeTree(this, d);
            } else {
                System.out.println("A JmlPrimitiveTypeTree expects an JmlTreeVisitor, not a " + v.getClass());
                return null; // return super.accept(v,d);
            }
        }
    }

    /** The system-defined end of line character string */
    static public final String eol = System.getProperty("line.separator");
    
    public static class JmlBBArrayAssignment extends JCMethodInvocation {
        public JmlBBArrayAssignment(JCIdent newarrs, JCIdent oldarrs, JCExpression arr, JCExpression index, JCExpression rhs) {
            super(null,null,null);
            ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
            list.append(newarrs);
            list.append(oldarrs);
            list.append(arr);
            list.append(index);
            list.append(rhs);
            args = list.toList();
        }
    }
    
    public static class JmlBBArrayHavoc extends JCMethodInvocation {
        public JmlBBArrayHavoc(JCIdent newarrs, JCIdent oldarrs, JCExpression arr, JCExpression indexlo, JCExpression indexhi, JCExpression precondition, boolean above) {
            super(null,null,null);
            ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
            list.append(newarrs);
            list.append(oldarrs);
            list.append(arr);
            list.append(indexlo);
            list.append(indexhi);
            list.append(precondition);
            this.above = above;
            args = list.toList();
        }
        public boolean above;
    }
    
    public static class JmlBBFieldAssignment extends JCMethodInvocation {
        public JmlBBFieldAssignment(JCIdent newfield, JCIdent oldfield, JCExpression selected, JCExpression rhs) {
            super(null,null,null);
            ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
            list.append(newfield);
            list.append(oldfield);
            list.append(selected);
            list.append(rhs);
            args = list.toList();
        }
    }
    
    public static class JmlBBArrayAccess extends JCArrayAccess {
        public JCIdent arraysId;
        public JmlBBArrayAccess(JCIdent arraysId, JCExpression arr, JCExpression index) {
            super(arr,index);
            this.arraysId = arraysId;
        }
        public JmlBBArrayAccess(JCIdent arraysId, JCExpression arr, JCExpression index, int pos, Type type) {
            super(arr,index);
            this.arraysId = arraysId;
            this.pos = pos;
            this.type = type;
        }
    }
    
    public static class JmlBBFieldAccess extends JCFieldAccess {
        public JCIdent fieldId;
        public JmlBBFieldAccess(JCIdent fieldId, JCExpression selected) {
            super(selected,fieldId.name,fieldId.sym);
            this.fieldId = fieldId;
            this.type = fieldId.type;
        }
    }    
}
