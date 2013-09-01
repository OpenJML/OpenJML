/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import static com.sun.tools.javac.code.Flags.UNATTRIBUTED;

import java.io.StringWriter;
import java.util.Map;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.esc.Label;

import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.ExpressionTree;
import com.sun.source.tree.TreeVisitor;
import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Scope.ImportScope;
import com.sun.tools.javac.code.Scope.StarImportScope;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCDoWhileLoop;
import com.sun.tools.javac.tree.JCTree.JCEnhancedForLoop;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCForLoop;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCTypeParameter;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.JCWhileLoop;
import com.sun.tools.javac.tree.TreeMaker;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;

// FIXME - review that getTag and getKind are appropriately used; check toString is where it is needed
// FIXME - review and fix the else branches of all the accept statements
// FIXME - the start and end positions are gotten from TreeInfo, which does not work for JML nodes
/** This class simply holds the classes which are JML-specific nodes of parse trees. */
public class JmlTree implements IJmlTree {

    /** Convert a tree to a pretty-printed string using the JmlPrettyPrinter; note that
     * this is not inherited by anyone, it is here as a utility method and needs
     * to be called by nodes of JmlTree. */
    static public String toString(JCTree node) {
        StringWriter sw = new StringWriter();
        JmlPretty p = new JmlPretty(sw,true);
        p.width = 2;
        node.accept(p);
        return sw.toString();
    }


    /** This interface extends the node factory for Java parse tree nodes by adding factory
     * methods for all of the JML nodes.  All these methods create the AST nodes;
     * the pos field is set using other methods on the factory.
     */
    public interface JmlFactory extends JCTree.Factory {
        JmlBinary JmlBinary(JmlToken t, JCTree.JCExpression left, JCTree.JCExpression right);
        JmlChoose JmlChoose(JmlToken token, List<JCBlock> orBlocks, /*@Nullable*/JCBlock elseBlock);
        JmlConstraintMethodSig JmlConstraintMethodSig(JCExpression expr, List<JCExpression> argtypes);
        JmlDoWhileLoop JmlDoWhileLoop(JCDoWhileLoop loop, List<JmlStatementLoop> loopSpecs);
        JmlEnhancedForLoop JmlEnhancedForLoop(JCEnhancedForLoop loop, List<JmlStatementLoop> loopSpecs);
        JmlStatementExpr JmlExpressionStatement(JmlToken t, Label label, JCTree.JCExpression e);
        JmlStatementHavoc JmlHavocStatement(List<JCTree.JCExpression> e);
        JmlForLoop JmlForLoop(JCForLoop loop, List<JmlStatementLoop> loopSpecs);
        JmlGroupName JmlGroupName(JCExpression selection);
        JmlImport JmlImport(JCTree qualid, boolean staticImport, boolean isModel);
        JmlLblExpression JmlLblExpression(int labelPosition, JmlToken token, Name label, JCTree.JCExpression expr);
        JmlMethodClauseGroup JmlMethodClauseGroup(List<JmlSpecificationCase> cases);
        JmlMethodClauseDecl JmlMethodClauseDecl(JmlToken t, List<JCTree.JCVariableDecl> decls);
        JmlMethodClauseExpr JmlMethodClauseExpr(JmlToken t, JCTree.JCExpression e);
        JmlDeclassifyClause JmlDeclassifyClause(JmlToken t, JCTree.JCExpression e, JCTree.JCMethodInvocation p);
        JmlLevelStatement JmlLevelStatement(JmlToken t, JCIdent level);

        JmlMethodClauseCallable JmlMethodClauseCallable(JmlStoreRefKeyword keyword);
        JmlMethodClauseCallable JmlMethodClauseCallable(List<JmlConstraintMethodSig> methodSignatures);
        JmlMethodClauseConditional JmlMethodClauseConditional(JmlToken t, JCTree.JCExpression e, JCTree.JCExpression predicate);
        JmlMethodClauseSignals JmlMethodClauseSignals(JmlToken t, JCTree.JCVariableDecl var, JCTree.JCExpression e);
        JmlMethodClauseSignalsOnly JmlMethodClauseSignalsOnly(JmlToken t, List<JCTree.JCExpression> e);
        JmlMethodClause JmlMethodClauseStoreRef(JmlToken t, List<JCExpression> list);
        JmlMethodInvocation JmlMethodInvocation(JmlToken token, List<JCExpression> args);
        JmlMethodSpecs JmlMethodSpecs(List<JmlSpecificationCase> cases);
        JmlModelProgramStatement JmlModelProgramStatement(JCTree item);
        JmlPrimitiveTypeTree JmlPrimitiveTypeTree(JmlToken jt);
        JmlQuantifiedExpr JmlQuantifiedExpr(JmlToken token, List<JCVariableDecl> decls, JCTree.JCExpression range, JCTree.JCExpression predicate);
        JmlSetComprehension JmlSetComprehension(JCTree.JCExpression type, JCTree.JCVariableDecl v, JCTree.JCExpression predicate);
        JmlSingleton JmlSingleton(JmlToken jt);
        JmlSpecificationCase JmlSpecificationCase(JCModifiers mods, boolean code, JmlToken t, JmlToken also, List<JmlMethodClause> clauses);
        JmlSpecificationCase JmlSpecificationCase(JmlSpecificationCase sc, List<JmlMethodClause> clauses);
        JmlSpecificationCase JmlSpecificationCase(JCModifiers mods, boolean code, JmlToken t, JmlToken also, JCBlock block);
        JmlStatement JmlStatement(JmlToken t, JCTree.JCExpressionStatement e);
        JmlStatementDecls JmlStatementDecls(List<JCTree.JCStatement> list);
        JmlStatementLoop JmlStatementLoop(JmlToken t, JCTree.JCExpression e);
        JmlStatementSpec JmlStatementSpec(JmlMethodSpecs specs);
        JmlStoreRefArrayRange JmlStoreRefArrayRange(JCExpression expr, JCExpression lo, JCExpression hi);
        JmlStoreRefKeyword JmlStoreRefKeyword(JmlToken t);
        JmlStoreRefListExpression JmlStoreRefListExpression(JmlToken t, List<JCExpression> list);
        JmlTypeClauseConditional JmlTypeClauseConditional(JCModifiers mods, JmlToken token, JCTree.JCIdent ident, JCTree.JCExpression p);
        JmlTypeClauseConstraint JmlTypeClauseConstraint(JCModifiers mods, JCExpression e, List<JmlConstraintMethodSig> sigs);
        JmlTypeClauseDecl JmlTypeClauseDecl(JCTree decl);
        JmlTypeClauseExpr JmlTypeClauseExpr(JCModifiers mods, JmlToken token, JCTree.JCExpression e);
        JmlTypeClauseIn JmlTypeClauseIn(List<JmlGroupName> list);
        JmlTypeClauseInitializer JmlTypeClauseInitializer(JmlToken token);
        JmlTypeClauseMaps JmlTypeClauseMaps(JCExpression e, List<JmlGroupName> list);
        JmlTypeClauseMonitorsFor JmlTypeClauseMonitorsFor(JCModifiers mods, JCTree.JCIdent ident, List<JCTree.JCExpression> list);
        JmlTypeClauseRepresents JmlTypeClauseRepresents(JCModifiers mods, JCTree.JCExpression ident, boolean suchThat, JCTree.JCExpression e);
        JmlWhileLoop JmlWhileLoop(JCWhileLoop loop, List<JmlStatementLoop> loopSpecs);
        JCExpression Type(Type t);
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
                @Override
                public Maker make(Context context) {
                    return new Maker(context);
                }
            });
        }
        
        /** The public method for obtaining a JmlTree.Maker instance. */
        public static JmlTree.Maker instance(Context context) {
            JmlTree.Maker instance = (JmlTree.Maker)context.get(treeMakerKey);
            if (instance == null)
                instance = new JmlTree.Maker(context); // registers itself
            return instance;
        }
        
        /** Sets the preferred token position to be used for subsequent
         * factory produced nodes, typically used like this, for example:
         * maker.at(pos).JmlPrimitiveTypeTree(token); overridden simply to 
         * return the derived type
         * @param pos the 0-based character position from the beginning of the input file
         */
        @Override
        public Maker at(int pos) {
            super.at(pos);
            return this;
        }
        
        @Override
        public Maker at(DiagnosticPosition pos) {
            this.pos = (pos == null ? Position.NOPOS : pos.getPreferredPosition()); // FIXME - decide on preferred or start position
            //super.at(pos);
            return this;
        }
        
        /** Creates a JmlCompilationUnit */
        @Override
        public JmlCompilationUnit TopLevel(List<JCAnnotation> packageAnnotations,
                JCExpression pid,
                List<JCTree> defs) {
            JmlCompilationUnit t = new JmlCompilationUnit(packageAnnotations,
                    pid,
                    defs,
                    null,null,null,null);
            t.pos = this.pos;
            for (JCTree d: defs) {
                if (d instanceof JmlClassDecl) ((JmlClassDecl)d).toplevel = t;
            }
            return t;
        }
        
        /** Convenience method to create a qualified identifier - either a 
         * JCIdent or a JCFieldAccess; this is used for field names and
         * for qualified type names.
         * @param names the identifiers that are dot-separated
         * @return the resulting JCIdent of JCFieldAccess
         */
        public JCExpression QualIdent(Name... names) {
            JCExpression t = Ident(names[0]);
            for (int i = 1; i < names.length; i++) {
                t = Select(t,names[i]);
            }
            return t;
        }
        
        /** Convenience method to create a qualified identifier - either a 
         * JCIdent or a JCFieldAccess; this is used for field names and
         * for qualified type names.
         * @param names the identifiers that are dot-separated
         * @return the resulting JCIdent of JCFieldAccess
         */
        public JCExpression QualIdent(String... names) {
            Names n = Names.instance(context);
            JCExpression t = Ident(n.fromString(names[0]));
            for (int i = 1; i < names.length; i++) {
                t = Select(t,n.fromString(names[i]));
            }
            return t;
        }
        
        /** Convenience method to create a JCIdent from a string
         * (use a Name if you have one, since this method creates a Name).
         * @param name the string to convert to wrap as an identifier
         * @return the resulting JCIdent
         */
        public JCIdent Ident(String name) {
            Names n = Names.instance(context);
            return Ident(n.fromString(name));
        }
        
        /** Convenience method to create a Name from a string
         * @param name the string to wrap as a Name
         * @return the resulting Name
         */
        public Name Name(String name) {
            Names n = Names.instance(context);
            return n.fromString(name);
        }
        
        /** Creates a class declaration from its components, overridden
         * in order to produce a JmlClassDecl; the new object keeps a
         * reference to the current sourcefile in the log */
        @Override
        public JmlClassDecl ClassDef(JCModifiers mods,
                Name name,
                List<JCTypeParameter> typarams,
                JCExpression extending,
                List<JCExpression> implementing,
                List<JCTree> defs) {
            JmlClassDecl tree = new JmlClassDecl(mods,name,typarams,extending,implementing,defs,null);
            tree.pos = pos;
            // In the normal course of things, context is never null, but there is a circular dependency of
            // instantiating tools that can occur in the constructors of the various tools.  In particular
            // TreeMaker -> Symtab -> ClassReader -> Annotate -> Attr -> MemberEnter -> Enter which calls
            // TreeMaker.ClassDef before TreeMaker has completed construction
            // where A -> B means A constructs B during A's construction.  This results in TreeMaker.ClassDef
            // being called with a null context during TreeMaker's construction
//            if (context != null) 
//                tree.toplevel.sourcefile = Log.instance(context).currentSourceFile();
//            else {
            if (context == null) {
                String msg = ("INTERNAL ERROR: JmlTree.ClassDef called with a null context, indicating a problem with circular dependencies in constructors.");
                System.err.println(msg);
                new Exception().printStackTrace(System.err);
                throw new JmlInternalError(msg);
            }
            return tree;
        }
        
        /** Creates a method declaration from its components, overridden
         * in order to produce a JmlMethodDecl; the new object keeps a
         * reference to the current sourcefile in the log */
        @Override
        public JmlMethodDecl MethodDef(JCModifiers mods,
                Name name,
                JCExpression restype,
                List<JCTypeParameter> typarams,
                List<JCVariableDecl> params,
                List<JCExpression> thrown,
                JCBlock body,
                JCExpression defaultValue) {
            JmlMethodDecl tree = new JmlMethodDecl(mods,name,restype,typarams,params,thrown,body,defaultValue,null); // DRC Introduced null parameter to deal with new/evolved signature.
            tree.pos = pos;
            tree.sourcefile = Log.instance(context).currentSourceFile();
            return tree;
        }
        
        /** Creates a method declaration from a method symbol and a method type */
        @Override
        public JmlMethodDecl MethodDef(MethodSymbol m, Type mtype, JCBlock body) {
            JmlMethodDecl tree = (JmlMethodDecl)
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
            tree.sourcefile = Log.instance(context).currentSourceFile();
            return tree;
        }

        /** Creates a variable declaration with symbol and type filled in from its components;
         * sourcefile set from current log */
        @Override
        public JmlVariableDecl VarDef(VarSymbol v, /*@Nullable*/ JCExpression init) {
            JmlVariableDecl tree = new JmlVariableDecl(
                Modifiers(v.flags(), Annotations(v.getAnnotationMirrors())),
                v.name,
                Type(v.type),
                init,
                v);
            tree.pos = pos;
            tree.setType(v.type);
            tree.sourcefile = Log.instance(context).currentSourceFile();
            // Not filled in: docComment, fieldSpecs, fieldSpecsCombined, specsDecl
            return tree;
        }

        
        /** Creates a variable declaration from its components; captures the sourcefile
         * from the current value in the log; no symbol created. */
        @Override
        public JmlVariableDecl VarDef(JCModifiers mods,
                Name name,
                JCExpression vartype,
                JCExpression init) {
            JmlVariableDecl tree =  new JmlVariableDecl(mods,name,vartype,init,null);
            tree.pos = pos;
            tree.type = vartype.type; // attribute if the type is known
            tree.sourcefile = Log.instance(context).currentSourceFile();
            // Not filled in: symbol, docComment, fieldSpecs, fieldSpecsCombined, specsDecl
            return tree;
        }

        /** Creates an expression for a JML type (such as \TYPE or \real or \bigint).*/
        @Override
        public JmlPrimitiveTypeTree JmlPrimitiveTypeTree(JmlToken jt) {
            return new JmlPrimitiveTypeTree(pos,jt);
        }
        
        @Override
        public JCExpression Type(Type t) {
            if (!(t instanceof JmlType)) return super.Type(t);
            return new JmlPrimitiveTypeTree(pos,((JmlType)t).jmlTypeTag());
        }

        
        /** Creates JML expressions from tokens without arguments (e.g. \result)*/
        @Override
        public JmlSingleton JmlSingleton(JmlToken jt) {
            return new JmlSingleton(pos,jt);
        }
        
        /** Creates a JML import statement (possibly a model import) */
        @Override
        public JmlImport JmlImport(JCTree qualid, boolean staticImport, boolean isModel) {
            return (JmlImport)new JmlImport(qualid, staticImport,isModel).setPos(pos);
        }
        
        /** Creates a regular import, but using a JmlImport AST node */
        @Override
        public JmlImport Import(JCTree qualid, boolean staticImport) {
            return (JmlImport)new JmlImport(qualid,staticImport,false).setPos(pos);
        }
        
        /** Creates a JML binary operation */
        @Override
        public JmlBinary JmlBinary(JmlToken t, JCTree.JCExpression left, JCTree.JCExpression right) {
            return new JmlBinary(pos,t,left,right);
        }
        
        /** Creates a JML method invocation (e.g. for JmlTokens with arguments, such as \typeof) */
        @Override
        public JmlMethodInvocation JmlMethodInvocation(JmlToken token, List<JCExpression> args) {
            return new JmlMethodInvocation(pos,token,args);
        }
        
        /** Creates a method invocation from a method name expression (e.g. o.name) */
        public JmlMethodInvocation JmlMethodInvocation(JCExpression method, List<JCExpression> args) {
            return new JmlMethodInvocation(pos,method,args);
        }
        
        /** Creates a JML method invocation for the special case of one argument (e.g. for JmlTokens with arguments, such as \typeof) */
        public JmlMethodInvocation JmlMethodInvocation(JmlToken token, JCExpression arg) {
            return new JmlMethodInvocation(pos,token,List.<JCExpression>of(arg));
        }
        
        /** Creates a JML method invocation for the special case of two arguments */
        public JmlMethodInvocation JmlMethodInvocation(JmlToken token, JCExpression arg, JCExpression arg2) {
            return new JmlMethodInvocation(pos,token,List.<JCExpression>of(arg,arg2));
        }
        
        /** Creates a JML quantified expression */
        @Override
        public JmlQuantifiedExpr JmlQuantifiedExpr(JmlToken t, List<JCTree.JCVariableDecl> decls, JCTree.JCExpression range, JCTree.JCExpression value) {
            return new JmlQuantifiedExpr(pos,t,decls,range,value);
        }
        
        /** Creates a JML set-comprehension expression */
        @Override
        public JmlSetComprehension JmlSetComprehension(JCTree.JCExpression type, JCTree.JCVariableDecl varDecl, JCTree.JCExpression value) {
            return new JmlSetComprehension(pos,type,varDecl,value);
        }
        
        /** Creates a JML labeled expression */
        @Override
        public JmlLblExpression JmlLblExpression(int labelPosition, JmlToken token, Name label, JCTree.JCExpression expr) {
            JmlLblExpression p = new JmlLblExpression(pos,labelPosition,token,label,expr);
            return p;
        }

        /** Creates a JML expression statement (e.g. assert) */
        @Override
        public JmlStatementExpr JmlExpressionStatement(JmlToken t, Label label, JCTree.JCExpression e) {
            return new JmlStatementExpr(pos,t,label,e);
        }
        
        /** Creates a JML havoc statement */
        @Override
        public JmlStatementHavoc JmlHavocStatement(List<JCTree.JCExpression> e) {
            return new JmlStatementHavoc(pos,e);
        }
        
        /** This creates a pseudo-statement in a method body that is actually a block of method specifications */
        @Override
        public JmlStatementSpec JmlStatementSpec(JmlMethodSpecs specs) {
            return new JmlStatementSpec(pos,specs);
        }
        
        /** Creates a JML loop specification statement (e.g. loop_invariant, decreases, ... )*/
        @Override
        public JmlStatementLoop JmlStatementLoop(JmlToken t, JCTree.JCExpression e) {
            return new JmlStatementLoop(pos,t,e);
        }

        /** Creates a JML do-while loop node that wraps a Java loop statement and a set of loop specifications */
        @Override
        public JmlDoWhileLoop JmlDoWhileLoop(JCDoWhileLoop loop, List<JmlStatementLoop> loopSpecs) {
            return new JmlDoWhileLoop(loop,loopSpecs); // pos set from loop argument
        }
        
        /** Creates a regular for-loop with no specifications */
        @Override
        public JmlForLoop ForLoop(List<JCStatement> init,
                JCExpression cond,
                List<JCExpressionStatement> step,
                JCStatement body)
        {
            JCForLoop tree = super.ForLoop(init, cond, step, body);
            tree.pos = pos;
            return JmlForLoop(tree,null);
        }
        
        /** Creates a regular foreach-loop with no specifications */
        @Override
        public JCEnhancedForLoop ForeachLoop(JCVariableDecl var, JCExpression expr, JCStatement body) {
            JCEnhancedForLoop tree = super.ForeachLoop(var, expr, body);
            tree.pos = pos;
            return JmlEnhancedForLoop(tree,null);
        }
        
        /** Creates a regular do-loop with no specifications */
        @Override
        public JmlDoWhileLoop DoLoop(JCStatement body, JCExpression cond) {
            JCDoWhileLoop tree = super.DoLoop(body, cond);
            tree.pos = pos;
            return JmlDoWhileLoop(tree,null);
        }

        /** Creates a regular while-loop with no specifications */
        @Override
        public JmlWhileLoop WhileLoop(JCExpression cond, JCStatement body) {
            JCWhileLoop tree = super.WhileLoop(cond, body);
            tree.pos = pos;
            return JmlWhileLoop(tree,null);
        }

        /** Creates a for-loop with specifications */
        @Override
        public JmlForLoop JmlForLoop(JCForLoop loop, List<JmlStatementLoop> loopSpecs) {
            return new JmlForLoop(loop,loopSpecs);
        }
        
        /** Creates a foreach-loop with specifications */
        @Override
        public JmlEnhancedForLoop JmlEnhancedForLoop(JCEnhancedForLoop loop, List<JmlStatementLoop> loopSpecs) {
            return new JmlEnhancedForLoop(loop,loopSpecs);
        }
        
        /** Creates a while-loop with specifications */
        @Override
        public JmlWhileLoop JmlWhileLoop(JCWhileLoop loop, List<JmlStatementLoop> loopSpecs) {
            return new JmlWhileLoop(loop,loopSpecs); // pos and type set from loop
        }

        /** Creates a JML statement such as ghost declarations */
        @Override
        public JmlStatementDecls JmlStatementDecls(List<JCTree.JCStatement> list) {
            return new JmlStatementDecls(pos,list);
        }
        
        /** Creates JML statements such as set and debug */
        @Override
        public JmlStatement JmlStatement(JmlToken t, JCTree.JCExpressionStatement e) {
            return new JmlStatement(pos,t,e);
        }

        @Override
        public JmlStoreRefListExpression JmlStoreRefListExpression(JmlToken t, List<JCExpression> list) {
            return new JmlStoreRefListExpression(pos,t,list);
        }

        @Override
        public JmlStoreRefKeyword JmlStoreRefKeyword(JmlToken t) {
            return new JmlStoreRefKeyword(pos,t);
        }

        @Override
        public JmlStoreRefArrayRange JmlStoreRefArrayRange(JCExpression expr, JCExpression lo, JCExpression hi) {
            return new JmlStoreRefArrayRange(pos,expr,lo,hi);
        }

        @Override
        public JmlTypeClauseExpr JmlTypeClauseExpr(JCModifiers mods, JmlToken token, JCTree.JCExpression e) {
            JmlTypeClauseExpr t = new JmlTypeClauseExpr(pos,mods,token,e);
            t.source = Log.instance(context).currentSourceFile();
            return t;
        }
        
        @Override
        public JmlTypeClauseDecl JmlTypeClauseDecl(JCTree decl) {
            JmlTypeClauseDecl t = new JmlTypeClauseDecl(pos,decl);
            t.source = Log.instance(context).currentSourceFile();
            return t;
        }
        
        @Override
        public JmlTypeClauseInitializer JmlTypeClauseInitializer(JmlToken token) {
            JmlTypeClauseInitializer t = new JmlTypeClauseInitializer(pos, token);
            t.source = Log.instance(context).currentSourceFile();
            return t;
        }
        
        @Override
        public JmlTypeClauseConstraint JmlTypeClauseConstraint(JCModifiers mods, JCTree.JCExpression e, List<JmlConstraintMethodSig> sigs) {
            JmlTypeClauseConstraint t = new JmlTypeClauseConstraint(pos,mods,e,sigs);
            t.source = Log.instance(context).currentSourceFile();
            return t;
        }
        
        @Override
        public JmlChoose JmlChoose(JmlToken token, List<JCBlock> orBlocks, /*@Nullable*/JCBlock elseBlock) {
            return new JmlChoose(pos,token,orBlocks,elseBlock);
        }
        
        @Override
        public JmlConstraintMethodSig JmlConstraintMethodSig(JCExpression expr, List<JCExpression> argtypes) {
            return new JmlConstraintMethodSig(pos,expr,argtypes);
        }

        @Override
        public JmlTypeClauseRepresents JmlTypeClauseRepresents(JCModifiers mods, JCTree.JCExpression ident, boolean suchThat, JCTree.JCExpression e) {
            JmlTypeClauseRepresents t = new JmlTypeClauseRepresents(pos, mods, ident,suchThat,e);
            t.source = Log.instance(context).currentSourceFile();
            return t;
        }

        @Override
        public JmlTypeClauseConditional JmlTypeClauseConditional(JCModifiers mods, JmlToken token, JCTree.JCIdent ident, JCTree.JCExpression p) {
            JmlTypeClauseConditional t = new JmlTypeClauseConditional(pos, mods, token,ident,p);
            t.source = Log.instance(context).currentSourceFile();
            return t;
        }

        @Override
        public JmlTypeClauseMonitorsFor JmlTypeClauseMonitorsFor(JCModifiers mods, JCTree.JCIdent ident, List<JCTree.JCExpression> list) {
            JmlTypeClauseMonitorsFor t = new JmlTypeClauseMonitorsFor(pos, mods, ident, list);
            t.source = Log.instance(context).currentSourceFile();
            return t;
        }

        @Override
        public JmlMethodClauseGroup JmlMethodClauseGroup(List<JmlSpecificationCase> list) {
            return new JmlMethodClauseGroup(pos,list);
        }
        
        @Override
        public JmlMethodClauseDecl JmlMethodClauseDecl(JmlToken t, List<JCTree.JCVariableDecl> decls) {
            return new JmlMethodClauseDecl(pos,t,decls);
        }
        
        @Override
        public JmlMethodClauseExpr JmlMethodClauseExpr(JmlToken t, JCTree.JCExpression e) {
            return new JmlMethodClauseExpr(pos,t,e);
        }
        
        @Override
        public JmlDeclassifyClause JmlDeclassifyClause(JmlToken t, JCTree.JCExpression e, JCMethodInvocation policy) {
            return new JmlDeclassifyClause(pos,t,e, policy);
        }
        
        @Override
        public JmlLevelStatement JmlLevelStatement(JmlToken t, JCIdent level) {
            return new JmlLevelStatement(pos, level);
        }
        
        @Override
        public JmlMethodClauseCallable JmlMethodClauseCallable(JmlStoreRefKeyword keyword) {
        	return new JmlMethodClauseCallable(pos,keyword,null);
        }
        
        @Override
        public JmlMethodClauseCallable JmlMethodClauseCallable(List<JmlConstraintMethodSig> methodSignatures) {
        	return new JmlMethodClauseCallable(pos,null,methodSignatures);
        }
        
        @Override
        public JmlMethodClauseConditional JmlMethodClauseConditional(JmlToken t, JCTree.JCExpression e, JCTree.JCExpression p) {
            return new JmlMethodClauseConditional(pos,t,e,p);
        }
        
        @Override
        public JmlMethodClauseSignals JmlMethodClauseSignals(JmlToken t, JCTree.JCVariableDecl var, JCTree.JCExpression e) {
            return new JmlMethodClauseSignals(pos,t,var,e);
        }
        
        @Override
        public JmlMethodClauseSignalsOnly JmlMethodClauseSignalsOnly(JmlToken t, List<JCTree.JCExpression> e) {
            return new JmlMethodClauseSignalsOnly(pos,t,e);
        }

        @Override
        public JmlMethodClauseStoreRef JmlMethodClauseStoreRef(JmlToken t, List<JCExpression> list) {
            return new JmlMethodClauseStoreRef(pos, t, list);
        }

        @Override
        public JmlModelProgramStatement JmlModelProgramStatement(JCTree item) {
            return new JmlModelProgramStatement(pos, item);
        }

        @Override
        public JmlSpecificationCase JmlSpecificationCase(JCModifiers mods, boolean code, JmlToken t, JmlToken also, List<JmlMethodClause> clauses) {
            JmlSpecificationCase jcase = new JmlSpecificationCase(pos,mods,code,t,also,clauses);
            jcase.sourcefile = Log.instance(context).currentSourceFile();
            return jcase;
        }
        
        @Override
        public JmlSpecificationCase JmlSpecificationCase(JCModifiers mods, boolean code, JmlToken t, JmlToken also, JCBlock block) {
            JmlSpecificationCase jcase = new JmlSpecificationCase(pos,mods,code,t,also,block);
            jcase.sourcefile = Log.instance(context).currentSourceFile();
            return jcase;
        }
        
        @Override
        public JmlSpecificationCase JmlSpecificationCase(JmlSpecificationCase sc, List<JmlMethodClause> clauses) {
            return new JmlSpecificationCase(sc,clauses);
        }
        
        @Override
        public JmlMethodSpecs JmlMethodSpecs(List<JmlSpecificationCase> cases) {
            return new JmlMethodSpecs(pos,cases);
        }
        
        @Override
        public JmlGroupName JmlGroupName(JCExpression selection) {
            return new JmlGroupName(pos,selection);
        }
        
        @Override
        public JmlTypeClauseIn JmlTypeClauseIn(List<JmlGroupName> list) {
            JmlTypeClauseIn r = new JmlTypeClauseIn(pos,list);
            r.source = Log.instance(context).currentSourceFile();
            return r;
        }
        
        @Override
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
    // Here, the getKind method is implemented to return Kind.OTHER.  This is because
    // this method returns a Kind of node, but Kind is an enum of Java node kinds
    // and cannot be extended.  We use OTHER, despite the warning in Tree.java,
    // because there is no other option, besides null.  For JML nodes we don't
    // use this anyway (because of this problem).  

    // These numbers used for getTag();
    
    public static final int JMLFUNCTION = JCTree.LETEXPR + 100;  // The 100 is just to give some space, just in case LETEXPR stops being the largest tag number
    public static final int JMLBINARY = JMLFUNCTION + 1;
    public static final int JMLSTATEMENT = JMLBINARY + 1;
    public static final int JMLSTATEMENTSPEC = JMLBINARY + 1;
    public static final int JMLSTATEMENTLOOP = JMLSTATEMENTSPEC + 1;
    public static final int JMLSTATEMENTEXPR = JMLSTATEMENTLOOP + 1;
    public static final int JMLSTATEMENTHAVOC = JMLSTATEMENTEXPR + 1;
    public static final int JMLSTATEMENTDECLS = JMLSTATEMENTHAVOC + 1;
    public static final int JMLMETHODCLAUSEGROUP = JMLSTATEMENTDECLS + 1;
    public static final int JMLMETHODCLAUSECALLABLE = JMLMETHODCLAUSEGROUP + 1;
    public static final int JMLMETHODCLAUSEDECL = JMLMETHODCLAUSECALLABLE + 1;
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
    public static final int JMLTYPECLAUSEEXPR = JMLSINGLETON + 1;
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
    public static final int JMLDECLASSIFYCLAUSE = JMLSTOREREFARRAYRANGE + 1;
    public static final int JMLLEVELSTATEMENT   = JMLDECLASSIFYCLAUSE + 1;
    public static final int JMLLASTTAG = JMLLEVELSTATEMENT;

    /** The system-defined end of line character string */
    static public final String eol = System.getProperty("line.separator");

    static public void unexpectedVisitor(JCTree t, Object visitor) {
        // FIXME - a better error
        System.out.println("A " + t.getClass() + " expects an IJmlVisitor, not a " + visitor.getClass());
    }
    
    /** This is an interface for any node that contains source file information. */
    public interface JmlSource {
        
        /** Returns the file object containing the source code for the AST node */
        @NonNull JavaFileObject source();
    }
    
    /** This class adds some JML specific information to the JCCompilationUnit toplevel node. */
    public static class JmlCompilationUnit extends JCTree.JCCompilationUnit {
        
        /** This list contains the parse tree of the specification file, if any, for this compilation unit. 
         *  This field may point to 'this' if the compilation unit is its own specs file. */
        public /*@ nullable */ JmlCompilationUnit specsCompilationUnit = null;
        
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

        // FIXME - review the use of this value
        /** The use to be made of this parse tree - one of the int constants below. */
        public int mode = 0; // init to an unknown value
        
        /** An unspecified value. */
        public static final int UNKNOWN = 0; 
        
        // FIXME - the whole use of this mode needs reviewing
        
        // Properties are encoded as bits:
        // Note that a specification file can be .java or not .java
        //  1-bit  this is a file that can contain source code (i.e. has a .java suffix)
        //  2-bit  this is a specification file
        //  4-bit  the implementation is in a binary file, not a source file
        //  8-bit  full typechecking is desired - FIXME - do away with this I think
        
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
        
//        static public boolean isJava(int mode) { return (mode & 1) != 0; }
//        
//        static public boolean isSpec(int mode) { return (mode & 2) != 0; }
        
        static public boolean isForSource(int mode) { return (mode & 4) == 0; }
        
        static public boolean isForBinary(int mode) { return (mode & 4) != 0; }
        
//        static public boolean isFull(int mode) { return (mode & 8) == 0; }

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlCompilationUnit(List<JCAnnotation> packageAnnotations,
                JCExpression pid,
                List<JCTree> defs,
                JavaFileObject sourcefile,
                PackageSymbol packge,
                ImportScope namedImportScope,
                StarImportScope starImportScope) {
            super(packageAnnotations,pid,defs,sourcefile,packge,namedImportScope,starImportScope);
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlCompilationUnit(this); 
            } else {
                // unexpectedVisitor(this,v);
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlCompilationUnit(this, d);
            } else {
                // unexpectedVisitor(this,v);
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

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlImport(JCTree qualid, boolean importStatic, boolean isModel) {
            super(qualid,importStatic);
            this.isModel = isModel;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlImport(this); 
            } else {
                // unexpectedVisitor(this,v);
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlImport(this, d);
            } else {
                // unexpectedVisitor(this,v);
                return super.accept(v,d);
            }
        }
        
        @Override
        public String toString() {
            return JmlTree.toString(this);
        }

    }
    
    /** This class represents model program choose and choose_if statements. */
    public static class JmlChoose extends JmlAbstractStatement {

        public JmlToken token;
        public List<JCBlock> orBlocks;
        /*@Nullable*/ public JCBlock elseBlock;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlChoose(int pos, JmlToken token, List<JCBlock> orBlocks, /*@Nullable*/ JCBlock elseBlock) {
            this.pos = pos;
            this.token = token;
            this.orBlocks = orBlocks;
            this.elseBlock = elseBlock;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlChoose(this); 
            } else {
                // unexpectedVisitor(this,v);
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlChoose(this, d);
            } else {
                // unexpectedVisitor(this,v);
                return super.accept(v,d);
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
         * NOTE: JML has been revised to have only one specs file per java file, so this list
         * will at most have one element (which may be the original class definition from the
         * .java file itself)
         */
        public /*@Nullable*/ JmlClassDecl specsDecls;

        /** This field is the combination of specifications from all
         * specification sources (valid for the Java declaration, or, for
         * binary files, for the most refined specs file)
         */        
        public JmlSpecs.TypeSpecs typeSpecsCombined; 
        
        /** This field holds the class-level specifications given in this 
         * particular class declaration; it may not be all the specs of the class.
         */
        public JmlSpecs.TypeSpecs typeSpecs;

        /** The top-level tree that this class declaration belongs to; for specification
         * declarations this is the compilation unit containing the spec declaration, which
         * may be different than the compilation unit containing the java class declaration. 
         * Note that the sourcefile for this class declaration can be obtained from
         * toplevel.sourcefile*/
        public JmlCompilationUnit toplevel;
        
        // FIXME - is this used; why would it not be in JCClassDecl?
        public String docComment = null;
        
        /** The scope environment just inside this class (e.g. with type parameters
         * added.  Not set or used in parsing; set during the enter phase and
         * used there and during type attribution. // FIXME - clarify why we need this
         */
        public Env<AttrContext> env;
        
        /** Set during attribution, used during RAC - the value in Enter is 
         * removed by then.
         */
        public VarSymbol thisSymbol;
        public VarSymbol superSymbol;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlClassDecl(JCModifiers mods, Name name,
                List<JCTypeParameter> typarams, JCExpression extending,
                List<JCExpression> implementing, List<JCTree> defs,
                ClassSymbol sym) {
            super(mods, name, typarams, extending, implementing, defs, sym);
            specsDecls = null;
            typeSpecs = null;
        }
        
        /** The source this class was declared in (model classes may be declared
         * in a source file different than the class that owns the model class)
         */
        @Override
        public JavaFileObject source() { return toplevel == null ? null : toplevel.sourcefile; }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlClassDecl(this); 
            } else {
                // unexpectedVisitor(this,v);
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlClassDecl(this, d);
            } else {
                // unexpectedVisitor(this,v);
                return super.accept(v,d);
            }
        }
        
        @Override
        public String toString() {
            return JmlTree.toString(this);
        }
        
        public boolean isTypeChecked() {
            ClassSymbol c = sym;
            if (c == null) return false;
            return ((c.flags_field & UNATTRIBUTED) == 0);
        }
    }

    /** This class adds some JML specific information to the JCMethodDecl node. */
    public static class JmlMethodDecl extends JCTree.JCMethodDecl implements JmlSource {
        // FIXME - need some documentation of these fields
        public JmlMethodDecl specsDecl;
        public JmlMethodSpecs cases;  // FIXME - change to JmlSpecificationCase?
        public JmlSpecs.MethodSpecs methodSpecsCombined;
        //public JmlClassDecl owner;
        public JavaFileObject sourcefile;
        public String docComment = null; // FIXME - clarify why needed
        public VarSymbol _this = null; // The Symbol for 'this' inside the method, if not static;
                                        // valid after attribution
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        public JmlMethodDecl(JCModifiers mods, Name name, JCExpression restype,  // FIXME - backdoor use - should not be public
                List<JCTypeParameter> typarams, List<JCVariableDecl> params,
                List<JCExpression> thrown, JCBlock body,
                JCExpression defaultValue, MethodSymbol sym) {
            super(mods, name, restype, typarams, params, thrown, body, defaultValue, sym);
            specsDecl = null;
            sourcefile = null;
        }
        
        /** The source this method was declared in (model methods may be declared
         * in a source file different than the class that owns the model method)
         */
        @Override
        public JavaFileObject source() { return sourcefile; }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodDecl(this); 
            } else {
                // unexpectedVisitor(this,v);
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodDecl(this, d);
            } else {
                // unexpectedVisitor(this,v);
                return super.accept(v,d);
            }
        }
        
        @Override
        public String toString() {
            return JmlTree.toString(this);
        }

    }
    
    /** This class adds some JML specific information to the JCVariableDecl node. */
    public static class JmlVariableDecl extends JCTree.JCVariableDecl implements JmlSource {
        // FIXME - need some documentation of these fields
        public JmlVariableDecl specsDecl;
        public JmlSpecs.FieldSpecs fieldSpecs;
        public JmlSpecs.FieldSpecs fieldSpecsCombined;
        public JavaFileObject sourcefile;
        //
        public JmlLevelStatement levelType;
        
        public String docComment = null; // FIXME - why?
        
        /** A fixed ident used in ESC */
        public JCIdent ident = null;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlVariableDecl(JCModifiers mods, Name name,
                JCExpression vartype, JCExpression init, VarSymbol sym) {
            super(mods, name, vartype, init, sym);
            specsDecl = null;
            fieldSpecs = null;
            fieldSpecsCombined = null;
            sourcefile = null;
        }
        
        /** The source this variable was declared in (model variable may be declared
         * in a source file different than the class that owns the model variable)
         */
        @Override
        public JavaFileObject source() { return sourcefile; }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlVariableDecl(this); 
            } else {
                // unexpectedVisitor(this,v);
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlVariableDecl(this, d);
            } else {
                // unexpectedVisitor(this,v);
                return super.accept(v,d);
            }
        }
        
        @Override
        public String toString() {
            return JmlTree.toString(this);
        }

    }

    /** An abstract class that parents any Jml expression classes (that are not
     * special cases of other specific Java expressions)
     */
    abstract public static class JmlExpression extends JCTree.JCExpression {
        @Override
        public String toString() {
            return JmlTree.toString(this);
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

    /** This class represents binary expressions with JML operators */
    public static class JmlBinary extends JmlExpression implements IJmlBinary {
        public JmlToken op;
        public JCExpression lhs;
        public JCExpression rhs;
        
        @Override
        public ExpressionTree getLeftOperand() { return lhs; }
        
        @Override
        public JmlToken getOp() { return op; }
        
        @Override
        public ExpressionTree getRightOperand() {return rhs; }

        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
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

//        public Symbol getOperator() {
//            return null; // FIXME
//        }

        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public int getTag() {
            // This is used in determining start and end positions
            return JCTree.OR;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlBinary(this); 
            } else {
                lhs.accept(v);
                rhs.accept(v);
                //unexpectedVisitor(this,v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlBinary(this, d);
            } else {
                unexpectedVisitor(this,v);
                return null;
            }
        }
        
    }

    /** This class represents the method signatures in the constraint type
     * specification clause or the callable method specification clause.
     * @author David Cok
     */
    public static class JmlConstraintMethodSig extends JCTree {
        public JCExpression expression;
        public List<JCExpression> argtypes;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlConstraintMethodSig(int pos, JCExpression expr, List<JCExpression> argtypes) {
            this.pos = pos;
            this.expression = expr;
            this.argtypes = argtypes;
        }
    
        @Override
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
               ((IJmlVisitor)v).visitJmlConstraintMethodSig(this); 
            } else {
                unexpectedVisitor(this,v);
                //super.accept(v);
            }
        }
    
        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlConstraintMethodSig(this, d);
            } else {
                unexpectedVisitor(this,v);
                return null; //return super.accept(v,d);
            }
        }
        
        @Override
        public String toString() {
            return JmlTree.toString(this);
        }
    }

    /** This class wraps a Java do while loop just so it can attach some specs
     * to it.
     */
    public static class JmlDoWhileLoop extends JCDoWhileLoop {
    
        public List<JmlStatementLoop> loopSpecs;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlDoWhileLoop(JCDoWhileLoop loop, List<JmlStatementLoop> loopSpecs) {
            super(loop.body,loop.cond);
            this.pos = loop.pos;
            this.type = loop.type; // copied for completeness, in case a loop ever has a type
            this.loopSpecs = loopSpecs;
        }
    
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlDoWhileLoop(this); 
            } else {
                // unexpectedVisitor(this,v);
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
        
        @Override
        public String toString() {
            return JmlTree.toString(this);
        }
    
    }

    /** This class wraps a Java enhanced loop just so it can attach some specs
     * to it.
     */
    public static class JmlEnhancedForLoop extends JCEnhancedForLoop {

        public List<JmlStatementLoop> loopSpecs;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlEnhancedForLoop(JCEnhancedForLoop loop, List<JmlStatementLoop> loopSpecs) {
            super(loop.var, loop.expr, loop.body);
            this.pos = loop.pos;
            this.type = loop.type; // copied for completeness, in case a loop ever has a type
            this.loopSpecs = loopSpecs;
        }
        
        // These are used for rewriting the loop in JmlAttr
        public JCVariableDecl indexDecl;
        public JCVariableDecl valuesDecl;
        public JCVariableDecl iterDecl;
        public JCBlock implementation;
        public JmlForLoop internalForLoop;

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
        
        @Override
        public String toString() {
            return JmlTree.toString(this);
        }

    }

    /** This class wraps a Java for loop just so it can attach some specs
     * to it.
     */
    public static class JmlForLoop extends JCForLoop {
    
        public List<JmlStatementLoop> loopSpecs;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlForLoop(JCForLoop loop, List<JmlStatementLoop> loopSpecs) {
            super(loop.init,loop.cond,loop.step,loop.body);
            this.pos = loop.pos;
            this.type = loop.type; // copied for completeness, in case a loop ever has a type
            this.loopSpecs = loopSpecs;
        }
    
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
        
        @Override
        public String toString() {
            return JmlTree.toString(this);
        }
    
    }

    /** This class wraps a Java while loop just so it can attach some specs
     * to it.
     */
    public static class JmlWhileLoop extends JCWhileLoop {
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlWhileLoop(JCWhileLoop loop, List<JmlStatementLoop> loopSpecs) {
            super(loop.cond,loop.body);
            this.pos = loop.pos;
            this.type = loop.type; // copied for completeness, in case a loop ever has a type
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
        
        @Override
        public String toString() {
            return JmlTree.toString(this);
        }
    
    }

    /** This class represents a group in an "in" or "maps" type clause in a class specification */
    public static class JmlGroupName extends JCTree {
    
        public JCExpression selection;
        public VarSymbol sym;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlGroupName(int pos, JCExpression selection) {
            this.pos = pos;
            this.selection = selection;
        }
        
        @Override
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
        
        @Override
        public String toString() {
            return JmlTree.toString(this);
        }
    }

    /** This class represents JML LBL expressions */
    public static class JmlLblExpression extends JmlExpression {
        /** The kind of label (BSLBLANY, BSLBLPOS, BSLBLNEG) */
        public JmlToken token;
        /** The name given by the label*/
        public Name label;
        /** The expression that is labelled */
        public JCExpression expression;
        
        public int labelPosition;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlLblExpression(int pos, int labelPosition, JmlToken token, Name label, JCTree.JCExpression expr) {
            this.pos = pos;
            this.token = token;
            this.label = label;
            this.expression = expr;
            this.labelPosition = labelPosition;
        }
        
        /*@ pure */
        public int getLabelPosition() {
            return labelPosition;
        }
    
        @Override
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

    /** This is an abstract class that is a parent to any type of clause in
     * a method specification (e.g. requires).
     */
    abstract public static class JmlMethodClause extends JmlAbstractStatement implements JmlSource {
        public JmlToken token;
        public JavaFileObject sourcefile;  // FIXME - don't think this belongs here
        public JavaFileObject source() { return sourcefile; }
    }
    
    /** This class represents a method specification clause that has an
     * expression, but also a conditional when it is enabled. (FIXME - examples?)
     */
    public static class JmlMethodClauseConditional extends JmlMethodClause {
    
        public JCTree.JCExpression expression;
        /*@ nullable */ public JCTree.JCExpression predicate;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseConditional(int pos, JmlToken token, JCTree.JCExpression expression, /*@ nullable*/ JCTree.JCExpression predicate) {
            this.pos = pos;
            this.token = token;
            this.expression = expression;
            this.predicate = predicate;
        }
    
        @Override
        public int getTag() {
            return JMLMETHODCLAUSECONDITIONAL;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
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

    /** This class represents JML function invocations (e.g. \typeof, \old, ...);
     * note that the method expression may be null if the JML token is present. */
    public static class JmlMethodInvocation extends JCMethodInvocation {
        public int startpos;
        public JmlToken token;
        public Label label = null; // FIXME - explain this
        public boolean javaType = false; // FIXME - this is a hack
        
        /** Creates a method invocation for a JML specific construct (e.g. \typeof) -
         * no type arguments and no expression for the method name, just a token.
          - but use the factory to get new nodes, not this */
        protected JmlMethodInvocation(int pos,
                JmlToken token,
                List<JCExpression> args)
        {
            super(List.<JCExpression>nil(),null,args);
            this.token = token;
            this.pos = pos; // preferred position
            this.startpos = pos;
        }
        
        /** Creates a method invocation like a Java method invocation, except without type qualifiers */
        protected JmlMethodInvocation(int pos,
                JCExpression method,
                List<JCExpression> args)
        {
            super(List.<JCExpression>nil(),method,args);
            this.token = null;
            this.pos = pos; // preferred position
            this.startpos = pos;
        }
        
        @Override
        public int getStartPosition() {
            return meth == null ? startpos : super.getStartPosition();
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
        
//        @Override  -- FIXME - do we want this?
//        public int getTag() {
//            return JMLFUNCTION;
//        }
//    
    }

    /** This class represents a method specification clause that has just an
     * expression (e.g. requires, ensures).
     */
    public static class JmlMethodClauseCallable extends JmlMethodClause {

        public JmlStoreRefKeyword keyword;
        public List<JmlConstraintMethodSig> methodSignatures;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseCallable(int pos, JmlStoreRefKeyword keyword, List<JmlConstraintMethodSig> methodSignatures) {
            this.pos = pos;
            this.keyword = keyword;
            this.methodSignatures = methodSignatures;
        }

        @Override
        public int getTag() {
            return JMLMETHODCLAUSECALLABLE;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodClauseCallable(this); 
            } else {
                //System.out.println("A JmlMethodClauseExpr expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodClauseCallable(this, d);
            } else {
                System.out.println("A JmlMethodClauseCallable expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    
    
    /** This class represents a forall or old method specification clause.*/
    public static class JmlMethodClauseDecl extends JmlMethodClause {

        public List<JCTree.JCVariableDecl> decls;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseDecl(int pos, JmlToken token, List<JCTree.JCVariableDecl> decls) {
            this.pos = pos;
            this.token = token;
            this.decls = decls;
        }

        @Override
        public int getTag() {
            return JMLMETHODCLAUSEDECL;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
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
     * expression (e.g. requires, ensures).
     */
    public static class JmlMethodClauseExpr extends JmlMethodClause {

        public JCTree.JCExpression expression;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseExpr(int pos, JmlToken token, JCTree.JCExpression expression) {
            this.pos = pos;
            this.token = token;
            this.expression = expression;
        }

        @Override
        public int getTag() {
            return JMLMETHODCLAUSEEXPR;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
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
    
    public static class JmlDeclassifyClause extends JmlMethodClause {

        public JCTree.JCExpression expression;
        public JCTree.JCMethodInvocation policy;

        protected JmlDeclassifyClause(int pos, JmlToken token, JCTree.JCExpression expression, JCTree.JCMethodInvocation policy) {
            this.pos = pos;
            this.token = token;
            this.expression = expression;
            this.policy = policy;
        }

        @Override
        public int getTag() {
            return JMLDECLASSIFYCLAUSE;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlDeclassifyClause(this); 
            } else {
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlDeclassifyClause(this, d);
            } else {
                //TODO -- do we need these?
                System.out.println("A JmlMethodClauseExpr expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
    }
    
    
    /** This represents the sequence of method specs lists that are the sequence
     * of nested specs
     */
    public static class JmlMethodClauseGroup extends JmlMethodClause {

        public List<JmlSpecificationCase> cases;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseGroup(int pos, List<JmlSpecificationCase> cases) {
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

    /** This class represents a signals clause in a method specification. */
    public static class JmlMethodClauseSignals extends JmlMethodClause {

        public JCTree.JCVariableDecl vardef;
        public JCTree.JCExpression expression;

        // NOTE: the ident in the variable declaration may be null
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseSignals(int pos, JmlToken token, JCTree.JCVariableDecl var, JCTree.JCExpression expression) {
            this.pos = pos;
            this.token = token;
            this.vardef = var;
            this.expression = expression;
        }
        
        @Override
        public int getTag() {
            return JMLMETHODCLAUSESIGNALS;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
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
    public static class JmlMethodClauseSignalsOnly extends JmlMethodClause {

        /** The list of names of exceptions - either JCIdent or JCFieldAccess */
        // FIXME - why not Names?
        public List<JCTree.JCExpression> list;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseSignalsOnly(int pos, JmlToken token, List<JCTree.JCExpression> list) {
            this.pos = pos;
            this.token = token;
            this.list = list;
        }

        @Override
        public int getTag() {
            return JMLMETHODCLAUSESIGNALSONLY;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodClauseSigOnly(this); 
            } else {
                //System.out.println("A JmlMethodClauseSignalsOnly expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodClauseSigOnly(this, d);
            } else {
                System.out.println("A JmlMethodClauseSignalsOnly expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }

    /** This class represents an assignable clause in a method specification */
    public static class JmlMethodClauseStoreRef extends JmlMethodClause {

        /** The list of store-ref expressions in the clause */
        public List<JCExpression> list;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseStoreRef(int pos, JmlToken token, List<JCExpression> list) {
            this.pos = pos;
            this.token = token;
            this.list = list;
        }

        @Override
        public int getTag() {
            return JMLMETHODCLAUSEASSIGNABLE;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
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
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodClauseStoreRef(this, d);
            } else {
                //System.out.println("A JmlMethodClauseAssignable expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    
    /** This class represents the specifications of a method (a list of 
     * specification cases); it may be the combined set of cases across multiple
     * compilation units.
     */
    public static class JmlMethodSpecs extends JmlAbstractStatement {
        /** This is a reference to a parent declaration, in order to have access 
         * to the parameter and result modifiers
         */
        public JmlMethodDecl decl = null;
        
        /** The standard specification cases */
        public List<JmlSpecificationCase> cases;
        
        /** The implies-that specification cases */
        public List<JmlSpecificationCase> impliesThatCases;
        
        /** The for-example specification cases */
        public List<JmlSpecificationCase> forExampleCases;
        
        
        public JmlMethodSpecs deSugared = null; // FIXME - should this be here?
        
        // FIXME - should these constructors be public?
        
        /** Creates an instance with only regular cases (no impliesThat or example cases)*/
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

    /** This class represents JML statements within the body of a model
     * program that are not statements themselves, such as 
     * invariants, specification cases
     */
    public static class JmlModelProgramStatement extends JmlAbstractStatement {
        // FIXME - nthis needs filling out with various kinds of model program statements
        public JCTree item;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlModelProgramStatement(int pos, JCTree item) {
            this.pos = pos;
            this.item = item;
        }
        
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
            // Simply delegate to the wrapped construct
            item.accept(v);
        }
    
        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            return item.accept(v,d);
        }
    }

    /** This class represents JML primitive types */
    static public class JmlPrimitiveTypeTree extends JCTree.JCPrimitiveTypeTree {
        
        public JmlToken token;
        
        /** The representation of this JML type when used in RAC */
        public JCExpression repType;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlPrimitiveTypeTree(int pos, JmlToken token) {
        	super(TypeTags.NONE);
            this.pos = pos;
            this.token = token;
        }
        
        @Override
        public String toString() {
            return token != null ? token.internedName() : super.toString();
        }
    
        @Override
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

    /** This class represents JML quantified expressions */
    public static class JmlQuantifiedExpr extends JmlExpression {
        // Current JML allows multiple bound variables in a quantified expression,
        // but requires them all to have the same type.  However, in anticipation of
        // relaxing this requirement and for use elsewhere (i.e. in ESC) this
        // class permits different types.
        
        /** The operation, e.g \\forall, \\exists, \\let, ... */
        public JmlToken op;
        
        /** The declarations over which the expressions are quantified */
        public List<JCVariableDecl> decls;
        
        /** The predicate restricting the range of iteration */
        public JCExpression range;
        
        /** The value - e.g. a predicate for forall, a numeric value for sum, etc. */
        public JCExpression value;
        
        /** A (partial) expression used in RAC, but constructed here for convenience */
        public JCExpression racexpr;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlQuantifiedExpr(int pos, JmlToken op,
                List<JCVariableDecl> decls,
                JCExpression range, JCExpression value) {
            this.pos = pos;
            this.op = op;
            this.decls = decls;
            this.range = range;
            this.value = value;
            this.racexpr = null;
        }
        
        @Override
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
                // FIXME - this does get visited during type entering and annotation
                // by TypeAnnotate and Attr - should make JML versions of these
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

    
    /** This class represents JML expression constructs which do not have arguments (syntactically). */
    public static class JmlSingleton extends JmlExpression {
        public JmlToken token;
        public Symbol symbol;  // Convenience for some node types
        public Object info = null;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlSingleton(int pos, JmlToken token) {
            this.pos = pos;
            this.token = token;
        }

        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }

        @Override
        public int getTag() {
            return JMLSINGLETON;
        }

        @Override
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

    /** This class represents JML set comprehension expressions */
    public static class JmlSetComprehension extends JmlExpression {
        public JCExpression newtype;
        public JCVariableDecl variable;
        public JCExpression predicate;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlSetComprehension(int pos, JCExpression type, JCVariableDecl var, JCExpression predicate) {
            this.pos = pos;
            this.newtype = type;
            this.variable = var;
            this.predicate = predicate;
        }
    
        @Override
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

    /** This class represents a specification case in a method specification */
    public static class JmlSpecificationCase extends JmlAbstractStatement implements JmlSource {
        public JCModifiers modifiers;
        public JmlToken token;
        public JmlToken also;
        public boolean code;
        public List<JmlMethodClause> clauses; // A behavior spec case has clauses but no block of statements
        public JCBlock block;  // A model program has a block (of statements) but no clauses
        public JavaFileObject sourcefile;
        
        // FIXME - public constructors - use facctory?
        
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
        
        @Override
        public JavaFileObject source() { return sourcefile; }
    
    
        @Override
        public int getTag() {
            return JMLSPECIFICATIONCASE;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
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

    /** This class represents JML statements within the body of a method
     * that take a statement, such as set and debug
     */
    public static class JmlStatement extends JmlAbstractStatement {
        public JmlToken token;
        public JCTree.JCExpressionStatement statement;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStatement(int pos, JmlToken token, JCTree.JCExpressionStatement statement) {
            this.pos = pos;
            this.token = token;
            this.statement = statement;
        }
    
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

    public static class JmlLevelStatement extends JmlAbstractStatement {
        public JmlToken token;
        public JCIdent   level;
        
        protected JmlLevelStatement(int pos, JCIdent level){
            this.pos = pos;
            this.token = JmlToken.LEVEL;
            this.level = level;
        }
        
        @Override
        public int getTag() {
            return JMLLEVELSTATEMENT;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
    
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlLevelStatement(this); 
            } else {
                super.accept(v);            
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlLevelStatement(this, d);
            } else {
                //TODO -- do we need these?
                System.out.println("A JmlLevelStatement expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }

        
        
    }
    
    /** This class represents JML ghost declarations and model local class
     * declarations (FIXME _ local class?)
     */
    public static class JmlStatementDecls extends JmlAbstractStatement {
        public JmlToken token;
        public List<JCTree.JCStatement> list;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStatementDecls(int pos, List<JCTree.JCStatement> list) {
            this.pos = pos;
            this.token = JmlToken.GHOST;
            this.list = list;
        }
    
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

    /** This class represents JML statements within the body of a method
     * that take an expression, such as assert, assume, unreachable, reachable
     */
    public static class JmlStatementExpr extends JmlAbstractStatement {
        /** The kind of statement - e.g. ASSERT, ASSUME, COMMENT, ... */
        public JmlToken token;
        
        /** The associated expression (e.g. the asserted condition) */
        public JCTree.JCExpression expression;
        
        /** An associated optional expression (e.g. such as the one that
         * can come with a Java assert statement).
         */
        public JCTree.JCExpression optionalExpression = null;
        
//        /** The line number corresponding to pos */
//        public int line; 
//        
        /** The source file in which the statement sits (and the file to which pos and line correspond) */
        public JavaFileObject source;
        
        /** A Label that gives detail about the kind of assertion or assumption */
        public Label label;
        
        /** A String just used to distinguish assertions for reporting purposes */
        public String id = null;
        
        /** A descriptive string for reporting purposes */
        public String description = null;
        
        /** The file containing the specification (e.g. clause) from which this
         * assertion or assumption arises; if null then is the same as source. 
         * (source and pos are the location in 
         * the code where the assertion or assumption is being stated.)
         */
        public JavaFileObject associatedSource = null;
        
        /** The position within associatedSource */
        public int associatedPos;  // TODO - change to DiagnosticPosition
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStatementExpr(int pos, JmlToken token, Label label, JCTree.JCExpression expression) {
            this.pos = pos;
            this.token = token;
            this.expression = expression;
            this.label = label;
            this.associatedPos = pos;
        }
    
        @Override
        public int getTag() {
            return JMLSTATEMENTEXPR;
        }
        
        @Override
        public int getStartPosition() {
            return expression != null ? expression.getStartPosition() : this.pos;
        }
        @Override
        public int getEndPosition(Map<JCTree,Integer> table) {
            return optionalExpression != null ? optionalExpression.getEndPosition(table) : expression != null ? expression.getEndPosition(table) : this.pos;
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

    /** This class represents a JML havoc statement, which declares that
     * the specified variables (store-refs) have unknown values.
     */
    public static class JmlStatementHavoc extends JmlAbstractStatement {
        /** Should always be HAVOC */
        public JmlToken token;
        
        /** The store-refs whose values are unknown */
        public List<JCTree.JCExpression> storerefs;
                
        /** The source file in which the statement sits (and the file to which pos and line correspond) */
        public JavaFileObject source;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStatementHavoc(int pos, List<JCTree.JCExpression> storerefs) {
            this.pos = pos;
            this.token = JmlToken.HAVOC;
            this.storerefs = storerefs;
        }
    
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
                ((IJmlVisitor)v).visitJmlStatementHavoc(this); 
            } else {
                //System.out.println("A JmlStatementExpr expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }
    
        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlStatementHavoc(this, d);
            } else {
                //System.out.println("A JmlStatementHavoc expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    /** This is a special kind of assume statement, one that is defining a new variable;
     * it does not occur in source code, but is created upon transforming declarations and
     * assignments into assume statements. Some provers are able to deal differently with
     * declarations/definitions rather than simple logical assumptions.
     */ // FIXME - not yet used anywhere - use a factory - protected constructor
    public static class JmlDefinition extends JmlStatementExpr {
        public JCIdent id;
        public JCExpression value;
        public JmlDefinition(int pos, JCIdent id, JCExpression value, JCExpression expr) {
            super(pos,JmlToken.ASSUME,null,expr);
            this.id = id;
            this.value = value;
        }
    }

    /** This class represents JML method specifications within the body of a method
     * that then apply to the next statement
     */
    public static class JmlStatementSpec extends JmlAbstractStatement {
        public JmlMethodSpecs statementSpecs;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStatementSpec(int pos, JmlMethodSpecs statementSpecs) {
            this.pos = pos;
            this.statementSpecs = statementSpecs;
        }
    
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
     */
    public static class JmlStatementLoop extends JmlAbstractStatement {
        public JmlToken token;
        public JCTree.JCExpression expression;
        public VarSymbol sym; // FIXME - put this in the copy constructors etc. - what is it for?
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStatementLoop(int pos, JmlToken token, JCTree.JCExpression expression) {
            this.pos = pos;
            this.token = token;
            this.expression = expression;
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
    
    /** This node represents a store-ref expression denoting an array range:
     *   a[*] or a[1 .. 2] or a[1 .. ]   FIXME - or is that a[1 .. *]
     * @author David Cok
     */
    public static class JmlStoreRefArrayRange extends JmlExpression {
        public JCExpression expression;
        public @Nullable JCExpression lo;
        public @Nullable JCExpression hi;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStoreRefArrayRange(int pos, JCExpression expr, @Nullable JCExpression lo, @Nullable JCExpression hi) {
            this.pos = pos;
            this.expression = expr;
            this.lo = lo;
            this.hi = hi;
        }
    
        @Override
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

    /** Represents a nothing, everything or informal comment token */
    // FIXME - is the content of the informal comment stored somewhere?  JmlExpression???
    public static class JmlStoreRefKeyword extends JmlExpression {
        public JmlToken token; // nothing or everything or informal comment

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStoreRefKeyword(int pos, JmlToken token) {
            this.pos = pos;
            this.token = token;
        }

        @Override
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
    }

    /** This class represents JML functions that take a list of store-refs as arguments. */
    public static class JmlStoreRefListExpression extends JmlExpression {
        public JmlToken token;
        public List<JCExpression> list;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStoreRefListExpression(int pos, JmlToken token, List<JCExpression> list) {
            this.pos = pos;
            this.token = token;
            this.list = list;
        }

        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }

        @Override
        public int getTag() {
            return JMLSTOREREFLISTEXPR;
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

    /** This class represents type clauses (e.g. invariant, constraint,...) in a class specification */
    abstract public static class JmlTypeClause extends JCTree implements JmlSource {
        
        /** The token identifying the kind of clause this represents */
        public JmlToken token;
        
        /** The source of this clause, since it might be from a different compilation unit. */
        public JavaFileObject source;
        
        /** The modifiers for the clause */
        public JCModifiers modifiers;

        /** Returns the source file for the clause */
        public JavaFileObject source() { return source; }
        
        /** This implements toString() for all the type clause nodes */
        public String toString() {
            return JmlTree.toString(this);
        }
    }
    
    /** This class represents 'represents' type clauses  in a class specification */
    public static class JmlTypeClauseConstraint extends JmlTypeClause {

        /** The constraint expression */
        public JCTree.JCExpression expression;
        
        /** The list of method signatures to which the constraint applies */
        public @Nullable List<JmlConstraintMethodSig> sigs;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlTypeClauseConstraint(int pos, JCModifiers mods, JCExpression expression, List<JmlConstraintMethodSig> sigs) {
            this.pos = pos;
            this.modifiers = mods;
            this.token = JmlToken.CONSTRAINT;
            this.expression = expression;
            this.sigs = sigs; // Method signatures
        }
        
        @Override
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
    
    /** This class represents readable_if and writable_if type clauses */
    public static class JmlTypeClauseConditional extends JmlTypeClause {
    
        public JCTree.JCIdent identifier;
        public JCTree.JCExpression expression;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlTypeClauseConditional(int pos, JCModifiers mods, JmlToken token, JCTree.JCIdent ident, JCTree.JCExpression expression) {
            this.pos = pos;
            this.modifiers = mods;
            this.token = token;
            this.identifier = ident;
            this.expression = expression;
        }
        
        @Override
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

    /** This class represents type clauses that are declarations (ghost and model) */
    public static class JmlTypeClauseDecl extends JmlTypeClause {
        
        public JCTree decl;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlTypeClauseDecl(int pos, JCTree decl) {
            this.pos = pos;
            this.token = JmlToken.JMLDECL;
            this.modifiers = 
                    decl instanceof JCVariableDecl ? ((JCVariableDecl)decl).mods :
                        decl instanceof JCMethodDecl ? ((JCMethodDecl)decl).mods :
                            decl instanceof JCClassDecl ? ((JCClassDecl)decl).mods :
                        null;  // FIXME - something wrong if this is null
            this.decl = decl;
        }
        
        @Override
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

    /** This class represents type clauses (e.g. invariant, axiom, 
     * ...) in a class specification */
    public static class JmlTypeClauseExpr extends JmlTypeClause {
        /** The expression that is part of the clause */
        public JCTree.JCExpression expression;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlTypeClauseExpr(int pos, JCModifiers mods, JmlToken token, JCTree.JCExpression expression) {
            this.pos = pos;
            this.modifiers = mods;
            this.token = token;
            this.expression = expression;
        }
        
        @Override
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
    
    /** This class represents an "in" type clause in a class specification */
    public static class JmlTypeClauseIn extends JmlTypeClause {
    
        /** The list of names that is the target of the in clause */
        public List<JmlGroupName> list;
        
        /** The variable declaration that this clause is associated with
         * (this is a reference to a parent node, not a subtree) */
        public JmlVariableDecl parentVar;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlTypeClauseIn(int pos, List<JmlGroupName> list) {
            this.pos = pos;
            this.token = JmlToken.IN;
            this.list = list;
            this.parentVar = null;
        }
        
        @Override
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

    /** This class represents initializer and static_initializer clauses  in a class specification */
    public static class JmlTypeClauseInitializer extends JmlTypeClause {
    
        /** The specifications that go with a JML initializer declaration */
        public JmlMethodSpecs specs;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlTypeClauseInitializer(int pos, JmlToken token) {
            this.pos = pos;
            this.token = token;
            this.source = null;
            this.modifiers = null; 
            // FIXME - needs to set modifiers
        }
        
        @Override
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

    /** This class represents type clauses (e.g. invariant, constraint,...) in a class specification */
    public static class JmlTypeClauseMaps extends JmlTypeClause {
    
        /** The maps store-ref expression */
        public JCExpression expression;
        
        /** The list of datagroup targets */
        public List<JmlGroupName> list;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlTypeClauseMaps(int pos, JCExpression e, List<JmlGroupName> list) {
            this.pos = pos;
            this.expression = e;
            this.modifiers = null;
            this.token = JmlToken.MAPS;
            this.list = list;
        }
        
        @Override
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

    /** This class represents monitors_for type clauses */
    public static class JmlTypeClauseMonitorsFor extends JmlTypeClause {

        public JCTree.JCIdent identifier;
        public List<JCTree.JCExpression> list;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlTypeClauseMonitorsFor(int pos, JCModifiers mods, JCIdent ident, List<JCTree.JCExpression> list) {
            this.pos = pos;
            this.modifiers = mods;
            this.identifier = ident;
            this.token = JmlToken.MONITORS_FOR;
            this.list = list;
        }
        
        @Override
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
    
    /** This class represents 'represents' type clauses  in a class specification */
    public static class JmlTypeClauseRepresents extends JmlTypeClause {
    
        /** The identifier or store-ref expression that is the target of the represents clause */
        public JCTree.JCExpression ident; // a store-ref expression  // FIXME - doesn't this need to be a simple name?
        
        /** true if this is a such-that rather than an equality represents clause */
        public boolean suchThat;
        
        /** The representing expression or boolean predicate */
        public JCTree.JCExpression expression;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlTypeClauseRepresents(int pos, JCModifiers mods, JCTree.JCExpression ident, boolean suchThat, JCTree.JCExpression expression) {
            this.pos = pos;
            this.modifiers = mods;
            this.token = JmlToken.REPRESENTS;
            this.ident = ident;
            this.expression = expression;
            this.suchThat = suchThat;
        }
        
        @Override
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

    // FIXME - the following do not have factory methods - do not set pos, do not have accept, getKind, getTag, toString methods, or documentation
    
    public static class JmlBBArrayAssignment extends JCMethodInvocation {
        public JmlBBArrayAssignment(JCIdent newarrs, JCIdent oldarrs, JCExpression arr, JCExpression index, JCExpression rhs) {
            super(null,null,null);
            ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
            list.append(newarrs);
            list.append(oldarrs);
            list.append(arr);
            if (index != null) list.append(index);
            if (rhs != null) list.append(rhs);
            args = list.toList();
        }
        
        
        @Override
        public int getStartPosition() {
            return args.get(0).getStartPosition(); // newarrs
        }
        
        @Override
        public int getEndPosition(Map<JCTree,Integer> table) {
            return args.get(args.length()-1).getEndPosition(table); // rhs
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
        
        @Override
        public int getStartPosition() {
            return args.get(0).getStartPosition(); // newfield
        }
        
        @Override
        public int getEndPosition(Map<JCTree,Integer> table) {
            return args.get(3).getEndPosition(table); // rhs
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
        public JCIdent arraysId;
        public JCIdent fieldId;
        public JmlBBFieldAccess(JCIdent fieldId, JCExpression selected) {
            super(selected,fieldId.name,fieldId.sym);
            this.fieldId = fieldId;
            this.type = fieldId.type;
        }
    }    
}
