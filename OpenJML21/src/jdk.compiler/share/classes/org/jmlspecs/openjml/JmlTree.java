/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import static com.sun.tools.javac.code.Flags.UNATTRIBUTED;
import static org.jmlspecs.openjml.ext.Refining.*;

import java.io.StringWriter;
import java.util.HashMap;
import java.util.Map;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.IJmlClauseKind.ModifierKind;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.ext.*;
import org.jmlspecs.openjml.ext.LineAnnotationClauses.ExceptionLineAnnotation;
import org.jmlspecs.openjml.visitors.IJmlVisitor;
import org.jmlspecs.openjml.visitors.JmlTreeVisitor;

import static org.jmlspecs.openjml.ext.TypeRepresentsClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeInitializerClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeMapsClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeMonitorsForClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeDeclClauseExtension.*;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.*;
import static org.jmlspecs.openjml.ext.MethodExprListClauseExtensions.*;

import com.sun.source.tree.*;
import static com.sun.source.tree.CaseTree.*;
import com.sun.tools.javac.code.JmlType;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Scope.NamedImportScope;
import com.sun.tools.javac.code.Scope.StarImportScope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.parser.JmlToken;
import com.sun.tools.javac.parser.Tokens.ITokenKind;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.JCTree.JCOperatorExpression.OperandPos;
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
public class JmlTree {
	protected JmlTree() {}
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
    
    static boolean isJML(long flags) {
        return (flags & Utils.JMLBIT) != 0;
    }
    
    /** This is a marker interface for all JMLTree nodes, to distinguish them from JCTree nodes  */
    public static interface IJmlTree {
    	/** JCTree notes use TreeInfo.getStartPos to return start position, which does not work
    	 * correctly for most JMLTree nodes, so those implement their own, class dependent, getStartPosition
    	 */
    	int getStartPosition();
    	/** JCTree notes use TreeInfo.getEndPos to return start position, which does not work
    	 * correctly for most JMLTree nodes, so those implement their own, class dependent, getEndPosition
    	 */
    	int getEndPosition(EndPosTable t);
    }
    
    public static interface IInJML extends IJmlTree{
        boolean isJML();
    }
    
    /** This interface extends the node factory for Java parse tree nodes by adding factory
     * methods for all of the JML nodes.  All these methods create the AST nodes;
     * the pos field is set using other methods on the factory.
     */
    public interface JmlFactory extends JCTree.Factory {
        JmlAnnotation Annotation(JCTree type, List<JCExpression> args);
        JmlAnnotation TypeAnnotation(JCTree annotationType, List<JCExpression> args);
        JmlBinary JmlBinary(IJmlClauseKind t, JCTree.JCExpression left, JCTree.JCExpression right);
        JmlBlock Block(long flags, List<JCStatement> stats);
        JmlChained JmlChained(List<JCBinary> conjuncts);
        JmlChoose JmlChoose(String keyword, IJmlClauseKind clauseType, List<JCBlock> orBlocks, /*@Nullable*/JCBlock elseBlock);
        JmlMethodSig JmlConstraintMethodSig(JCExpression expr, List<JCExpression> argtypes);
        JmlDoWhileLoop JmlDoWhileLoop(JCDoWhileLoop loop, List<JmlStatementLoop> loopSpecs);
        JmlEnhancedForLoop JmlEnhancedForLoop(JCEnhancedForLoop loop, List<JmlStatementLoop> loopSpecs);
        JmlStatementExpr JmlExpressionStatement(String keyword, IJmlClauseKind t, Label label, JCTree.JCExpression e);
        JmlStatementHavoc JmlHavocStatement(List<JCTree.JCExpression> e);
        JmlForLoop JmlForLoop(JCForLoop loop, List<JmlStatementLoop> loopSpecs);
        JmlGroupName JmlGroupName(JCExpression selection);
        JmlImport JmlImport(JCTree qualid, boolean staticImport, boolean isModel);
        JmlInlinedLoop JmlInlinedLoop(List<JmlStatementLoop> loopSpecs);
        JmlLabeledStatement JmlLabeledStatement(Name label, ListBuffer<JCStatement> extra, JCStatement block);
        JmlLambda JmlLambda(List<JCVariableDecl> params, JCTree body, JCExpression jmlType);
        JmlLblExpression JmlLblExpression(int labelPosition, IJmlClauseKind kind, Name label, JCTree.JCExpression expr);
        JmlLetExpr JmlLetExpr(List<JCStatement> defs, JCExpression expr, boolean explicit);
        JmlMatchExpression JmlMatchExpression(JCTree.JCExpression expr, List<JmlMatchExpression.MatchCase> cases);
        JmlMethodClauseGroup JmlMethodClauseGroup(List<JmlSpecificationCase> cases);
        JmlMethodClauseDecl JmlMethodClauseDecl(String keyword, IJmlClauseKind t, List<JCTree.JCVariableDecl> decls);
        JmlMethodClauseExpr JmlMethodClauseExpr(String keyword, IJmlClauseKind t, JCTree.JCExpression e);
        JmlMethodClauseBehaviors JmlMethodClauseBehaviors(String command);
        JmlMethodClauseInvariants JmlMethodClauseInvariants(List<JCExpression> expressions);
        JmlMethodClauseCallable JmlMethodClauseCallable(JmlSingleton keyword);
        JmlMethodClauseCallable JmlMethodClauseCallable(List<JmlMethodSig> methodSignatures);
        JmlMethodClauseConditional JmlMethodClauseConditional(String keyword, IJmlClauseKind kind, JCTree.JCExpression e, JCTree.JCExpression predicate);
        JmlMethodClauseSignals JmlMethodClauseSignals(String keyword, IJmlClauseKind kind, JCTree.JCVariableDecl var, JCTree.JCExpression e);
        JmlMethodClauseSignalsOnly JmlMethodClauseSignalsOnly(String keyword, IJmlClauseKind kind, List<JCTree.JCExpression> e);
        JmlMethodClause JmlMethodClauseStoreRef(String keyword, IJmlClauseKind kind, List<JCExpression> list);
        JmlMethodInvocation JmlMethodInvocation(JmlTokenKind token, List<JCExpression> args);
        JmlMethodInvocation JmlMethodInvocation(IJmlClauseKind kind, List<JCExpression> args);
        JmlMethodInvocation JmlMethodInvocation(String token, List<JCExpression> args);
        JmlMethodSpecs JmlMethodSpecs(List<JmlSpecificationCase> cases);
        JmlModelProgramStatement JmlModelProgramStatement(JCTree item);
        JmlPrimitiveTypeTree JmlPrimitiveTypeTree(JmlTokenKind jt, IJmlClauseKind kind, Name id);
        JmlQuantifiedExpr JmlQuantifiedExpr(IJmlClauseKind kind, List<JCVariableDecl> decls, JCTree.JCExpression range, JCTree.JCExpression predicate);
        JmlRange JmlRange(JCExpression lo, JCExpression hi);
        JmlSetComprehension JmlSetComprehension(JCTree.JCExpression type, JCTree.JCVariableDecl v, JCTree.JCExpression predicate);
        JmlSingleton JmlSingleton(IJmlClauseKind jt);
        JmlSpecificationCase JmlSpecificationCase(JCModifiers mods, boolean code, IJmlClauseKind t, IJmlClauseKind also, List<JmlMethodClause> clauses, JCBlock block);
        JmlSpecificationCase JmlSpecificationCase(JmlSpecificationCase sc, List<JmlMethodClause> clauses);
        JmlStatement JmlStatement(IJmlClauseKind t, JCTree.JCStatement e);
        JmlStatementShow JmlStatementShow(IJmlClauseKind t, List<JCExpression> expressions);
        JmlStatementDecls JmlStatementDecls(List<JCTree.JCStatement> list);
        JmlStatementLoopExpr JmlStatementLoopExpr(IJmlClauseKind t, JCTree.JCExpression e);
        JmlStatementLoopModifies JmlStatementLoopModifies(IJmlClauseKind t, List<JCTree.JCExpression> e);
        JmlStatementSpec JmlStatementSpec(JmlMethodSpecs specs);
//        JmlStoreRefArrayRange JmlStoreRefArrayRange(JCExpression expr, JCExpression lo, JCExpression hi);
//        JmlStoreRefKeyword JmlStoreRefKeyword(IJmlClauseKind t);
        JmlStoreRefListExpression JmlStoreRefListExpression(JmlTokenKind t, List<JCExpression> list);
        JmlStoreRef JmlStoreRef(boolean isEverything, Symbol local, JCExpression expression, JCExpression receiver, JmlRange range, VarSymbol field, JCExpression originalStoreRef);

        JmlTuple JmlTuple(java.util.List<JCExpression> list);
        JmlTypeClauseConditional JmlTypeClauseConditional(JCModifiers mods, IJmlClauseKind token, JCTree.JCIdent ident, JCTree.JCExpression p);
        JmlTypeClauseConstraint JmlTypeClauseConstraint(JCModifiers mods, JCExpression e, List<JmlMethodSig> sigs);
        JmlTypeClauseDecl JmlTypeClauseDecl(JCTree decl);
        JmlTypeClauseExpr JmlTypeClauseExpr(JCModifiers mods, String keyword, IJmlClauseKind token, JCTree.JCExpression e);
        JmlTypeClauseIn JmlTypeClauseIn(List<JmlGroupName> list);
        JmlTypeClauseInitializer JmlTypeClauseInitializer(IJmlClauseKind token, JCModifiers mods);
        JmlTypeClauseMaps JmlTypeClauseMaps(List<JCExpression> exprs, List<JmlGroupName> list);
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
        public Context context;
        
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
        
        protected Maker(JCCompilationUnit toplevel, Names names, Types types, Symtab syms) {
        	super(toplevel, names, types, syms);
        }

        
        /** Create a new tree maker for a given toplevel.
         */
        @Override
        public TreeMaker forToplevel(JCCompilationUnit toplevel) {
            return new JmlTree.Maker(toplevel, names, types, syms);
        }

        
        /** Creates a JmlCompilationUnit */
        @Override
        public JmlCompilationUnit TopLevel(List<JCTree> defs) {
            JmlCompilationUnit t = new JmlCompilationUnit(defs,null,null,null,null);
            t.pos = this.pos;
            return t;
        }
        
        public JmlBlock Block(long flags, List<JCStatement> stats) {
            JmlBlock t = new JmlBlock(flags,stats);
            t.pos = this.pos;
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
        
        @Override
        public JmlAnnotation Annotation(JCTree type, List<JCExpression> args) {
            JmlAnnotation a = new JmlAnnotation(JCTree.Tag.ANNOTATION,type,args);
            a.pos = pos;
            return a;
        }
        
        @Override
        public JmlAnnotation TypeAnnotation(JCTree annotationType, List<JCExpression> args) {
            JmlAnnotation tree = new JmlAnnotation(Tag.TYPE_ANNOTATION, annotationType, args);
            tree.pos = pos;
            return tree;
        }
        
        @Override
        public JCModifiers Modifiers(long flags, List<JCAnnotation> annotations) {
        	return Modifiers(flags, annotations, new java.util.LinkedList<JmlToken>());
        }
 
        // @Override // TODO - used to have Override
        public JCModifiers Modifiers(JCModifiers mods, long flags, List<JCAnnotation> annotations) {
        	return Modifiers(flags, annotations, mods == null ? new java.util.LinkedList<JmlToken>() : ((JmlModifiers)mods).jmlmods);
        }
        
        public JmlModifiers Modifiers(long flags, List<JCAnnotation> annotations, java.util.List<JmlToken> jmlmods) {
        	JmlModifiers m = new JmlModifiers(flags, annotations, jmlmods);
        	m.pos = pos;
        	return m;
        }

        public JmlModifiers Modifiers(long flags, java.util.List<JmlToken> jmlmods) {
        	return Modifiers(flags, List.<JCAnnotation>nil(), jmlmods);
        }
       
        /** Convenience method to create a JCIdent from a string
         * (use a Name if you have one, since this method creates a Name).
         * @param name the string to convert to wrap as an identifier
         * @return the resulting JCIdent
         */
        public JCIdent Ident(String name) {
            return Ident(Names.instance(context).fromString(name));
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
        	return ClassDef(mods, name, typarams, extending, implementing,  List.<JCExpression>nil(), defs);
        }
        @Override
        public JmlClassDecl ClassDef(JCModifiers mods,
                Name name,
                List<JCTypeParameter> typarams,
                JCExpression extending,
                List<JCExpression> implementing,
                List<JCExpression> permitting,
                List<JCTree> defs) {
            JmlClassDecl tree = new JmlClassDecl(mods,name,typarams,extending,implementing,defs,null);
            tree.pos = pos;
            tree.sourcefile = context == null ? null : Log.instance(context).currentSourceFile();
            // In the normal course of things, context is never null, but there is a circular dependency of
            // instantiating tools that can occur in the constructors of the various tools.  In particular
            // TreeMaker -> Symtab -> ClassReader -> Annotate -> Attr -> MemberEnter -> Enter which calls
            // TreeMaker.ClassDef before TreeMaker has completed construction
            // where A -> B means A constructs B during A's construction.  This results in TreeMaker.ClassDef
            // being called with a null context during TreeMaker's construction
//            if (context != null) 
//                tree.toplevel.sourcefile = Log.instance(context).currentSourceFile();
//            else {
//            if (context == null) {
//                String msg = ("INTERNAL ERROR: JmlTree.ClassDef called with a null context, indicating a problem with circular dependencies in constructors.");
//                System.err.println(msg);
//                new Exception().printStackTrace(System.err);
//                throw new JmlInternalError(msg);
//            }
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
                JCVariableDecl receiver,
                List<JCVariableDecl> params,
                List<JCExpression> thrown,
                JCBlock body,
                JCExpression defaultValue) {
            JmlMethodDecl tree = new JmlMethodDecl(mods,name,restype,typarams,receiver,params,thrown,body,defaultValue,null); // DRC Introduced null parameter to deal with new/evolved signature.
            tree.pos = pos;
            tree.sourcefile = context == null ? null : Log.instance(context).currentSourceFile();
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
                    null, // FIXME - receiver parameter
                    m.params != null ? Params(m) : Params(m, mtype.getParameterTypes()),
                    Types(mtype.getThrownTypes()),
                    body,
                    null,
                    m).setPos(pos).setType(mtype);
            tree.sourcefile = context == null ? null : Log.instance(context).currentSourceFile();
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
            tree.sourcefile = context == null ? null : Log.instance(context).currentSourceFile();
            // Not filled in: docComment, fieldSpecs, fieldSpecsCombined, specsDecl
            return tree;
        }

        @Override
        public JmlVariableDecl ReceiverVarDef(JCModifiers mods, JCExpression nameexpr, JCExpression vartype) {
            JmlVariableDecl tree = new JmlVariableDecl(mods, nameexpr, vartype);
            tree.pos = pos;
            tree.sourcefile = context == null ? null : Log.instance(context).currentSourceFile();
            return tree;
        }

       /** Creates a variable declaration from its components; captures the sourcefile
         * from the current value in the log; no symbol created. */
        @Override
        public JmlVariableDecl VarDef(JCModifiers mods,
                Name name,
                /*@ nullable */ JCExpression vartype, // null if we are in a lambda expression
                JCExpression init, boolean declaredUsingVar) {
            JmlVariableDecl tree =  new JmlVariableDecl(mods,name,vartype,init,null, declaredUsingVar);
            tree.pos = pos;
            if (vartype != null) tree.type = vartype.type; // attribute if the type is known
            tree.sourcefile = context == null ? null : Log.instance(context).currentSourceFile();
            // Not filled in: symbol, docComment, fieldSpecs, fieldSpecsCombined, specsDecl
            return tree;
        }

        @Override
        public JCVariableDecl VarDef(JCModifiers mods, Name name, JCExpression vartype, JCExpression init) {
            return VarDef(mods, name, vartype, init, false);
        }

        /** Creates an expression for a JML type (such as \TYPE or \real or \bigint).*/
        @Override
        public JmlPrimitiveTypeTree JmlPrimitiveTypeTree(JmlTokenKind jt, IJmlClauseKind kind, Name id) {
            return new JmlPrimitiveTypeTree(pos,jt,kind,id);
        }
        
        @Override
        public JCExpression Type(Type t) {
            if (!(t instanceof JmlType)) return super.Type(t);
            return new JmlPrimitiveTypeTree(pos,((JmlType)t).jmlTypeTag(), null, t.tsym.name); // FIXME - not sure this is right primitive types
        }

        @Override
        public JmlRange JmlRange(JCExpression lo, JCExpression hi) {
        	return new JmlRange(pos, lo, hi);
        }
        
        /** Creates JML expressions from tokens without arguments (e.g. \result)*/
        @Override
        public JmlSingleton JmlSingleton(IJmlClauseKind jt) {
            return new JmlSingleton(pos,jt);
        }
        
        /** Creates a JML import statement (possibly a model import) */
        @Override
        public JmlImport JmlImport(JCTree qualid, boolean staticImport, boolean isModel) {
            return (JmlImport)new JmlImport(qualid, staticImport,isModel).setPos(pos);
        }
        
        /** Creates a regular import, but using a JmlImport AST node */
        @Override
        public JmlImport Import(JCFieldAccess qualid, boolean staticImport) {
            return (JmlImport)new JmlImport(qualid,staticImport,false).setPos(pos);
        }
        
        @Override
        public JmlCase Case(CaseKind caseKind, List<JCCaseLabel> labels, JCExpression guard,
                            List<JCStatement> stats, JCTree body) {
            var r = new JmlCase(caseKind, labels, guard, stats, body);
            r.pos = pos;
            return r;
        }
        
        /** Creates a JML binary operation */
        @Override
        public JmlBinary JmlBinary(IJmlClauseKind t, JCTree.JCExpression left, JCTree.JCExpression right) {
            return new JmlBinary(pos,t,left,right);
        }
        
        /** Creates a JML chained operation */
        @Override
        public JmlChained JmlChained(List<JCBinary> conjuncts) {
            JmlChained c = new JmlChained(conjuncts);
            c.pos = pos;
            return c;
        }
       /* 
        @Override
        public JmlMethodInvocation Apply(List<JCExpression> typeargs,
                JCExpression fn,
                List<JCExpression> args)
		{
        	return new JmlMethodInvocation(pos, typeargs, fn, args);
		}
*/
		        
        /** Creates a JML method invocation (e.g. for JmlTokens with arguments, such as \typeof) */
        @Override
        public JmlMethodInvocation JmlMethodInvocation(JmlTokenKind token, List<JCExpression> args) {
            return new JmlMethodInvocation(pos,token,args);
        }
        
        @Override
        public JmlMethodInvocation JmlMethodInvocation(String token, List<JCExpression> args) {
            return new JmlMethodInvocation(pos,token,args);
        }
        
        /** Creates a method invocation from a method name expression (e.g. o.name) */
        public JmlMethodInvocation JmlMethodInvocation(JCExpression method, List<JCExpression> args) {
            return new JmlMethodInvocation(pos,method,args);
        }
        
        /** Creates a JML method invocation for the special case of one argument (e.g. for JmlTokens with arguments, such as \typeof) */
        public JmlMethodInvocation JmlMethodInvocation(JmlTokenKind token, JCExpression arg) {
            return new JmlMethodInvocation(pos,token,List.<JCExpression>of(arg));
        }
        
        /** Creates a JML method invocation for the special case of two arguments */
        public JmlMethodInvocation JmlMethodInvocation(JmlTokenKind token, JCExpression arg, JCExpression arg2) {
            return new JmlMethodInvocation(pos,token,List.<JCExpression>of(arg,arg2));
        }
        
        /** Creates a JML method invocation for the special case of one argument (e.g. for JmlTokens with arguments, such as \typeof) */
        public JmlMethodInvocation JmlMethodInvocation(IJmlClauseKind kind, JCExpression arg) {
            return new JmlMethodInvocation(pos,kind,List.<JCExpression>of(arg));
        }
        
        /** Creates a JML method invocation for the special case of two arguments */
        public JmlMethodInvocation JmlMethodInvocation(IJmlClauseKind kind, JCExpression arg, JCExpression arg2) {
            return new JmlMethodInvocation(pos,kind,List.<JCExpression>of(arg,arg2));
        }

        /** Creates a JML method invocation */
        @Override
        public org.jmlspecs.openjml.JmlTree.JmlMethodInvocation JmlMethodInvocation(IJmlClauseKind kind, List<JCExpression> args) {
            return new JmlMethodInvocation(pos,kind,args);
        }

        /** Creates a JML quantified expression */
        @Override
        public JmlQuantifiedExpr JmlQuantifiedExpr(IJmlClauseKind kind, List<JCTree.JCVariableDecl> decls, JCTree.JCExpression range, JCTree.JCExpression value) {
            return new JmlQuantifiedExpr(pos,kind,decls,range,value);
        }
        
        /** Creates a JML set-comprehension expression */
        @Override
        public JmlSetComprehension JmlSetComprehension(JCTree.JCExpression type, JCTree.JCVariableDecl varDecl, JCTree.JCExpression value) {
            return new JmlSetComprehension(pos,type,varDecl,value);
        }
        
        /** Creates a JML inlined loop statement */
        @Override
        public JmlInlinedLoop JmlInlinedLoop(List<JmlStatementLoop>  loopSpecs) {
            JmlInlinedLoop p = new JmlInlinedLoop(pos,loopSpecs);
            return p;
        }
        
        @Override
        public JmlLambda JmlLambda(List<JCVariableDecl> params, JCTree body, JCExpression jmlType) {
            return new JmlLambda(params,body,jmlType);
        }

        @Override
        public JmlNewClass NewClass(JCExpression encl, List<JCExpression> typeargs,
                JCExpression clazz, List<JCExpression> args, JCClassDecl def) {
            return new JmlNewClass(pos,encl,typeargs,clazz,args,def);
        }

        /** Creates a JML labeled statement */
        @Override
        public JmlLabeledStatement JmlLabeledStatement(Name label, ListBuffer<JCStatement> extra, JCStatement body) {
            JmlLabeledStatement p = Labelled(label,body);
            if (extra == null) extra = new ListBuffer<JCStatement>();
            p.extraStatements = extra;
            return p;
        }

        /** Creates a JML labeled statement */
        @Override
        public JmlLabeledStatement Labelled(Name label, JCStatement body) {
            if (body == null) body = JmlTree.Maker.instance(context).Block(0L, List.<JCStatement>nil());
            JmlLabeledStatement p = new JmlLabeledStatement(label,body);
            p.pos = pos;
            p.extraStatements = new ListBuffer<JCStatement>();
            return p;
        }

        /** Creates a JML labeled expression */
        @Override
        public JmlLblExpression JmlLblExpression(int labelPosition, IJmlClauseKind kind, Name label, JCTree.JCExpression expr) {
            JmlLblExpression p = new JmlLblExpression(pos,labelPosition,kind,label,expr);
            return p;
        }
        
        /** Creates a JML \let expression */
        @Override
        public LetExpr LetExpr(List<JCStatement> defs, JCExpression expr) {
        	JmlLetExpr p = new JmlLetExpr(defs,expr,false);
            return p;
        }
        
        /** Creates a JML \let expression */
        @Override
        public JmlLetExpr JmlLetExpr(List<JCStatement> defs, JCExpression expr, boolean explicit) {
        	JmlLetExpr p = new JmlLetExpr(defs,expr,explicit);
        	p.pos = pos;
            return p;
        }
        
        /** Creates a JML match expression */
        @Override
        public JmlMatchExpression JmlMatchExpression(JCTree.JCExpression expr, List<JmlMatchExpression.MatchCase> cases) {
            JmlMatchExpression p = new JmlMatchExpression(pos,expr,cases);
            return p;
        }
        
        /** Creates a JML expression statement (e.g. assert) */
        @Override
        public JmlStatementExpr JmlExpressionStatement(String keyword, IJmlClauseKind t, Label label, JCTree.JCExpression e) {
            return new JmlStatementExpr(pos,t,label,e);
        }
        
        @Override
        public JmlIfStatement If(JCExpression cond, JCStatement t, JCStatement e) {
            var tree = new JmlIfStatement(cond,t,e);
            tree.pos = pos;
            return tree;
        }
        
        @Override
        public JmlSwitchStatement Switch(JCExpression selector, List<JCCase> cases) {
            var tree = new JmlSwitchStatement(selector,cases);
            tree.pos = pos;
            return tree;
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
        public JmlStatementLoopExpr JmlStatementLoopExpr(IJmlClauseKind t, JCTree.JCExpression e) {
            return new JmlStatementLoopExpr(pos,t,e);
        }

        /** Creates a JML loop specification statement (e.g. loop_invariant, decreases, ... )*/
        @Override
        public JmlStatementLoopModifies JmlStatementLoopModifies(IJmlClauseKind t, List<JCTree.JCExpression> e) {
            return new JmlStatementLoopModifies(pos,t,e);
        }

        /** Creates a JML do-while loop node that wraps a Java loop statement and a set of loop specifications */
        @Override
        public JmlDoWhileLoop JmlDoWhileLoop(JCDoWhileLoop loop, List<JmlStatementLoop> loopSpecs) {
            return new JmlDoWhileLoop(loop,loopSpecs); // pos set from loop argument
        }
        
        public JmlLambda Lambda(List<JCVariableDecl> params,
                JCTree body) {
            //return super.Lambda(params, body);
            return JmlLambda(params, body, null);
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
        
        /** Creates JML statements such as set and debug and end */
        @Override
        public JmlStatement JmlStatement(IJmlClauseKind t, JCStatement e) {
            return new JmlStatement(pos,t.keyword().toString(),t,e);
        }

        @Override
        public JmlStatementShow JmlStatementShow(IJmlClauseKind t, List<JCExpression> expressions) {
            return new JmlStatementShow(pos,t,expressions);
        }

        @Override
        public JmlStoreRefListExpression JmlStoreRefListExpression(JmlTokenKind t, List<JCExpression> list) {
            return new JmlStoreRefListExpression(pos,t,list);
        }

        @Override
        public JmlStoreRef JmlStoreRef(boolean isEverything, Symbol local, JCExpression expression, JCExpression receiver, JmlRange range, VarSymbol field, JCExpression originalStoreRef) {
            return new JmlStoreRef(pos,isEverything, local, expression, receiver, range, field, originalStoreRef);
        }

        public JmlStoreRef JmlStoreRef(JmlStoreRef that) {
            return JmlStoreRef(that.isEverything, that.local, that.expression, that.receiver, that.range, that.field, that.originalStoreRef);
        }

        @Override
        public JmlTuple JmlTuple(java.util.List<JCExpression> list) {
            return new JmlTuple(pos,list);
        }

//        @Override
//        public JmlStoreRefKeyword JmlStoreRefKeyword(IJmlClauseKind t) {
//            return new JmlStoreRefKeyword(pos,t);
//        }
//
//        @Override
//        public JmlStoreRefArrayRange JmlStoreRefArrayRange(JCExpression expr, JCExpression lo, JCExpression hi) {
//            return new JmlStoreRefArrayRange(pos,expr,lo,hi);
//        }

        @Override
        public JmlTypeClauseExpr JmlTypeClauseExpr(JCModifiers mods, String keyword, IJmlClauseKind token, JCTree.JCExpression e) {
            JmlTypeClauseExpr t = new JmlTypeClauseExpr(pos,mods,keyword,token,e);
            t.source = context == null ? null : Log.instance(context).currentSourceFile();
            return t;
        }
        
        @Override
        public JmlTypeClauseDecl JmlTypeClauseDecl(JCTree decl) {
            JmlTypeClauseDecl t = new JmlTypeClauseDecl(pos,decl);
            t.source = context == null ? null : Log.instance(context).currentSourceFile();
            return t;
        }
        
        @Override
        public JmlTypeClauseInitializer JmlTypeClauseInitializer(IJmlClauseKind token, JCModifiers mods) {
            JmlTypeClauseInitializer t = new JmlTypeClauseInitializer(pos, token, mods);
            t.source = context == null ? null : Log.instance(context).currentSourceFile();
            return t;
        }
        
        @Override
        public JmlTypeClauseConstraint JmlTypeClauseConstraint(JCModifiers mods, JCTree.JCExpression e, List<JmlMethodSig> sigs) {
            JmlTypeClauseConstraint t = new JmlTypeClauseConstraint(pos,mods,e,sigs);
            t.source = context == null ? null : Log.instance(context).currentSourceFile();
            return t;
        }
        
//        @Override
//        public JmlChoose JmlChoose(JmlTokenKind token, List<JCBlock> orBlocks, /*@Nullable*/JCBlock elseBlock) {
//            return new JmlChoose(pos,token,orBlocks,elseBlock);
//        }
        
        @Override
        public JmlChoose JmlChoose(String keyword, IJmlClauseKind clauseType, List<JCBlock> orBlocks, /*@Nullable*/JCBlock elseBlock) {
            return new JmlChoose(pos,keyword,clauseType,orBlocks,elseBlock);
        }
        
        @Override
        public JmlMethodSig JmlConstraintMethodSig(JCExpression expr, List<JCExpression> argtypes) {
            return new JmlMethodSig(pos,expr,argtypes);
        }

        @Override
        public JmlTypeClauseRepresents JmlTypeClauseRepresents(JCModifiers mods, JCTree.JCExpression ident, boolean suchThat, JCTree.JCExpression e) {
            JmlTypeClauseRepresents t = new JmlTypeClauseRepresents(pos, mods, ident,suchThat,e);
            t.source = context == null ? null : Log.instance(context).currentSourceFile();
            return t;
        }

        @Override
        public JmlTypeClauseConditional JmlTypeClauseConditional(JCModifiers mods, IJmlClauseKind token, JCTree.JCIdent ident, JCTree.JCExpression p) {
            JmlTypeClauseConditional t = new JmlTypeClauseConditional(pos, mods, token,ident,p);
            t.source = context == null ? null : Log.instance(context).currentSourceFile();
            return t;
        }

        @Override
        public JmlTypeClauseMonitorsFor JmlTypeClauseMonitorsFor(JCModifiers mods, JCTree.JCIdent ident, List<JCTree.JCExpression> list) {
            JmlTypeClauseMonitorsFor t = new JmlTypeClauseMonitorsFor(pos, mods, ident, list);
            t.source = context == null ? null : Log.instance(context).currentSourceFile();
            return t;
        }

        @Override
        public JmlMethodClauseGroup JmlMethodClauseGroup(List<JmlSpecificationCase> list) {
            return new JmlMethodClauseGroup(pos,"",null,list); // FIXME
        }
        
        @Override
        public JmlMethodClauseDecl JmlMethodClauseDecl(String keyword, IJmlClauseKind t, List<JCTree.JCVariableDecl> decls) {
            return new JmlMethodClauseDecl(pos,t,decls);
        }
        
        @Override
        public JmlMethodClauseExpr JmlMethodClauseExpr(String keyword, IJmlClauseKind t, JCTree.JCExpression e) {
            return new JmlMethodClauseExpr(pos,keyword,t,e);
        }
        
        @Override
        public JmlMethodClauseBehaviors JmlMethodClauseBehaviors(String command) {
            return new JmlMethodClauseBehaviors(pos,command);
        }
        
        @Override
        public JmlMethodClauseCallable JmlMethodClauseCallable(JmlSingleton keyword) {
            return new JmlMethodClauseCallable(pos,keyword,null);
        }
        
        @Override
        public JmlMethodClauseCallable JmlMethodClauseCallable(List<JmlMethodSig> methodSignatures) {
        	return new JmlMethodClauseCallable(pos,null,methodSignatures);
        }
        
        @Override
        public JmlMethodClauseConditional JmlMethodClauseConditional(String keyword, IJmlClauseKind t, JCTree.JCExpression e, JCTree.JCExpression p) {
            return new JmlMethodClauseConditional(pos,keyword,t,e,p);
        }
        
        @Override
        public JmlMethodClauseInvariants JmlMethodClauseInvariants(List<JCTree.JCExpression> e) {
            return new JmlMethodClauseInvariants(pos,e);
        }
        
        @Override
        public JmlMethodClauseSignals JmlMethodClauseSignals(String keyword, IJmlClauseKind t, JCTree.JCVariableDecl var, JCTree.JCExpression e) {
            return new JmlMethodClauseSignals(pos,keyword,t,var,e);
        }
        
        @Override
        public JmlMethodClauseSignalsOnly JmlMethodClauseSignalsOnly(String keyword, IJmlClauseKind t, List<JCTree.JCExpression> e) {
            return new JmlMethodClauseSignalsOnly(pos,keyword,t,e);
        }

        @Override
        public JmlMethodClauseStoreRef JmlMethodClauseStoreRef(String keyword, IJmlClauseKind t, List<JCExpression> list) {
            return new JmlMethodClauseStoreRef(pos, keyword, t, list);
        }

        @Override
        public JmlModelProgramStatement JmlModelProgramStatement(JCTree item) {
            return new JmlModelProgramStatement(pos, item);
        }

        @Override
        public JmlSpecificationCase JmlSpecificationCase(JCModifiers mods, boolean code, IJmlClauseKind t, IJmlClauseKind also, List<JmlMethodClause> clauses, JCBlock block) {
            JmlSpecificationCase jcase = new JmlSpecificationCase(pos,mods,code,t,also,clauses,block);
            jcase.sourcefile = context == null ? null : Log.instance(context).currentSourceFile();
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
            r.source = context == null ? null : Log.instance(context).currentSourceFile();
            return r;
        }
        
        @Override
        public JmlTypeClauseMaps JmlTypeClauseMaps(List<JCExpression> exprs, List<JmlGroupName> list) {
            JmlTypeClauseMaps r = new JmlTypeClauseMaps(pos,exprs,list);
            r.source = context == null ? null : Log.instance(context).currentSourceFile();
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
    
    public static final int JMLFUNCTION = 1000;  // The 1000 used to be enough to be higher than the JCTree tags, but those are enums now
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
    public static final int JMLLASTTAG = JMLSTOREREFARRAYRANGE;

    /** The system-defined end of line character string */
    static public final String eol = System.getProperty("line.separator");

    static public void unexpectedVisitor(JCTree t, Object visitor) {
        // FIXME - a better error
        System.out.println("A " + t.getClass() + " expects an IJmlVisitor, not a " + visitor.getClass());
    }
    
    /** This is an interface for any node that contains source file information. */
    public interface JmlSource {
        
        /** Returns the file object containing the source code for the AST node */
        /*@nullable*/ JavaFileObject source();
        /*@nullable*/ void setSource(JavaFileObject jfo);
        DiagnosticPosition pos();
    }
    
    /** This class adds some JML specific information to the JCCompilationUnit toplevel node. */
    public static class JmlCompilationUnit extends JCTree.JCCompilationUnit {
        
        /** This list contains the parse tree of the specification file, if any, for this compilation unit. 
         *  This field may point to 'this' if the compilation unit is its own specs file. */
    	/*@ nullable */
    	public JmlCompilationUnit specsCompilationUnit = null;

        /** The tree representing the package clause. */
        /*@ nullable */
        public JCPackageDecl pid;

//        /** This list contains the top-level model types declared in this compilation unit; this
//         * is not necessarily all or even part of the top-level model types that the CUs specifications
//         * specify, since (a) other spec files may contribute top-level model types 
//         * and (b) this CU may not be part of its own spec sequence.
//         */
//        public ListBuffer<JmlClassDecl> parsedTopLevelModelTypes = new ListBuffer<JmlClassDecl>();
//        
//        /** This list is the set of top-level model types specified by the
//         * CUs specifications.  It is assembled when types are entered in JmlEnter.
//         */
//        public java.util.List<JmlClassDecl> specsTopLevelModelTypes = new java.util.LinkedList<JmlClassDecl>();

//        // FIXME - review the use of this value
//        /** The use to be made of this parse tree - one of the int constants below. */
//        public int mode = 0; // init to an unknown value
        
        public Env<AttrContext> topLevelEnv;
        
        public boolean isSpecs() { return sourcefile.getKind() != JavaFileObject.Kind.SOURCE; }
        public boolean forBinary() { return sourceCU == null; }
        public JmlCompilationUnit sourceCU = null; // Set to self if a source file
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlCompilationUnit(List<JCTree> defs,
                JavaFileObject sourcefile,
                PackageSymbol packge,
                NamedImportScope namedImportScope,
                StarImportScope starImportScope) {
        	super(defs);
        	this.sourcefile = sourcefile;
        	this.packge = packge;
        	this.namedImportScope = namedImportScope;
        	this.starImportScope = starImportScope;
            if (defs.length() > 0 && defs.head instanceof JCPackageDecl) {
            	this.pid = (JCPackageDecl)defs.head;           	
            }
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitTopLevel(this); 
            } else {
                // unexpectedVisitor(this,v);
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitCompilationUnit(this, d);
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
            super((JCFieldAccess)qualid,importStatic); // FIXME - did not used to need the cast
            this.isModel = isModel;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitImport(this); 
            } else {
                // unexpectedVisitor(this,v);
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitImport(this, d);
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
    
    public static class JmlModifiers extends JCModifiers {
    	
    	public boolean anyModsInJava = false;
    	
    	public java.util.List<JmlToken> jmlmods = new java.util.LinkedList<>();
    	
        public JmlModifiers(long flags, List<JCAnnotation> annotations, java.util.List<JmlToken> jmlmods) {
    		super(flags, annotations);
    		if (jmlmods != null) this.jmlmods.addAll(jmlmods);
    	}
    	
    	public void add(JmlToken k) {
    		this.jmlmods.add(k);
    	}
    	
    	public boolean has(ModifierKind k) {
    		for (var kk: jmlmods) {
    			if (kk.jmlclausekind == k) return true;
    		}
    		return false;
    	}
    	
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitModifiers(this); 
            } else {
                // unexpectedVisitor(this,v);
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitModifiers(this, d);
            } else {
                // unexpectedVisitor(this,v);
                return super.accept(v,d);
            }
        }
        
//        @Override
//        public String toString() {
//        	StringBuilder sb = new StringBuilder();
//    		for (var kk: jmlmods) {
//    			sb.append(kk.toString());
//    			sb.append(" ");
//    		}
//            return sb.toString();
//        }    
    }
    
    /** This class represents model program choose and choose_if statements. */
    public static class JmlChoose extends JmlAbstractStatement {

        public String keyword;
        public IJmlClauseKind clauseType;
        public List<JCBlock> orBlocks;
        /*@Nullable*/ public JCBlock elseBlock;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlChoose(int pos, String keyword, IJmlClauseKind clauseType, List<JCBlock> orBlocks, /*@Nullable*/ JCBlock elseBlock) {
            this.pos = pos;
            this.keyword = keyword;
            this.clauseType = clauseType;
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
    public static class JmlClassDecl extends JCTree.JCClassDecl implements JmlSource, IInJML {
        /** This is the class declaration that holds the specifications for the
         * containing class. It may be the same as the containing class, or a different AST
         * (e.g., from a .jml file), or null if there are no specifications for this class.
         * A class declaration in a .jml file will have a null value for this field.
         */
        public /*@Nullable*/ JmlClassDecl specsDecl;
        
        /** The Env<> to use for process the specsDecl */
        public Env<AttrContext> specEnv;

        /** This field holds the class-level specifications for the type corresponding
         * to this declaration; it is an alias for the specs that are found in the JmlSpecs database
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
        
        /** The scope environment for this class declaration.
         * For a source file, this is the same as typeEnvs.get()
         * but for a specifications file it may be different.
         */
        public Env<AttrContext> env;
        
        /** Set during attribution, used during RAC - the value in Enter is 
         * removed by then.
         */
        public VarSymbol thisSymbol;
        public VarSymbol superSymbol;
        
        public JCBlock initializerBlock;
        public Env<AttrContext> initializerBlockEnv;
        public JCBlock staticInitializerBlock;
        public Env<AttrContext> staticInitializerBlockEnv;
        
        public java.util.List<ExceptionLineAnnotation> lineAnnotations;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlClassDecl(JCModifiers mods, Name name,
                List<JCTypeParameter> typarams, JCExpression extending,
                List<JCExpression> implementing, List<JCTree> defs,
                ClassSymbol sym) {
            super(mods, name, typarams, extending, implementing, List.<JCExpression>nil(), defs, sym);
            specsDecl = null;
            typeSpecs = null;
        }
        
        /** The source this class was declared int - may be different than the top-level compilation
         * unit after model classes are moved around, etc.
         */
        public JavaFileObject sourcefile;
        
        /** The source this class was declared in (model classes may be declared
         * in a source file different than the class that owns the model class)
         */
        @Override
        public JavaFileObject source() { return sourcefile; }

        @Override
        public void setSource(JavaFileObject jfo) { sourcefile = jfo; }

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
        
        @Override
        public boolean isJML() {
            return JmlTree.isJML(mods.flags);
        }
        
        public boolean isTypeChecked() {
            ClassSymbol c = sym;
            if (c == null) return false;
            return ((c.flags_field & UNATTRIBUTED) == 0);
        }
    }

    /** This class adds some JML specific information to the JCMethodDecl node. */
    public static class JmlMethodDecl extends JCTree.JCMethodDecl implements JmlSource, IInJML {

        /** The file containing this declaration */
        public JavaFileObject sourcefile;

        /** The declaration in the jml file, 
         * or null if there is a jml file but no declaration of this method in it, 
         * or the same as the java declaration if there is no jml file
         * (set in JmlMemberEnter); set to self in the parser for 
         * methods in anonymous classes.
         */
        /*@nullable*/ public JmlMethodDecl specsDecl; 

        /** The final, combined specs from all sources (set in JmlMemberEnter);
         * set to self in parser for methods in anonymous classes */
        public JmlSpecs.MethodSpecs methodSpecsCombined; 

        public JmlMethodSpecs cases;  // FIXME - change to JmlSpecificationCase?

        public String docComment = null; // FIXME - clarify why needed
        public VarSymbol _this = null; // The Symbol for 'this' inside the method, if not static;
                                        // valid after attribution
        
        public boolean usedBitVectors = false;
        public boolean isInitializer = false;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        public JmlMethodDecl(JCModifiers mods, Name name, JCExpression restype,  // FIXME - backdoor use - should not be public
                List<JCTypeParameter> typarams, JCVariableDecl recvparam, List<JCVariableDecl> params,
                List<JCExpression> thrown, JCBlock body,
                JCExpression defaultValue, MethodSymbol sym) {
            super(mods, name, restype, typarams, recvparam, params, thrown, body, defaultValue, sym);
            specsDecl = null;
            sourcefile = null;
        }
        
        /** The source this method was declared in (model methods may be declared
         * in a source file different than the class that owns the model method)
         */
        @Override
        public JavaFileObject source() { return sourcefile; }
        
        @Override
        public void setSource(JavaFileObject jfo) { sourcefile = jfo; }
        
        @Override
        public boolean isJML() {
            return JmlTree.isJML(mods.flags);
        }

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
    

    /** This class adds some JML specific information to the JCMethodDecl node. */
    public static class JmlBlock extends JCTree.JCBlock implements JmlSource, IInJML {

    	//@ invariant isInitializerBlock ==> sourcefile != null;
    	
        /** The file containing this declaration */
        public JavaFileObject sourcefile;
        
        /** True is the block is an initializer block for a class, false otherwise, e.g., if part of a method or lambda */
        public boolean isInitializerBlock = false;

        /** The specs for the block, along with attribution status and env, computed during attribution */
        public JmlSpecs.BlockSpecs blockSpecs; 

        /** The specs for the block, as parsed -- can be null, if there are no specs (or empty)*/
        //@ nullable
        public JmlMethodSpecs specificationCases;

        public String docComment = null; // FIXME - clarify why needed
        public VarSymbol _this = null; // The Symbol for 'this' inside the method, if not static;
                                        // valid after attribution
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        public JmlBlock(long flags, List<JCStatement> stats) {
            super(flags, stats);
            sourcefile = null;
        }
        
        /** The source this method was declared in (model methods may be declared
         * in a source file different than the class that owns the model method)
         */
        @Override
        public JavaFileObject source() { return sourcefile; }
        
        @Override
        public void setSource(JavaFileObject jfo) { sourcefile = jfo; }
        
        @Override
        public boolean isJML() {
            return JmlTree.isJML(flags);
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor jv) {
                jv.visitBlock(this); 
            } else {
                // unexpectedVisitor(this,v);
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor<R,D> jv) {
                return jv.visitBlock((BlockTree)this, d);
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
    public static class JmlVariableDecl extends JCTree.JCVariableDecl implements JmlSource, IInJML {
        // FIXME - need some documentation of these fields
        public JmlVariableDecl specsDecl;
        public JmlSpecs.FieldSpecs fieldSpecs;
        public JavaFileObject sourcefile;
        public String docComment = null; // FIXME - why?
        public boolean jmltype = false; // if true, type is replaced and may be a model type
        public JCExpression originalVartype;
        public Type originalType;
        
        /** A fixed ident used in ESC */
        public JCIdent ident = null;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlVariableDecl(JCModifiers mods, Name name,
                /*@ nullable */ JCExpression vartype, JCExpression init, VarSymbol sym, boolean declaredUsingVar) {
            super(mods, name, vartype, init, sym, declaredUsingVar);
            specsDecl = null;
            fieldSpecs = null;
            sourcefile = null;
        }
        
        protected JmlVariableDecl(JCModifiers mods, Name name,
                /*@ nullable */ JCExpression vartype, JCExpression init, VarSymbol sym) {
            super(mods, name, vartype, init, sym, false);
        }
        
        protected JmlVariableDecl(JCModifiers mods,
        		JCExpression nameexpr,
        		JCExpression vartype) {
        	super(mods, nameexpr, vartype);
        }

        
        /** The source this variable was declared in (model variable may be declared
         * in a source file different than the class that owns the model variable)
         */
        @Override
        public JavaFileObject source() { return sourcefile; }
        
        @Override
        public void setSource(JavaFileObject jfo) { sourcefile = jfo; }
        
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
        
        @Override
        public boolean isJML() {
            return JmlTree.isJML(mods.flags);
        }

    }

    /** An abstract class that parents any Jml expression classes (that are not
     * special cases of other specific Java expressions)
     */
    abstract public static class JmlExpression extends JCTree.JCExpression implements IJmlTree {
    	protected JmlExpression() {}

    	@Override
        public String toString() {
            return JmlTree.toString(this);
        }
        
        @Override 
        public int getStartPosition() {
            return pos;
        }
        
        // This should be overridden in derived classes, but if it is not, we get a 
        // stack overflow. So this implementation is defensive.
        @Override 
        public int getEndPosition(EndPosTable endPosTable) {
            return pos;
        }
        
        @Override
        public Tag getTag() {
            return Tag.NO_TAG;
        }

        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
    }
    
    /** This class is simply a superclass for all AST classes representing 
     * statements within the body of a method.  From a Java perspective, these
     * need to behave like Skip statements.
     */
    public static abstract class JmlAbstractStatement extends JCTree.JCSkip {
    	protected JmlAbstractStatement() {}
        
    	public Name name;
    	
        public String toString() {
            return JmlTree.toString(this);
        }
        
        public int getStartPosition() {
            return pos;
        }
        
        @Override
        public Tag getTag() {
            return Tag.NO_TAG;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
    }

    /** This class represents binary expressions with JML operators */
    public static class JmlBinary extends JmlExpression {
        public IJmlClauseKind op;
        public JCExpression lhs;
        public JCExpression rhs;
        
        public ExpressionTree getLeftOperand() { return lhs; }
        public ExpressionTree getRightOperand() {return rhs; }
//        public JCExpression getOperand(OperandPos pos) {
//        	return pos == OperandPos.LEFT ? lhs : rhs;
//        }

        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlBinary(int pos, IJmlClauseKind op,
                JCExpression lhs,
                JCExpression rhs) {
            this.pos = pos;
            this.op = op;
            this.lhs = lhs;
            this.rhs = rhs;
        }
        
        /** A shallow copy constructor */
        public JmlBinary(JmlBinary that) {
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
        
        @Override
        public int getStartPosition() {
            return lhs.getStartPosition();
        }
    
        @Override
        public int getEndPosition(EndPosTable table) {
            return rhs.getEndPosition(table);
        }
    }

    public static class JmlChained extends JmlExpression {
        public List<JCBinary> conjuncts;
                
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlChained(List<JCBinary> conjuncts) {
            this.conjuncts = conjuncts;
        }
        
        /** A shallow copy constructor */
        public JmlChained(JmlChained that) {
            this.conjuncts = that.conjuncts;
            this.type = that.type;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlChained(this); 
            } else {
                unexpectedVisitor(this,v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlChained(this, d);
            } else {
                unexpectedVisitor(this,v);
                return null;
            }
        }
        
        @Override
        public int getStartPosition() {
            return conjuncts.head.getStartPosition();
        }
    
        @Override
        public int getEndPosition(EndPosTable table) {
            return conjuncts.last().getEndPosition(table);
        }
    }

    /** This class represents the method signatures in the constraint type
     * specification clause or the callable method specification clause.
     * @author David Cok
     */
    public static class JmlMethodSig extends JCTree {
        public JCExpression expression;
        public List<JCExpression> argtypes;
        public MethodSymbol methodSymbol;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodSig(int pos, JCExpression expr, List<JCExpression> argtypes) {
            this.pos = pos;
            this.expression = expr;
            this.argtypes = argtypes;
            this.methodSymbol = null;
        }
    
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public Tag getTag() {
            return Tag.NO_TAG;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
               ((IJmlVisitor)v).visitJmlMethodSig(this); 
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
        
        @Override
        public int getStartPosition() {
            return pos;
        }
    }

    /** This class wraps a Java do while loop just so it can attach some specs
     * to it.
     */
    public static class JmlDoWhileLoop extends JCDoWhileLoop implements IJmlLoop {
    
        public boolean split;
        public boolean isSplit() { return split; }
        public void setSplit(boolean s) { split = s; }
        
        public List<JmlStatementLoop> loopSpecs;

        public List<JmlStatementLoop> loopSpecs() { return loopSpecs; }
        public void setLoopSpecs(List<JmlStatementLoop> loopSpecs) { this.loopSpecs = loopSpecs; }

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
        
        @Override
        public JCStatement body() {
            return body;
        }
     }

    /** This class wraps a Java enhanced loop just so it can attach some specs
     * to it.
     */
    public static class JmlEnhancedForLoop extends JCEnhancedForLoop implements IJmlLoop {

        public boolean split;
        public boolean isSplit() { return split; }
        public void setSplit(boolean s) { split = s; }

        public List<JmlStatementLoop> loopSpecs;

        public List<JmlStatementLoop> loopSpecs() { return loopSpecs; }
        public void setLoopSpecs(List<JmlStatementLoop> loopSpecs) { this.loopSpecs = loopSpecs; }

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
        
        @Override
        public JCStatement body() {
            return body;
        }
    }
    
    public static interface IJmlLoop {
        List<JmlStatementLoop> loopSpecs();
        void setLoopSpecs(List<JmlStatementLoop> loopSpecs);
        boolean isSplit();
        void setSplit(boolean s);
        JCStatement body();
    }
    
    public static class JmlInlinedLoop extends JmlAbstractStatement implements IJmlLoop {

        public boolean split;
        public boolean isSplit() { return split; }
        public void setSplit(boolean s) { split = s; }

        public boolean consumed;
        public List<JmlStatementLoop> loopSpecs;
        public List<JmlStatementLoop> translatedSpecs;
        public java.util.List<JCIdent> countIds = new java.util.LinkedList<>();
        
        public List<JmlStatementLoop> loopSpecs() { return loopSpecs; }
        public void setLoopSpecs(List<JmlStatementLoop> loopSpecs) { this.loopSpecs = loopSpecs; }

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        // FIXME change to protected when factory method is implemented
        public JmlInlinedLoop(int pos, List<JmlStatementLoop> loopSpecs) {
            super();
            this.pos = pos;
            this.type = null;
            this.loopSpecs = loopSpecs;
            this.consumed = false;
        }
    
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlInlinedLoop(this); 
            } else {
                //System.out.println("A JmlInlinedLoop expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }
    
        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlInlinedLoop(this, d);
            } else {
                //System.out.println("A JmlInlinedLoop expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
        @Override
        public String toString() {
            return JmlTree.toString(this); 
        }

        @Override
        public int getEndPosition(EndPosTable table) {
            return pos;  // FIXME - end position is not set apparently; also really want the end, not he begining
        }
        
        @Override
        public JCStatement body() {
            return null;
        }
    }

    /** This class wraps a Java for loop just so it can attach some specs
     * to it.
     */
    public static class JmlForLoop extends JCForLoop implements IJmlLoop {
    
        public boolean split;
        public boolean isSplit() { return split; }
        public void setSplit(boolean s) { split = s; }

        public List<JmlStatementLoop> loopSpecs;
        
        public List<JmlStatementLoop> loopSpecs() { return loopSpecs; }
        public void setLoopSpecs(List<JmlStatementLoop> loopSpecs) { this.loopSpecs = loopSpecs; }
    
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
        
        @Override
        public JCStatement body() {
            return body;
        }
    }

    /** This class wraps a Java while loop just so it can attach some specs
     * to it.
     */
    public static class JmlWhileLoop extends JCWhileLoop implements IJmlLoop {
 
        public boolean split;
        public boolean isSplit() { return split; }
        public void setSplit(boolean s) { split = s; }

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlWhileLoop(JCWhileLoop loop, List<JmlStatementLoop> loopSpecs) {
            super(loop.cond,loop.body);
            this.pos = loop.pos;
            this.type = loop.type; // copied for completeness, in case a loop ever has a type
            this.loopSpecs = loopSpecs;
        }
        public List<JmlStatementLoop> loopSpecs;

        public List<JmlStatementLoop> loopSpecs() { return loopSpecs; }
        public void setLoopSpecs(List<JmlStatementLoop> loopSpecs) { this.loopSpecs = loopSpecs; }

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
        
        @Override
        public int getStartPosition() {
            return loopSpecs.size() > 0 ? loopSpecs.head.getStartPosition() : pos;
        }
        
        @Override
        public JCStatement body() {
            return body;
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
        public Tag getTag() {
            return Tag.NO_TAG;
        }
        
        @Override
        public int getStartPosition() {
            return pos;
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
    
    public static class JmlLabeledStatement extends JCTree.JCLabeledStatement {
        public ListBuffer<JCStatement> extraStatements = new ListBuffer<>();
        
        protected JmlLabeledStatement(Name label, JCStatement body) {
            super(label,body);
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitLabelled(this); 
            } else {
                for (JCStatement s: extraStatements) {
                    s.accept(v);
                }
                v.visitLabelled(this);
            }
        }
    
        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitLabeledStatement(this, d);
            } else {
                System.out.println("A JmlLabeledStatement expects an JmlTreeVisitor, not a " + v.getClass());
                return null; // return super.accept(v,d);
            }
        }
}

    /** This class represents JML LBL expressions */
    public static class JmlLblExpression extends JmlExpression {
        /** The kind of label (BSLBLANY, BSLBLPOS, BSLBLNEG) */
        public IJmlClauseKind kind;
        /** The name given by the label*/
        public Name label;
        /** The expression that is labelled */
        public JCExpression expression;
        
        public int labelPosition;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlLblExpression(int pos, int labelPosition, IJmlClauseKind kind, Name label, JCTree.JCExpression expr) {
            this.pos = pos;
            this.labelPosition = labelPosition;
            this.kind = kind;
            this.label = label;
            this.expression = expr;
        }
        
        public JmlLblExpression(JmlLblExpression that) {
            this(that.pos,that.labelPosition,that.kind,that.label,that.expression);
            
        }
        
        /*@ pure */
        public int getLabelPosition() {
            return labelPosition;
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

    public static class JmlIfStatement extends JCIf {
        
        public boolean split = false;
        
        public JmlIfStatement(JCExpression cond, JCStatement then, JCStatement els) {
            super(cond,then,els);
        }
    }

    public static class JmlSwitchStatement extends JCSwitch {
        
        public boolean split = false;
        
        public JmlSwitchStatement(JCExpression selector, List<JCCase> cases) {
            super(selector,cases);
        }
    }
    
    public static class JmlCase extends JCCase {
        
        public JCExpression check;
        public JmlCase(CaseKind caseKind, List<JCCaseLabel> labels,
                JCExpression guard, List<JCStatement> stats, JCTree body) {
            super(caseKind, labels, guard, stats, body);
            check = null;
        }
    }

    /** This class represents a match expression, which has the form
           match(expr) {
           case expr -> expr;
           ...
           default -> expr;
           }
      */
    public static class JmlMatchExpression extends JmlExpression {
        
        public static class MatchCase {
            public JCExpression caseExpression;
            public JCExpression value;
            public MatchCase(JCExpression c, JCExpression v) { caseExpression = c; value = v; }
            public MatchCase copy() { return new MatchCase(caseExpression, value); }
        }
        
        /** The expression to match */
        public JCExpression expression;
        
        public List<MatchCase> cases;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMatchExpression(int pos, JCTree.JCExpression expr, List<MatchCase> cases) {
            this.expression = expr;
            this.cases = cases;
        }
    
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMatchExpression(this); 
            } else {
                //System.out.println("A JmlLblExpression expects an IJmlVisitor, not a " + v.getClass());
                expression.accept(v);
            }
        }
    
        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMatchExpression(this, d);
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
        public String keyword; // May be a synonym of the canonical keyword
        public Name name;
        public IJmlClauseKind clauseKind;
        public JavaFileObject sourcefile;  // FIXME - don't think this belongs here
        public JavaFileObject source() { return sourcefile; }
        public void setSource(JavaFileObject jfo) { sourcefile = jfo; }
        protected JmlMethodClause(int pos, String keyword, IJmlClauseKind clauseKind) {
            this.pos = pos;
            this.keyword = keyword;
            this.clauseKind = clauseKind;
        }
    }
    
    /** This class represents a method specification clause that has an
     * expression, but also a conditional when it is enabled. (FIXME - examples?)
     */
    public static class JmlMethodClauseConditional extends JmlMethodClause {
    
        public JCTree.JCExpression expression;
        /*@ nullable */ public JCTree.JCExpression predicate;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseConditional(int pos, String keyword, IJmlClauseKind clauseKind, JCTree.JCExpression expression, /*@ nullable*/ JCTree.JCExpression predicate) {
            super(pos, keyword, clauseKind);
            this.expression = expression;
            this.predicate = predicate;
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
        public JmlTokenKind token;
        public IJmlClauseKind kind;
        public String name;
        public Object labelProperties = null; // FIXME - explain this
        public boolean javaType = false; // FIXME - this is a hack
        
        /** Creates a method invocation for a JML specific construct (e.g. \typeof) -
         * no type arguments and no expression for the method name, just a token.
          - but use the factory to get new nodes, not this */
        protected JmlMethodInvocation(int pos,
                JmlTokenKind token,
                List<JCExpression> args)
        {
            super(List.<JCExpression>nil(),null,args);
            this.token = token;
            this.name = null;
            this.pos = pos; // preferred position
            this.startpos = pos;
        }
        protected JmlMethodInvocation(int pos,
                IJmlClauseKind kind,
                List<JCExpression> args)
        {
            super(List.<JCExpression>nil(),null,args);
            this.token = null;
            this.kind = kind;
            this.name = null;
            this.pos = pos; // preferred position
            this.startpos = pos;
        }
        
        protected JmlMethodInvocation(int pos,
                String name,
                List<JCExpression> args)
        {
            super(List.<JCExpression>nil(),null,args);
            this.token = null;
            this.name = name;
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
            this.name = null;
            this.pos = pos; // preferred position
            this.startpos = pos;
        }
        
        protected JmlMethodInvocation(int pos, List<JCExpression> typeargs,
                JCExpression meth,
                List<JCExpression> args)
		{
		    super(typeargs, meth, args);
		    this.pos = pos;
            this.startpos = pos; // FIXME
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
                v.visitTree(this);
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
    }

    /** This class represents a method specification clause that has just an
     * expression (e.g. requires, ensures).
     */
    public static class JmlMethodClauseCallable extends JmlMethodClause {

        public JmlSingleton keyword;
        public List<JmlMethodSig> methodSignatures;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseCallable(int pos, JmlSingleton keyword, List<JmlMethodSig> methodSignatures) {
            super(pos, CallableClauseExtension.callableID, CallableClauseExtension.callableClause);
            this.keyword = keyword;
            this.methodSignatures = methodSignatures;
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
    
    
    /** This class represents a old method specification clause.*/
    public static class JmlMethodClauseDecl extends JmlMethodClause {

        public List<JCTree.JCVariableDecl> decls;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseDecl(int pos, IJmlClauseKind clauseType, List<JCTree.JCVariableDecl> decls) {
            super(pos, clauseType.keyword(), clauseType);
            this.decls = decls;
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
        public JCTree.JCExpression exception; // just for clauses with 'else' suffixes

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseExpr(int pos, String keyword, IJmlClauseKind clauseType, JCTree.JCExpression expression) {
            super(pos,keyword,clauseType);
            this.expression = expression;
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
        
        @Override
        public int getStartPosition() {
            return pos;
        }
    }
    
    /** This class represents a method specification clause that has just an
     * expression (e.g. requires, ensures).
     */
    public static class JmlMethodClauseBehaviors extends JmlMethodClauseExpr {

        public String command;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseBehaviors(int pos, String command) {
            super(pos,behaviorsID,behaviorsClauseKind,null);
            this.command = command;
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodClauseBehaviors(this); 
            } else {
                //System.out.println("A visitJmlMethodClauseBehaviors expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodClauseBehaviors(this, d);
            } else {
                System.out.println("A visitJmlMethodClauseBehaviors expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
        @Override
        public int getStartPosition() {
            return pos;
        }
    }
    
    /** This class represents a method specification clause that has just an
     * expression (e.g. requires, ensures).
     */
    public static class JmlMethodClauseInvariants extends JmlMethodClause {

        public List<JCTree.JCExpression> expressions;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseInvariants(int pos, List<JCTree.JCExpression> expressions) {
            super(pos,invariantsID,invariantsClauseKind);
            this.expressions = expressions;
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodClauseInvariants(this); 
            } else {
                //System.out.println("A JmlMethodClauseInvariants expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlMethodClauseInvariants(this, d); 
            } else {
                System.out.println("A JmlMethodClauseInvariants expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
        @Override
        public int getStartPosition() {
            return pos;
        }
    }
    
    /** This represents the sequence of method specs lists that are the sequence
     * of nested specs
     */
    public static class JmlMethodClauseGroup extends JmlMethodClause {

        public List<JmlSpecificationCase> cases;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseGroup(int pos, String keyword, IJmlClauseKind clauseType, List<JmlSpecificationCase> cases) {
            super(pos, keyword, clauseType);
            this.cases = cases;
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
        protected JmlMethodClauseSignals(int pos, String keyword, IJmlClauseKind clauseType, JCTree.JCVariableDecl var, JCTree.JCExpression expression) {
            super(pos, keyword, clauseType);
            this.vardef = var;
            this.expression = expression;
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

        public boolean defaultClause;
        
        /** The list of names of exceptions - either JCIdent or JCFieldAccess */
        // FIXME - why not Names?
        public List<JCTree.JCExpression> list;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlMethodClauseSignalsOnly(int pos, String keyword, IJmlClauseKind clauseType, List<JCTree.JCExpression> list) {
            super(pos, keyword, clauseType);
            this.list = list;
            this.defaultClause = false;
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
        protected JmlMethodClauseStoreRef(int pos, String keyword, IJmlClauseKind clauseType, List<JCExpression> list) {
            super(pos, keyword, clauseType);
            this.list = list;
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
         * to the parameter and result modifiers; is null if the JmlMethodSpecs
         * is owned by a block.
         */
        public JmlMethodDecl decl = null;
        
        /** The standard specification cases */
        public List<JmlSpecificationCase> cases;
        
        /** The implies-that specification cases */
        public List<JmlSpecificationCase> impliesThatCases;
        
        /** The for-example specification cases */
        public List<JmlSpecificationCase> forExampleCases;
        
        /** The behaviors specification cases */
        public List<JmlMethodClauseBehaviors> behaviors;
        
        public List<JmlMethodClause> feasible;
        
        public JmlMethodSpecs deSugared = null; // FIXME - should this be here?
        
        // FIXME - should these constructors be public?
        
        /** Creates an instance with only regular cases (no impliesThat or example cases)*/
        public JmlMethodSpecs(int pos, List<JmlSpecificationCase> cases) {
            this.pos = pos;
            this.cases = cases;
            this.impliesThatCases = List.<JmlSpecificationCase>nil();
            this.forExampleCases = List.<JmlSpecificationCase>nil();
            this.behaviors = null;
            this.feasible = null;
        }
        
        public JmlMethodSpecs() {
            this.pos = Position.NOPOS;
            this.cases = List.<JmlSpecificationCase>nil();;
            this.impliesThatCases = List.<JmlSpecificationCase>nil();
            this.forExampleCases = List.<JmlSpecificationCase>nil();
            this.behaviors = null;
            this.feasible = null;
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
        
        public JmlTokenKind token;
        public IJmlClauseKind jmlclausekind;
        public Name typeName;
        
        /** The representation of this JML type when used in RAC */
        public JCExpression repType;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlPrimitiveTypeTree(int pos, JmlTokenKind token, IJmlClauseKind kind, Name id) {
        	super(TypeTag.NONE);
            this.pos = pos;
            this.token = token;
            this.jmlclausekind = kind;
            this.typeName = id;
        }
        
        @Override
        public String toString() {
            return token != null ? token.internedName() : super.toString();
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
        
        @Override
        public int getStartPosition() {
            return pos;
        }

    }

    /** This class represents JML quantified expressions */
    public static class JmlQuantifiedExpr extends JmlExpression {
        // Current JML allows multiple bound variables in a quantified expression,
        // but requires them all to have the same type.  However, in anticipation of
        // relaxing this requirement and for use elsewhere (i.e. in ESC) this
        // class permits different types.
    	
        /** The operation, e.g \\forall, \\exists, \\let, ... */
        public IJmlClauseKind kind;
        
        /** The declarations over which the expressions are quantified */
        public List<JCVariableDecl> decls;
        
        /** The predicate restricting the range of iteration */
        public JCExpression range;
        
        /** The value - e.g. a predicate for forall, a numeric value for sum, etc. */
        public JCExpression value;
        
        /** A (partial) expression used in RAC, but constructed here for convenience */
        public JCExpression racexpr;
        
        /** The user-specified triggers for the quantification */
        //@ nullable
        public List<JCExpression> triggers = null;
        
        public JmlVariableDecl founddef = null; // Not part or the parsed AST -- set and used in RAC translations
        public JCStatement failure = null; // Not part or the parsed AST -- set and used in RAC translations
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlQuantifiedExpr(int pos, IJmlClauseKind kind,
                List<JCVariableDecl> decls,
                JCExpression range, JCExpression value) {
            this.pos = pos;  // Start of the token
            this.kind = kind;
            this.decls = decls;
            this.range = range;
            this.value = value;
            this.racexpr = null;
        }
                
        @Override 
        public int getStartPosition() {
            return pos;
        }
        
        @Override 
        public int getEndPosition(EndPosTable endPosTable) {
            return value.getEndPosition(endPosTable);
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
    
    public static class JmlRange extends JmlExpression {
    	public /*@ nullable */ JCExpression lo;
    	public /*@ nullable */ JCExpression hi;
    	public boolean hiExclusive = false;
    	
    	protected JmlRange(int pos, JCExpression lo, JCExpression hi) {
    		this.pos = pos;
    		this.lo = lo;
    		this.hi = hi;
    	}
    	
        @Override
        public int getEndPosition(EndPosTable endPosTable) {
            return hi == null ? pos : hi.getEndPosition(endPosTable);
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlRange(this); 
            } else {
                v.visitTree(this);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlRange(this,d); 
            } else {
            	//return (R)kind.typecheck((com.sun.tools.javac.comp.JmlAttr)((Attr)v).attr, this, (Env<AttrContext>)d);
                System.out.println("A JmlRange expects a JmlTreeVisitor, not a " + v.getClass() + " " + this);
                new RuntimeException().printStackTrace(System.out);
                return null; //return super.accept(v,d);
            }
        }
    }

    
    /** This class represents JML expression constructs which do not have arguments (syntactically). */
    public static class JmlSingleton extends JmlExpression {
        
        /** The kind of singleton expression */
        public IJmlClauseKind kind;
        
        /** Used for additional information, such as the comment string of an informal expression */
        public Object info = null;

//        /** The constructor for the AST node - but use the factory to get new nodes, not this */
//        protected JmlSingleton(int pos, JmlTokenKind token) {
//            this.pos = pos;
//            this.token = token;
//        }

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlSingleton(int pos, IJmlClauseKind kind) {
            this.pos = pos;
//            this.token = null;
            this.kind = kind;
        }

        @Override
        public String toString() {
            return kind.keyword();
        }
        
        @Override
        public int getEndPosition(EndPosTable endPosTable) {
            return pos + kind.keyword().length();
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlSingleton(this); 
            } else {
                v.visitTree(this);
            }
        }

        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlSingleton(this,d); 
            } else {
            	//return (R)kind.typecheck((com.sun.tools.javac.comp.JmlAttr)((Attr)v).attr, this, (Env<AttrContext>)d);
                System.out.println("A JmlSingleton expects a JmlTreeVisitor, not a " + v.getClass() + " " + this);
                new RuntimeException().printStackTrace(System.out);
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
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlSetComprehension(this); 
            } else {
                v.visitTree(this);
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
    	public int alsoPos = Position.NOPOS; // NOPOS if there is no also token
        public JCModifiers modifiers;
        public IJmlClauseKind token;
        public IJmlClauseKind also;
        public boolean code;
        public boolean callee_only;
        public List<JmlMethodClause> clauses; // A behavior spec case has clauses but no block of statements
        public JCBlock block;  // A model program has a block (of statements) but no clauses
        public JavaFileObject sourcefile;
        public Name name;
        
        public JmlSpecificationCase(int pos, JCModifiers mods, boolean code, IJmlClauseKind token, IJmlClauseKind also, List<JmlMethodClause> clauses, JCBlock block) {
            this.pos = pos;
            this.sourcefile = null;
            this.modifiers = mods;
            this.code = code;
            this.callee_only = false;
            this.token = token;
            this.also = also;
            this.clauses = clauses;
            this.block = block;
        }
        
        public JmlSpecificationCase(JmlSpecificationCase old, List<JmlMethodClause> clauses) {
            this.pos = old.pos;
            this.modifiers = old.modifiers;
            this.code = old.code;
            this.callee_only = false;
            this.token = old.token;
            this.also = old.also;
            this.sourcefile = old.sourcefile;
            this.clauses = clauses;
            this.block = old.block;
            this.name = old.name;
        }
        
        @Override
        public JavaFileObject source() { return sourcefile; }
        
        @Override
        public void setSource(JavaFileObject jfo) { sourcefile = jfo; }
    
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlSpecificationCase(this); 
            } else {
                super.accept(v);
            }
        }
    
        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlSpecificationCase(this, d);
            } else {
                return super.accept(v,d);
            }
        }
    }

    /** This class represents JML statements within the body of a method
     * that take a statement, such as set and debug and end
     */
    public static class JmlStatement extends JmlAbstractStatement {
        public String keyword;
        public IJmlClauseKind clauseType;
        
        //@ nullable
        public JCTree.JCStatement statement;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStatement(int pos, String keyword, IJmlClauseKind clauseType, JCTree.JCStatement statement) {
            this.pos = pos;
            this.clauseType = clauseType;
            this.keyword = clauseType.keyword();
            this.statement = statement;
        }
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStatement(int pos, IJmlClauseKind clauseType, JCTree.JCExpressionStatement statement) {
            this.pos = pos;
            this.clauseType = clauseType;
            this.statement = statement;
        }
    
        @Override
        public int getEndPosition(EndPosTable table) {
            if (clauseType == endClause || statement == null) return pos; // FIXME - could be better
            return statement.getEndPosition(table);
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

    public static class JmlStatementShow extends JmlAbstractStatement {
        public IJmlClauseKind clauseType;
        public List<JCTree.JCExpression> expressions;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStatementShow(int pos, IJmlClauseKind clauseType, List<JCTree.JCExpression> expressions) {
            this.pos = pos;
            this.clauseType = clauseType;
            this.expressions = expressions;
        }
    
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlStatementShow(this); 
            } else {
                //System.out.println("A JmlStatement expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }
    
        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlStatementShow(this, d);
            } else {
                //System.out.println("A JmlStatement expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
        @Override
        public int getEndPosition(EndPosTable table) {
            return pos;  
            // FIXME - end position is not set apparently; also really want the end, not he begining
        }
    }

    /** This class represents JML ghost declarations and model local class
     * declarations (FIXME _ local class?)
     */
    public static class JmlStatementDecls extends JmlAbstractStatement {
        public ModifierKind token;
        public List<JCTree.JCStatement> list;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStatementDecls(int pos, List<JCTree.JCStatement> list) {
            this.pos = pos;
            this.token = Modifiers.GHOST;
            this.list = list;
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
    public static class JmlStatementExpr extends JmlAbstractStatement implements JmlSource {
        /** The kind of statement - e.g. ASSERT, ASSUME, COMMENT, ... */
        public String keyword;
        public IJmlClauseKind clauseType;
        
        /** The associated expression (e.g. the asserted condition) */
        public JCTree.JCExpression expression;
        
        /** An associated optional expression (e.g. such as the one that
         * can come with a Java assert statement).
         */
        public JCTree.JCExpression optionalExpression = null;
        
        public JmlMethodClause associatedClause = null;
        
        /** The source file in which the statement sits (and the file to which pos and line correspond) */
        public JavaFileObject source;
        
        @Override
        public JavaFileObject source() { return associatedSource; }
        
        @Override
        public void setSource(JavaFileObject jfo) { source = jfo; }
        
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
        protected JmlStatementExpr(int pos, String keyword, IJmlClauseKind clauseType, Label label, JCTree.JCExpression expression) {
            this.pos = pos;
            this.keyword = keyword;
            this.clauseType = clauseType;
            this.expression = expression;
            this.label = label;
            this.associatedPos = pos;
        }
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStatementExpr(int pos, IJmlClauseKind token, Label label, JCTree.JCExpression expression) {
            this.pos = pos;
            this.clauseType = token;
            this.expression = expression;
            this.label = label;
            this.associatedPos = pos;
        }
    
        @Override
        public int getStartPosition() {
            return this.pos;
        }
        
        @Override
        public int getEndPosition(EndPosTable table) {
            return optionalExpression != null ? optionalExpression.getEndPosition(table) : expression != null ? expression.getEndPosition(table) : this.pos;
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
        public IJmlClauseKind clauseType;
        
        /** The store-refs whose values are unknown */
        public List<JCTree.JCExpression> storerefs;
                
        /** The source file in which the statement sits (and the file to which pos and line correspond) */
        public JavaFileObject source;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStatementHavoc(int pos, List<JCTree.JCExpression> storerefs) {
            this.pos = pos;
            this.clauseType = StatementLocationsExtension.havocStatement;
            this.storerefs = storerefs;
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
            super(pos,null,null,expr); // FIXME
            this.id = id;
            this.value = value;
        }
    }

    /** This class represents JML method specifications within the body of a method
     * that then apply to the next statement
     */
    public static class JmlStatementSpec extends JmlAbstractStatement {
        public JmlMethodSpecs statementSpecs;
        public List<JCStatement> statements;
        public List<JCIdent> exports;
        public List<JCVariableDecl> decls;
        public List<JCStatement> newStatements;
        public Name label;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStatementSpec(int pos, JmlMethodSpecs statementSpecs) {  // FIXME - fix constructors and copiers
            this.pos = pos;
            this.statementSpecs = statementSpecs;
            this.exports = List.<JCIdent>nil();
            this.decls = null;
            this.newStatements = null;
            this.label = null;
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
    
    /** This is just an abstract class to mark all the kinds of statements that are
     * part of a loop specification.
     */
    public static abstract class JmlStatementLoop extends JmlAbstractStatement implements JmlSource {
    	protected JmlStatementLoop() {}

    	public IJmlClauseKind clauseType;
        public boolean translated;
 
        /** The source file in which the statement sits (and the file to which pos and line correspond) */
        public JavaFileObject source;
        
        @Override
        public JavaFileObject source() { return source; }
        
        @Override
        public void setSource(JavaFileObject jfo) { source = jfo; }
}

    /** This class represents JML statements within the body of a method
     * that apply to a following loop statement (decreases, loop_invariant)
     */
    public static class JmlStatementLoopExpr extends JmlStatementLoop {
        public JCTree.JCExpression expression;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStatementLoopExpr(int pos, IJmlClauseKind token, JCTree.JCExpression expression) {
            this.pos = pos;
            this.clauseType = token;
            this.expression = expression;
        }
    
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlStatementLoopExpr(this); 
            } else {
                //System.out.println("A JmlStatementLoop expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }
    
        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlStatementLoopExpr(this, d);
            } else {
                //System.out.println("A JmlStatementLoop expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    
    /** This class represents JML statements within the body of a method
     * that apply to a following loop statement (decreases, loop_invariant)
     */
    public static class JmlStatementLoopModifies extends JmlStatementLoop {
        public List<JCTree.JCExpression> storerefs;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStatementLoopModifies(int pos, IJmlClauseKind token, List<JCTree.JCExpression> storerefs) {
            this.pos = pos;
            this.clauseType = token;
            this.storerefs = storerefs;
        }
    
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlStatementLoopModifies(this); 
            } else {
                //System.out.println("A JmlStatementLoop expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }
    
        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlStatementLoopModifies(this, d);
            } else {
                //System.out.println("A JmlStatementLoop expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
        
        @Override
        public int getEndPosition(EndPosTable table) {
            return pos;  
            // FIXME - end position is not set apparently; also really want the end, not he begining
        }

    }
    
    /** This node represents a store-ref expression denoting an array range:
     *   a[*] or a[1 .. 2] or a[1 .. ]   FIXME - or is that a[1 .. *]
     * @author David Cok
     */
    public static class JmlStoreRefArrayRange extends JmlExpression {
        public JCExpression expression;
        public /*@nullable*/ JCExpression lo;
        public /*@nullable*/ JCExpression hi;
    
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStoreRefArrayRange(int pos, JCExpression expr, /*@nullable*/ JCExpression lo, /*@nullable*/ JCExpression hi) {
            this.pos = pos;
            this.expression = expr;
            this.lo = lo;
            this.hi = hi;
        }
        
        @Override 
        public int getEndPosition(EndPosTable endPosTable) {
            int p = endPosTable.getEndPos(this);
            if (p == Position.NOPOS) p = pos; // FIXMNE - this should never happen - ofrgot to set endpos
            return p;
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
    
    /** A portmanteau of all store-ref expressions.
     */
    public static class JmlStoreRef extends JmlExpression {
    	
    	protected JmlStoreRef(int pos, boolean isEverything, Symbol local, JCExpression expression, JCExpression receiver, JmlRange range, VarSymbol field, JCExpression originalStoreRef) {
    		this.pos = pos;
    		this.isEverything = isEverything;
    		this.local = local; // Might be 'this'
    		this.expression = expression;
    		this.receiver = receiver;
    		this.range = range;
    		this.field = field;
    		this.originalStoreRef = originalStoreRef;
    	}
    	
    	public JavaFileObject source;
    	
    	public boolean isEverything() { return isEverything; }
    	public boolean isNothing() { return originalStoreRef instanceof JmlSingleton sing && sing.kind == JmlPrimitiveTypes.nothingKind; }
    	
    	// Cases: before type attribution (type == null)
    	// isEverything=true: \everything
        // isEverything=false, receiver=null, id!=null, range==null: simple id
        // isEverything=false, receiver!=null, id!=null, range==null: static or non-static field access
        // isEverything=false, receiver!=null, id==null, range==null: static or non-static field .*
        // isEverything=false, receiver!=null, id==null, range!=null: array access
    	
    	// Cases after type attribution: (a simple id can become something else) (type != null)
    	// isEverything=true, other fields null: \everything
    	// isEverything=false, local nonnull; others null: a local variable
    	// isEverything=false, expression nonull; others null: a locset expression (expression.type is \locset
    	// isEverything=false, range nonnull, receiver nonnull, expression null, fields null: an array range or isngle index
    	public boolean isEverything;
    	/*@ nullable */ public Symbol local;
    	/*@ nullable */ public JCExpression expression;
    	/*@ nullable */ public JCExpression receiver;
    	/*@ nullable */ public JCIdent id;
    	/*@ nullable */ public JmlRange range;
    	/*@ nullable */ public VarSymbol field;
    	public JCExpression originalStoreRef = null;

    	@Override
		public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlStoreRef(this); 
            } else {
                System.out.println("A JmlStoreRefKeyword expects an IJmlVisitor, not a " + v.getClass());
                //super.accept(v);
            }
		}
		@Override
		public <R, D> R accept(TreeVisitor<R, D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlStoreRef(this, d);
            } else {
                System.out.println("A JmlStoreRefKeyword expects an JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
		}
    }

    /** Represents a nothing, everything or informal comment token */
    // FIXME - is the content of the informal comment stored somewhere?  JmlExpression???
    public static class JmlStoreRefKeyword extends JmlExpression {
        public IJmlClauseKind kind; // nothing or everything or informal comment

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStoreRefKeyword(int pos, IJmlClauseKind kind) {
            this.pos = pos;
            this.kind = kind;
        }
        
        @Override
        public int getEndPosition(EndPosTable endPosTable) {
            return pos + kind.keyword().length();
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
        public JmlTokenKind token;
        public List<JCExpression> list;

        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlStoreRefListExpression(int pos, JmlTokenKind token, List<JCExpression> list) {
            this.pos = pos;
            this.token = token;
            this.list = list;
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
    abstract public static class JmlTypeClause extends JCTree implements JmlSource, IInJML {
        
        /** The token identifying the kind of clause this represents */
        public String keyword;
        public Name name;
        public IJmlClauseKind clauseType;
        
        /** The source of this clause, since it might be from a different compilation unit. */
        public JavaFileObject source;
        
        /** The modifiers for the clause */
        public JCModifiers modifiers;

        /** Returns the source file for the clause */
        public JavaFileObject source() { return source; }
        
        @Override
        public void setSource(JavaFileObject jfo) { source = jfo; }
        
        public boolean isJML() {
            return true;
        }
        
        /** This implements toString() for all the type clause nodes */
        public String toString() {
            return JmlTree.toString(this);
        }
        
        public int getStartPosition() {
            int p = pos;
            if (modifiers != null) p = modifiers.getStartPosition();
            if (p == Position.NOPOS) p = pos;
            return p;
        }
        
        @Override
        public Kind getKind() { 
            return Kind.OTHER; // See note above
        }
        
        @Override
        public Tag getTag() {
            return Tag.NO_TAG;
        }
    }
    
    /** This class represents 'represents' type clauses  in a class specification */
    public static class JmlTypeClauseConstraint extends JmlTypeClause {

        /** The constraint expression */
        public JCTree.JCExpression expression;
        
        /** The list of method signatures to which the constraint applies */
        public /*@nullable*/ List<JmlMethodSig> sigs;
        
        /** If true then the list is the method signatures to which the constraint does not apply (a JML extension)*/
        public boolean notlist = false;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlTypeClauseConstraint(int pos, JCModifiers mods, JCExpression expression, List<JmlMethodSig> sigs) {
            this.pos = pos;
            this.modifiers = mods;
            this.keyword = TypeExprClauseExtension.constraintID;
            this.clauseType = TypeExprClauseExtension.constraintClause;
            this.expression = expression;
            this.sigs = sigs; // Method signatures
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
        protected JmlTypeClauseConditional(int pos, JCModifiers mods, IJmlClauseKind token, JCTree.JCIdent ident, JCTree.JCExpression expression) {
            this.pos = pos;
            this.modifiers = mods;
            this.clauseType = token;
            this.identifier = ident;
            this.expression = expression;
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
            this.clauseType = typedeclClause;
            this.modifiers = 
                    decl instanceof JCVariableDecl ? ((JCVariableDecl)decl).mods :
                        decl instanceof JCMethodDecl ? ((JCMethodDecl)decl).mods :
                            decl instanceof JCClassDecl ? ((JCClassDecl)decl).mods :
                        null;  // FIXME - something wrong if this is null
            this.decl = decl;
        }
        
        @Override
        public Tag getTag() {
            return decl.getTag();
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
        protected JmlTypeClauseExpr(int pos, JCModifiers mods, String keyword, IJmlClauseKind token, JCTree.JCExpression expression) {
            this.pos = pos;
            this.modifiers = mods;
            this.clauseType = token;
            this.expression = expression;
            if (mods.pos == Position.NOPOS) mods.pos = pos;
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
                //System.out.println("A JmlTypeClauseExpr expects an JmlTreeVisitor, not a " + v.getClass());
                return null; //return super.accept(v,d);
            }
        }
        
        public int getStartPosition() {
            return modifiers.getStartPosition();
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
            this.keyword = TypeInClauseExtension.inID;
            this.clauseType = TypeInClauseExtension.inClause;
            this.list = list;
            this.parentVar = null;
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
        protected JmlTypeClauseInitializer(int pos, IJmlClauseKind token, JCModifiers mods) {
            this.pos = pos;
            this.keyword = token.keyword();
            this.clauseType = token;
            this.source = null;
            this.modifiers = mods; 
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
        public List<JCExpression> expressions;
        
        /** The list of datagroup targets */
        public List<JmlGroupName> list;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlTypeClauseMaps(int pos, List<JCExpression> e, List<JmlGroupName> list) {
            this.pos = pos;
            this.expressions = e;
            this.modifiers = null;
            this.clauseType = mapsClause;
            this.list = list;
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
            this.clauseType = monitorsforClause;
            this.list = list;
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
            this.clauseType = representsClause;
            this.ident = ident;
            this.expression = expression;
            this.suchThat = suchThat;
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
    
    public static class JmlTuple extends JmlExpression {
        public java.util.List<JCExpression> values;
        
        public JmlTuple(int pos, java.util.List<JCExpression> values) {
            this.pos = pos;
            this.values = values;
        }

        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlTuple(this); 
            } else {
                for (JCExpression e: values) e.accept(v);
            }
        }

        @Override
        public <R, D> R accept(TreeVisitor<R, D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitJmlTuple(this, d);
            } else {
                for (JCExpression e: values) e.accept(v, d);
                return null;
            }
        }
        
    }
    
    public static class JmlLambda extends JCLambda {
        public JCExpression jmlType;
        public JCIdent literal;
        public JavaFileObject sourceLocation;
        
        public JmlLambda(List<JCVariableDecl> params,
                JCTree body, JCExpression jmlType) {
            super(params, body);
            this.jmlType = jmlType;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitLambda(this); 
            } else {
                //System.out.println("A JmlLambda expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }
    
        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return v.visitLambdaExpression(this, d);
            } else {
                //System.out.println("A JmlLambda expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }

    }
    
    public static class JmlLetExpr extends LetExpr {
        public boolean explicit = false;
        
        public JmlLetExpr(List<JCStatement> defs, JCExpression expr, boolean explicit) {
            super(defs, expr);
            this.explicit = explicit;
        }
        
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitLetExpr(this); 
            } else {
                //System.out.println("A JmlLambda expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }
    
        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitLetExpr(this, d);
            } else {
                //System.out.println("A JmlLetExpr expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
    
    public static class JmlNewClass extends JCNewClass {
        protected JmlNewClass(int pos, JCExpression encl, List<JCExpression> typeargs,
                JCExpression clazz, List<JCExpression> args, JCClassDecl def) {
            super(encl, typeargs, clazz, args, def);
            this.pos = pos;
        }

        public Map<Name,JCExpression> capturedExpressions = new HashMap<>();

        
//        @Override
//        public void accept(Visitor v) {
//            if (v instanceof IJmlVisitor) {
//                v.visitNewClass(this); 
//            } else {
//                //System.out.println("A JmlNewClass expects an IJmlVisitor, not a " + v.getClass());
//                super.accept(v);
//            }
//        }
    
        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitNewClass(this, d);
            } else {
                //System.out.println("A JmlNewClass expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }

    // FIXME - the following do not have factory methods - do not set pos, do not have accept, getKind, getTag, toString methods, or documentation
    // Arrays are represented by a 2 level map, representing all the arrays of a given type
    // THis object represents   newarrs = oldarrs[ arr := arr[ index := rhs ]]
    // If index is rhs is null, then this is a havoc; if index is null then all element are havoced
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
        
        public JmlBBArrayAssignment(JCIdent newarrs, JCExpression arr, JCExpression index, JCExpression rhs) {
            super(null,null,null);
            ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
            list.append(newarrs);
            list.append(arr);
            list.append(index);
            list.append(rhs);
            args = list.toList();
        }
        
        
        @Override
        public int getStartPosition() {
            return args.get(0).getStartPosition(); // newarrs
        }
        
        @Override
        public int getEndPosition(EndPosTable table) {
            return args.get(args.length()-1).getEndPosition(table); // rhs
        }        
    }
    
    // TODO: Not used?
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
        public int getEndPosition(EndPosTable table) {
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

    public static class JmlAnnotation extends JCAnnotation {
    	public ModifierKind kind;
        public JmlAnnotation(Tag tag, JCTree annotationType, List<JCExpression> args) {
            super(tag,annotationType,args);
            kind = null;
        }
        
        public JmlAnnotation(Tag tag, ModifierKind kind, JCTree annotationType) {
            super(tag,annotationType,List.<JCExpression>nil());
            this.kind = kind;
        }
        
        /** The origin of the annotation, which may not be the same as the item being annotated;
         * if null, the annotation is inserted to make a default explicit.
         */
        /*@nullable*/ public JavaFileObject sourcefile;
        @Override
        public void accept(Visitor v) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitAnnotation(this); 
            } else {
                //System.out.println("A JmlNewClass expects an IJmlVisitor, not a " + v.getClass());
                super.accept(v);
            }
        }
    
        @Override
        public <R,D> R accept(TreeVisitor<R,D> v, D d) {
            if (v instanceof JmlTreeVisitor) {
                return ((JmlTreeVisitor<R,D>)v).visitAnnotation(this, d);
            } else {
                //System.out.println("A JmlNewClass expects an JmlTreeVisitor, not a " + v.getClass());
                return super.accept(v,d);
            }
        }
    }
}
