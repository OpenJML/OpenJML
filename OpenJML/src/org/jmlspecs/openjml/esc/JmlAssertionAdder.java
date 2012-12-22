/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;


import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.BasicBlocker2.TargetFinder;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;

/** This class translates an attributed Java+JML AST, creating a new Java-compatible AST
 * that includes assertions to check for all the various JML conditions that need checking.
 * The resulting AST is a complete copy - it does not share any mutable structure with the original
 * AST, so the original AST can be reused; it represents each identifier in a separate
 * JCIdent, so that a succeeding Single-assignment step can change identifier names in place.
 * <P>
 * There are three modes of translation:
 * <UL>
 * <LI>esc=true,rac=false: This inserts all required assertions as JML assert
 * and assume statements, Java assignments and variable declarations,
 * retaining the Java control flow statements.
 * <LI>rac=true,esc=false: This inserts all executable JML checks as Java assert statements.
 * The translated AST is a transformation of the original program, but is
 * functionally equivalent to it.
 * <LI>esc=false, rac=false: This creates a copy of the original AST, without
 * any JML checks. It is a functionally equivalent strict copy.
 * <LI>esc=true,rac=true: unsupported.
 * </UL>
 * <P>
 * With either rac or esc on, the translated AST uses only a subset of Java
 * functionality. All JML features are translated into assertions.
 * <UL>
 * <LI>Java expressions:
 * </UL>
 * <LI>binary operations - arithmetic, bit, logical all allowed in Java statements and JML assertions;
 * instanceof is allowed in Java, translated into a type relationship in JML
 * <LI>unary operations - minus and negation allowed; pre- and post-increment
 * and decrement converted to separate operations and assignment
 * <LI>assignment - retained 
 * <LI>assign-op - separated into operation and assignment
 * <LI>type cast - TBD
 * <LI>field selection - TBD
 * <LI>array index - retained, but uses JmlBBArrayAccess nodes instead of JCArrayAccess
 * <LI> 
 * <LI>object allocation - TBD
 * <LI>array allocation - TBD
 * <LI>anonymous class expression - TBD
 * <LI>...TBD
 * </UL>
 * <LI>Java statements:
 * <UL>
 * <LI>if, switch, try statements are retained
 * <LI>for, while, do, foreach statements are retained but may be transformed 
 * into other loop types to accommodate inserting loop specifications
 * <LI>variable declarations - TBD
 * <LI>local class declarations - TBD
 * <LI>method declarations, class declarations, import declarations - all retained
 * </UL>
 * <LI> JML expressions:
 * <UL>
 * <LI> binary logical operations - converted to Java equivalents
 * <LI> subtype operation - TBD
 * <LI> ... TBD
 * </UL>
 * <LI> JML statements and features:
 * <UL>
 * <LI> assert, assume statements - is esc mode, these are retained as JML statements
 * in rac mode, they are converted to RAC checks
 * <LI> method clauses: requires, ensures, signals - converted to assertions
 * </UL>
 * 
 *
 */
// FIXME - should we use the copier instead??
public class JmlAssertionAdder extends JmlTreeScanner {

    // Parameters of this instance of JmlAssertionAdder 
    
    /** If true then every part of every AST is copied; if false then items
     * expected to be immutable such as JCLiteral, qualified ids (in import
     * statements, static type designators), JCAnnotation are not copied. 
     * Non-AST objects
     * such as Type, Token or JmlToken values are not copied in any case.
     */
    public boolean fullTranslation = false;
    
    // NOTE: We support !esc || !rac but not esc && rac.
    //@ invariant !esc || !rac;
    
    /** True if we are translating for static checks */
    public boolean esc ;
    
    /** True if we are translating for RAC */
    public boolean rac ;
    

    // Constant items set in the constructor
    
    /** The compilation context */
    final protected Context context;
    
    /** Cached value of the Log tool */
    final protected Log log;
    
    /** Cached value of the specs database */
    final protected JmlSpecs specs;
    
    /** Cached value of the AST node factory */
    final protected JmlTree.Maker M;
    
    /** Cached value of the names table */
    final protected Names names;
    
    /** Cached value of the symbol table */
    final protected Symtab syms;
    
    /** Cached value of the Types tool */
    final protected Types types;
    
    /** The JmlTreeUtils object, holding a bunch of tree-making utilities */
    final protected JmlTreeUtils treeutils;

    /** An AST visitor for translating JML expressions; since JML expressions
     * do not have side effects, this visitor can be simpler than 
     * JmlAssertionAdder itself.
     */
    final protected JmlExpressionRewriter jmlrewriter = new JmlExpressionRewriter();
    
    // TODO = document
    final protected Name resultName;
    protected Symbol resultSym = null;
    
    
    // TODO = document
    final protected Name exceptionName;
    protected Symbol exceptionSym = null;
    
    // TODO = document
    final protected Name terminationName;
    protected Symbol terminationSym = null;

    // Fields used and modified during translation
    
    /** The AST being processed - set in convertMethodBody */
    protected JCMethodDecl methodDecl = null;
    
    /** The parent class of the method being converted, for use while the
     * method's SAT is being walked.
     */
    protected JmlClassDecl classDecl = null;
    
    // FIXME
    protected ListBuffer<JCTree> classDefs;
    
    // TODO - document - is this needed?
    public Map<String,DiagnosticPositionSES> positionMap = new HashMap<String,DiagnosticPositionSES>();
    
    /** A map holding the names of the ids that are the actual parameters
     * for the given formal parameters
     */
    protected Map<VarSymbol,JCIdent> currentArgsMap = new HashMap<VarSymbol,JCIdent>();

    /** The counter used to make uniquely named variables for preconditions,
     * unique within a method body. */
    int precount = 0;
    
    /** The counter used to make uniquely named variables for assertions,
     * unique within a method body. */
    protected int assertCount = 0;
    
    /** A counter that ensures unique variable names. */
    protected int count = 0;
    
    // TODO = docuemnt
    protected Map<Symbol,JCVariableDecl> preparams = new HashMap<Symbol,JCVariableDecl>();
    protected Map<JmlSpecificationCase,JCIdent> preconditions = new HashMap<JmlSpecificationCase,JCIdent>();
    
    
    // TODO = document
    final protected java.util.List<String> labels = new LinkedList<String>();
    
    /** A list to collect statements as they are being generated. */
    protected ListBuffer<JCStatement> currentStatements;

    /** A stack of 'currentStatments' . The current value of 'currentStatements'
     * is NOT on this stack. */
    protected LinkedList<ListBuffer<JCStatement>> statementStack = new LinkedList<ListBuffer<JCStatement>>();
    
    /** Used to hold the result of non-expression AST nodes */
    protected JCTree result;
    
    /** Used to hold the result of expression AST nodes */
    protected JCExpression eresult;
    
    /** Returns a new JCBlock representing the rewritten body of the given method declaration */
    public JCBlock convertMethodBody(JCMethodDecl decl, JmlClassDecl cd) {
        JCMethodDecl prev = methodDecl;
        // We have the classDecl as an argument and save it here because
        // convertMethodBody may be called directly and not necessarily while
        // of walking the AST.
        this.classDecl = cd;
        
        // FIXME - these should not be reset for anonymous and local classes
        this.count = 0;
        this.assertCount = 0;
        this.precount = 0;
        this.preparams.clear();
        this.preconditions.clear();
        this.labels.clear();
        try {
            this.methodDecl = decl;
            return convertBody();
        } catch (RuntimeException e) {
            String message = e.getMessage();
            if (message == null) message = "Internal exception: " + e.getClass();
            // FIXME - include the stack trace
            Log.instance(context).error("jml.internal.notsobad",message);
            return null;
        } finally {
            methodDecl = prev;
        }
    }
    
    /** Creates an object to do the rewriting and assertion insertion. This object
     * can be reused to translate different method bodies, so long as the arguments
     * to this constructor remain appropriate.
     * @param context the compilation context to be used
     * @param esc true if the resulting AST is to be used for ESC, false if it is to be used for RAC
     */
    public JmlAssertionAdder(Context context, boolean esc, boolean rac) {
        this.context = context;
        this.esc = esc;
        this.rac = rac;
        this.log = Log.instance(context);
        this.M = JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.syms = Symtab.instance(context);
        this.types = Types.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.resultName = names.fromString(Strings.resultVarString);
        this.exceptionName = names.fromString(Strings.exceptionVarString);
        this.terminationName = names.fromString(Strings.terminationVarString);
    }
    
    /** Creates the overall framework for the block:
     * <PRE> 
         preconditions
         try {
            method body
         } finally {
            postconditions
         }
        </PRE>
     * <P>
     * The converted method body is a new block with the following characteristics:
     * <UL>
     * <LI>control flow statements are still present: if-then-else, switch, try-catch-finally blocks
     * <LI>expressions in Java code are decomposed into individual operations, with temporaries. This is so that
     * (a) it is easy to add any assertions prior to a specific operation
     * (b) it is straightforward to handle any operation with side-effects, even in the context of
     * short-circuit operations
     * <LI>assertions are added in for any checks that are desired (see the list below)
     * <LI>specification expressions are not decomposed into individual operations, since all the
     * sub-expressions are supposed to be pure; however, additional assertions are added before any
     * specification expression to check that the specification expression is well-defined - TODO
     * <LI>conditional and short-circuit expressions (in Java code) are converted into if-then-else statements;
     * again, this is to simplify handling of side-effects in sub-expressions - TODO for short-circuit
     * <LI>all identifiers are made unique by combining the name with location information; but no
     * conversions for single-assignment are performed - TODO
     * </UL>
     * <P>
     * These operations are converted: 
     * <UL>
     * <LI>JML equivalence to boolean =
     * <LI>JML inequivalence to boolean !=
     * <LI>JML reverse implies (p <== q) to (p || !q)
     * <LI>Java assignments with operations are decomposed into the operation and the assignment
     * </UL>
     * <LI>These operations are retained:
     * <UL>
     * <LI>assignment
     * <LI>integer and floating +, -, *, /, %
     * <LI>== and !=
     * <LI>comparison operations (integer and floating)
     * <LI>bit and or xor
     * 
     * </UL>
     * <LI>TODO: mod, integer division, shift operations, bit operations, JML implies, JML subtype,
     * instanceof, short-circuit boolean operations
     * <LI>TODO: handle method calls
     * <LI>TODO: handle method calls in specifications
     * <LI>TODO: new Object, new Array expressions
     * <LI>TODO: quantifier and set comprehension expressions
     * <LI>TODO: \fresh operation
     * <LI>TODO: \nonnullelements
     * </UL>
     * <P>
     * These assumptions and checks are added in:
     * <UL>
     * <LI>assume the method preconditions, including null method parameters
     * <LI>assume any class invariants, including null field declarations
     * <LI>assert the method postconditions
     * <LI>assume any explicit assumption
     * <LI>assert any explicit assertion
     * <LI>assert the method exceptional postconditions - TODO
     * <LI>check for null-dereference on each field access
     * <LI>check for null-dereference on each array access - TODO
     * <LI>check for index out of bounds on each array access - TODO
     * <LI>check for assignment of null to any non-null variable or field
     * <LI>check for out of range arithmetic operations - TODO
     * </UL>
     * 
     * @return JCBlock with all assumptions, assertions, added declarations
     */
    protected JCBlock convertBody() {
        JCMethodDecl decl = methodDecl;
        ListBuffer<JCStatement> initialStatements = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> outerFinalizeStats = new ListBuffer<JCStatement>();
        if (decl.restype != null && decl.restype.type.tag != TypeTags.VOID) {
            JCVariableDecl d = treeutils.makeVarDef(decl.restype.type,resultName,decl.sym,0);
            resultSym = d.sym;
            initialStatements.add(d);
        }
        
        {
            JCVariableDecl d = treeutils.makeVarDef(syms.exceptionType,exceptionName,decl.sym,treeutils.nulllit);
            exceptionSym = d.sym;
            initialStatements.add(d);
        }
        {
            JCVariableDecl d = treeutils.makeVarDef(syms.intType,terminationName,decl.sym,treeutils.zero);
            d.pos = decl.pos;
            terminationSym = d.sym;
            initialStatements.add(d);
        }
        
        pushBlock();
        addPrePostConditions(decl, initialStatements,outerFinalizeStats);
        decl.body.accept(this);
        JCBlock b = popBlock(0,decl.body.pos);
        JCTry outerTryStatement = M.Try(b,List.<JCCatch>nil(),
                M.Block(0, outerFinalizeStats.toList()));
        initialStatements.add(outerTryStatement);
        return M.at(decl.pos()).Block(0,initialStatements.toList());
    }
    
    /** Converts a non-expression AST, returning the converted tree;
     * this may be called externally on ClassDecl and CompilationUnit
     * trees, but should not be called outside of JmlAssertionAdder
     * on trees lower in the AST. */
    public <T extends JCTree> T convert(T tree) {
        scan(tree);
        return (T)result;
    }
    
//    /** Converts an expression AST, returning the converted tree. */
//    protected <T extends JCExpression> JCExpression convert(T tree) {
//        scan(tree);
//        return eresult;
//    }
    
    /** Start collecting statements for a new block; push currentStatements onto a stack for later use */
    protected void pushBlock() {
        statementStack.add(0,currentStatements);
        currentStatements = new ListBuffer<JCStatement>();
    }
    
    /** Wrap the active currentStatements as a block (which is returned) and then resume collecting
     * statements with currentStatements value on the top of the stack (which is also removed
     * from the stack) */
    protected JCBlock popBlock(long flags, int pos) {
        JCBlock b = M.at(pos).Block(flags, currentStatements.toList());
        currentStatements = statementStack.removeFirst();
        return b;
    }
    
    /** Add a statement at the end of the active currentStatements sequence */ 
    protected void addStat(JCStatement stat) {
        currentStatements.add(stat);
    }
    
    /** Add a statement at the end of the given buffer of statements */ 
    protected void addStat(ListBuffer<JCStatement> stats, JCStatement stat) {
        stats.add(stat);
    }
    
    /** This generates a JmlExpressionStatement comment statement with the given string as
     * text; the statement is not added to any statement list.
     */
    protected JmlStatementExpr comment(int pos, String s) {
        return M.at(pos).JmlExpressionStatement(JmlToken.COMMENT,null,M.Literal(s));
    }
    
    /** This generates a comment statement whose content is the
     * given JCTree, pretty-printed; the statement is not added to any statement list
     */
    protected JmlStatementExpr comment(JCTree t) {
        return comment(t.pos,JmlPretty.write(t,false));
    }
    
    /** Issue an internal error message and throw an exception. */
    protected void error(int pos, String msg) {
        log.error(pos, "esc.internal.error", msg);
        throw new JmlInternalError(msg);
    }
    

    /** Adds an assertion with the given label and (already translated) expression
     * to the given statement list. 'codepos' is the position within the code where
     * the assertion is triggered; log.currentSource() is used as the sourcefile
     * in which 'codepos' lies. 'associatedSource' and 'associatedPos' are the
     * location of the specification clause from which this assertion derives,
     * if any.
     */
//    protected JCStatement addAssert(DiagnosticPosition codepos, Label label, JCExpression expr, ListBuffer<JCStatement> stats, int associatedPos, JavaFileObject associatedSource, JCExpression info) {
//        String assertID = Strings.assertPrefix + (++assertCount);
//        Name assertname = names.fromString(assertID);
//        JavaFileObject dsource = log.currentSourceFile();
//        JCVariableDecl decl = treeutils.makeVarDef(syms.booleanType,assertname,methodDecl.sym,expr);
//        stats.add(decl);
//        if (esc) {
//            JmlStatementExpr st = treeutils.makeAssert(codepos,label,treeutils.makeIdent(expr.pos,decl.sym),associatedPos);
//            st.source = dsource;
//            st.declPos = associatedPos;
//            st.associatedSource = associatedSource;
//            st.optionalExpression = info;
//            stats.add(st);
//            return st;
//        } 
//        if (rac) {  // FIXME - implement different styles of rac checking
//            JCDiagnostic diag = JCDiagnostic.Factory.instance(context).warning(log.currentSource(), null, "rac." + label);
//            String msg = diag.getMessage(null);
//            if (info == null) {
//                info = treeutils.makeStringLiteral(msg,expr.pos);
//            }
//            JCStatement st = assertFailure(msg,codepos);
//            st = M.at(codepos).If(treeutils.makeNot(expr.pos,expr), st, null);
////            JCAssert st = M.at(codepos).Assert(treeutils.makeIdent(expr.pos,decl.sym),null);
////            st.detail = info;
//            stats.add(st);
//            return st;
//        }
//        return null;
//}

    protected JCStatement addAssert(DiagnosticPosition codepos, Label label, JCExpression expr, ListBuffer<JCStatement> stats, DiagnosticPosition associatedPos, JavaFileObject associatedSource, JCExpression info) {
        String assertID = Strings.assertPrefix + (++assertCount);
        Name assertname = names.fromString(assertID);
        JavaFileObject dsource = log.currentSourceFile();
        JCVariableDecl decl = treeutils.makeVarDef(syms.booleanType,assertname,methodDecl == null? classDecl.sym : methodDecl.sym,expr);
        if (stats != null) stats.add(decl);
        if (esc) {
            JmlStatementExpr st = treeutils.makeAssert(codepos,label,treeutils.makeIdent(expr.pos,decl.sym),associatedPos);
            st.source = dsource;
            st.declPos = associatedPos == null ? Position.NOPOS : associatedPos.getPreferredPosition();
            st.associatedSource = associatedSource;
            st.optionalExpression = info;
            if (stats != null) stats.add(st);
            return st;
        } 
        if (rac) {  // FIXME - implement different styles of rac checking
            JCDiagnostic diag = JCDiagnostic.Factory.instance(context).warning(log.currentSource(), codepos, "rac." + label);
            boolean withSource = false;
            String msg = (withSource? diag.toString() : diag.noSource()).replace("warning: ", "");
            if (info == null) {
                info = treeutils.makeStringLiteral(msg,expr.pos);
            }
            // FIXME - if info is not null, we don't get line information
            JCStatement st = assertFailure(info,codepos); // FIXME - pass in the whole DiagnosticPosition to get a range instead of a single position?
            st = M.at(codepos).If(treeutils.makeNot(codepos == null ? Position.NOPOS : codepos.getPreferredPosition(), treeutils.makeIdent(expr.pos,decl.sym)), st, null);
            //JCAssert st = M.at(codepos).Assert(treeutils.makeIdent(expr.pos,decl.sym),null);
            //st.detail = info;
            if (stats != null) stats.add(st);
            return st;
        }
        return null;
}

    /** Adds an assertion with the given label and (already translated) expression
     * to the given statement list. 'codepos' is the position within the code where
     * the assertion is triggered; log.currentSource() is used as the sourcefile
     * in which 'codepos' lies. There is no associated position.
     */
    protected JCStatement addAssert(DiagnosticPosition codepos, Label label, JCExpression expr, ListBuffer<JCStatement> stats) {
        return addAssert(codepos,label,expr,stats,null,null,null);
    }
    
    /** Adds an assertion with the given label and (already translated) expression
     * to the given statement list. 'codepos' is the position within the code where
     * the assertion is triggered; log.currentSource() is used as the sourcefile
     * in which 'codepos' lies. The last two arguments give the file and position
     * within the file of the associated specification that is potentially violated.
     */
    protected JCStatement addAssert(DiagnosticPosition codepos, Label label, JCExpression expr, ListBuffer<JCStatement> stats, DiagnosticPosition associatedPos, JavaFileObject associatedSource) {
        return addAssert(codepos,label,expr,stats,associatedPos,associatedSource,null);
    }

 
    /** Creates an AST for calling a method with the given name from the
     * org.jmlspecs.utils class (that is available at runtime)
     * @param methodName the name of the method 
     * @return the corresponding AST
     */
    public JCFieldAccess findUtilsMethod(String methodName) {  // FIXME - needs position informatino
        ClassReader reader = ClassReader.instance(context);
        reader.init(syms);
        ClassSymbol utilsClass = reader.enterClass(names.fromString("org.jmlspecs.utils.Utils"));
        JCIdent utilsClassIdent = M.Ident(utilsClass);
        Name n = names.fromString(methodName);
        Scope.Entry e = utilsClass.members().lookup(n);
        Symbol ms = e.sym;
        if (e.sym == null) {
            return null;
        } else {
            JCFieldAccess m = M.Select(utilsClassIdent,n);
            m.sym = ms;
            m.type = m.sym.type;
            return m;
        }
    }
    /** Creates a call of org.jmlspecs.utils.assertionFailure(s), where
     * s is a literal containing the value of the argument
     * @param sp the string to make into the literal argument of the call
     * @param pos the character position of the created AST
     * @return an assert statement indication an assertion failure
     */
    public JCStatement assertFailure(String sp, DiagnosticPosition pos) {
        JCExpression lit = treeutils.makeLit(pos.getPreferredPosition(),syms.stringType,sp);
        JCFieldAccess m = findUtilsMethod("assertionFailure");
        JCExpression c = M.at(pos).Apply(null,m,List.<JCExpression>of(lit));
        c.setType(syms.voidType);
        return M.at(pos).Exec(c);
    }

    public JCStatement assertFailure(JCExpression sp, DiagnosticPosition pos) {
        JCFieldAccess m = findUtilsMethod("assertionFailure");
        JCExpression c = M.at(pos).Apply(null,m,List.<JCExpression>of(sp));
        c.setType(syms.voidType);
        return M.at(pos).Exec(c);
    }

//    /** Adds an assertion with the given label and (already translated) expression
//     * to the given statement list. 'codepos' is the position within the code where
//     * the assertion is triggered; log.currentSource() is used as the sourcefile
//     * in which 'codepos' lies. 'associatedSource' and 'associatedPos' are the
//     * location of the specification clause from which this assertion derives,
//     * if any.
//     */
//    public JmlStatementExpr addAssert(DiagnosticPosition codepos, Label label, JCExpression expr, ListBuffer<JCStatement> stats, DiagnosticPosition associatedPos, JavaFileObject associatedSource) {
//        String assertID = Strings.assertPrefix + (++assertCount);
//        Name assertname = names.fromString(assertID);
//        JavaFileObject dsource = log.currentSourceFile();
//        JCVariableDecl decl = treeutils.makeVarDef(syms.booleanType,assertname,methodDecl.sym,expr);
//        stats.add(decl);
//        JmlStatementExpr st = treeutils.makeAssert(codepos,label,treeutils.makeIdent(expr.pos,decl.sym),associatedPos);
//        st.source = dsource;
//        st.declPos = associatedPos;
//        st.associatedSource = associatedSource;
//        stats.add(st);
//        return st;
//    }
//    
//    /** Adds an assertion with the given label and (already translated) expression
//     * to the given statement list. 'codepos' is the position within the code where
//     * the assertion is triggered; log.currentSource() is used as the sourcefile
//     * in which 'codepos' lies. There is no associated position.
//     */
//    public JmlStatementExpr addAssert(DiagnosticPosition codepos, Label label, JCExpression expr, ListBuffer<JCStatement> stats) {
//        return addAssertX(codepos,label,expr,stats,Position.NOPOS,null);
//    }
    
// FIXME - use DiagnosticPosition in addAssert and addAssume, in order to get end position information?    
    

    
    
    /** Creates an assumption that two expressions are equal, adding the assumption to the given statement list. */
    protected JmlStatementExpr addAssumeEqual(DiagnosticPosition pos, Label label, JCExpression ex, JCExpression exx, @Nullable ListBuffer<JCStatement> stats) {
        return addAssume(pos,label,treeutils.makeBinary(pos.getPreferredPosition(),JCTree.EQ,ex,exx),stats,null,null);
    }
    
    /** Creates an assumption, adding it to the given statement list */
    protected JmlStatementExpr addAssume(DiagnosticPosition pos, Label label, JCExpression ex, @Nullable ListBuffer<JCStatement> stats) {
        return addAssume(pos,label,ex,stats,null,null,null);
    }
    
    /** Creates an assumption with an associated declaration (perhaps in a different file), adding it to the given statement list */
    protected JmlStatementExpr addAssume(DiagnosticPosition pos, Label label, JCExpression ex, @Nullable ListBuffer<JCStatement> stats, DiagnosticPosition associatedPos, JavaFileObject associatedSource) {
        JmlStatementExpr st = null;
        if (esc) {
            st = treeutils.makeAssume(pos,label,ex);
            st.source = log.currentSourceFile();
            st.declPos = associatedPos == null ? Position.NOPOS : associatedPos.getPreferredPosition();
            st.associatedSource = associatedSource;
            if (stats != null) stats.add(st);
        }
        if (rac) {
            boolean checkAssumeStatements = true;
            if (checkAssumeStatements) {
                addAssert(pos,label,ex,stats,associatedPos,associatedSource);
            }
        }
        return st;
    }
    
    /** Creates an assumption with an associated declaration (perhaps in a different file), adding it to the given statement list */
    protected JmlStatementExpr addAssume(DiagnosticPosition pos, Label label, JCExpression ex, @Nullable ListBuffer<JCStatement> stats, DiagnosticPosition associatedPosition, JavaFileObject associatedSource, JCExpression info) {
        JmlStatementExpr st = null;
        if (esc) {
            st = treeutils.makeAssume(pos,label,ex);
            st.source = log.currentSourceFile();
            st.declPos = associatedPosition == null ? Position.NOPOS : associatedPosition.getPreferredPosition();
            st.associatedSource = associatedSource;
            st.optionalExpression = info;
            if (stats != null) stats.add(st);
        }
        if (rac) {
            boolean checkAssumeStatements = true;
            if (checkAssumeStatements) {
                addAssert(pos,label,ex,stats,associatedPosition,associatedSource,info);
            }
        }
        return st;
    }
    
    /** Computes and adds checks for all the pre and postcondition clauses. */
    // FIXME - review this
    protected void addPrePostConditions(JCMethodDecl decl, ListBuffer<JCStatement> initialStats, ListBuffer<JCStatement> finalizeStats) {
        if (decl.sym == null) {
            log.warning("jml.internal.nosobad", "Unexpected null symbol for " + decl.getName());
        }
        JmlMethodSpecs denestedSpecs = decl.sym == null ? null : JmlSpecs.instance(context).getDenestedSpecs(decl.sym);
        // Add a precondition that the parameter != null on each formal parameter, if needed
        for (JCVariableDecl d: decl.params) {
            if (specs.isNonNull(d.sym, (Symbol.ClassSymbol)d.sym.owner.owner)) { // FIXME - needs to go through jmlrewriter ?
                // FIXME - should have an associated location
                addAssume(d.pos(),Label.NULL_CHECK,treeutils.makeNeqObject(d.pos,treeutils.makeIdent(d.pos, d.sym), treeutils.nulllit), 
                        initialStats);
            }
            JCVariableDecl dd = treeutils.makeVariableDecl(M.Name("PRE_"+d.name.toString()), d.type, 
                    M.Ident(d.sym), decl.pos);
            if (rac) dd.sym.owner = d.sym.owner;
            preparams.put(d.sym,dd);
            addStat(initialStats,dd);
        }
        
        ListBuffer<JCStatement> ensureStats = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> exsureStats = new ListBuffer<JCStatement>();
        DiagnosticPosition p = methodDecl.pos();
        JCExpression cond = treeutils.makeEqObject(p.getPreferredPosition(),
                treeutils.makeIdent(p.getPreferredPosition(), exceptionSym),treeutils.nulllit);
        addAssume(p,Label.BRANCHT,cond,ensureStats);
        addAssume(p,Label.BRANCHE,treeutils.makeNot(cond.pos,cond),exsureStats);
        
        boolean methodIsStatic = methodDecl.sym.isStatic();
        JmlSpecs.TypeSpecs tspecs = specs.get(classDecl.sym);
        // FIXME - iterate over parent classes and interfaces
        for (JmlTypeClause clause : tspecs.clauses) {
            JmlTypeClauseExpr t;
            switch (clause.token) {
                // FIXME - add in assume of non-null fields
                case INVARIANT:
                    if (!methodIsStatic || Utils.instance(context).hasAny(clause.modifiers,Flags.STATIC)) {
                        t = (JmlTypeClauseExpr)clause;
                        addAssume(methodDecl.pos(),Label.INVARIANT,
                                jmlrewriter.translate(t.expression),initialStats,
                                clause.pos(),clause.source);
                    }
                    break;
                case AXIOM:
                    t = (JmlTypeClauseExpr)clause;
                    addAssume(methodDecl.pos(),Label.AXIOM,
                               jmlrewriter.translate(t.expression),initialStats,
                               clause.pos(),clause.source);
                    break;
                default:
                    // Skip
                    
            }
        }
        ListBuffer<JCStatement> saved = currentStatements;
        JCExpression combinedPrecondition = null;
        for (JmlSpecificationCase scase : denestedSpecs.cases) {
            JCIdent preident = null;
            JCExpression preexpr = null;
            currentStatements = initialStats;
            for (JmlMethodClause clause : scase.clauses) {
                switch (clause.token) {
                    case REQUIRES:
                        JCExpression ex = ((JmlMethodClauseExpr)clause).expression;
                        if (preexpr == null) preexpr = ex;
                        else preexpr = treeutils.makeAnd(ex.pos, preexpr, ex);
                        break;
                    default:
                }
            }
            if (preexpr == null) {
                preexpr = treeutils.trueLit;
            } else {
                preexpr = jmlrewriter.translate(preexpr);
            }
            precount++;
            Name prename = names.fromString(Strings.prePrefix + precount);
            JCVariableDecl d = treeutils.makeVarDef(syms.booleanType, prename, decl.sym, preexpr);
            preident = treeutils.makeIdent(preexpr.pos, d.sym);
            addStat(initialStats,d);
            preconditions.put(scase, preident);
            if (combinedPrecondition == null || preexpr == treeutils.trueLit) {
                combinedPrecondition = preident;
            } else {
                combinedPrecondition = treeutils.makeOr(combinedPrecondition.pos, combinedPrecondition, preident);
            }
            
            for (JmlMethodClause clause : scase.clauses) {
                switch (clause.token) {
                    case ENSURES:
                    {
                        currentStatements = ensureStats;
                        JCExpression ex = ((JmlMethodClauseExpr)clause).expression;
                        ex = jmlrewriter.translate(ex,preident,true);
                        ex = treeutils.makeImplies(clause.pos, preident, ex);
                        // FIXME - if the clause is synthetic, the source file may be null, and for signals clause
                        addAssert(null,Label.POSTCONDITION,ex,ensureStats,clause.pos(),clause.sourcefile);
                        break;
                    }

                    case SIGNALS: // FIXME - need to check exception type of the exception
                    {
                        currentStatements = exsureStats;
                        JCVariableDecl vd = ((JmlMethodClauseSignals)clause).vardef;
                        JCIdent exceptionId = treeutils.makeIdent(clause.pos,exceptionSym);
                        JCVariableDecl evar = treeutils.makeVarDef(vd.type, vd.name, decl.sym, exceptionId); // FIXME - needs a unique name
                        addStat(evar);
                        JCExpression ex = ((JmlMethodClauseSignals)clause).expression;
                        ex = jmlrewriter.translate(ex,preident,true);
                        ex = treeutils.makeImplies(clause.pos, preident, ex);
                        addAssert(null,Label.SIGNALS,ex,exsureStats,clause.pos(),clause.sourcefile);
                        break;
                    }

                    case SIGNALS_ONLY:
                    {
                        // FIXME - implement?
                        log.warning(clause.pos,"esc.not.implemented","Post-condition clause type " + clause.token);
                        break;
                    }
                    
                    // FIXME - more clauses to implement?

                    case REQUIRES:
                    default:
                }
            }
        }

        // FIXME - iterate over parent classes and interfaces
        for (JmlTypeClause clause : tspecs.clauses) {
            JmlTypeClauseExpr t;
            switch (clause.token) {
                // FIXME - add in assert of non-null fields - check staticness
                case INVARIANT:
                    if (!methodIsStatic || Utils.instance(context).hasAny(clause.modifiers,Flags.STATIC)) {
                        t = (JmlTypeClauseExpr)clause;
                        addAssert(methodDecl.pos(),Label.INVARIANT,
                                jmlrewriter.translate(t.expression),ensureStats,
                                clause.pos(),clause.source);
                    }
                    break;
                case CONSTRAINT:
                    // FIXME - need to check the list of method signatures
                    if (!methodIsStatic || Utils.instance(context).hasAny(clause.modifiers,Flags.STATIC)) {
                        JmlTypeClauseConstraint tt = (JmlTypeClauseConstraint)clause;
                        addAssert(methodDecl.pos(),Label.CONSTRAINT,
                                jmlrewriter.translate(tt.expression),ensureStats,
                                clause.pos(),clause.source);
                    }
                    break;
                default:
                    // Skip
                    
            }
        }

        currentStatements = saved;
        p = methodDecl.pos();
        JCStatement ifstat = M.at(p).If(cond,M.Block(0, ensureStats.toList()),M.Block(0,exsureStats.toList()));
        finalizeStats.add(ifstat);
        // If combinedPrecondition is null then there were no specs, so the implicit precondition is true and does not
        // need to be checked
        if (combinedPrecondition != null) {
            // FIXME - associated location? where?
            addAssume(combinedPrecondition.pos(),Label.PRECONDITION,combinedPrecondition,initialStats);
        }
        

    }
    
//    /** Checks that an assignment is allowed by the class's assignable clauses*/
//    public void addAssignableChecks(JCExpression that) {
//        if (that.lhs instanceof JCIdent) addAssignableChecksVar((JCIdent)that.lhs,that);
//    }
    
//    /** Adds checks that a given variable is allowed to be assigned to per the class's assignable clauses. */
//    // FIXME - review
//    public void addAssignableChecksVar(JCIdent id, JCTree location) {
//        // Locally declared identifiers and method arguments are owned by the method - we don't check those
//        // Class fields are owned by the class - we do check those
//        if (!(id.sym.owner instanceof Symbol.ClassSymbol)) return;
//        if (methodDecl.sym == null) {
//            log.error(methodDecl.pos,"jml.internal.notsobad","Unexpected null symbol for method Declaration");
//        }
//        JmlMethodSpecs denestedSpecs = methodDecl.sym == null ? null : JmlSpecs.instance(context).getDenestedSpecs(methodDecl.sym);
//        for (JmlSpecificationCase scase : denestedSpecs.cases) {
//            JCIdent preident = preconditions.get(scase);
//            JCExpression cond = treeutils.falseLit;
//            int assignablePos = scase.pos;
//            JavaFileObject assignableFile = scase.source();
//            for (JmlMethodClause clause : scase.clauses) {
//                if (clause.token != JmlToken.ASSIGNABLE) continue;
//                assignablePos = clause.pos;
//                assignableFile = clause.source();
//                JmlMethodClauseStoreRef assignable = (JmlMethodClauseStoreRef)clause;
//                for (JCExpression sref: assignable.list) {
//                    if (sref instanceof JCIdent) {
//                        Symbol target = ((JCIdent)sref).sym;
//                        if (target == id.sym) {
//                            cond = treeutils.trueLit;
//                        }
//                    } else if (sref instanceof JCFieldAccess) {
//                        JCFieldAccess fa = (JCFieldAccess)sref;
//                        JCExpression selected = fa.selected;
//                        boolean classRef = (selected instanceof JCIdent && ((JCIdent)selected).sym instanceof Symbol.ClassSymbol) ||
//                                (selected instanceof JCFieldAccess && ((JCFieldAccess)selected).sym instanceof Symbol.ClassSymbol);
//                        if (fa.name == null || fa.sym == id.sym) {
//                            if (classRef && id.sym.isStatic() && id.sym.owner == selected.type.tsym) {
//                                // FIXME -should we allow id.sym.owner to be a superclass of fa.selected.sym ?
//                                cond = treeutils.trueLit;
//                            } else if (!classRef && !id.sym.isStatic()) {
//                                // Require that tree.selected == this
//                                cond = treeutils.trueLit; // FIXME
//                            }
//                        }
//                    } else if (sref instanceof JCArrayAccess) {
//                        // does not match
//                    } else {
//                        log.warning(sref.pos, "esc.not.implemented","Can't handle assignable clauses with " + sref);
//                    }
//                }
//            }
//            cond = treeutils.makeImplies(id.pos,preident,cond);
//            addAssert(location.pos,Label.ASSIGNABLE,cond,currentStatements,assignablePos,assignableFile);
//
//        }
//    }


    // VISITOR METHODS
    
    // All these methods may push new statements onto 'currentStatements'

    /** Returns a translation of an expression, possibly pushing additional
     * statements onto 'currentStatements'
     */
    protected JCExpression scanret(JCTree tree) {
        if (tree==null) eresult = null;
        else super.scan(tree);
        return eresult;
    }
    
    /** Returns a translation of a list of tree, possibly pushing additional
     * statements onto 'currentStatements'
     */
    protected List<JCTree> scanret(List<JCTree> trees) {
        if (trees==null) return null;
        ListBuffer<JCTree> newlist = new ListBuffer<JCTree>();
        for (JCTree t: trees) {
            scan(t);
            newlist.add(result);
        }
        return newlist.toList();
    }
    
    /** Returns a translation of a list of expression, possibly pushing additional
     * statements onto 'currentStatements'
     */
    protected List<JCExpression> scanexprlist(List<JCExpression> trees) {
        if (trees==null) return null;
        ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
        for (JCTree t: trees) {
            scan(t);
            newlist.add(eresult);
        }
        return newlist.toList();
    }
    
    /** Translates the block, returning a block */
    protected JCBlock translateIntoBlock(JCBlock block) {
        if (block == null) return null;
        pushBlock();
        scan(block.stats);
        return popBlock(block.flags,block.pos);
    }

    /** Translates a list of statements, returning a block containing the translations */
    protected JCBlock translateIntoBlock(int pos, List<JCStatement> stats) {
        pushBlock();
        scan(stats);
        return popBlock(0,pos);
    }

    /** Translates one statement, returning a block containing the translation
     * (including any statements it spawns) */
    protected JCBlock translateIntoBlock(int pos, JCStatement stat) {
        pushBlock();
        scan(stat);
        return popBlock(0,pos);
    }

    /** Translates one statement, returning a block containing the translation
     * (including any statements it spawns) */
    protected JCBlock translateIntoBlock(int pos, JCBlock stat) {
        pushBlock();
        scan(stat.stats);
        return popBlock(0,pos);
    }

    // FIXME - should we implement?
    @Override
    public void visitTopLevel(JCCompilationUnit that) {
        error(that.pos,"Unexpected call of JmlAssertionAdder.visitTopLevel: " + that.getClass());
//        // esc does not get here, but rac does
//        if (!rac) error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitCompilationUnit: " + that.getClass());
//        List<JCTree> defs = scanret(that.defs);
//        // FIXME - replicate all the other AST nodes
//        JCCompilationUnit n = M.at(that.pos()).TopLevel(that.packageAnnotations,that.pid,defs);
//        n.docComments = that.docComments;
//        n.endPositions = that.endPositions;
//        n.flags = that.flags;
//        n.mode = that.mode;
//        n.lineMap = that.lineMap;
//        n.namedImportScope = that.namedImportScope;
//        n.packge = that.packge;
//        n.type = that.type;
//        n.sourcefile = that.sourcefile;
//        n.starImportScope = that.starImportScope;
//        n.specsCompilationUnit = that.specsCompilationUnit;
//        n.specsTopLevelModelTypes = that.specsTopLevelModelTypes;
//        result = n;
    }

    @Override
    public void visitImport(JCImport that) {
        // FIXME - rewrite the qualid; this produces a JmlImport instead of an Import
        JCTree qualid = that.qualid;
        //if (fullTranslation) qualid = treeutils.makeQualid(qualid);
        result = M.at(that.pos()).Import(qualid, that.staticImport);
    }

    @Override
    public void visitClassDef(JCClassDecl that) {
        error(that.pos, "Unexpectedly calling JmlAssertionAdder.visitClassDef: " + that.getClass());
        // Normally will be overridden by JmlClassDecl
        // TODO - can these happen in an anonymous class expression or local class definition; also top-level calls from RAC?
        if (this.classDecl != null) System.out.println("SHOULD STACK CLASS DECLS?");
//        this.classDecl = that;  // FIXME - do we need to stack these?
        List<JCTree> defs = scanret(that.defs);
        this.classDecl = null;
        // FIXME - replicate all the other AST nodes - produces a JmlClassDecl but we don't have the data to populate it
        JCClassDecl n = M.at(that.pos()).ClassDef(that.mods,that.name,that.typarams,that.extending,that.implementing,defs);
        n.sym = that.sym;
        n.type = that.type;
//        n.superSymbol = that.superSymbol;
//        n.thisSymbol = that.thisSymbol;
//        n.toplevel = that.toplevel;
//        n.docComment = that.docComment;
//        n.env = that.env;
//        n.specsDecls = that.specsDecls;
//        n.typeSpecs = that.typeSpecs;
//        n.typeSpecsCombined = that.typeSpecsCombined;
        result = n;
    }

    @Override
    public void visitMethodDef(JCMethodDecl that) {
        // TODO - can these happen in an anonymous class expression or local class definition
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitMethodDef: " + that.getClass());
    }

    @Override
    public void visitVarDef(JCVariableDecl that) {
        JCExpression init = scanret(that.init);
        if (init != null) init = addImplicitConversion(that.pos(),that.type,init);
        
        if (init != null && !init.type.isPrimitive() && specs.isNonNull(that.sym,that.sym.enclClass())) {
            // FIXME _ fix this back at the declaration of $$values$...
            //if (!that.getName().toString().startsWith("$$values$")) 
            JCExpression nn = treeutils.makeNeqObject(init.pos,  init, treeutils.nulllit);
            // FIXME - should have an associated position
            addAssert(that.pos(),Label.POSSIBLY_NULL_INITIALIZATION,nn,currentStatements);
        }
        
        // FIXME - need to make a unique symbol
        JCVariableDecl stat = M.at(that.pos()).VarDef(that.sym,init);
        addStat(stat);
    }

    //OK
    @Override
    public void visitSkip(JCSkip that) {
        addStat(M.at(that.pos()).Skip());
        // Caution - JML statements are subclasses of JCSkip
    }

    //OK
    @Override
    public void visitBlock(JCBlock that) {
        if (currentStatements == null) {
            // We are in an initializer block
            // We need a method symbol to be the owner of declarations 
            // (otherwise they will have the class as owner and be thought to
            // be fields)
            MethodSymbol msym = new MethodSymbol(
                    that.flags, 
                    classDecl.name, 
                    null, 
                    classDecl.sym);
            methodDecl = //M.MethodDef(msym, null,null);
                    new JmlMethodDecl(
                            M.Modifiers(that.flags, M.Annotations(List.<com.sun.tools.javac.code.Attribute.Compound>nil())),
                            classDecl.name,
                            null,
                            null,
                            null,
                            null,
                            null, //body,
                            null,
                            msym);

        }
        JCBlock bl = translateIntoBlock(that);
        bl.flags = that.flags;
        if (currentStatements != null) {
            addStat(bl);
        } else {
            methodDecl = null;
        }
        result = bl;
    }

    // OK - should call visitJmlDoWhileLoop instead
    @Override
    public void visitDoLoop(JCDoWhileLoop that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitDoLoop: " + that.getClass());
    }

    // OK - should call visitJmlWhileLoop instead
    @Override
    public void visitWhileLoop(JCWhileLoop that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitWhileLoop: " + that.getClass());
    }

    // OK - should call visitJmlForLoop instead
    @Override
    public void visitForLoop(JCForLoop that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitForLoop: " + that.getClass());
    }

    // OK - should call visitJmlEnhancedForLoop instead
    @Override
    public void visitForeachLoop(JCEnhancedForLoop that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitForeachLoop: " + that.getClass());
    }

    //OK
    @Override
    public void visitLabelled(JCLabeledStatement that) {
        addStat(comment(that.pos,"label:: " + that.label + ": ..."));
        // FIXME - need to check labelled statements when the associated loop gets extra statements in front of it
        // Note that the labeled statement will turn into a block
        JCBlock block = translateIntoBlock(that.pos,that.body);
        JCLabeledStatement stat = M.at(that.pos()).Labelled(that.label, block);
        addStat(stat);
    }

    //OK
    @Override
    public void visitSwitch(JCSwitch that) {
        JCExpression selector = scanret(that.selector);
        ListBuffer<JCCase> cases = new ListBuffer<JCCase>();
        for (JCCase c: that.cases) {
            JCExpression pat = scanret(c.pat);
            JCBlock b = translateIntoBlock(c.pos,c.stats); // FIXME - will hide some declarations
            JCCase cc = M.at(c.pos).Case(pat,b.stats);
            cases.add(cc);
        }
        addStat(M.at(that.pos()).Switch(selector, cases.toList()));
    }

    //OK
    @Override
    public void visitCase(JCCase that) {
        // JCCase is handled directly in visitSwitch
        error(that.pos,"JmlAssertionAdder.visitCase should not be called");
    }
    
    // OK except concurrency checks
    @Override
    public void visitSynchronized(JCSynchronized that) {
        JCExpression lock = scanret(that.lock);
        if (that.lock instanceof JCParens && ((JCParens)that.lock).expr instanceof JCIdent && ((JCIdent)((JCParens)that.lock).expr).name.toString().equals("this")) {
            // Don't need to check that 'this' is not null
            // FIXME - the above is complicated - I expect it will fail in anything but the trivial case
        } else {
            JCExpression e = treeutils.makeNeqObject(that.lock.pos, lock, treeutils.nulllit);
            addAssert(that.lock.pos(), Label.POSSIBLY_NULL, e, currentStatements);
        }
        JCBlock block = translateIntoBlock(that.body);
        addStat(M.at(that.pos()).Synchronized(lock, block));
        // FIXME - need to add concurrency checks
    }

    // OK
    // FIXME - review for both esc and rac
    @Override
    public void visitTry(JCTry that) {
        JCBlock body = translateIntoBlock(that.body);
        
        ListBuffer<JCStatement> finalizerstats = new ListBuffer<JCStatement>();

        if (that.catchers != null && !that.catchers.isEmpty()) {
            // If we have catch clauses, we create the following structure
            // if (EXCEPTION == NULL) {
            //      -- this is for non-exception returns and continued execution
            // } else if (EXCEPTION instanceof ETYPE) { -- where ETYPE is the type in the catch clause declaration
            //      ETYPE [catch declaration variable] = EXCEPTION;
            //      EXCEPTION = null ;   -- because we don't have an exceptional exit any more once the exception is caught
            //      TERMINATION = 0;     -- ditto
            //      all the statements of the catch clause
            // } else if (... -- for each catch clause in order
            // }
            // -- now do all the statements of the finally clause, if any
            // if (TERMINATION > 0) return RESULT;
            // if (TERMINATION < 0) throw EXCEPTION;
            
            // FIXME - not sure we are properly executing the finally statements when there is a return or throw from a catch clause
            
            JCIdent id = M.at(that.pos()).Ident(exceptionSym);
            JCExpression ret = treeutils.makeEqObject(that.pos, id, treeutils.nulllit);
            M.at(that.pos());
            JCIf ifstat = M.If(ret, M.Block(0, List.<JCStatement>nil()), null);
            finalizerstats.add(ifstat);

            for (JCCatch catcher: that.catchers) {
                ListBuffer<JCStatement> stats = new ListBuffer<JCStatement>();
                
                // [type of catch clause] [catch clause id ] = EXCEPTION
                id = M.at(that.pos()).Ident(exceptionSym);
                JCVariableDecl vd = treeutils.makeVarDef(catcher.param.type, catcher.param.name, catcher.param.sym.owner, id);
                stats.add(vd);
                
                // EXCEPTION = null
                id = M.at(that.pos()).Ident(exceptionSym);
                stats.add(M.Exec(M.Assign(id, treeutils.nulllit)));
                
                // TERMINATION = 0
                id = M.at(that.pos()).Ident(terminationSym);
                stats.add(M.Exec(M.Assign(id, treeutils.zero)));
                
                // FIXME - need to put in the instanceof operation

                // add statements from the catch block
                JCBlock catchblock = translateIntoBlock(catcher.body);
                stats.addAll(catchblock.stats);
                
                M.at(catcher.pos());
                JCIf ifstatc = M.If(treeutils.trueLit, M.Block(catcher.body.flags, stats.toList()), null);
                ifstat.elsepart = ifstatc;
                ifstat = ifstatc;
            }
        }
        
        if (that.finalizer != null) {
            JCBlock finalizer = translateIntoBlock(that.finalizer);
            finalizerstats.add(finalizer);
        }
        
        // if (TERMINATION > 0) return ...
        JCIdent id = treeutils.makeIdent(that.pos, terminationSym);
        JCBinary cond = treeutils.makeBinary(that.pos,JCTree.GT, id, treeutils.zero );
        JCIf ifstat = M.If(cond,  M.Return(M.Ident(resultSym)), null);
        finalizerstats.add(ifstat);
        
        // if (TERMINATION < 0) throw ...
        id = treeutils.makeIdent(that.pos, terminationSym);
        cond = treeutils.makeBinary(that.pos,JCTree.LT, id, treeutils.zero );
        ifstat = M.If(cond,  M.Throw(M.Ident(exceptionSym)), null);
        finalizerstats.add(ifstat);
        
        
        JCStatement stat = M.at(that.pos()).Try(body, List.<JCCatch>nil(), M.Block(0, finalizerstats.toList()));
        addStat(stat);
    }

    // OK
    @Override
    public void visitCatch(JCCatch that) {
        // Catch statements are handled along with Try
        error(that.pos,"JmlAssertionAdder.visitCatch should not be called");
    }

    // OK
    @Override
    public void visitConditional(JCConditional that) {
        addStat(comment(that.pos," ... conditional ..."));
        JCExpression cond = scanret(that.cond);
        Name ifname = names.fromString("conditionalResult" + (++count));
        JCVariableDecl vdecl = treeutils.makeVarDef(that.type, ifname, null, that.pos);
        addStat(vdecl);
        pushBlock();
        addAssume(that.truepart.pos(),Label.BRANCHT,cond,currentStatements); // FIXME - move these to the BasicBlocker
        scan(that.truepart);
        addAssumeEqual(that.truepart.pos(), Label.ASSIGNMENT, 
                treeutils.makeIdent(that.truepart.pos, vdecl.sym), eresult, currentStatements);
        JCBlock trueblock = popBlock(0,that.truepart.pos);
        pushBlock();
        addAssume(that.truepart.pos(),Label.BRANCHE,treeutils.makeNot(that.cond.pos, cond),currentStatements);
        scan(that.falsepart);
        addAssumeEqual(that.falsepart.pos(), Label.ASSIGNMENT, 
                treeutils.makeIdent(that.falsepart.pos, vdecl.sym), eresult, currentStatements);
        JCStatement stat = M.If(cond, trueblock, popBlock(0,that.falsepart.pos));
        currentStatements.add(stat);
        eresult = treeutils.makeIdent(that.pos, vdecl.sym);
    }

    // OK
    @Override
    public void visitIf(JCIf that) {
        addStat(comment(that.pos," ... if ..."));
        JCExpression cond = scanret(that.cond);

        pushBlock();
        addAssume(that.cond.pos(),Label.BRANCHT,cond,currentStatements); // FIXME - move to the basic blocker
        scan(that.thenpart);
        JCBlock thenpart = popBlock(0,that.thenpart.pos);
        
        pushBlock();
        JCExpression ne = treeutils.makeNot(that.cond.pos,cond);
        addAssume(that.cond.pos(),Label.BRANCHE,ne,currentStatements);
        if (that.elsepart != null) scan(that.elsepart);
        JCBlock elsepart = popBlock(0,that.elsepart != null ? that.elsepart.pos : that.cond.pos);

        addStat(M.at(that.pos()).If(cond,thenpart,elsepart));
    }

    @Override
    public void visitExec(JCExpressionStatement that) {
        addStat(comment(that));
        JCExpression arg = scanret(that.getExpression());
        
        // FIXME p- not sure this is ever needed - it isn't for assignments; is it  needed for method calls?
        // is there anything else that gets wrapped in an Exec? What about method calls that return values
        if (arg instanceof JCMethodInvocation) {
            JCStatement stat = M.at(that.pos()).Exec(arg);
            addStat(stat);
        }
    }

    // OK
    @Override
    public void visitBreak(JCBreak that) {
        addStat(M.at(that.pos()).Break(that.label));
    }

    // OK
    @Override
    public void visitContinue(JCContinue that) {
        addStat(M.at(that.pos()).Continue(that.label));
    }
    

    // OK
    @Override
    public void visitReturn(JCReturn that) {
        addStat(comment(that));
        JCExpression arg = null;
        JCExpression retValue = that.getExpression();
        if (retValue != null) {
            arg = scanret(retValue);
            JCIdent resultid = M.at(that.pos()).Ident(resultSym);
            JCStatement stat = treeutils.makeAssignStat(that.pos,resultid,arg);
            addStat(stat);
            arg = resultid;
        }
        // Record the value of the termination location
        JCIdent id = treeutils.makeIdent(that.pos,terminationSym);
        JCLiteral intlit = treeutils.makeIntLiteral(that.pos,that.pos);
        JCStatement stat = treeutils.makeAssignStat(that.pos,id,intlit);
        addStat(stat);
        // If the return statement is in a finally block, there may have been an exception
        // in the process of being thrown - so we set EXCEPTION to null.
        id = treeutils.makeIdent(that.pos,exceptionSym);
        stat = treeutils.makeAssignStat(that.pos,id,treeutils.nulllit);
        addStat(stat);
        
        stat = M.at(that.pos()).Return(arg);
        addStat(stat);
    }

    // OK
    // FIXME - review
    @Override
    public void visitThrow(JCThrow that) {
        addStat(comment(that));
        // assert expr != null;
        pushBlock();
        JCExpression e = treeutils.makeNeqObject(that.expr.pos, scanret(that.expr), treeutils.nulllit);
        addAssert(that.expr.pos(), Label.POSSIBLY_NULL, e, currentStatements);
        if (that.expr.type.tag != TypeTags.BOT) {
            // ???Exception EXCEPTION_??? = expr;
            Name local = names.fromString(Strings.exceptionVarString + "_L_" + that.pos);
            JCVariableDecl decl = treeutils.makeVarDef(that.expr.type,local,exceptionSym.owner,eresult); 
            addStat(decl);
            // EXCEPTION = EXCEPTION_???;
            JCIdent id = treeutils.makeIdent(that.pos,exceptionSym);
            JCIdent localid = treeutils.makeIdent(that.pos,decl.sym);
            JCStatement assign = M.at(that.pos()).Exec(treeutils.makeAssign(that.pos,id,localid));
            addStat(assign);
            // TERMINATION = ???
            JCIdent tid = treeutils.makeIdent(that.pos,terminationSym);
            JCStatement term = M.Exec(M.Assign(tid,treeutils.makeIntLiteral(that.pos,-that.pos)));
            addStat(term);
            // throw EXCEPTION_??? ;
            localid = treeutils.makeIdent(that.pos,decl.sym);
            JCThrow thrw = M.at(that.pos()).Throw(localid);
            addStat(thrw);
            
        }
        JCBlock block = popBlock(0,that.pos);
        addStat(block);
    }

    // OK - this is a Java assert statement
    @Override
    public void visitAssert(JCAssert that) {
        // FIXME - in esc we may want to treat this as an exceptino throwing Java statement
        
        // ESC will eventually convert this to a Jml assertion, but RAC wants
        // it left as a Java assertion statement
        addStat(comment(that));
        JCExpression cond = scanret(that.getCondition());
        JCExpression info = scanret(that.getDetail());
        
        if (esc) addAssert(that.pos(),Label.EXPLICIT_ASSERT,cond,currentStatements,null,null,info);
        if (!esc) {
            JCStatement s = M.at(that.pos()).Assert(cond, info).setType(that.type);
            addStat(s);
        }
    }
    
    // FIXME - document and check
    protected
    JCExpression assignmentAllowed(boolean isjml, JmlStoreRefKeyword storeref, JCExpression pstoreref) {
        int pos = storeref.pos;
        if (pstoreref instanceof JmlStoreRefKeyword && ((JmlStoreRefKeyword)pstoreref).token == JmlToken.BSEVERYTHING) return treeutils.trueLit;
        JmlToken token = storeref.token;
        if (token == JmlToken.BSNOTHING) return treeutils.trueLit; 
        if (pstoreref instanceof JmlStoreRefKeyword) {
            JmlToken ptoken = ((JmlStoreRefKeyword)pstoreref).token;
            if (token == JmlToken.BSEVERYTHING && ptoken == JmlToken.BSEVERYTHING) return treeutils.trueLit;
            if (token == JmlToken.BSEVERYTHING && ptoken == JmlToken.BSNOTHING) return treeutils.falseLit;

        } else if (pstoreref instanceof JCIdent) {
            if (token == JmlToken.BSEVERYTHING) return treeutils.falseLit; 

        } else if (pstoreref instanceof JCFieldAccess) {
            if (token == JmlToken.BSEVERYTHING) return treeutils.falseLit; 

        } else if (pstoreref instanceof JCArrayAccess) {
            if (token == JmlToken.BSEVERYTHING) return treeutils.falseLit; 

        } else if (pstoreref instanceof JmlStoreRefArrayRange) {
            if (token == JmlToken.BSEVERYTHING) return treeutils.falseLit; 

        }
        log.error(pos,"esc.not.implemented", "Assignability comparison: " + storeref + " vs. " + pstoreref);
        return treeutils.falseLit;
    }
    
    // FIXME - document and check
    protected
    JCExpression assignmentAllowed(boolean isjml, JCIdent id, JCExpression pstoreref) {
        int pos = id.pos;
        if (pstoreref instanceof JmlStoreRefKeyword) {
            JmlToken ptoken = ((JmlStoreRefKeyword)pstoreref).token;
            if (ptoken == JmlToken.BSEVERYTHING) return treeutils.trueLit;
            if (ptoken == JmlToken.BSNOTHING) return treeutils.falseLit;

        } else if (pstoreref instanceof JCIdent) {
            // FIXME - these may be unadorned class field names, but storeref has a receiver that is not 'this'
            JCIdent pid = (JCIdent)pstoreref;
            if (id.sym == pid.sym) return treeutils.trueLit;
            else return treeutils.falseLit;

        } else if (pstoreref instanceof JCFieldAccess) {
            // TODO: Check that this.* includes static fields of a class
            JCFieldAccess pfa = (JCFieldAccess)pstoreref;
            JCExpression sel = pfa.selected;
            Symbol s0 = sel instanceof JCIdent ? ((JCIdent)sel).sym : 
                sel instanceof JCFieldAccess ? ((JCFieldAccess)sel).sym :
                    null;
                while (true) {
                    if (sel instanceof JCArrayAccess) { sel = ((JCArrayAccess)sel).indexed; continue; }
                    if (sel instanceof JmlStoreRefArrayRange) { sel = ((JmlStoreRefArrayRange)sel).expression; continue; }
                    break;
                }
                Symbol s = sel instanceof JCIdent ? ((JCIdent)sel).sym : 
                    sel instanceof JCFieldAccess ? ((JCFieldAccess)sel).sym :
                        null;
                    if (id.sym != pfa.sym && pfa.sym != null) return treeutils.falseLit;
                    if (id.sym.isStatic()  && pfa.sym != null) return treeutils.trueLit;
                    if (id.sym.isStatic()  && pfa.sym == null && s0 == classDecl.sym) return treeutils.trueLit;
                    if (id.sym.isStatic()  && pfa.sym == null && s0 != classDecl.sym) return treeutils.falseLit;
                    if (!id.sym.isStatic() && pfa.sym == null) {
                        if (s instanceof Symbol.ClassSymbol) return treeutils.falseLit;
                    }
                    JCIdent idthis = treeutils.makeIdent(pos, classDecl.thisSymbol);
                    JCExpression result = treeutils.makeEqObject(pos, idthis, 
                            jmlrewriter.translate(pfa.selected));
                    // FIXME - handle case where storeref has a different implicit this
                    return result; 

        } else if (pstoreref instanceof JCArrayAccess) {
            return treeutils.falseLit; 

        } else if (pstoreref instanceof JmlStoreRefArrayRange) {
            return treeutils.falseLit; 
        }
        log.error(pos,"esc.not.implemented", "Assignability comparison: " + id + " vs. " + pstoreref);
        return treeutils.falseLit;
    }
    
    // FIXME - document and check
    protected
    JCExpression assignmentAllowed(boolean isjml, JCFieldAccess fa, JCExpression pstoreref) {
        int pos = fa.pos;
        if (pstoreref instanceof JmlStoreRefKeyword) {
            JmlToken ptoken = ((JmlStoreRefKeyword)pstoreref).token;
            if (ptoken == JmlToken.BSEVERYTHING) return treeutils.trueLit;
            if (ptoken == JmlToken.BSNOTHING) return treeutils.falseLit;

        } else if (pstoreref instanceof JCIdent) {
            JCIdent pid = (JCIdent)pstoreref;
            if (fa.sym != pid.sym) return treeutils.falseLit;
            if (pid.sym.isStatic()) return treeutils.trueLit;
            JCIdent idthis = treeutils.makeIdent(pos, classDecl.thisSymbol);
            JCExpression result = treeutils.makeEqObject(pos, idthis, 
                     fa.selected);
            // FIXME - handle case where storeref has a different implicit this

            return result; 

        } else if (pstoreref instanceof JCFieldAccess) {
            JCFieldAccess pfa = (JCFieldAccess)pstoreref;
            if (pfa.sym != null && fa.sym != pfa.sym) {
                // a.x vs b.y with x != y, so automatically false
                return treeutils.falseLit;
            }
            if (pfa.sym != null && fa.sym == pfa.sym && !pfa.sym.isStatic()) {
                // a.x vs. b.x  with b (and a) not static, so result is (a == b)
                JCExpression result = treeutils.makeEqObject(pos, fa.selected, jmlrewriter.translate(pfa.selected));
                return result;
            }
            if (pfa.sym != null && fa.sym == pfa.sym && pfa.sym.isStatic()) {
                // a.x vs. b.x  with b (and a) static, so result is true if a and b are the same type
                JCExpression e = fa.selected;
                Symbol fs = e instanceof JCIdent ? ((JCIdent)e).sym :
                    e instanceof JCFieldAccess ? ((JCFieldAccess)e).sym :
                        null;
                e = pfa.selected;
                Symbol pfs = e instanceof JCIdent ? ((JCIdent)e).sym :
                        e instanceof JCFieldAccess ? ((JCFieldAccess)e).sym :
                            null;
                boolean same = fs == pfs;
                JCExpression result = same ? treeutils.trueLit : treeutils.falseLit;
                return result;
            }
            if (pfa.sym == null) {
                // a.x vs b.* (x may be *, a,b may be expressions or types)
                // FIXME - it matters here whether this.* includes static fields
                JCExpression e = fa.selected;
                Symbol fs = e instanceof JCIdent ? ((JCIdent)e).sym :
                    e instanceof JCFieldAccess ? ((JCFieldAccess)e).sym :
                        null;
                e = pfa.selected;
                Symbol pfs = e instanceof JCIdent ? ((JCIdent)e).sym :
                        e instanceof JCFieldAccess ? ((JCFieldAccess)e).sym :
                            null;
                if (pfs instanceof Symbol.ClassSymbol) {
                    // ?.x vs
                    boolean same = fs == pfs;
                    JCExpression result = same ? treeutils.trueLit : treeutils.falseLit;
                    return result;
                } else if (fs instanceof Symbol.ClassSymbol) {
                    boolean same = fs == pfs;
                    JCExpression result = same ? treeutils.trueLit : treeutils.falseLit;
                    return result;
                } else {
                    JCExpression result = treeutils.makeEqObject(pos, fa.selected, jmlrewriter.translate(pfa.selected));
                    return result;
                }
            }
            
        } else if (pstoreref instanceof JCArrayAccess) {
            return treeutils.falseLit; 
            
        } else if (pstoreref instanceof JmlStoreRefArrayRange) {
            return treeutils.falseLit; 
            
        }
        log.error(pos,"esc.not.implemented", "Assignability comparison: " + fa + " vs. " + pstoreref);
        return treeutils.falseLit;
    }

    // FIXME - document and check
    protected
    JCExpression assignmentAllowed(boolean isjml, JCArrayAccess aa, JCExpression pstoreref) {
        int pos = aa.pos;
        if (pstoreref instanceof JmlStoreRefKeyword) {
            JmlToken ptoken = ((JmlStoreRefKeyword)pstoreref).token;
            if (ptoken == JmlToken.BSEVERYTHING) return treeutils.trueLit;
            if (ptoken == JmlToken.BSNOTHING) return treeutils.falseLit;

        } else if (pstoreref instanceof JCIdent) {
            return treeutils.falseLit; 

        } else if (pstoreref instanceof JCFieldAccess) {
            return treeutils.falseLit; 
            
        } else if (pstoreref instanceof JCArrayAccess) {
            JCArrayAccess paa = (JCArrayAccess)pstoreref;
            JCExpression a1 = isjml ? (aa.indexed) : (aa.indexed);
            JCExpression result = treeutils.makeEqObject(pos, a1, (paa.indexed));
            if (paa.index == null ) return result;
            if (aa.index == null) return treeutils.falseLit;
            a1 = isjml ? (aa.index) : (aa.index);
            result = treeutils.makeAnd(pos,result,
                    treeutils.makeBinary(pos,JCTree.EQ,treeutils.inteqSymbol,a1,(paa.index)));
            return result;
            
        } else if (pstoreref instanceof JmlStoreRefArrayRange) {
            JmlStoreRefArrayRange paa = (JmlStoreRefArrayRange)pstoreref;
            JCExpression a1 = isjml ? (aa.indexed) : (aa.indexed);
            JCExpression result = treeutils.makeEqObject(pos, a1, jmlrewriter.translate(paa.expression));
            if (aa.index == null) {
                if (paa.lo == null && paa.hi == null) return result;
                if (paa.hi == null) return treeutils.makeAnd(pos, result, treeutils.makeBinary(pos, JCTree.EQ, treeutils.inteqSymbol, jmlrewriter.translate(paa.lo),treeutils.zero));
                
                // FIXME - compare paa.hi to array.length, paa.lo to zero if not null
                return treeutils.falseLit;
            } else {
                JCExpression aat = isjml ? jmlrewriter.translate(aa.index) : (aa.index);
                result = treeutils.makeAnd(pos,result,
                        treeutils.makeAnd(pos,
                                treeutils.makeBinary(pos,JCTree.LE,treeutils.intleSymbol,
                                        paa.lo == null ? treeutils.zero : jmlrewriter.translate(paa.lo),aat),
                                treeutils.makeBinary(pos,JCTree.LE,treeutils.intleSymbol,
                                                aat, paa.hi == null ? null /* FIXME - need length of array */ : jmlrewriter.translate(paa.hi))
                               ));
                return result;
            }
        }
        log.error(pos,"esc.not.implemented", "Assignability comparison: " + aa + " vs. " + pstoreref);
        return treeutils.falseLit;
    }

    // FIXME - document and check
    protected
    JCExpression assignmentAllowed(boolean isjml, JmlStoreRefArrayRange aa, JCExpression pstoreref) {
        int pos = aa.pos;
        if (pstoreref instanceof JmlStoreRefKeyword) {
            JmlToken ptoken = ((JmlStoreRefKeyword)pstoreref).token;
            if (ptoken == JmlToken.BSEVERYTHING) return treeutils.trueLit;
            if (ptoken == JmlToken.BSNOTHING) return treeutils.falseLit;

        } else if (pstoreref instanceof JCIdent) {
            return treeutils.falseLit; 

        } else if (pstoreref instanceof JCFieldAccess) {
            return treeutils.falseLit; 
            
        } else if (pstoreref instanceof JCArrayAccess) {
            JCArrayAccess paa = (JCArrayAccess)pstoreref;
            JCExpression result = treeutils.makeEqObject(pos, jmlrewriter.translate(aa.expression), jmlrewriter.translate(paa.indexed));
            if (paa.index == null) return result;
            JCExpression paat = jmlrewriter.translate(paa.index);
            result = treeutils.makeAnd(pos, result, treeutils.makeBinary(pos,JCTree.EQ,treeutils.inteqSymbol, 
                    aa.lo == null ? treeutils.zero : jmlrewriter.translate(aa.lo), paat));
//            result = treeutils.makeAnd(pos, result, treeutils.makeBinary(pos,JCTree.EQ,treeutils.inteqSymbol, 
//                    aa.hi == null ? /* FIXME - array length -1 */ : jmlrewriter.translate(aa.hi), paat));
            return result;
        } else if (pstoreref instanceof JmlStoreRefArrayRange) {
            JmlStoreRefArrayRange paa = (JmlStoreRefArrayRange)pstoreref;
            JCExpression result = treeutils.makeEqObject(pos, jmlrewriter.translate(aa.expression), jmlrewriter.translate(paa.expression));
            JCExpression a1 = aa.lo == null ? treeutils.zero : jmlrewriter.translate(aa.lo);
            JCExpression a2 = paa.lo == null ? treeutils.zero : jmlrewriter.translate(paa.lo);
            result = treeutils.makeAnd(pos, result, treeutils.makeBinary(pos,JCTree.LE,treeutils.intleSymbol, 
                    a2, a1));

            // FIXME - in the null case we want array length - 1
            a1 = aa.hi == null ? treeutils.zero : jmlrewriter.translate(aa.hi);
            a2 = paa.hi == null ? treeutils.zero : jmlrewriter.translate(paa.hi);
            result = treeutils.makeAnd(pos, result, treeutils.makeBinary(pos,JCTree.LE,treeutils.intleSymbol, 
                    a1, a2));

            return result;
        }
        
        log.error(pos,"esc.not.implemented", "Assignability comparison: " + aa + " vs. " + pstoreref);
        return treeutils.falseLit;
    }

    // FIXME - choose scanret or jmlrewriter for storeref based on source of argument
    // FIXME - document and check
    protected 
    JCExpression assignmentAllowed(boolean isjml, JCExpression storeref, JCExpression pstoreref) {
        if (storeref instanceof JmlStoreRefKeyword) {
            return assignmentAllowed(isjml,(JmlStoreRefKeyword)storeref,pstoreref);

        } else if (storeref instanceof JCIdent) {
            return assignmentAllowed(isjml,(JCIdent)storeref,pstoreref);
            
        } else if (storeref instanceof JCFieldAccess) {
            return assignmentAllowed(isjml,(JCFieldAccess)storeref,pstoreref);
            
        } else if (storeref instanceof JCArrayAccess) {
            return assignmentAllowed(isjml,(JCArrayAccess)storeref,pstoreref);
            
        } else if (storeref instanceof JmlStoreRefArrayRange) {
            return assignmentAllowed(isjml,(JmlStoreRefArrayRange)storeref,pstoreref);
            
        }
        
        log.error(storeref.pos,"esc.not.implemented", "Assignability comparison: " + storeref + " vs. " + pstoreref);
        return treeutils.falseLit;
    }
    
    // FIXME - document and check
    protected void checkAssignable(JCMethodDecl mdecl, JCExpression lhs, JCAssignOp that) {
        for (JmlSpecificationCase c: specs.getDenestedSpecs(methodDecl.sym).cases) {
            JCExpression check = checkAssignable(false,lhs,c);
            if (check != treeutils.trueLit) {
                DiagnosticPosition pos = c.pos();
                for (JmlMethodClause m : c.clauses) {
                    if (m.token == JmlToken.ASSIGNABLE) { pos = m.pos(); break; }
                }
                addAssert(that.pos(),Label.ASSIGNABLE,check,currentStatements,pos,c.sourcefile);
            }
        }

    }
    // FIXME - document and check
    protected @Nullable
    JCExpression checkAssignable(boolean isjml, JCExpression storeref, JmlSpecificationCase c) {
        if ((storeref instanceof JCIdent) && ((JCIdent)storeref).sym.owner instanceof Symbol.MethodSymbol) return treeutils.trueLit; 

        JCIdent pre = preconditions.get(c);
        pre = treeutils.makeIdent(pre.pos, pre.sym);
        JCExpression asg = treeutils.falseLit;
        for (JmlMethodClause mclause : c.clauses) {
            switch (mclause.token) {
                case ASSIGNABLE:
                    // Is storeref allowed by some item in the parent method's list?
                    List<JCExpression> pstorerefs = ((JmlMethodClauseStoreRef)mclause).list;
                    for (JCExpression pstoreref: pstorerefs) {
                        JCExpression nasg = assignmentAllowed(isjml,storeref,pstoreref); 
                        asg = nasg == treeutils.trueLit ? nasg :
                            asg == treeutils.falseLit ? nasg :
                                nasg == treeutils.falseLit ? asg :
                                    asg == treeutils.trueLit ? asg :
                                        treeutils.makeOr(storeref.pos,asg,nasg);
                    }
                    break;
                default:
                    break;
            }
        }
        if (asg != treeutils.trueLit) {
            return treeutils.makeImplies(storeref.pos, pre, asg);
        } else {
            return asg;
        }
    }

    // FIXME - needs work
    @Override
    public void visitApply(JCMethodInvocation that) {
        JCExpression now;
        JCExpression obj;
        MethodSymbol msym = null;
        Type.ForAll tfa = null;
        Symbol savedSym = resultSym;
        
        //pushBlock();
        Map<VarSymbol,JCIdent> prevArgsMap = currentArgsMap;

        try {
            // Translate the method name, and determine the thisid for the
            // method call

            JCMethodInvocation trExpr = null;
            if (that.meth instanceof JCIdent) {
                now = scanret(that.meth);
                if (now instanceof JCIdent &&  ((JCIdent)now).sym instanceof MethodSymbol) {

                    msym = (MethodSymbol)((JCIdent)now).sym;
                    //                if (msym.isStatic()) obj = null;
                    //                else obj = currentThisId;
                } else if (now instanceof JCFieldAccess &&  ((JCFieldAccess)now).sym instanceof MethodSymbol) {

                        msym = (MethodSymbol)((JCFieldAccess)now).sym;
                        //                if (msym.isStatic()) obj = null;
                        //                else obj = currentThisId;

                } else { msym=null; obj = null; } // FIXME - this shouldn't really happen - there is a mis translation in creating makeTYPE expressions

                List<JCExpression> args = scanexprlist(that.args);
                trExpr = M.at(that.pos()).Apply(that.typeargs,now,args);
                trExpr.type = that.type;
                trExpr.varargsElement = that.varargsElement;

            } else if (that.meth instanceof JCFieldAccess) {
                // FIXME - need assertions
                JCFieldAccess fa = (JCFieldAccess)that.meth;
                JCExpression sel = scanret(fa.selected);
                JCFieldAccess meth = M.at(that.meth.pos).Select(sel, fa.name);
                meth.sym = fa.sym;
                meth.type = fa.type;
                msym = (MethodSymbol)fa.sym;
//                if (fa instanceof JCIdent &&  ((JCIdent)fa).sym instanceof MethodSymbol) {
//                    msym = (MethodSymbol)((JCIdent)fa).sym;
//                } else if (fa instanceof JCFieldAccess &&  ((JCFieldAccess)fa).sym instanceof MethodSymbol) {
//                    msym = (MethodSymbol)((JCFieldAccess)fa).sym;
//                } else { msym=null; obj = null; } // FIXME - this shouldn't really happen - there is a mis translation in creating makeTYPE expressions
                
                List<JCExpression> args = scanexprlist(that.args);
                trExpr = M.at(that.pos()).Apply(that.typeargs,meth,args);
                trExpr.type = that.type;
                trExpr.varargsElement = that.varargsElement;
//                JCFieldAccess fa = (JCFieldAccess)that.meth;
//                msym = (MethodSymbol)(fa.sym);
//                if (msym.isStatic()) obj = null;
//                else {
//                    obj = scanret( fa.selected );
//                    
//                    // FIXME - should do better than converting to String
//                    //if (!fa.selected.type.toString().endsWith("JMLTYPE")) checkForNull(obj,fa.pos,trueLiteral,null);
//                    log.warning("esc.not.implemented","BasicBlocker.visitApply for " + that.meth.getClass());
//                }
            } else {
                // FIXME - not implemented
                log.warning("esc.not.implemented","BasicBlocker.visitApply for " + that.meth.getClass());
                msym = null;
                obj = null;
                eresult = treeutils.trueLit;
                return;
            }
            

            // FIXME - what is the next line?
            //if (msym.type instanceof Type.ForAll) tfa = (Type.ForAll)msym.type;

            // FIXME - what does this translation mean?
            //        ListBuffer<JCExpression> newtypeargs = new ListBuffer<JCExpression>();
            //        for (JCExpression arg: that.typeargs) {
            //            JCExpression n = trExpr(arg);
            //            newtypeargs.append(n);
            //        }

            // translate the arguments
//            Map<VarSymbol,JCExpression> newArgsMap = new HashMap<VarSymbol,JCExpression>();
//            int i = 0;
//            if (msym.params() != null) {
//                for (VarSymbol vd  : msym.params) {
//                    newArgsMap.put(vd,id);
//                }
//            }
//            currentArgsMap = newArgsMap;
            

            JmlMethodSpecs mspecs = specs.getDenestedSpecs(msym);
            if (mspecs == null) {
                // This happens for a binary class with no specs for the given method.
                //log.noticeWriter.println("NO SPECS FOR METHOD CALL(A) " + sym.owner + "." + sym);
                mspecs = JmlSpecs.defaultSpecs(that.pos).cases;
            } 

            ListBuffer<JCStatement> postStats = new ListBuffer<JCStatement>();
            ListBuffer<JCStatement> assignStats = new ListBuffer<JCStatement>();
            java.util.List<JCExpression> preExpressions = new LinkedList<JCExpression>();
            if (!mspecs.cases.isEmpty()) {
                JCExpression combinedPre = treeutils.falseLit;
                JmlMethodClause mc = null;
                for (JmlSpecificationCase cs : mspecs.cases) {
                    JCExpression pre = treeutils.trueLit;
                    for (JmlMethodClause clause : cs.clauses) {
                        switch (clause.token) {
                            case REQUIRES:
                                if (mc == null) mc = clause;
                                JCExpression e = scanret(((JmlMethodClauseExpr)clause).expression);
                                pre = pre == treeutils.trueLit ? e : treeutils.makeAnd(pre.pos, pre, e);
                                break;
                            case ASSIGNABLE:
                                // Presumes all of the requires clauses for this spec case are already processed
                                List<JCExpression> storerefs = ((JmlMethodClauseStoreRef)clause).list;
                                for (JCExpression item: storerefs) {
                                    List<JmlSpecificationCase> cases = specs.getDenestedSpecs(methodDecl.sym).cases;
                                    for (JmlSpecificationCase c : cases) {

                                        JCExpression condition = checkAssignable(false,jmlrewriter.translate(item),c);
                                        if (condition != treeutils.trueLit) {
                                            condition = treeutils.makeImplies(item.pos, pre, condition);
                                            addAssert(item.pos(),Label.ASSIGNABLE,condition,assignStats,c.pos(),c.sourcefile);
                                        }
                                    }
                                }
                                break;
                            default:
                        }
                    }
                    preExpressions.add(pre);
                    combinedPre = combinedPre == treeutils.falseLit ? pre : treeutils.makeOr(combinedPre.pos, combinedPre, pre);
                    pushBlock();
                }
                if (mc != null) addAssert(that.pos(),Label.PRECONDITION,combinedPre,currentStatements,
                        mc.pos(),mc.source());
                currentStatements.addAll(assignStats);
            }


            JCIdent result;
            if (((Type.MethodType)msym.type).restype.tag != TypeTags.VOID) {
                result = newTemp(trExpr);
                resultSym = result.sym;
            } else {
                JCStatement s = M.Exec(trExpr);
                s.pos = trExpr.pos;
                currentStatements.add(s);
                result = null;
                resultSym = null;
            }
            eresult = result;

            if (!mspecs.cases.isEmpty()) {
                    // FIXME - we should set condition
                JCExpression combinedPre = treeutils.falseLit;
                for (JmlSpecificationCase cs : mspecs.cases) {
                    JCExpression pre = preExpressions.remove(0);
                    for (JmlMethodClause clause : cs.clauses) {
                        switch (clause.token) {
                            case REQUIRES: break;
                            case ENSURES:
                                JCExpression e = jmlrewriter.translate(((JmlMethodClauseExpr)clause).expression);
                                addAssert(that.pos(),Label.POSTCONDITION,e,currentStatements,clause.pos(),clause.sourcefile);
                                break;
                            case ASSIGNABLE:
                                JCStatement havoc = M.at(clause.pos).JmlHavocStatement(
                                        jmlrewriter.translate(((JmlMethodClauseStoreRef)clause).list));
                                addStat(havoc);
                                break;
                            default:
                                // FIXME - implement others
                                break;
                        }
                    }
                    JCBlock b = popBlock(0,cs.pos);
                    JCStatement s = M.at(cs.pos).If(pre,b,null);
                    addStat(postStats,s);
                }
                // This asserts the full combined precondition
                // The error position is that of the first specification case.
                // FIXME - the source must be handled properly
                // FIXME - should be addAssertOther
                //addAssertOther(mc,Label.PRECONDITION,combinedPre,currentStatements,that.pos);
// FIXME - need to put in the actual call.
                currentStatements.addAll(postStats);

            }
        
        } finally {
            //JCBlock b = popBlock(0,that.pos);
            //addStat(b);

            resultSym = savedSym;
            currentArgsMap = prevArgsMap;
        }
    }

        // FIXME - what about type arguments
//        pushTypeArgs();
//        if (tfa != null) {
//            // tfa is the declaration of a parameterized method
//            // that is the actual call, which may not have explicit parameters
//            Iterator<Type> tv = tfa.tvars.iterator();
//            Iterator<JCExpression> e = that.typeargs.iterator();
//            if (e.hasNext()) {
//                while (tv.hasNext()) {
//                    typeargs.put(tv.next().tsym,e.next().type);
//                }
//            } else {
//                log.noticeWriter.println("NOT IMPLEMENTED - parameterized method call with implicit type parameters");
//            }
//        }

//        // FIXME - concerned that the position here is not after the
//        // positions of all of the arguments
//        if (false) {
//            eresult = insertSpecMethodCall(that.pos,msym,obj,that.typeargs,newargs.toList());
//        } else {
//            eresult = insertMethodCall(that,msym,obj,that.getTypeArguments(),newargs.toList()); // typeargs ? FIXME
//        }
//
////        popTypeArgs();
//        
//        
//
//        MethodSymbol msym = null;
////        if (that.meth instanceof JCIdent) msym = (MethodSymbol)((JCIdent)that.meth).sym;
////        else if (that.meth instanceof JCFieldAccess) msym = (MethodSymbol)((JCFieldAccess)that.meth).msym;
////        else {
////            //FIXME ERROR
////        }
////        JmlMethodSpecs calleeSpecs = JmlSpecs.instance(context).getDenestedSpecs(msym).deSugared;
////        calleeSpecs.
//        JCExpression e = M.Apply(that.typeargs,method,newargs.toList());
//        e.pos = that.pos;
//        e.type = that.type;
//        if (that.type.tag != TypeTags.VOID) eresult = newTemp(e);
//        else eresult = e;
//        // TODO Auto-generated method stub
//        //throw new RuntimeException("Unexpected visit call in JmlAssertionAdder: " + that.getClass());
//    }

//    // Note - obj and the args are already translated
//    // pos is the preferred position of the method call (e.g. the left parenthesis)
//    // FIXME - review and document
//    protected JCIdent insertMethodCall(JCMethodInvocation tree, MethodSymbol methodSym, JCExpression obj, List<JCExpression> typeargs, List<JCExpression> args) {
//        int pos = tree.pos;
//        MethodSymbol baseMethodSym = methodSym;
////        VarMap prevOldMap = oldMap;
////        JCIdent prevThisId = thisId;
////        JCIdent retId = methodSym.type == null ? null : newAuxIdent(RESULT_PREFIX+pos,methodSym.getReturnType(),pos,true);
////        JCIdent exceptionId = methodSym.type == null ? null : newIdentIncarnation(this.exceptionVar,pos);
////        JCExpression prevResultVar = resultVar;
////        JCIdent prevExceptionVar = exceptionVar;
//
//        try {
//            JmlMethodSpecs mspecs = specs.getDenestedSpecs(methodSym);
//            if (mspecs == null) {
//                // This happens for a binary class with no specs for the given method.
//                //log.noticeWriter.println("NO SPECS FOR METHOD CALL(A) " + sym.owner + "." + sym);
//                mspecs = JmlSpecs.defaultSpecs(pos).cases;
//            } //else 
//            
//            {
//                boolean isStaticCalled = methodSym.isStatic();
//                boolean isConstructorCalled = methodSym.isConstructor();
//                boolean isHelperCalled = Utils.instance(context).isHelper(methodSym);
//                
//                JCExpression expr;
//                // all expressions are already translated, so we can now create
//                // a new 'this' - the specs of the called method are translated
//                // with 'this' being the receiver object
//                
//                // Assign the receiver to a new variable.  If the method called
//                // is static, obj is null.
//                if (obj != null) {
//                    currentThisId = newAuxIdent("this$"+pos,methodSym.owner.type,pos,false);
//                    addAssume(obj.pos,Label.RECEIVER,treeutils.makeEqObject(obj.pos,currentThisId,obj));
//                }
//                
//                
//                
////                // Assign each of the arguments to a new variable
////                JmlMethodDecl decl = mspecs.decl;
////                
////                // FIXME - change this loop to use JmlMethodInfo.overrides - and what about interfaceOverrides?
////                while (decl == null && methodSym.params == null) {
////                    if (isConstructorCalled || isStaticCalled) break;
////                    methodSym = getOverrided(methodSym);
////                    if (methodSym == null) break;
////                    mspecs = specs.getDenestedSpecs(methodSym);
////                    if (mspecs != null) decl = mspecs.decl;
////                }
////                
////                boolean hasArgs = methodSym != null;
////                        
////                if (hasArgs) {        
////                    int i = 0;
////                    if (decl != null) {
////                        JavaFileObject source = ((ClassSymbol)decl.sym.owner).sourcefile;
////                        if (obj == null) {
////                            // static
////                            List<JCExpression> argtypes = typeargs;
////                            List<JCTypeParameter> ptypes = decl.typarams;
////                            if (argtypes != null && ptypes != null) {
////                                Iterator<JCExpression> argiter = argtypes.iterator();
////                                Iterator<JCTypeParameter> piter = ptypes.iterator();
////                                while (argiter.hasNext() && piter.hasNext()) {
////                                    Type argtype = argiter.next().type;
////                                    Type ptype = piter.next().type;
////                                    // for each type argument T (number i)
////                                    // assume \typ)e(T) == \typeof(receiver).getArg(i);
////                                    JCIdent id = newIdentIncarnation(ptype.tsym,pos);
////                                    JCExpression e = makeTypeLiteral(argtype,pos);
////                                    e = treeutils.makeEqObject(pos,id,e);
////                                    addAssume(pos,Label.ARGUMENT,trSpecExpr(e,source));
////                                }
////                            } else if (ptypes == null) {
////                                List<Type> pptypes = decl.sym.owner.type.getTypeArguments();
////                                if (argtypes != null && pptypes != null) {
////                                    Iterator<JCExpression> argiter = argtypes.iterator();
////                                    Iterator<Type> piter = pptypes.iterator();
////                                    while (argiter.hasNext() && piter.hasNext()) {
////                                        Type argtype = argiter.next().type;
////                                        Type ptype = piter.next();
////                                        // for each type argument T (number i)
////                                        // assume \type(T) == \typeof(receiver).getArg(i);
////                                        JCIdent id = newIdentIncarnation(ptype.tsym,pos);
////                                        JCExpression e = makeTypeLiteral(argtype,pos);
////                                        e = treeutils.makeEqObject(pos,id,e);
////                                        addAssume(pos,Label.ARGUMENT,trSpecExpr(e,source));
////                                    }
////                                }
////
////                            }
////                        } else {
////                            List<Type> argtypes = obj.type.getTypeArguments();
////                            if (obj.type.getEnclosingType() != Type.noType) argtypes = allTypeArgs(obj.type);
////                            List<Type> ptypes = decl.sym.owner.type.getTypeArguments();
////                            if (decl.sym.owner.type.getEnclosingType() != Type.noType) ptypes = allTypeArgs(decl.sym.owner.type);
////                            if (argtypes != null && ptypes != null) {
////                                Iterator<Type> argiter = argtypes.iterator();
////                                Iterator<Type> piter = ptypes.iterator();
////                                while (argiter.hasNext() && piter.hasNext()) {
////                                    Type argtype = argiter.next();
////                                    Type ptype = piter.next();
////                                    // for each type argument T (number i)
////                                    // assume \type(T) == \typeof(receiver).getArg(i);
////                                    JCIdent id = newIdentIncarnation(ptype.tsym,pos);
////                                    JCExpression e = makeTypeLiteral(argtype,pos);
////                                    e = treeutils.makeEqObject(pos,id,e);
////                                    addAssume(pos,Label.ARGUMENT,jmlrewriter.translate(e));
////                                }
////                            }
////                        }
//                        for (JCVariableDecl vd  : decl.params) {
//                            expr = args.get(i++);
//                            //expr = trSpecExpr(expr,source);
//                            JCIdent id = newIdentIncarnation(vd,pos);
//                            addAssume(expr.getStartPosition(),Label.ARGUMENT, treeutils.makeEquality(expr.pos,id,expr));
//                        }
//                    } else if (methodSym.params != null) {
//                        for (VarSymbol vd  : methodSym.params) {
//                            expr = args.get(i++);
//                            JCIdent id = newIdentIncarnation(vd,pos);
//                            addAssume(expr.getStartPosition(),Label.ARGUMENT, treeutils.makeEquality(expr.pos,id,expr));
//                        }
//                    } else {
//                        // No specifications for a binary method
//
//                        // FIXME - but there might be specs for a super method and we need to have parameter mappings for them
//                    }
//                }
//                
//
//                if (isConstructorCalled) {
//                    // Presuming that isConstructor
//                    // We are calling a this or super constructor
//                    // static invariants have to hold
//                    if (!isHelperCalled && calledClassInfo != null) {
//                        for (JmlTypeClauseExpr inv : calledClassInfo.staticinvariants) {
//                            JCExpression e = inv.expression;
//                            e = trSpecExpr(e,inv.source());
//                            addAssert(Label.INVARIANT,e,inv.getStartPosition(),newstatements,pos,inv.source(),inv);
//                        }
//                    }
//                } else if (!isConstructor && !isHelper) {
//                    for (JmlTypeClauseExpr inv : calledClassInfo.staticinvariants) {
//                        JCExpression e = inv.expression;
//                        e = trSpecExpr(e,inv.source());
//                        addAssert(Label.INVARIANT,e,inv.getStartPosition(),newstatements,pos,inv.source(),inv);
//                    }
//                    if (!isStatic) {
//                        for (JmlTypeClauseExpr inv : calledClassInfo.invariants) {
//                            JCExpression e = inv.expression;
//                            e = trSpecExpr(e,inv.source());
//                            addAssert(Label.INVARIANT,e,inv.getStartPosition(),newstatements,pos,inv.source(),inv);
//                        }
//                    }
//                }
//                
//                JmlMethodInfo mi = null;
//                if (hasArgs) {
//                    JCExpression exprr = null;
//                    mi = getMethodInfo(methodSym);
//                    int dpos = mi.decl == null ? pos : mi.decl.pos;
//                    JavaFileObject source = null; boolean multipleSource = false;
//                    for (JmlMethodClauseExpr pre: mi.requiresPredicates) {
//                        JCExpression pexpr = trSpecExpr(pre.expression,pre.source());
//                        if (exprr == null) exprr = pexpr;
//                        else {
//                            exprr = treeutils.makeBinary(exprr.pos,JCTree.BITOR,exprr,pexpr);
//                            copyEndPosition(exprr,pexpr);
//                        }
//                        source = pre.source();
//                    }
//
//                    if (!isConstructorCalled && !isStaticCalled) {
//                        MethodSymbol msym = methodSym;
//                        // FIXME - do this for interfaces as well
//                        for (MethodSymbol m: mi.overrides) { 
//                            exprr = addMethodPreconditions(currentBlock,m,mi.decl,dpos,exprr); // FIXME - what position to use?
//                            if (getMethodInfo(m).requiresPredicates.size() > 0) {
//                                if (source == null) source = getMethodInfo(m).requiresPredicates.get(0).source();
//                                else multipleSource = true;
//                            }
//                        }
//                    }
//                    if (exprr == null) exprr = treeutils.makeBooleanLiteral(dpos,true);
//                    JCTree first = mi.requiresPredicates.size() > 0 ? mi.requiresPredicates.get(0) : exprr;
//
//                    addAssert(Label.PRECONDITION,exprr,exprr.getStartPosition(),newstatements,pos,
//                                    source,first);
//
//                    // Grap a copy of the map before we introduce havoced variables
//                    oldMap = currentMap.copy();
//
//                    // FIXME - I think there is a problem if the modifies list uses expressions
//                    // that are also being havoced
//                    havocAssignables(pos,mi); // expressions are evaluated in the pre-state
//                }
//                
//                // Bump up the version of the heap
//                // FIXME - does a class get pure from its container?
//                boolean isPure = utils.isPure(methodSym) || utils.isPure(methodSym.enclClass());
//                if (!isPure) newIdentIncarnation(heapVar,pos);
//
//                // Bump up the allocation, in case there are any fresh declarations
//                
//                JCIdent oldalloc = newIdentUse(allocSym,pos);
//                JCIdent alloc = newIdentIncarnation(allocSym,allocCount); alloc.pos = pos;
//
//                // assume <oldalloc> < <newalloc>
//                JCExpression ee = treeutils.makeBinary(pos,JCTree.LT,oldalloc,alloc);
//                addAssume(pos,Label.SYN,ee);
//
//                
//                // Take care of termination options
//                
//                resultVar = retId;
//                exceptionVar = exceptionId;
//                JCIdent termVar = newIdentIncarnation(terminationSym,pos);
//                JCExpression termExp = treeutils.makeBinary(pos,
//                                        JCTree.OR,
//                                        treeutils.makeBinary(pos,JCTree.EQ,termVar,zeroLiteral),treeutils.makeBinary(pos,
//                                              JCTree.AND,
//                                              treeutils.makeBinary(pos,JCTree.EQ,termVar,treeutils.makeBinary(pos,JCTree.MINUS,zeroLiteral,treeutils.makeIntLiteral(pos,pos)))
//                                                ,makeInstanceof(exceptionVar,pos,syms.exceptionType,pos)));
//                termExp = trSpecExpr(termExp,null);
//                addAssume(tree.getStartPosition(),tree,Label.TERMINATION,termExp,currentBlock.statements);
//
//                // If there is a non-primitive result, we need to say that it is allocated (if not null)
//                if (!baseMethodSym.isConstructor() && !baseMethodSym.getReturnType().isPrimitive()) {
//                    declareAllocated(resultVar,pos);
////                    JCExpression eee = new JmlBBFieldAccess(allocIdent,resultVar);
////                    eee.pos = pos;
////                    eee.type = syms.intType;
////                    eee = treeutils.makeBinary(JCTree.LT,eee,newIdentUse(allocSym,pos),pos);
////                    eee = treeutils.makeBinary(JCTree.OR,eee,treeutils.makeBinary(JCTree.EQ,resultVar,nullLiteral,pos),pos);
////                    addAssume(Label.SYN,eee,currentBlock.statements,false);
//                }
//
//                if (hasArgs) {   
//                    JCExpression prevCondition2 = condition;
//                    JCBinary nn = treeutils.makeNeqObject(pos,exceptionVar,nullLiteral);
//                    try {
//                        JCBinary normalTerm = treeutils.makeBinary(pos,JCTree.LE,zeroLiteral,termVar);
//                        condition = treeutils.makeBinary(pos,JCTree.AND,condition,normalTerm);
//                        for (JmlMethodClauseExpr post: mi.ensuresPredicates) {
//                            // (termVar >= 0) ==> <ensures condition>
//                            addAssume(pos,Label.POSTCONDITION,treeutils.makeJmlBinary(pos,JmlToken.IMPLIES,normalTerm,trSpecExpr(post.expression,post.source())),newstatements);
//                        }
//                        JCBinary excTerm = treeutils.makeBinary(pos,JCTree.GT,zeroLiteral,termVar);
//                        condition = treeutils.makeBinary(pos,JCTree.AND,prevCondition2,excTerm);
//                            // NOW: condition is  prevCondition2 && (0 > termVar)
//                        for (JmlMethodClauseExpr post: mi.exPredicates) {
//                            JCExpression ex = ((JmlBinary)post.expression).lhs;
//                            signalsVar = null;
//                            if (ex instanceof JmlBinary) {
//                                ex = ((JmlBinary)ex).lhs;
//                                ex = ((JmlMethodInvocation)ex).args.get(0);
//                                signalsVar = ex instanceof JCIdent ? (JCIdent)ex : null;
//                            }
//                            // (termVar < 0) ==> ( exceptionVar != null && <signals condition> )
//                            addAssume(pos,Label.SIGNALS,treeutils.makeJmlBinary(pos,JmlToken.IMPLIES,excTerm,trSpecExpr(treeutils.makeBinary(pos,JCTree.AND,nn,post.expression),post.source())),newstatements);
//                            signalsVar = null;
//                        }
//                        for (JmlMethodClauseExpr post: mi.sigPredicates) {
//                            // (termVar < 0) ==> <signals condition>
//                            addAssume(pos,Label.SIGNALS_ONLY,treeutils.makeJmlBinary(pos,JmlToken.IMPLIES,excTerm,trSpecExpr(treeutils.makeBinary(pos,JCTree.AND,nn,post.expression),post.source())),newstatements);
//                        }
//                    } finally {
//                        condition = prevCondition2;
//                    }
//                    if (!isConstructorCalled && !isStaticCalled) {
//                        // FIXME - do this for interfaces as well
//                        for (MethodSymbol msym: getMethodInfo(methodSym).overrides) {
//                            mi = getMethodInfo(msym);
//                            addParameterMappings(mspecs.decl,mi.decl,pos,currentBlock);
//                            for (JmlMethodClauseExpr post: mi.ensuresPredicates) {
//                                addAssume(post.getStartPosition(),Label.POSTCONDITION,treeutils.makeJmlBinary(pos,JmlToken.IMPLIES,treeutils.makeBinary(pos,JCTree.LE,zeroLiteral,termVar),trSpecExpr(treeutils.makeBinary(pos,JCTree.AND,nn,post.expression),post.source())));
//                            }
//                            for (JmlMethodClauseExpr post: mi.exPredicates) {
//                                JCExpression ex = ((JmlBinary)post.expression).lhs;
//                                ex = ex instanceof JmlBinary ? ((JmlBinary)ex).lhs : null;
//                                ex = ex instanceof JmlMethodInvocation ? ((JmlMethodInvocation)ex).args.get(0) : null;
//                                signalsVar = ex instanceof JCIdent ? (JCIdent)ex : null;
//                                addAssume(post.getStartPosition(),Label.SIGNALS,treeutils.makeJmlBinary(pos,JmlToken.IMPLIES,treeutils.makeBinary(pos,JCTree.GT,zeroLiteral,termVar),trSpecExpr(treeutils.makeBinary(pos,JCTree.AND,nn,post.expression),post.source())));
//                                signalsVar = null;
//                            }
//                            for (JmlMethodClauseExpr post: mi.sigPredicates) {
//                                // (termVar < 0) ==> <signals condition>
//                                addAssume(post.getStartPosition(),Label.SIGNALS_ONLY,treeutils.makeJmlBinary(pos,JmlToken.IMPLIES,treeutils.makeBinary(pos,JCTree.GT,zeroLiteral,termVar),trSpecExpr(treeutils.makeBinary(pos,JCTree.AND,nn,post.expression),post.source())));
//                            }
//                        }
//                    }
//                }
//                
//                if (isConstructorCalled) {
//                    // Presuming that isConstructor
//                    // Calling a super or this constructor
//                    if (!isHelperCalled && calledClassInfo != null) {
//                        for (JmlTypeClauseExpr inv : calledClassInfo.staticinvariants) {
//                            JCExpression e = inv.expression;
//                            e = trSpecExpr(e,inv.source());
//                            addAssume(e.pos,Label.INVARIANT,e,newstatements);
//                        }
//                        for (JmlTypeClauseExpr inv : calledClassInfo.invariants) {
//                            JCExpression e = inv.expression;
//                            e = trSpecExpr(e,inv.source());
//                            addAssume(e.pos,Label.INVARIANT,e,newstatements);
//                        }
//                        for (JmlTypeClauseConstraint inv : calledClassInfo.staticconstraints) {
//                            JCExpression e = inv.expression;
//                            e = trSpecExpr(e,inv.source());
//                            addAssume(e.pos,Label.CONSTRAINT,e,newstatements);
//                        }
//                    }
//                } else if (!isHelper) {
//                    for (JmlTypeClauseExpr inv : calledClassInfo.staticinvariants) {
//                        JCExpression e = inv.expression;
//                        e = trSpecExpr(e,inv.source());
//                        addAssume(e.pos,Label.INVARIANT,e,newstatements);
//                    }
//                    if (!isStatic) {
//                        for (JmlTypeClauseExpr inv : calledClassInfo.invariants) {
//                            JCExpression e = inv.expression;
//                            e = trSpecExpr(e,inv.source());
//                            addAssume(e.pos,Label.INVARIANT,e,newstatements);
//                        }
//                    }
//                    for (JmlTypeClauseConstraint inv : calledClassInfo.staticconstraints) {
//                        JCExpression e = inv.expression;
//                        e = trSpecExpr(e,inv.source());
//                        addAssume(e.pos,Label.CONSTRAINT,e,newstatements);
//                    }
//                    if (!isConstructor) {
//                        if (!isStatic) {
//                            for (JmlTypeClauseConstraint inv : calledClassInfo.constraints) {
//                                JCExpression e = inv.expression;
//                                e = trSpecExpr(e,inv.source());
//                                addAssume(e.pos,Label.CONSTRAINT,e,newstatements);
//                            }
//                        }
//                    }
//                }
//                // Take out the temporary variables for the arguments
//                if (decl != null && decl.params != null) for (JCVariableDecl vd  : decl.params) {
//                    currentMap.remove(vd.sym);
//                }
//                
//                // Now create an (unprocessed) block for everything that follows the
//                // method call 
//                String restName = blockPrefix + pos + "$afterCall$" + (unique++);
//                BasicBlock brest = newBlock(restName,pos,currentBlock);// it gets all the followers of the current block
//                List<JCStatement> temp = brest.statements; // Empty - swapping lists to avoid copying
//                brest.statements = remainingStatements; // it gets all of the remaining statements
//                remainingStatements = temp;
//                // Don't because we are going to begin it below
//                //blocksToDo.add(0,brest); // push it on the front of the to do list
//                follows(currentBlock,brest);
//                
//                // We also need an empty block for the exception to go to.  We cannot
//                // go directly to the exception block because some DSA variable
//                // renaming may need to be done.
//                BasicBlock bexc = newBlock(blockPrefix+pos+"$afterCallExc$" + (unique++),pos);
//                blocksToDo.add(0,bexc); // push it on the front of the to do list
//                follows(currentBlock,bexc);
//                addUntranslatedAssume(pos,Label.SYN,treeutils.makeBinary(pos,JCTree.LT,terminationVar,zeroLiteral),bexc.statements);
//                
//                if (tryreturnStack.isEmpty()) {
//                    follows(bexc,exceptionBlock);
//                } else {
//                    List<BasicBlock> catchList = catchListStack.get(0);
//                    for (BasicBlock b: catchList) {
//                        follows(bexc,b);
//                    }
//                }
//                
//                // Now we have to complete the currentBlock and start brest
//                // because we may be in the middle of translating an 
//                // expression and any statement after this point has to go
//                // into the next (the non-exception) block
//                
//                completed(currentBlock);
//                startBlock(brest);
//                addAssume(pos,Label.SYN,treeutils.makeBinary(pos,JCTree.EQ,termVar,zeroLiteral),brest.statements);
//            }
//        } finally {
//            oldMap = prevOldMap;
//            currentThisId = prevThisId;
//            resultVar = prevResultVar;
//            exceptionVar = prevExceptionVar;
//            result = retId;
//        }
//        return retId;
//    }
    

    @Override
    public void visitNewClass(JCNewClass that) {
        ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
        for (JCExpression arg: that.args) {
            args.add(scanret(arg));
        }
        // FIXME - need to call the constructor; need an assertion about the type of the result; about allocation time
        if (esc) {
            JCVariableDecl id = treeutils.makeVarDef(that.type,names.fromString(Strings.newObjectVarString + that.pos), null, 0);
            addStat(id);
            eresult=treeutils.makeIdent(that.pos, id.sym);
            addAssume(that.pos(),Label.NULL_CHECK,treeutils.makeBinary(that.pos,JCTree.NE, eresult, treeutils.nulllit), currentStatements);
        }
        
        if (rac) {
            // FIXME - copy the rest of the stuff
            JCNewClass expr = M.at(that.pos()).NewClass(that.encl, that.typeargs, that.clazz, args.toList(), that.def);
            expr.constructor = that.constructor;
            expr.constructorType = that.constructorType;
            expr.varargsElement = that.varargsElement;
            expr.type = that.type;
            eresult = newTemp(expr);
        }
    }

    @Override
    public void visitNewArray(JCNewArray that) {
        ListBuffer<JCExpression> dims = new ListBuffer<JCExpression>();
        for (JCExpression dim: that.dims) {
            dims.add(scanret(dim));
        }
        ListBuffer<JCExpression> elems = new ListBuffer<JCExpression>();
        if (that.elems != null) {
            for (JCExpression elem: that.elems) {
                elems.add(scanret(elem));
            }
        }
        
        // This will create a fully-qualilfied version of the type name // FIXME - test this
        JCExpression elemtype = scanret(that.elemtype);
        
        // FIXME - need assertions about size of array and about any known array elements; about allocation time
        // also about type of the array
        // FIXME - have the rac version check those assumptions?
        
        if (esc) {
            JCVariableDecl id = treeutils.makeVarDef(that.type,names.fromString(Strings.newArrayVarString + that.pos), null, 0);
            addStat(id);
            eresult=treeutils.makeIdent(that.pos, id.sym);
            addAssume(that.pos(),Label.NULL_CHECK,treeutils.makeBinary(that.pos,JCTree.NE, eresult, treeutils.nulllit), currentStatements);
        }
        
        if (rac) {
            eresult = M.at(that.pos()).NewArray(elemtype, dims.toList(), elems.toList());
            eresult.type = that.type;
        }
    }

    // OK
    @Override
    public void visitParens(JCParens that) {
        JCExpression arg = scanret(that.getExpression());
        eresult = M.at(that.pos()).Parens(arg);
        eresult.setType(that.type);
    }
    
    // FIXME - need endpos in the above, and presumably nearly everywhere else???
    
    // FIXME - check this; document this
    protected JCExpression addImplicitConversion(DiagnosticPosition pos, Type lhstype, JCExpression rhs) {
        if (types.isSameType(lhstype,rhs.type)) return rhs;
        if (lhstype.isPrimitive() && !rhs.type.isPrimitive()) {
            // int = Integer and the like
            eresult = newTemp(rhs.pos, lhstype);
            // assert TValue(rhs) == eresult
            JCIdent id = M.Ident(names.fromString("intValue"));
            JCExpression e = treeutils.makeEquality(rhs.pos,
                    M.JmlMethodInvocation(id, List.<JCExpression>of(rhs)),
                    eresult);
            addAssume(rhs.pos(),Label.EXPLICIT_ASSUME,e,currentStatements); // FIXME - these EXPLICIT_ASSUME are not explicit - check others
        } else if (!lhstype.isPrimitive() && rhs.type.isPrimitive()) {
            // Integer = int and the like
            eresult = newTemp(rhs.pos, lhstype);
            // assert TValue(eresult) == rhs
            JCIdent id = M.Ident(names.fromString("intValue"));
            JCExpression e = treeutils.makeEquality(rhs.pos,
                    M.JmlMethodInvocation(id, List.<JCExpression>of(eresult)),
                    rhs);
            addAssume(rhs.pos(),Label.EXPLICIT_ASSUME,e,currentStatements);
            e = treeutils.makeNeqObject(pos.getPreferredPosition(), eresult, treeutils.nulllit);
            addAssume(pos,Label.EXPLICIT_ASSUME,e,currentStatements);

        } else {
            
        }
        return eresult;
    }

    // FIXME - review
    @Override
    public void visitAssign(JCAssign that) {
        if (that.lhs instanceof JCIdent) {
            JCIdent id = (JCIdent)that.lhs;
            JCExpression lhs = scanret(that.lhs);
            JCExpression rhs = scanret(that.rhs);
            rhs = addImplicitConversion(that.pos(),lhs.type, rhs);

            if (specs.isNonNull(id.sym,methodDecl.sym.enclClass())) {
                JCExpression e = treeutils.makeNeqObject(that.pos, rhs, treeutils.nulllit);
                // FIXME - location of nnonnull declaration?
                addAssert(that.pos(), Label.POSSIBLY_NULL_ASSIGNMENT, e, currentStatements);
            }
            for (JmlSpecificationCase c: specs.getDenestedSpecs(methodDecl.sym).cases) {
                JCExpression check = checkAssignable(false,lhs,c);
                if (check != treeutils.trueLit) {
                    DiagnosticPosition pos = c.pos();
                    for (JmlMethodClause m : c.clauses) {
                        if (m.token == JmlToken.ASSIGNABLE) { pos = m.pos(); break; }
                    }
                    addAssert(that.pos(),Label.ASSIGNABLE,check,currentStatements,pos,c.sourcefile);
                }
            }
            
            JCExpression assign = treeutils.makeAssign(that.pos,  lhs, rhs);
            addStat(M.at(that.pos()).Exec(assign));
            eresult = lhs;
            
        } else if (that.lhs instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)(that.lhs);
            JCFieldAccess newfa;
            if (!fa.sym.isStatic()) {
                JCExpression obj = scanret(fa.selected);
                JCExpression e = treeutils.makeNeqObject(obj.pos, obj, treeutils.nulllit);
                addAssert(that.lhs.pos(), Label.POSSIBLY_NULL, e, currentStatements);
                newfa = treeutils.makeSelect(that.pos, obj, fa.sym);
            } else {
                // We must evaluate the fa.lhs if it is an expression and not a type; null does not matter
                if (!isATypeTree(fa.selected)) {
                    scan(fa.selected);
                }
                // If the field is static, substitute the type tree
                
                JCExpression obj = treeutils.makeType(fa.pos, fa.sym.owner.type);
                newfa = treeutils.makeSelect(that.pos, obj, fa.sym);
                
            }
            newfa.sym = fa.sym;
            newfa.type = fa.type;
            JCExpression rhs = scanret(that.rhs);
            if (specs.isNonNull(fa.sym,methodDecl.sym.enclClass())) {
                JCExpression e = treeutils.makeNeqObject(fa.pos, rhs, treeutils.nulllit);
                // FIXME - location of nnonnull declaration?
                addAssert(that.pos(), Label.POSSIBLY_NULL_ASSIGNMENT, e, currentStatements);
            }
            JCExpression assign = treeutils.makeAssign(that.pos, newfa, rhs);
            addStat(M.at(that.pos()).Exec(assign));
            eresult = newfa;
               
        } else if (that.lhs instanceof JCArrayAccess) {
            // that.lhs.getPreferredPosition() is the position of the [ in 
            // the array access expression
            JCArrayAccess aa = (JCArrayAccess)(that.lhs);
            JCExpression array = scanret(aa.indexed);
            JCExpression e = treeutils.makeNeqObject(array.pos, array, treeutils.nulllit);
            addAssert(that.lhs.pos(), Label.POSSIBLY_NULL, e, currentStatements);

            JCExpression index = scanret(aa.index);
            e = treeutils.makeBinary(index.pos, JCTree.GE, index, treeutils.zero);
            addAssert(that.lhs.pos(), Label.POSSIBLY_NEGATIVEINDEX, e, currentStatements);
            JCFieldAccess newfa = M.at(array.pos).Select(array, syms.lengthVar.name);
            newfa.type = syms.intType;
            newfa.sym = syms.lengthVar;
            e = treeutils.makeBinary(index.pos, JCTree.LT, index, newfa);
            addAssert(that.lhs.pos(), Label.POSSIBLY_TOOLARGEINDEX, e, currentStatements);
            
            JCExpression rhs = scanret(that.rhs);
            JCArrayAccess lhs = new JmlBBArrayAccess(null,array,index);
            lhs.pos = aa.pos;
            lhs.type = aa.type;
            JCExpression assign = treeutils.makeAssign(that.pos,lhs,rhs);
            addStat(M.at(that.pos()).Exec(assign));
            eresult = lhs;
            
        } else {
            error(that.pos,"An unknown kind of assignment seen in JmlAssertionAdder: " + that.lhs.getClass());
        }
    }
    
    // FIXME _ document; does this work correctly for this and super?
    protected boolean isATypeTree(JCExpression tree) {
        if (tree instanceof JCIdent) {
            return !(((JCIdent)tree).sym instanceof VarSymbol);
        }
        if (tree instanceof JCFieldAccess) {
            return !(((JCFieldAccess)tree).sym instanceof VarSymbol);
        }
        return false;
    }

    // OK
    @Override
    public void visitAssignop(JCAssignOp that) {
        visitAssignopHelper(that,false);
    }

    // FIXME - review
    protected void visitAssignopHelper(JCAssignOp that, boolean scanned) {
        JCExpression lhs = that.lhs;
        JCExpression rhs = that.rhs;
        int op = that.getTag();
        op -= JCTree.ASGOffset;
        if (lhs instanceof JCIdent) {
            // We start with: id = expr
            // We generate
            //    ... statements for the subexpressions of expr
            //    tempRHS = ...
            //    temp = lhs' op tempRHS
            //    lhs' = temp
            
            lhs = scanned ? lhs : scanret(lhs); // This may no longer be a JCIdent
            rhs = scanned ? rhs : scanret(rhs);
            addBinaryChecks(that, op, lhs, rhs);

            rhs = treeutils.makeBinary(that.pos,op ,lhs,rhs);

            checkAssignable(methodDecl, lhs, that);

            // Note that we need to introduce the temporary since the rhs contains
            // identifiers that may be captured by the lhs.
            JCIdent id = newTemp(rhs);
            addStat(M.at(that.pos()).Exec(treeutils.makeAssign(that.pos, lhs, id))); // type not set
            if (lhs instanceof JCIdent) eresult = treeutils.makeIdent(lhs.pos,((JCIdent)lhs).sym);
            else {
                eresult = newTemp(lhs);
            }
            
        } else if (lhs instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)lhs;
            if (fa.sym.isStatic()) {
                // FIXME - if fa.selected is actually an expression, we need to evaluate and discard it
                JCExpression tree = treeutils.makeType(fa.selected.pos, fa.sym.owner.type);
                JCFieldAccess newfa = treeutils.makeSelect(fa.selected.pos, tree, fa.sym);
                newfa.name = fa.name;
                lhs = newfa;
                rhs = scanned ? rhs : scanret(rhs);
                
            } else {
                lhs = scanned ? fa.selected : scanret(fa.selected);
                JCExpression e = treeutils.makeNeqObject(lhs.pos, lhs, treeutils.nulllit);
                addAssert(that.pos(), Label.POSSIBLY_NULL, e, currentStatements);

                rhs = scanned ? rhs : scanret(rhs);
                if (specs.isNonNull(fa.sym,methodDecl.sym.enclClass())) {
                    e = treeutils.makeNeqObject(fa.pos, rhs, treeutils.nulllit);
                    // FIXME - location of nnonnull declaration?
                    addAssert(that.pos(), Label.POSSIBLY_NULL_ASSIGNMENT, e, currentStatements);
                }

                lhs = treeutils.makeSelect(fa.pos, lhs, fa.sym);

            }
            addBinaryChecks(that,op,lhs,rhs);
            checkAssignable(methodDecl, lhs, that);

            // Note that we need to introduce the temporary since the rhs contains
            // identifiers that will be captured by the lhs.
            rhs = treeutils.makeBinary(that.pos,op ,lhs,rhs);
            JCIdent id = newTemp(rhs);
            JCAssign assign = treeutils.makeAssign(that.pos, lhs, id);
            currentStatements.add(M.at(that.pos()).Exec(assign));
            eresult = lhs;
        } else if (lhs instanceof JCArrayAccess) {
            JCArrayAccess aa = (JCArrayAccess)lhs;
            JCExpression array = scanned ? aa.indexed : scanret(aa.indexed);
            JCExpression e = treeutils.makeNeqObject(array.pos, array, treeutils.nulllit);
            // FIXME - location of nnonnull declaration?
            addAssert(that.pos(), Label.POSSIBLY_NULL, e, currentStatements);

            JCExpression index = scanned ? aa.index: scanret(aa.index);
            e = treeutils.makeBinary(index.pos, JCTree.GE, index, treeutils.zero);
            addAssert(that.pos(), Label.POSSIBLY_NEGATIVEINDEX, e, currentStatements);
            JCFieldAccess newfa = M.at(array.pos).Select(array, syms.lengthVar.name);
            newfa.type = syms.intType;
            newfa.sym = syms.lengthVar;
            e = treeutils.makeBinary(index.pos, JCTree.LT, index, newfa);
            addAssert(that.pos(), Label.POSSIBLY_TOOLARGEINDEX, e, currentStatements);

            rhs = scanned ? rhs : scanret(rhs);
            lhs = new JmlBBArrayAccess(null,array,index);
            lhs.pos = aa.pos;
            lhs.type = aa.type;

            addBinaryChecks(that,op,lhs,rhs);
            checkAssignable(methodDecl, lhs, that);
            
            // Note that we need to introduce the temporary since the rhs contains
            // identifiers that will be captured by the lhs.
            rhs = treeutils.makeBinary(that.pos,op ,lhs,rhs);
            JCIdent id = newTemp(rhs);
            
            eresult = treeutils.makeAssign(that.pos, lhs, id);
        } else {
            error(that.pos,"Unexpected kind of AST in jmlAssertionAdder.visitAssignOp: " + that.getClass());
        }
    }

    // OK
    @Override
    public void visitUnary(JCUnary that) {
        int tag = that.getTag();
        if (tag == JCTree.PREDEC) {
            JCAssignOp b = M.at(that.pos()).Assignop(JCTree.MINUS_ASG,that.getExpression(),treeutils.one);
            b.type = that.type;
            visitAssignop(b);
            return;
        } else if (tag == JCTree.PREINC) {
            JCAssignOp b = M.at(that.pos()).Assignop(JCTree.PLUS_ASG,that.getExpression(),treeutils.one);
            b.type = that.type;
            visitAssignop(b);
            return;
        } else if (tag == JCTree.POSTDEC){
            JCExpression arg = scanret(that.getExpression());
            JCIdent id = newTemp(arg);
            JCAssignOp b = M.at(that.pos()).Assignop(JCTree.MINUS_ASG,arg,treeutils.one);
            b.type = that.type;
            visitAssignopHelper(b,true);
            eresult = id;
        } else if (tag == JCTree.POSTINC){
            JCExpression arg = scanret(that.getExpression());
            JCIdent id = newTemp(arg);
            JCAssignOp b = M.at(that.pos()).Assignop(JCTree.PLUS_ASG,arg,treeutils.one);
            b.type = that.type;
            visitAssignopHelper(b,true);
            eresult = id;
        } else {
            JCExpression arg = scanret(that.getExpression());
            addUnaryChecks(that,that.getTag(),arg);
            JCExpression expr = treeutils.makeUnary(that.pos,that.getTag(),that.getOperator(),arg);
            eresult = newTemp(expr);
        }
    }
    
    /** Creates a declaration for a unique temporary name with the given type and position. */
    protected JCIdent newTemp(int pos, Type t) {
        Name n = M.Name(Strings.tmpVarString + (++count));
        JCVariableDecl d = treeutils.makeVarDef(t, n, esc ? null : methodDecl.sym , pos); // FIXME - see note below
        currentStatements.add(d);
        JCIdent id = M.at(pos).Ident(d.sym);
        return id;
    }
    
    /** Creates a declaration for a unique temporary initialized to the given expression. */
    protected JCIdent newTemp(JCExpression expr) {
        return newTemp(Strings.tmpVarString + (++count),expr);
    }
    
    /** Creates a declaration for the given name initialized to the given expression. */
    protected JCIdent newTemp(String name, JCExpression expr) {
        Name n = M.Name(name);
        // By having the owner be null, the BasicBlocker2 does not append any unique-ifying suffix - FIXME - does this affect RAC?
        JCVariableDecl d = treeutils.makeVarDef(
                expr.type.tag == TypeTags.BOT ? syms.objectType : expr.type, 
                n, 
                esc ? null : methodDecl.sym, 
                expr); // FIXME - here and above is the owner the new methodDecl or the old one, or doesn't it matter
        currentStatements.add(d);
        JCIdent id = treeutils.makeIdent(expr.pos,d.sym);
        return id;
    }
    
    /** Add any assertions to check for problems with binary operations. */
    protected void addBinaryChecks(JCExpression that, int op, JCExpression lhs, JCExpression rhs) {

        if (op == JCTree.DIV || op == JCTree.MOD) {
            JCExpression nonzero = treeutils.makeBinary(that.pos, JCTree.NE, rhs, treeutils.makeIntLiteral(that.pos, 0));
            addAssert(that.pos(),Label.POSSIBLY_DIV0,nonzero,currentStatements);
        }
        // FIXME - add checks for numeric overflow
        
    }

    /** Add any assertions to check for problems with unary operations. */
    protected void addUnaryChecks(JCExpression that, int op, JCExpression expr) {

        // FIXME - add checks for numeric overflow
        
    }

    // OK
    @Override
    public void visitBinary(JCBinary that) {
        if (that.getTag() == JCTree.OR){
            JCConditional cond = M.at(that.pos()).Conditional(that.lhs,treeutils.trueLit,that.rhs);
            cond.type = that.type;
            visitConditional(cond);
            return;
        }
        if (that.getTag() == JCTree.AND){
            JCConditional cond = M.at(that.pos()).Conditional(that.lhs,that.rhs,treeutils.falseLit);
            cond.type = that.type;
            visitConditional(cond);
            return;
        }
        JCExpression lhs = scanret(that.getLeftOperand());
        JCExpression rhs = scanret(that.getRightOperand());
        addBinaryChecks(that,that.getTag(),lhs,rhs);
        JCBinary bin = treeutils.makeBinary(that.pos,that.getTag(),that.getOperator(),lhs,rhs);
        eresult = newTemp(bin);
    }

    @Override
    public void visitTypeCast(JCTypeCast that) {
        JCExpression lhs = scanret(that.getExpression());
        JCTree clazz = scanret(that.getType()); // FIXME - change to treeutils.makeType?
        
        JCTypeCast e = M.at(that.pos()).TypeCast(clazz,lhs);
        e.setType(that.type);
        treeutils.copyEndPosition(e,that);
        // Check that expression is either null or the correct type
        JCExpression eqnull = treeutils.makeEqObject(that.pos,lhs,treeutils.makeNullLiteral(that.pos));

        // FIXME - check semantics of null in typecase and type test
        if (esc) {
            if (types.isSameType(clazz.type,lhs.type)) {
                // redundant
            } else if (clazz.type.isPrimitive()) {
                if (lhs.type.isPrimitive()) {
                    // Must be numeric to numeric - do numeric range checks
                    // FIXME - implement

                } else {
                    // must be unboxing (object to primitive)
                    // FIXME - implement

                }
            } else {
                if (lhs.type.isPrimitive()) {
                    // Must be primitive to object (boxing) 
                    // FIXME - implement
                } else {
                    // object to object
                    JCExpression typeok = M.at(that.pos()).TypeTest(lhs, clazz);
                    typeok.setType(syms.booleanType);
                    // FIXME - end position?
                    JCExpression cond = treeutils.makeOr(that.pos, eqnull, typeok);
                    addAssert(that.pos(),Label.POSSIBLY_BADCAST,cond,currentStatements);
                }
            }
        }
        if (rac) {
            // FIXME - here and elsewhere, do we check for conditions that Java will check for itself?
            if (types.isSameType(clazz.type,lhs.type)) {
                // redundant
            } else if (clazz.type.isPrimitive()) {
                if (lhs.type.isPrimitive()) {
                    // Must be numeric to numeric - do numeric range checks
                    // FIXME - implement

                } else {
                    // must be unboxing (object to primitive)
                    // FIXME - implement

                }
            } else {
                if (lhs.type.isPrimitive()) {
                    // Must be primitive to object (boxing) 
                    // FIXME - implement
                } else {
                    // object to object
                    JCExpression typeok = M.at(that.pos()).TypeTest(lhs, clazz);
                    typeok.setType(syms.booleanType);
                    // FIXME - end position?
                    JCExpression cond = treeutils.makeOr(that.pos, eqnull, typeok);
                    addAssert(that.pos(),Label.POSSIBLY_BADCAST,cond,currentStatements);
                }
                
            }
            
        }
        eresult = newTemp(e);
    }

    @Override
    public void visitTypeTest(JCInstanceOf that) {
        JCExpression lhs = scanret(that.getExpression());
        JCTree clazz = scanret(that.getType());
        // No checks needed
        if (esc) {
            // FIXME - not yet implemented as an assertion
        }
        if (rac) {
            JCInstanceOf e = M.at(that.pos()).TypeTest(lhs,clazz);
            e.setType(that.type);
            treeutils.copyEndPosition(e,that);
            eresult = newTemp(e);
        }
    }

    // OK
    @Override
    public void visitIndexed(JCArrayAccess that) {
        JCExpression indexed = scanret(that.indexed);
        JCExpression nonnull = treeutils.makeBinary(that.indexed.pos, JCTree.NE, indexed, 
                treeutils.nulllit);
        addAssert(that.pos(),Label.POSSIBLY_NULL,nonnull,currentStatements);

        JCExpression index = scanret(that.index);
        JCExpression compare = treeutils.makeBinary(that.index.pos, JCTree.LE, treeutils.zero, 
                index);
        addAssert(that.pos(),Label.POSSIBLY_NEGATIVEINDEX,compare,currentStatements);
        
        JCExpression length = treeutils.makeLength(that.indexed.pos,indexed);
        compare = treeutils.makeBinary(that.pos, JCTree.LT, index, 
                length);
        addAssert(that.pos(),Label.POSSIBLY_TOOLARGEINDEX,compare,currentStatements);

        JCArrayAccess aa = new JmlBBArrayAccess(null,indexed,index);
        aa.pos = that.pos;
        aa.setType(that.type);
        eresult = newTemp(aa);
    }

    // OK
    @Override
    public void visitSelect(JCFieldAccess that) {
        if (that.sym.isStatic()) {
            // This is the type name, so the tree should be copied, but without inserting temporary assignments
            // FIXME - check whether this is fully-qualifying the result
            JCExpression typetree = treeutils.makeType(that.selected.pos,that.selected.type);
            JCFieldAccess fa = treeutils.makeSelect(that.pos,typetree,that.sym);
            fa.name = that.name;
            eresult = newTemp(fa);
            
        } else {
            JCExpression selected = scanret(that.selected);

            JCExpression nonnull = treeutils.makeNeqObject(that.pos, selected, 
                    treeutils.nulllit);
            addAssert(that.pos(),Label.POSSIBLY_NULL,nonnull,currentStatements);
            
            JCFieldAccess fa = treeutils.makeSelect(that.pos,selected,that.sym);
            eresult = newTemp(fa);
        }
    }
    
    // OK
    // FIXME - need to test this, document this
    @Override
    public void visitIdent(JCIdent that) {
        JCIdent id = currentArgsMap.get(that.sym);
        if (id != null) {
            // If the symbol is in the currentArgsMap it is an argument and
            // may have been renamed
            id = treeutils.makeIdent(that.pos, id.sym);
            eresult = id;
           // The symbol is not an argument
        } else if (!(that.sym.owner instanceof Symbol.ClassSymbol)) {
            // local variable  - just leave it as 
            // an ident
            id = treeutils.makeIdent(that.pos, that.sym);
            eresult = id;

            // FIXME - can compare against symbols, or names?
        } else if (that.sym.name.toString().equals("this")) {
            // 'this' - leave it as it is
            id = treeutils.makeIdent(that.pos, that.sym);
            eresult = id;
        } else if (that.sym.name.toString().equals("super")) {
            // 'super' - leave it as it is
            id = treeutils.makeIdent(that.pos, that.sym);
            eresult = id;

        } else if (!that.sym.isStatic()) {
            // It is a non-static class field, so we prepend 'this'
            // FIXME - do we need to use the current this?
            id = treeutils.makeIdent(that.pos,classDecl.thisSymbol);
            JCFieldAccess fa = treeutils.makeSelect(that.pos,id,that.sym);
            eresult = fa;
        } else {
            // static class field - add the qualified name
            JCExpression typetree = treeutils.makeType(that.pos,that.sym.owner.type);
            JCFieldAccess fa = treeutils.makeSelect(that.pos,typetree,that.sym);
            eresult = fa;
        }
    }

    // OK
    @Override
    public void visitLiteral(JCLiteral that) {
        eresult = treeutils.makeDuplicateLiteral(that.pos, that);
    }

    @Override
    public void visitTypeIdent(JCPrimitiveTypeTree that) {
        eresult = that;
        if (fullTranslation) {} // FIXME - fully translate
        //error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitTypeIdent: " + that.getClass());
    }

    @Override
    public void visitTypeArray(JCArrayTypeTree that) {
        error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitTypeArray: " + that.getClass());
    }

    @Override
    public void visitTypeApply(JCTypeApply that) {
        error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitTypeApply: " + that.getClass());
    }

    @Override
    public void visitTypeParameter(JCTypeParameter that) {
        error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitTypeParameter: " + that.getClass());
    }

    @Override
    public void visitWildcard(JCWildcard that) {
        error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitWildcard: " + that.getClass());
    }

    @Override
    public void visitTypeBoundKind(TypeBoundKind that) {
        error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitTypeBoundKind: " + that.getClass());
    }

    @Override
    public void visitAnnotation(JCAnnotation that) {
        // A JCAnnotation is a kind of JCExpression
        if (fullTranslation) {
            // FIXME - is there a currentStatements to put the result of scanning into?
            JCTree aType = that.annotationType; // scan(that.annotationType);
            List<JCExpression> args = that.args; //scanexprlist(that.args);
            JCAnnotation a = M.at(that.pos()).Annotation(aType,args);
            a.type = that.type;
            treeutils.copyEndPosition(a,that);
            eresult = a;
        } else {
            eresult = that;
        }
    }

    @Override
    public void visitModifiers(JCModifiers that) {
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitModifiers: " + that.getClass());
    }

    // OK
    @Override
    public void visitErroneous(JCErroneous that) {
        // Note - errs is shared with the old node
        // FIXME implement fullTranslation
        JCErroneous e = M.at(that.pos()).Erroneous(that.errs);
        e.setType(that.type);
        eresult = e;
    }

    @Override
    public void visitLetExpr(LetExpr that) {
        // TODO Auto-generated method stub
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitLetExpr: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlBinary(JmlBinary that) {
        // Should be using jmlrewriter
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlBinary: " + that.getClass());
    }

    @Override
    public void visitJmlChoose(JmlChoose that) {
        // TODO Auto-generated method stub
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlChoose: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        JmlClassDecl prev = this.classDecl;
        try {
            this.classDecl = that;

            this.classDefs = new ListBuffer<JCTree>();
            for (JCTree t: that.defs) {
                scan(t);
                if (result != null) this.classDefs.add(result);
            }

            List<JCTree> defs = this.classDefs.toList();
            // FIXME - replicate all the other AST nodes
            JmlClassDecl n = M.at(that.pos()).ClassDef(that.mods,that.name,that.typarams,that.extending,that.implementing,defs);
            n.sym = that.sym;
            n.type = that.type;
            n.superSymbol = that.superSymbol;
            n.thisSymbol = that.thisSymbol;
            n.toplevel = that.toplevel;
            n.docComment = that.docComment;
            n.env = that.env;
            n.specsDecls = that.specsDecls;
            n.typeSpecs = that.typeSpecs;
            n.typeSpecsCombined = that.typeSpecsCombined;
            result = n;
        } finally {
            this.classDecl = prev;
            this.classDefs = null;
        }
    }

    // OK
    @Override
    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        // esc does not get here, but rac does
        if (esc) error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitCompilationUnit: " + that.getClass());
        List<JCTree> defs = scanret(that.defs);
        // FIXME - replicate all the other AST nodes
        JmlCompilationUnit n = M.at(that.pos()).TopLevel(that.packageAnnotations,that.pid,defs);
        n.docComments = that.docComments;
        n.endPositions = that.endPositions;
        n.flags = that.flags;
        n.mode = that.mode;
        n.lineMap = that.lineMap;
        n.namedImportScope = that.namedImportScope;
        n.packge = that.packge;
        n.type = that.type;
        n.parsedTopLevelModelTypes = that.parsedTopLevelModelTypes;
        n.sourcefile = that.sourcefile;
        n.starImportScope = that.starImportScope;
        n.specsCompilationUnit = that.specsCompilationUnit;
        n.specsTopLevelModelTypes = that.specsTopLevelModelTypes;
        result = n;
    }

    @Override
    public void visitJmlConstraintMethodSig(JmlConstraintMethodSig that) {
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
      
        pushBlock();
        
        // Havoc any variables changed in the loop
        if (esc) {
            ListBuffer<JCExpression> targets = TargetFinder.findVars(that.getStatement(),null);
            TargetFinder.findVars(that.getCondition(),targets);
            // synthesize a modifies list
            JmlStatementHavoc st = M.at(that.body.pos).JmlHavocStatement(targets.toList());
            st.type = Type.noType;
            addStat(st);
        }

        scan(that.body);

        if (esc) {
            pushBlock();

            JCExpression test = scanret(that.cond);
            JCExpression ne = treeutils.makeNot(that.cond.pos, test);

            JmlStatementExpr as = addAssume(that.cond.pos(),Label.BRANCHT,ne,null);
            JCStatement br = M.at(that.cond.pos).Break(null);
            JCBlock bl = M.at(that.cond.pos).Block(0,List.<JCStatement>of(as,br));
            JCStatement ifs = M.at(that.cond.pos).If(ne,bl,null);
            ifs.type = Type.noType;
            addStat(ifs);

            addAssume(that.cond.pos(),Label.BRANCHE,test,currentStatements);

            bl = popBlock(0,that.cond.pos);
            addStat(bl);
        }
        
        JCBlock bl = popBlock(0,that.pos);

        if (esc) {
            JmlDoWhileLoop st = M.at(that.pos()).DoLoop(bl,treeutils.trueLit);
            st.type = Type.noType;
            st.loopSpecs = null;
            addStat(st);
        }
        
        if (rac) {
            // FIXME - need to translate the condition
            JmlDoWhileLoop st = M.at(that.pos()).DoLoop(bl,that.cond);
            st.type = Type.noType;
            st.loopSpecs = null;
            addStat(st);
        }
    }

    // FIXME - need to do for rac
    @Override
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        // FIXME Need to add specifications; also index and values variables
        JCVariableDecl v = M.at(that.var.pos).VarDef(that.var.sym,null);
        v.setType(that.var.type);
        JCExpression e = scanret(that.expr);
        pushBlock();
        // Now havoc any variables changed in the loop
        {
            ListBuffer<JCExpression> targets = TargetFinder.findVars(that.getStatement(),null);
            TargetFinder.findVars(that.getExpression(),targets);
            // synthesize a modifies list
            JmlStatementHavoc st = M.at(that.body.pos).JmlHavocStatement(targets.toList());
            addStat(st);
        }
        scan(that.body);
        JCBlock b = popBlock(0,that.body.pos);
        addStat(M.at(that.pos()).ForeachLoop(v, e, b));
    }

    @Override
    public void visitJmlForLoop(JmlForLoop that) {
        scan(that.init);
        if (esc) {
            // FIXME - need to scan the init, cond, step ; need to add specs
            Name loopCount = names.fromString("loopCount_" + that.pos);
            JCVariableDecl vd = treeutils.makeVariableDecl(loopCount,syms.intType,treeutils.zero,that.pos);
            addStat(vd);
            JCStatement increment = M.at(that.pos()).Exec(
                    treeutils.makeAssign(that.pos, treeutils.makeIdent(that.pos,vd.sym), 
                            treeutils.makeBinary(that.pos,JCTree.PLUS,treeutils.intplusSymbol,treeutils.makeIdent(that.pos, vd.sym),treeutils.makeLit(that.pos,syms.intType,1))));
            JCBlock condBlock = null;
            if (that.cond != null) {
                pushBlock();
                JCExpression e = scanret(that.cond);
                JCExpression notcond = treeutils.makeNot(e.pos,e);
                pushBlock();
                addAssume(e.pos(),Label.BRANCHT,notcond,currentStatements);
                addStat(M.Break(null));
                JCBlock thenBlock = popBlock(0,e.pos);
                pushBlock();
                addAssume(e.pos(),Label.BRANCHE,e,currentStatements);
                JCBlock elseBlock = popBlock(0,e.pos);
                JCStatement ifstat = M.at(that.cond.pos).If(notcond,thenBlock,elseBlock);
                addStat(ifstat);
                condBlock = popBlock(0,that.cond.pos);
            }
            pushBlock();

            // Now havoc any variables changed in the loop
            {
                ListBuffer<JCExpression> targets = TargetFinder.findVars(that.getStatement(),null);
                TargetFinder.findVars(that.getCondition(),targets);
                // synthesize a modifies list
                JmlStatementHavoc st = M.at(that.body.pos).JmlHavocStatement(targets.toList());
                addStat(st);
            }


            // FIXME - need to add the increment onto the update statements
            // FIXME - need to transform the update statements, but ForLoop wants a list of JCExpressionStatement not JCStatement
            if (condBlock != null) addStat(condBlock);
            scan(that.body);
            JCBlock b = popBlock(0,that.body.pos);
            addStat(M.at(that.pos()).ForLoop(List.<JCStatement>nil(), treeutils.trueLit, that.step, b));
        }
        
        if (rac) {
            pushBlock();
            scan(that.body);
            JCBlock b = popBlock(0,that.body.pos);
            // FIXME - need to scan the cond and step
            addStat(M.at(that.pos()).ForLoop(List.<JCStatement>nil(), that.cond, that.step, b));
        }
    }

    @Override
    public void visitJmlGroupName(JmlGroupName that) {
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    // OK - should never encounter this when processing method bodies
    @Override
    public void visitJmlImport(JmlImport that) {
        // FIXME - need to rewrite qualid
        result = M.at(that.pos()).Import(that.qualid, that.staticImport);
    }

    // OK
    @Override
    public void visitJmlLblExpression(JmlLblExpression that) {
        // should be using jmlrewriter
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlLblExpression: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that) {
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        // FIXME - implemente constructors - need super calls.
        if (that.restype == null) { result = that; return; } // FIXME - implement constructors
        JCBlock body = convertMethodBody(that,classDecl);
        // FIXME - replicate other ASTs
        JmlMethodDecl m = M.at(that.pos()).MethodDef(that.mods, that.name, that.restype, that.typarams, that.params, that.thrown, body, that.defaultValue);;
        m.sym = that.sym;
        m.type = that.type;
        m._this = that._this;
        m.sourcefile = that.sourcefile;
        m.owner = that.owner; // FIXME - new class decl?
        m.docComment = that.docComment;
        m.cases = that.cases;
        m.methodSpecsCombined = that.methodSpecsCombined;
        m.specsDecl = that.specsDecl;
        result = m;
    }

    // OK
    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        // should be using jmlrewriter
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlMethodInvocation: " + that.getClass());
    }

    @Override
    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitJmlMethodSpecs: " + that.getClass());
    }

    @Override
    public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitJmlModelProgramStatement: " + that.getClass());
    }

    @Override
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitJmlPrimitiveTypeTree: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        // should be using jmlrewriter
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlQuantifiedExpr: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlSetComprehension(JmlSetComprehension that) {
        // should be using jmlrewriter
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlSetComprehension: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlSingleton(JmlSingleton that) {
        // should be using jmlrewriter
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlSingleton: " + that.getClass());
    }
    

    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        // TODO Auto-generated method stub
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlSpecificationCase: " + that.getClass());
    }

    @Override
    public void visitJmlStatement(JmlStatement that) {
        switch (that.token) {
            // FIXME - should be using jmlrewriter to handle JML constructs in set, debug statements
            case SET:
                scan(that.statement);
                //jmlrewriter.translate(that.statement.getExpression());
                break;
            case DEBUG:
                Set<String> keys = Utils.instance(context).commentKeys;
                if (keys.contains("DEBUG")) {
                    scan(that.statement);
                    //jmlrewriter.translate(that.statement.getExpression());
                }
                break;
            default:
                String msg = "Unknown token in JmlAssertionAdder.visitJmlStatement: " + that.token.internedName();
                error(that.pos, msg);
        }
    }

    // jmlrewriter? FIXME; also explain what this is
    @Override
    public void visitJmlStatementDecls(JmlStatementDecls that) {
        for (JCStatement stat: that.list) {
            stat.accept(this);
        }
    }

    // OK
    @Override
    public void visitJmlStatementExpr(JmlStatementExpr that) {
        switch (that.token) {
            case ASSERT:
                addStat(comment(that));
                JCExpression e = jmlrewriter.translate(that.expression);
                addAssert(that.pos(),Label.EXPLICIT_ASSERT,e,currentStatements,null,null,that.optionalExpression);
                break;
            case ASSUME:
                addStat(comment(that));
                JCExpression ee = jmlrewriter.translate(that.expression);
                addAssume(that.pos(),Label.EXPLICIT_ASSUME,ee,currentStatements,null,null,that.optionalExpression);
                break;
            case COMMENT:
                // Not sure that we really need to make a copy, but to be 
                // consistent with the goal that we don't share mutable structure
                // we do. The String literal is not replicated however.
                addStat(M.at(that.pos()).JmlExpressionStatement(that.token,that.label,that.expression));
                break;
            case UNREACHABLE:
                addAssert(that.pos(),Label.UNREACHABLE,treeutils.falseLit,currentStatements);
                break;
            default:
                log.error("jml.internal","Unknown token type in JmlAssertionAdder.visitJmlStatementExpr: " + that.token.internedName());
                break;
        }
    }

    // OK
    @Override
    public void visitJmlStatementHavoc(JmlStatementHavoc that) {
        JmlStatementHavoc st = M.at(that.pos()).JmlHavocStatement(jmlrewriter.translate(that.storerefs));
        st.type = Type.noType;
        addStat(st);
        result = st;
    }

    @Override
    public void visitJmlStatementLoop(JmlStatementLoop that) {
        // TODO Auto-generated method stub
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlStatementLoop: " + that.getClass());
    }

    @Override
    public void visitJmlStatementSpec(JmlStatementSpec that) {
        // TODO Auto-generated method stub
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlStatementSpec: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlStoreRefArrayRange: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlStoreRefKeyword: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlStoreRefListExpression: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlTypeClauseConditional: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlTypeClauseConstraint: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlTypeClauseDecl: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlTypeClauseExpr: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlTypeClauseIn: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlTypeClauseInitializer: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlTypeClauseMaps: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlTypeClauseMonitorsFor: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlTypeClauseRepresents: " + that.getClass());
    }

    @Override
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        if (JmlAttr.instance(context).isGhost(that.mods)) {
            JCExpression init = jmlrewriter.translate(that.init);
            // FIXME - implicit conversion?
            JmlVariableDecl stat = M.at(that.pos()).VarDef(that.sym,init);
            addStat(stat);
            result = stat;
        } else if (that.init == null) {
            JmlVariableDecl stat = M.at(that.pos()).VarDef(that.sym,that.init);
            // type, vartype, sym, name, mods, init are filled in
            stat.mods = that.mods;
            stat.sourcefile = that.sourcefile;
            stat.docComment = that.docComment;
            stat.fieldSpecs = that.fieldSpecs;
            stat.fieldSpecsCombined = that.fieldSpecsCombined;
            stat.specsDecl = that.specsDecl;
            result = stat;
        } else {
            // FIXME - are these regular Java declarations?  what about model decls?

            // FIXME - need to make a unique symbol
            JmlVariableDecl stat = M.at(that.pos()).VarDef(that.sym,null);
            // type, vartype, sym, name, mods, init are filled in
            stat.mods = that.mods;
            stat.sourcefile = that.sourcefile;
            stat.docComment = that.docComment;
            stat.fieldSpecs = that.fieldSpecs;
            stat.fieldSpecsCombined = that.fieldSpecsCombined;
            stat.specsDecl = that.specsDecl;

            pushBlock();
            
            JCExpression init = scanret(that.init);
            if (init != null) init = addImplicitConversion(init.pos(),that.type,init);

            JCExpression nn = null;
            if (init != null && !init.type.isPrimitive() && specs.isNonNull(that.sym,that.sym.enclClass())) {
                // FIXME _ fix this back at the declaration of $$values$...
                //if (!that.getName().toString().startsWith("$$values$")) 
                nn = treeutils.makeNeqObject(init.pos, init, treeutils.nulllit);
                // FIXME - should have an associated location
                addAssert(that.pos(),Label.POSSIBLY_NULL_INITIALIZATION,nn,currentStatements);
            }
            

            if (statementStack.get(0) == null) {
                addStat(treeutils.makeAssignStat(that.pos, treeutils.makeIdent(that.pos, stat.sym), init));
                // Check about static
                JCBlock bl = popBlock(that.mods.flags & Flags.STATIC,that.pos);
                this.classDefs.add(stat);
                result = bl;
            } else {
                JCBlock bl = popBlock(0,that.pos);
                currentStatements.addAll(bl.stats);
                stat.init = init;
                addStat(stat);
                result = stat;
            }
            // FIXME - are we at the top-level or not?
            // FIXME - where to add this block?
        }
    }

    @Override
    public void visitJmlWhileLoop(JmlWhileLoop that) {
        // FIXME - need to add specs; 
        if (esc) {
            pushBlock();

            // Now havoc any variables changed in the loop
            ListBuffer<JCExpression> targets = TargetFinder.findVars(that.getStatement(),null);
            TargetFinder.findVars(that.getCondition(),targets);
            // synthesize a modifies list
            JmlStatementHavoc st = M.at(that.body.pos).JmlHavocStatement(targets.toList());
            addStat(st);

            JCExpression test = scanret(that.cond);
            JCExpression ne = treeutils.makeNot(that.cond.pos, test);

            //        // Now havoc any variables changed in the loop body
            //        {
            //            java.util.List<JCExpression> targets = TargetFinder.findVars(that.body,null);
            //            TargetFinder.findVars(test,targets);
            //            //if (update != null) TargetFinder.findVars(update,targets);
            //            // synthesize a modifies list
            //            int wpos = that.body.pos+1;
            //            //log.noticeWriter.println("HEAP WAS " + currentMap.get((VarSymbol) heapVar.sym));
            //            newIdentIncarnation(heapVar,wpos);
            //            //log.noticeWriter.println("HEAP NOW " + currentMap.get((VarSymbol) heapVar.sym) + " " + (wpos+1));
            //            for (JCExpression e: targets) {
            //                if (e instanceof JCIdent) {
            //                    JCIdent id = newIdentIncarnation((JCIdent)e,wpos);
            //                    program.declarations.add(id);
            //                //} else if (e instanceof JCFieldAccess) {
            //                //} else if (e instanceof JCArrayAccess) {
            //                    
            //                } else {
            //                    // FIXME - havoc in loops
            //                    log.noticeWriter.println("UNIMPLEMENTED HAVOC IN LOOP " + e.getClass());
            //                }
            //            }
            //        }

            DiagnosticPosition pos = that.cond.pos();
            JmlStatementExpr as = addAssume(pos,Label.BRANCHT,ne,null);
            JCStatement br = M.at(pos).Break(null);
            JCBlock bl = M.at(pos).Block(0,List.<JCStatement>of(as,br));
            JCStatement ifs = M.at(pos).If(ne,bl,null);
            ifs.type = Type.noType;
            addStat(ifs);

            addAssume(that.cond.pos(),Label.BRANCHE,test,currentStatements);

            scan(that.body);



            bl = popBlock(0,that.cond.pos);
            JmlWhileLoop stw = M.at(that.pos()).WhileLoop(treeutils.trueLit, bl);
            stw.type = that.type;
            stw.loopSpecs = null;
            addStat(stw);
        }

        if (rac) {
            // FIXME - need to translate the conditional - be careful of labels on the loop
            JCStatement bl = translateIntoBlock(that.body.pos, that.body);
            JmlWhileLoop st = M.at(that.pos()).WhileLoop(that.cond, bl);
            st.type = that.type;
            st.loopSpecs = null;
            addStat(st);
        }
// TODO- optimization - if there are no extra statements produced, we can keep the (translated) expression in the while condition        
//        else {
        // Something like this;
//            addStat(M.at(that.pos()).WhileLoop(e, b));
//        }
    }
    
    /** This class rewrites (making a full copy) JML expressions (but not Java statements or the
     * Java expressions in Java statements).
     * Since JML expressions are pure (at least have no visible side-effects), we do not dismember expressions
     * into individual subexpressions as we do for expressions in Java statements. However, we do issue 
     * JML assert statements that check whether the JML expression being translated is well-defined; also
     * identifiers are changed in the same way as they are changed for Java expressions.
     * <P>
     * This class is purposely not static, so it can use the context of the enclosing Java rewriter.
     * <P>
     * It would be possible to combine this rewriter with the visitor in JmlAssertionAdder; we would
     * then need a field that serves as a flag to distinguish the one mode from the other. I chose not
     * to do that, so that the two kinds of rewriting can be separated, at the cost of some similar code.
     */
    // TODO - this expression rewriter would be better off with a visitor that returned a value from the visit/scan/accept methods, or as a copier
    public class JmlExpressionRewriter extends JmlTreeScanner {
        
        /** Contains an expression that is used as a guard in determining whether expressions
         * are well-defined. For example, suppose we are translating the expression 
         * a != null && a[i] == 0. Then condition is 'true' when a!=null is translated.
         * But when a[i] is translated, 'condition' will be a != null. The well-definedness
         * check for a[i] will then be (a != null) ==> (a != null && i >= 0 && i < a.length).
         * So the full expression is well-defined only if that implication can be proved given 
         * other pre-conditions.
         */
        protected JCExpression condition;
        
        /** Set to true when we are translating a normal or exceptional postcondition. It is used
         * to be sure the correct scope is used when method parameters are used in the postcondition.
         * If a method parameter is used in a postcondition it is evaluated in the pre-state since
         * any changes to the parameter within the body of the method are discarded upon exit and
         * are invisible outside the method (i.e. in the postcondition).
         */
        protected boolean isPostcondition;
        
        /** Every visit method that translates an expression must put its result in this
         * variable.
         */
        protected JCExpression ejmlresult;
        
        /** The translate methods are the entry point into the rewriter; they make a rewritten
         * copy of the given expression, not changing the original. */
        protected JCExpression translate(JCExpression that, boolean isPostcondition) {
            return translate(that,treeutils.trueLit,isPostcondition);
        }
        
        /** The translate methods are the entry point into the rewriter; they make a rewritten
         * copy of the given expression, not changing the original. */
        protected JCExpression translate(JCExpression that) {
            return translate(that,treeutils.trueLit,false);
        }
        
        /** The translate methods are the entry point into the rewriter; this one
         * makes a copy of the input list, making copies of each list element, 
         * not changing the original list or its elements. */
        protected List<JCExpression> translate(List<JCExpression> list) {
            ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
            for (JCExpression item : list) {
                newlist.add(translate(item));
            }
            return newlist.toList();
        }

        /** The translate methods are the entry point into the rewriter; they make a rewritten
         * copy of the given expression, not changing the original. */
        protected JCExpression translate(JCExpression that, JCExpression condition, boolean isPostcondition) {
            if (that == null) return null;
            this.isPostcondition = isPostcondition;
            this.condition = condition;
            this.ejmlresult = null; // Just so it is initialized in case assignment is forgotten
            that.accept(this);
            return ejmlresult;
        }

        // VISITOR METHODS

        // OK
        @Override
        public void visitTopLevel(JCCompilationUnit that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        // OK
        @Override
        public void visitImport(JCImport that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }
        
        // FIXME - can any of these statements happen in anonymous class expressions or in mdoel programs?

        @Override
        public void visitClassDef(JCClassDecl that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());

        }

        @Override
        public void visitMethodDef(JCMethodDecl that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());

        }

        @Override
        public void visitVarDef(JCVariableDecl that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
//            scan(that.init);
//            JCExpression init = that.init == null ? null : eresult;
//            // FIXME - need to make a unique symbol
//            JCVariableDecl stat = M.at(that.pos()).VarDef(that.sym,init);
//            addStat(stat);
        }

        @Override
        public void visitSkip(JCSkip that) {
            //addStat(that); // using the same statement - no copying
                            // Caution - JML statements are subclasses of JCSkip
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitBlock(JCBlock that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
//            push();
//            scan(that.stats);
//            JCBlock block = popBlock(that.flags,that.pos);
//            addStat(block);
        }

        @Override
        public void visitDoLoop(JCDoWhileLoop that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitWhileLoop(JCWhileLoop that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitForLoop(JCForLoop that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitForeachLoop(JCEnhancedForLoop that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitLabelled(JCLabeledStatement that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitSwitch(JCSwitch that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitCase(JCCase that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitSynchronized(JCSynchronized that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitTry(JCTry that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitCatch(JCCatch that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        // OK
        @Override
        public void visitConditional(JCConditional that) {
            that.cond.accept(this);
            JCExpression cond = ejmlresult;
            JCExpression prev = condition;
            try {
                condition = treeutils.makeAnd(that.pos, prev, cond);
                that.truepart.accept(this);
                JCExpression truepart = ejmlresult;
                condition = treeutils.makeAnd(that.pos, prev, treeutils.makeNot(that.falsepart.pos, cond));
                that.falsepart.accept(this);
                JCExpression falsepart = ejmlresult;
                ejmlresult = M.at(that.pos()).Conditional(cond,truepart,falsepart);
                ejmlresult.type = that.type;
            } finally {
                condition = prev;
            }
        }

        @Override
        public void visitIf(JCIf that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
//            scan(that.cond);
//            JCExpression cond = ejmlresult;
//            push();
//            scan(that.thenpart);
//            JCBlock thenpart = popBlock(0,that.thenpart.pos);
//            push();
//            scan(that.elsepart);
//            JCBlock elsepart = popBlock(0,that.elsepart.pos);
//            addStat(M.at(that.pos()).If(cond,thenpart,elsepart));
        }

        @Override
        public void visitExec(JCExpressionStatement that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
//           addStat(comment(that));
//            scan(that.getExpression());
//            JCExpression arg = ejmlresult;
//            JCStatement stat = M.at(that.pos()).Exec(arg);
//            addStat(stat);
        }

        @Override
        public void visitBreak(JCBreak that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitContinue(JCContinue that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitReturn(JCReturn that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitThrow(JCThrow that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitAssert(JCAssert that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitApply(JCMethodInvocation that) {
            // FIXME - need to check definedness by testing preconditions
            JCExpression meth = translate(that.meth);
            List<JCExpression> args = translate(that.args);
            // FIXME - trnslate typeargs
            ejmlresult = M.at(that.pos()).Apply(that.typeargs, meth, args);
        }

        @Override
        public void visitNewClass(JCNewClass that) {
            // FIXME - definitely need this
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitNewArray(JCNewArray that) {
            // FIXME - definitely need this
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        // OK
        @Override
        public void visitParens(JCParens that) {
            scan(that.getExpression());
            ejmlresult = M.at(that.pos()).Parens(ejmlresult);
            ejmlresult.setType(that.type);
        }

        @Override
        public void visitAssign(JCAssign that) {
            // FIXME
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitAssignop(JCAssignOp that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitUnary(JCUnary that) {
            scan(that.getExpression());
            JCExpression arg = ejmlresult;
            JCExpression expr = treeutils.makeUnary(that.pos,that.getTag(),arg);
            ejmlresult = expr;
            // FIXME - check arithmetic error
        }

        @Override
        public void visitBinary(JCBinary that) {
            scan(that.lhs);
            JCExpression lhs = ejmlresult;
            JCExpression rhs;
            int tag = that.getTag();
            if (tag == JCTree.AND) {
                JCExpression prev = condition;
                try {
                    condition = treeutils.makeAnd(that.lhs.pos, condition, lhs);
                    scan(that.rhs);
                    rhs = ejmlresult;
                } finally {
                    condition = prev;
                }
            } else if (tag == JCTree.OR) { 
                JCExpression prev = condition;
                try {
                    condition = treeutils.makeAnd(that.lhs.pos, condition, treeutils.makeNot(that.lhs.pos,lhs));
                    scan(that.rhs);
                    rhs = ejmlresult;
                } finally {
                    condition = prev;
                }
            } else if (tag == JCTree.DIV || tag == JCTree.MOD) {
                scan(that.rhs);
                rhs = ejmlresult;
                JCExpression nonzero = treeutils.makeBinary(that.pos, JCTree.NE, rhs, treeutils.makeIntLiteral(that.rhs.pos, 0));
                addAssert(that.pos(),Label.UNDEFINED_DIV0,treeutils.makeImplies(that.pos, condition, nonzero),currentStatements);
            } else {
                scan(that.rhs);
                rhs = ejmlresult;
//                JCExpression bin = treeutils.makeBinary(that.pos,that.getTag(),lhs,rhs);
//                ejmlresult = bin;
//                return;
            }
            // FIXME - add checks for numeric overflow - PLUS MINUS MUL - what about SL SR USR
            JCExpression bin = treeutils.makeBinary(that.pos,that.getTag(),lhs,rhs);
            ejmlresult = bin;
            
        }

        @Override
        public void visitTypeCast(JCTypeCast that) {
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitTypeTest(JCInstanceOf that) {
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        // OK
        @Override
        public void visitIndexed(JCArrayAccess that) {
            scan(that.indexed);
            JCExpression indexed = ejmlresult;
            JCExpression nonnull = treeutils.makeNeqObject(that.indexed.pos, indexed, 
                    treeutils.nulllit);
            nonnull = treeutils.makeImplies(that.pos, condition, nonnull);
            addAssert(that.pos(),Label.UNDEFINED_NULL,nonnull,currentStatements);

            scan(that.index);
            JCExpression index = ejmlresult;
            JCExpression compare = treeutils.makeBinary(that.index.pos, JCTree.LE, treeutils.zero, 
                    index);
            compare = treeutils.makeImplies(that.pos, condition, compare);
            addAssert(that.pos(),Label.UNDEFINED_NEGATIVEINDEX,compare,currentStatements);
            
            JCExpression length = treeutils.makeLength(that.indexed.pos,indexed);
            compare = treeutils.makeBinary(that.pos, JCTree.LT, index, 
                    length);
            compare = treeutils.makeImplies(that.pos, condition, compare);
            addAssert(that.pos(),Label.UNDEFINED_TOOLARGEINDEX,compare,currentStatements);

            //JCArrayAccess aa = M.at(that.pos()).Indexed(indexed,index);
            JmlBBArrayAccess aa = new JmlBBArrayAccess(null,indexed,index); // FIXME - switch to factory
            aa.pos = that.pos;
            aa.setType(that.type);
            ejmlresult = aa;
        }

        @Override
        public void visitSelect(JCFieldAccess that) {
            scan(that.selected);
            JCExpression selected = ejmlresult;
            // Check that the selected expression is not null
            JCExpression nonnull = treeutils.makeNeqObject(that.pos, selected, 
                    treeutils.nulllit);
            nonnull = treeutils.makeImplies(that.pos, condition, nonnull);
            addAssert(that.pos(),Label.UNDEFINED_NULL,nonnull,currentStatements);
            
            JCFieldAccess fa = M.at(that.pos()).Select(selected,that.name);
            fa.sym = that.sym;
            fa.setType(that.type);
            
            ejmlresult = fa;
        }
        
        @Override
        public void visitIdent(JCIdent that) {
            // FIXME - do we need formal parameter lookup?
            JCVariableDecl decl;
            Symbol symToUse;
            if (isPostcondition && (decl=preparams.get(that.sym)) != null) {
                symToUse = decl.sym;
            } else {
                symToUse = that.sym;
            }
            JCIdent id;
            if (that.sym.owner instanceof Symbol.ClassSymbol 
                    && !that.sym.isStatic()
                    && !that.sym.name.toString().equals("this")) {
                // It is a non-static class field, so we prepend 'this'
                id = treeutils.makeIdent(that.pos,classDecl.thisSymbol);
                JCFieldAccess fa = M.at(that.pos()).Select(id,symToUse.name); // FIXME - or that.name?
                fa.sym = symToUse;
                fa.type = that.type;
                ejmlresult = fa;
            } else {
                // local variable or a static class field - just leave it as 
                // an ident
                id = treeutils.makeIdent(that.pos, symToUse);
                ejmlresult = id;
            }
        }

        @Override
        public void visitLiteral(JCLiteral that) {
            // Note that that.typetag can be different from that.type.tag - e.g for null values
            ejmlresult = treeutils.makeDuplicateLiteral(that.pos, that);
        }

        @Override
        public void visitTypeIdent(JCPrimitiveTypeTree that) {
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitTypeArray(JCArrayTypeTree that) {
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitTypeApply(JCTypeApply that) {
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitTypeParameter(JCTypeParameter that) {
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitWildcard(JCWildcard that) {
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitTypeBoundKind(TypeBoundKind that) {
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitAnnotation(JCAnnotation that) {
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitModifiers(JCModifiers that) {
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitErroneous(JCErroneous that) {
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitLetExpr(LetExpr that) {
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlBinary(JmlBinary that) {
            scan(that.lhs);
            JCExpression lhs = ejmlresult;
            JCExpression rhs,t;
            switch (that.op) {
                case IMPLIES:
                    condition = treeutils.makeAnd(that.pos, condition, lhs);
                    scan(that.rhs);
                    rhs = ejmlresult;
                    t = treeutils.makeNot(lhs.pos, lhs);
                    t = treeutils.makeOr(that.pos, t, rhs);
                    ejmlresult = t;
                    break;
                    
                case EQUIVALENCE:
                    scan(that.rhs);
                    rhs = ejmlresult;
                    t = treeutils.makeBinary(that.pos, JCTree.EQ, lhs, rhs);
                    ejmlresult = t;
                    break;
                    
                case INEQUIVALENCE:
                    scan(that.rhs);
                    rhs = ejmlresult;
                    t = treeutils.makeBinary(that.pos, JCTree.NE, lhs, rhs);
                    ejmlresult = t;
                    break;
                    
                case REVERSE_IMPLIES:
                    t = treeutils.makeNot(lhs.pos, lhs);
                    condition = treeutils.makeAnd(that.pos, condition, t);
                    scan(that.rhs);
                    rhs = treeutils.makeNot(that.rhs.pos, ejmlresult);
                    t = treeutils.makeOr(that.pos, lhs, rhs);
                    ejmlresult = t;
                    break;
                    
                 // FIXME - need <: operator
                 case SUBTYPE_OF:   
                 default:
                     error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
                    
            }
        }

        @Override
        public void visitJmlChoose(JmlChoose that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlClassDecl(JmlClassDecl that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlCompilationUnit(JmlCompilationUnit that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlConstraintMethodSig(JmlConstraintMethodSig that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlForLoop(JmlForLoop that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlGroupName(JmlGroupName that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlImport(JmlImport that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        // OK
        @Override
        public void visitJmlLblExpression(JmlLblExpression that) {
            // The format of this string is important in interpreting it in JmlEsc
            String nm = Strings.labelVarString + that.token.internedName().substring(1) + "_" + that.label;
            JCIdent id = newTemp(nm,scanret(that.expression));
            labels.add(nm);
            ejmlresult = id;
            JCExpression lit = treeutils.makeLit(that.getPreferredPosition(),syms.stringType,that.label.toString());
            if (rac) {
                String name = null;
                Type t = that.type;
                if (!t.isPrimitive()) {
                    name = "reportObject";
                } else if (t.tag == TypeTags.INT) {
                    name = "reportInt";
                } else if (t.tag == TypeTags.BOOLEAN) {
                    name = "reportBoolean";
                } else if (t.tag == TypeTags.LONG) {
                    name = "reportLong";
                } else if (t.tag == TypeTags.CHAR) {
                    name = "reportChar";
                } else if (t.tag == TypeTags.SHORT) {
                    name = "reportShort";
                } else if (t.tag == TypeTags.FLOAT) {
                    name = "reportFloat";
                } else if (t.tag == TypeTags.DOUBLE) {
                    name = "reportDouble";
                } else if (t.tag == TypeTags.BYTE) {
                    name = "reportByte";
                } else if (t.tag == TypeTags.BOT) {
                    name = "reportObject";
                } else  {
                    // this is a type error - should never get here
                    error(that.pos,"Unknown type in a \\lbl expression: " + t);
                }
                if (name != null) {
                    JCFieldAccess m = findUtilsMethod(name);
                    if (m == null) {
                        error(that.pos,"Method is not found in the runtime library: " + name);
                    } else {
                        JCMethodInvocation c = M.at(that.pos()).Apply(null,m,List.<JCExpression>of(lit,treeutils.makeIdent(id.pos,id.sym))); 
                        c.type = id.type;
                        JCStatement st = M.at(that.pos()).Exec(c);
                        if (that.token == JmlToken.BSLBLPOS) {
                            // Only report if the expression is true
                            // It is a type error if it is not boolean
                            st = M.at(that.pos()).If(treeutils.makeIdent(id.pos,id.sym), st, null);
                        } else if (that.token == JmlToken.BSLBLNEG) {
                            // Only report if the expression is true
                            // It is a type error if it is not boolean
                            st = M.at(that.pos()).If(treeutils.makeNot(that.pos, treeutils.makeIdent(id.pos,id.sym)), st, null);

                        }
                        addStat(st);
                    }
                }
            }
        }

        @Override
        public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlMethodDecl(JmlMethodDecl that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlMethodInvocation(JmlMethodInvocation that) {
            switch (that.token) {
                case BSOLD:
                case BSPRE:
                    JCExpression m = jmlrewriter.translate(that.meth);
                    JCExpression arg = jmlrewriter.translate(that.args.get(0));
                    JmlMethodInvocation meth;
                    if (that.args.size() == 1) {
                        meth = M.JmlMethodInvocation(that.token,arg);
                    } else {
                        // The second argument is a label, not an expression
                        meth = M.JmlMethodInvocation(that.token,arg,that.args.get(1));
                    }
                    meth.type = that.type;
                    meth.pos = that.pos;
                    meth.startpos = that.startpos;
                    meth.varargsElement = that.varargsElement;
                    meth.meth = m;
                    meth.label = that.label;
                    meth.typeargs = that.typeargs; // FIXME - do these need translating?
                    ejmlresult = meth;
                    break;
                case BSTYPEOF :
                case BSELEMTYPE :
                case BSNONNULLELEMENTS :
                case BSMAX :
                case BSFRESH :
                case BSREACH :
                case BSSPACE :
                case BSWORKINGSPACE :
                case BSDURATION :
                case BSISINITIALIZED :
                case BSINVARIANTFOR :
                case BSNOWARN:
                case BSNOWARNOP:
                case BSWARN:
                case BSWARNOP:
                case BSBIGINT_MATH:
                case BSSAFEMATH:
                case BSJAVAMATH:
                case BSNOTMODIFIED:
                case BSTYPELC:
                    // FIXME - implement these
                    Log.instance(context).error("esc.not.implemented","Not yet implemented token in JmlAssertionAdder: " + that.token.internedName());
                    ejmlresult = treeutils.trueLit; // FIXME - may not even be a boolean typed result
                    break;
                default:
                    Log.instance(context).error("esc.internal.error","Unknown token in JmlAssertionAdder: " + that.token.internedName());
                    ejmlresult = treeutils.trueLit; // FIXME - may not even be a boolean typed result
            }
        }

        @Override
        public void visitJmlMethodSpecs(JmlMethodSpecs that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlSetComprehension(JmlSetComprehension that) {
            // TODO Auto-generated method stub
            error(that.pos, "Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlSingleton(JmlSingleton that) {
            switch (that.token) {
                case BSRESULT:
                    if (resultSym == null) {
                        error(that.pos, "It appears that \\result is used where no return value is defined");
                    } else {
                        ejmlresult = treeutils.makeIdent(that.pos, resultSym);
                        if (methodDecl.name.toString().equals("m")) {
                            ejmlresult = ejmlresult;
                        }
                    }
                    break;

                case INFORMAL_COMMENT:
                    ejmlresult = treeutils.makeBooleanLiteral(that.pos,true);
                    break;
                    
                case BSEXCEPTION:
                    if (exceptionSym == null) {
                        error(that.pos,"It appears that \\exception is used where no exception value is defined" );
                    } else {
                        ejmlresult = treeutils.makeIdent(that.pos,exceptionSym);
                    }
                    break;
    //
//                case BSINDEX:
//                case BSVALUES:
//                    if (that.info == null) {
//                        log.error(that.pos,"esc.internal.error","No loop index found for this use of " + that.token.internedName());
//                        result = null;
//                    } else {
//                        result = newIdentUse((VarSymbol)that.info,that.pos);
//                    }
//                    break;
//                
//                case BSLOCKSET:
//                case BSSAME:
                   

                case BSNOTSPECIFIED:
                case BSNOTHING:
                case BSEVERYTHING:
                    error(that.pos, "Should not be attempting to translate this construct in JmlAssertion Adder's JML rewriter: " + that.token.internedName());
                    break;

                default:
                    Log.instance(context).error(that.pos, "jml.unknown.construct",that.token.internedName(),"BasicBlocker.visitJmlSingleton");
                // FIXME - recovery possible?
                    break;
            }
        }
        

        @Override
        public void visitJmlSpecificationCase(JmlSpecificationCase that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlStatement(JmlStatement that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlStatementDecls(JmlStatementDecls that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlStatementExpr(JmlStatementExpr that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlStatementLoop(JmlStatementLoop that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlStatementSpec(JmlStatementSpec that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlVariableDecl(JmlVariableDecl that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

        @Override
        public void visitJmlWhileLoop(JmlWhileLoop that) {
            error(that.pos,"Unexpected visit call in JmlExpressionRewriter: " + that.getClass());
        }

    }
}
