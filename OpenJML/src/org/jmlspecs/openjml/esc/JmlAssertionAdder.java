/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;


import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAccess;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlChoose;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlConstraintMethodSig;
import org.jmlspecs.openjml.JmlTree.JmlDoWhileLoop;
import org.jmlspecs.openjml.JmlTree.JmlEnhancedForLoop;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlImport;
import org.jmlspecs.openjml.JmlTree.JmlLblExpression;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseCallable;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignals;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignalsOnly;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlModelProgramStatement;
import org.jmlspecs.openjml.JmlTree.JmlPrimitiveTypeTree;
import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;
import org.jmlspecs.openjml.JmlTree.JmlSetComprehension;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlStatement;
import org.jmlspecs.openjml.JmlTree.JmlStatementDecls;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlStatementHavoc;
import org.jmlspecs.openjml.JmlTree.JmlStatementLoop;
import org.jmlspecs.openjml.JmlTree.JmlStatementSpec;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefArrayRange;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefKeyword;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefListExpression;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConditional;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConstraint;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseIn;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMaps;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMonitorsFor;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTree.JmlWhileLoop;
import org.jmlspecs.openjml.Utils.JmlNotImplementedException;
import org.jmlspecs.openjml.esc.BasicBlocker2.TargetFinder;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.Attr;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCArrayTypeTree;
import com.sun.tools.javac.tree.JCTree.JCAssert;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCAssignOp;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCBreak;
import com.sun.tools.javac.tree.JCTree.JCCase;
import com.sun.tools.javac.tree.JCTree.JCCatch;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCConditional;
import com.sun.tools.javac.tree.JCTree.JCContinue;
import com.sun.tools.javac.tree.JCTree.JCDoWhileLoop;
import com.sun.tools.javac.tree.JCTree.JCEnhancedForLoop;
import com.sun.tools.javac.tree.JCTree.JCErroneous;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCForLoop;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCIf;
import com.sun.tools.javac.tree.JCTree.JCImport;
import com.sun.tools.javac.tree.JCTree.JCInstanceOf;
import com.sun.tools.javac.tree.JCTree.JCLabeledStatement;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCNewArray;
import com.sun.tools.javac.tree.JCTree.JCNewClass;
import com.sun.tools.javac.tree.JCTree.JCParens;
import com.sun.tools.javac.tree.JCTree.JCPrimitiveTypeTree;
import com.sun.tools.javac.tree.JCTree.JCReturn;
import com.sun.tools.javac.tree.JCTree.JCSkip;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCSwitch;
import com.sun.tools.javac.tree.JCTree.JCSynchronized;
import com.sun.tools.javac.tree.JCTree.JCThrow;
import com.sun.tools.javac.tree.JCTree.JCTry;
import com.sun.tools.javac.tree.JCTree.JCTypeApply;
import com.sun.tools.javac.tree.JCTree.JCTypeCast;
import com.sun.tools.javac.tree.JCTree.JCTypeParameter;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.JCWhileLoop;
import com.sun.tools.javac.tree.JCTree.JCWildcard;
import com.sun.tools.javac.tree.JCTree.LetExpr;
import com.sun.tools.javac.tree.JCTree.TypeBoundKind;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.DiagnosticSource;
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
 * <P>
 * The resulting AST is an (almost) complete copy - it does not share any mutable structure with the original
 * AST, so the original AST can be reused; it represents each identifier in a separate
 * JCIdent, so that a succeeding Single-assignment step can change identifier names in place.
 * <UL>
 * <LI>If the field 'fullTranslation' is true, then all AST nodes, even non-mutable nodes, such as 
 * JCLiteral, are duplicated. The copied AST may still share non-AST objects such
 * as Name and Symbol objects, and references to MethodSpecs, TypeSpecs, and FieldSpecs.
 * <LI>If the field 'fullTranslation' is false, then, for efficiency, some node
 * classes, considered to be non-mutable, are still shared: JCLiteral, JCAnnotation,
 * JCModifiers.
 * <P>
 * There are three modes of translation:
 * <UL>
 * <LI>pureCopy=true: This makes an (alomst) pure copy of the AST, without converting or
 * adding any nodes. Note that any translation mode may use pureCopy for a 
 * sub-tree. Also note that some nodes include references to other nodes in the
 * tree (e.g., a class declaration includes a reference to its top-level 
 * compilation unit); these are appropriately translated. The 'almost' is because
 * (a) the result is still affected by the 'fullTranslation' option, and (b)
 * some nodes are expanded - type nodes are expanded to by fully-qualified types
 * and class field references may have 'this' prepended.
 * 
 * <LI>esc=true,rac=false,pureCopy=false: This inserts all JML semantics as new Java
 * constructs and JML assert and assume statements,
 * retaining the Java control flow statements.
 * 
 * <LI>rac=true,esc=false,pureCopy=false: This inserts all executable JML checks 
 * as calls to an assertionFailure method - which can dynamically choose to 
 * print out warning messages, throw exceptions, or execute a Java assert.
 * The translated AST is a transformation of the original program, but is
 * functionally equivalent to it, aside from the additional checks.
 * 
 * <LI>esc=true,rac=true,pureCopy=false: unsupported.
 * <LI>esc=false,rac=false,pureCopy=false: unsupported.
 * </UL>
 * <P>
 * With either rac or esc on, the translated AST uses only a subset of Java
 * functionality. All JML features are translated into assertions and Java statements.
 * <P>
 * Within both the rac and esc modes, subtrees may be translated with 
 * 'translatingJML' true - this should not be set by the caller, but is used to
 * translate Java constructs in JML expressions differently than Java constructs
 * in Java code.
// * <UL> -- FIXME - fix all of the following
// * <LI>Java expressions:
// * </UL>
// * <LI>binary operations - arithmetic, bit, logical all allowed in Java statements and JML assertions;
// * instanceof is allowed in Java, translated into a type relationship in JML
// * <LI>unary operations - minus and negation allowed; pre- and post-increment
// * and decrement converted to separate operations and assignment
// * <LI>assignment - retained 
// * <LI>assign-op - separated into operation and assignment
// * <LI>type cast - TBD
// * <LI>field selection - TBD
// * <LI>array index - retained, but uses JmlBBArrayAccess nodes instead of JCArrayAccess
// * <LI> 
// * <LI>object allocation - TBD
// * <LI>array allocation - TBD
// * <LI>anonymous class expression - TBD
// * <LI>...TBD
// * </UL>
// * <LI>Java statements:
// * <UL>
// * <LI>if, switch, try statements are retained
// * <LI>for, while, do, foreach statements are retained but may be transformed 
// * into other loop types to accommodate inserting loop specifications
// * <LI>variable declarations - TBD
// * <LI>local class declarations - TBD
// * <LI>method declarations, class declarations, import declarations - all retained
// * </UL>
// * <LI> JML expressions:
// * <UL>
// * <LI> binary logical operations - converted to Java equivalents
// * <LI> subtype operation - TBD
// * <LI> ... TBD
// * </UL>
// * <LI> JML statements and features:
// * <UL>
// * <LI> assert, assume statements - is esc mode, these are retained as JML statements
// * in rac mode, they are converted to RAC checks
// * <LI> method clauses: requires, ensures, signals - converted to assertions
// * </UL>
 * 
 *
 */

// DESIGN NOTE: This AST scanner operates in two modes - when translating Java
// and when translating JML. These are both implemented in the one scanner,
// controlled by the class field 'translatingJML'. I considered having two
// scanners, one for each mode. However, there was then a lot of code 
// duplication or similarity, with the similar code being separated into two
// classes. Also, calling the correct translation function proved to be more
// error prone than in the design with just one scanner class. For better or
// worse, the one-class design is what is implemented here.

// DESIGN NOTE: We can't simply extend a tree copier because (a) many nodes are
// transformed into nodes of a different class, and (b) many nodes produce
// multiple output nodes - e.g. statements are transformed into a series of
// statements.

public class JmlAssertionAdder extends JmlTreeScanner {

    // Parameters of this instance of JmlAssertionAdder 
    
    /** If true then every part of every AST is copied; if false then items
     * expected to be immutable such as JCLiteral, qualified ids (in import
     * statements, static type designators), JCAnnotation are not copied. 
     * Non-AST objects
     * such as Type, Token or JmlToken values are not copied in any case.
     */
    public boolean fullTranslation = true;
    
    // NOTE: We support !esc || !rac but not esc && rac.
    //@ invariant !esc || !rac;
    
    /** True if we are translating for static checks */
    public boolean esc ;
    
    /** True if we are translating for RAC */
    public boolean rac ;
    
    /** If true, we are making a pure copy */
    public boolean pureCopy;
    
    /** If true, then error messages in generated RAC code include source
     * code snippets with the customary textual ^ pointers to error locations.
     */
    public boolean showRacSource;
    
    /** If true, then in the RAC translation, assume statements and assumptions
     * generated by ESC, are checked as if they were assert statements.
     */
    public boolean racCheckAssumeStatements;

    /** If true, then in RAC, explicit checks are included even when the Java
     * language would catch the error itself (e.g., OpenJML will check for a
     * null reference in advance of a dereference and Java throwing a 
     * NullPointerException).
     */
    public boolean racJavaChecks;
    
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
    
    /** Cached value of the Nowarns object */
    final protected Nowarns nowarns;
    
    /** Cached value of the Attribute tool */
    final protected JmlAttr attr;
    
    /** The JmlTreeUtils object, holding a bunch of tree-making utilities */
    final protected JmlTreeUtils treeutils;
    
    /** The tool to find class symbols */
    final protected ClassReader reader;
    
    /** The symbol for the runtime Utils class */
    final protected ClassSymbol utilsClass;

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
    // These should only be modified by visit methods
    
    /** The AST being processed when in a sub-tree of a method declaration */
    protected JCMethodDecl methodDecl = null;
    
    /** The parent class of the method being converted, for use while the
     * declarations of the class are being walked, and while a method is
     * being translated stand-alone (without having been reached by walking
     * the tree from above).
     */
    protected JmlClassDecl classDecl = null;
    
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
    protected Map<Symbol,JCExpression> paramActuals;
    protected Map<Symbol,JCVariableDecl> preparams = new HashMap<Symbol,JCVariableDecl>();
    protected Map<JmlSpecificationCase,JCIdent> preconditions = new HashMap<JmlSpecificationCase,JCIdent>();
    
    /** A map from old nodes to new ones, for use when there are node references
     * (rather than copies of trees) within an AST.
     */
    protected java.util.Map<JCTree,JCTree> treeMap = new HashMap<JCTree,JCTree>();
    
    // TODO = document
    final protected java.util.List<String> labels = new LinkedList<String>();
    
    /** A List used to accumulate translated definitions of a class, for cases
     * where new declarations are needed.
     */
    protected ListBuffer<JCTree> classDefs;
    
    /** A list to collect statements as they are being generated. */
    protected ListBuffer<JCStatement> currentStatements;

    /** The prelude statements of the current method */
    protected ListBuffer<JCStatement> initialStatements;
    
    /** A stack of 'currentStatements' . The current value of 'currentStatements'
     * is NOT on this stack. */
    protected LinkedList<ListBuffer<JCStatement>> statementStack = new LinkedList<ListBuffer<JCStatement>>();
    
    /** true when translating JML constructs, false when translating Java constructs.
     * This is set and manipulated by the visitor methods 
     */
    protected boolean translatingJML;
    
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
    
    /** Used to hold the result of non-expression AST nodes - just used for 
     * declarations within a compilation unit. */
    protected JCTree result;
    
    /** Used to hold the result of expression AST nodes, so equal to result
     * when the result is a JCExpression. */
    protected JCExpression eresult;
    
    /** (Public API) Returns a new JCBlock representing the rewritten body of the given method declaration.
     */
    public JCBlock convertMethodBody(JCMethodDecl decl, JmlClassDecl cd) {
        JCMethodDecl prev = methodDecl;
        ListBuffer<JCStatement> prevStats = initialStatements;
        // We have the classDecl as an argument and save it here because
        // convertMethodBody may be called directly and not necessarily while
        // of walking the AST.
        this.classDecl = cd;
        
        // FIXME - these should not be reset for anonymous and local classes
        try {
            initialize();
            this.methodDecl = decl;
            this.initialStatements = new ListBuffer<JCStatement>();
            return convertBody();
        } catch (RuntimeException e) {
            String message = e.getMessage();
            if (message == null) message = "Internal exception: " + e.getClass();
            // FIXME - include the stack trace
            Log.instance(context).error("jml.internal.notsobad",message);
            return null;
        } finally {
            methodDecl = prev;
            initialStatements = prevStats;
        }
    }
    
    /** (Public API) Creates an object to do the rewriting and assertion insertion. This object
     * can be reused to translate different method bodies, so long as the arguments
     * to this constructor remain appropriate. May not have both esc and rac true;
     * if both are false, the mode is implicitly pureCopy.
     * @param context the compilation context to be used
     * @param esc true if the resulting AST is to be used for ESC, otherwise false
     * @param fac true if the resulting AST is to be used for RAC, otherwise false
     */
    public JmlAssertionAdder(Context context, boolean esc, boolean rac) {
        this.context = context;
        this.esc = esc;
        this.rac = rac;
        this.log = Log.instance(context);
        this.M = JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.nowarns = Nowarns.instance(context);
        this.syms = Symtab.instance(context);
        this.types = Types.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.attr = JmlAttr.instance(context);
        this.resultName = names.fromString(Strings.resultVarString);
        this.exceptionName = names.fromString(Strings.exceptionVarString);
        this.terminationName = names.fromString(Strings.terminationVarString);
        this.reader = ClassReader.instance(context);
        reader.init(syms);
        utilsClass = reader.enterClass(names.fromString(Strings.runtimeUtilsFQName));
        initialize();
    }
    
    /** (Public API) Reinitializes the object to start a new class or compilation unit or method */
    public void initialize() {
        this.showRacSource = !JmlOption.isOption(context,JmlOption.NO_RAC_SOURCE.optionName());
        this.racCheckAssumeStatements = true; // FIXME - add an option
        this.racJavaChecks = true;
        this.count = 0;
        this.assertCount = 0;
        this.precount = 0;
        this.preparams.clear();
        this.preconditions.clear();
        this.labels.clear();
        this.translatingJML = false;
        this.pureCopy = !(esc||rac);
        this.treeMap.clear();
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
        ListBuffer<JCStatement> outerFinalizeStats = new ListBuffer<JCStatement>();
        // restype is null for constructors and VOID for void methods
        boolean isConstructor = decl.restype == null;
        if (isConstructor) return decl.body; // FIXME - skip constructors until we have them working correctly
        if (!isConstructor && decl.restype.type.tag != TypeTags.VOID) {
            // The compiler complains that the result variable might not be
            // initialized on every path, even in programs in which it appears
            // obvious that it is. So we initialize it here.
            JCVariableDecl d = treeutils.makeVarDef(decl.restype.type,resultName,decl.sym,
                    treeutils.makeZeroEquivalentLit(0,decl.restype.type));
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
        addPrePostConditions(decl, initialStatements,outerFinalizeStats, isConstructor);
        decl.body.accept(this);
        JCBlock b = popBlock(0,decl.body.pos);
        JCTry outerTryStatement = M.Try(b,List.<JCCatch>nil(),
                M.Block(0, outerFinalizeStats.toList()));
        initialStatements.add(outerTryStatement);
        return M.at(decl.pos()).Block(0,initialStatements.toList());
    }
    
    // Generic node translation methods. Most of these may add statements to 
    // 'currentStatements'.
    
    // DESIGN NOTE: These routines expect all visit nodes to return a value in
    // 'result' and (for JCExpression derivatives) in 'eresult'. However, in
    // all modes except pureCopy, there may be side-effects of other statements
    // or declarations being produced; in addition, the class of the returned 
    // node may be different than that of the argument, because of the 
    // rac or esc translation.
    
    /** (Public API) Converts a non-expression AST, returning the converted tree;
     * this may be called externally on ClassDecl and CompilationUnit
     * trees, but should not be called outside of JmlAssertionAdder
     * on trees lower in the AST. Even inside of JmlAssertionAdder, the cast
     * to ensure that the result is the same type as the argument is only valid
     * in pureCopy mode and for specific argument types. */
    public <T extends JCTree> T convert(T tree) {
        if (tree == null) return null;
        scan(tree);
        return (T)result;
    }
    
    /** Returns a translation of a list of tree, possibly pushing additional
     * statements onto 'currentStatements'. The result list is only accurate
     * when in pureCopy mode.
     */
    protected <T extends JCTree> List<T> convert(List<T> trees) {
        if (trees==null) return null;
        ListBuffer<T> newlist = new ListBuffer<T>();
        for (T t: trees) {
            newlist.add(convert(t));
        }
        return newlist.toList();
    }
    
    /** Returns a translation of an expression, possibly pushing additional
     * statements onto 'currentStatements'
     */
    protected JCExpression scanExpr(JCExpression tree) {
        eresult = null; // Just so it is initialized in case assignment is forgotten
        if (tree != null) super.scan(tree);
        return eresult;
    }
    
    /** Returns a translation of a list of expression, possibly pushing additional
     * statements onto 'currentStatements'
     */
    protected List<JCExpression> scanExprList(List<? extends JCExpression> trees) {
        if (trees==null) return null;
        ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
        for (JCTree t: trees) {
            scan(t);
            newlist.add(eresult);
        }
        return newlist.toList();
    }
    
    /** Does a pure copy of the tree; once scanCopy is called on a node, child
     * calls to scanExpr or convert will also be in pureCopy mode. */
    protected <T extends JCTree> T scanCopy(T tree) {
        if (tree == null) return null;
        boolean savedCopy = pureCopy;
        try {
            pureCopy = true;
            scan(tree);
            return (T)result;
        } finally {
            pureCopy = savedCopy;
        }
    }

    /** Does a pure copy of the tree */
    protected  <T extends JCTree> List<T> scanCopy(List<T> trees) {
        boolean savedCopy = pureCopy;
        try {
            pureCopy = true;
            ListBuffer<T> newlist = new ListBuffer<T>();
            for (T t: trees) {
                newlist.add(scanCopy(t));
            }
            return newlist.toList();
        } finally {
            pureCopy = savedCopy;
        }
    }

    /** Does a pure copy of the tree */
    protected  <T extends JCTree> java.util.List<T> scanCopy(java.util.List<T> trees) {
        boolean savedCopy = pureCopy;
        try {
            pureCopy = true;
            java.util.List<T> newlist = new java.util.LinkedList<T>();
            for (T t: trees) {
                newlist.add(scanCopy(t));
            }
            return newlist;
        } finally {
            pureCopy = savedCopy;
        }
    }

    /** Translates an AST as JML - that is, assuming that the AST is pure;
     * this call is used to switch to the translatingJML mode, setting the
     * condition and isPostcondition to the given values,
     * restoring isPostcondition upon return.
     */
    protected JCExpression scanJML(JCExpression that, JCExpression condition, boolean isPostcondition) {
        if (that == null) return null;
        boolean savedp = this.isPostcondition;
        boolean savedt = this.translatingJML;
        try {
            this.isPostcondition = isPostcondition;
            this.condition = condition;
            this.translatingJML = true;
            return scanExpr(that);
        } finally {
            this.isPostcondition = savedp;
            this.translatingJML = savedt;
        }
    }

    /** Begins JML scanning for a non-postcondition */
    protected JCExpression scanJML(JCExpression that) {
        return scanJML(that, treeutils.trueLit, false);
    }

    
    /** Applies scanJML to a list of expressions, returning the new list. */
    protected List<JCExpression> scanJML(List<JCExpression> trees) {
        if (trees==null) return null;
        else {
            ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
            for (JCExpression tree: trees) {
                scanJML(tree, treeutils.trueLit, false);
                newlist.add(eresult);
            }
            return newlist.toList();
        }
    }
    

    /** Translates a block, but without adding the block to the statement list */
    protected JCBlock convertBlock(JCBlock block) {
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
    
    /** Add a statement at the end of the active currentStatements sequence,
     * returning the argument */ 
    protected <T extends JCStatement> T addStat(T stat) {
        currentStatements.add(stat); 
        return stat;
    }
    
    /** Add a statement at the end of the given buffer of statements,
     * returning the statement added */ 
    protected <T extends JCStatement> T addStat(ListBuffer<JCStatement> stats, T stat) {
        stats.add(stat);
        return stat;
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
    
    // FIXME - this is a hack - fix and docuyment
    
    static Set<String> racMessages = new HashSet<String>();
    static Set<String> escMessages = new HashSet<String>();
    
    protected void notImplemented(String location, JmlNotImplementedException source) {
        String message = location + source.getMessage();
        String key = source.pos.getPreferredPosition() + message;
        if (rac ? !racMessages.add(key) : !escMessages.add(key)) return;
        log.note(source.pos, 
                rac ? "rac.not.implemented" : "esc.not.implemented", 
                message);
    }
    
    protected void notImplemented(DiagnosticPosition pos, String message) {
        String key = pos.getPreferredPosition() + message;
        if (rac ? !racMessages.add(key) : !escMessages.add(key)) return;
        log.note(pos, 
                rac ? "rac.not.implemented" : "esc.not.implemented", 
                        message);
    }
    

    /** Adds an assertion with the given label and (already translated) expression
     * to the given statement list. 'codepos' is the position within the code where
     * the assertion is triggered; log.currentSource() is used as the sourcefile
     * in which 'codepos' lies. 'associatedSource' and 'associatedPos' are the
     * location of the specification clause from which this assertion derives,
     * if any.
     * The args are arguments for the resource key giving the error message
     * corresponding to the given Label.
     */

    protected JCStatement addAssert(
            DiagnosticPosition codepos, // FIXME _ document whether nullable and behavior
            Label label, 
            JCExpression expr, 
            ListBuffer<JCStatement> stats, 
            @Nullable DiagnosticPosition associatedPos, 
            @Nullable JavaFileObject associatedSource, 
            @Nullable JCExpression info, 
            Object ... args) {
        
        boolean isTrue = (expr instanceof JCLiteral && (Integer)((JCLiteral)expr).value != 0);
        boolean isFalse = (expr instanceof JCLiteral && (Integer)((JCLiteral)expr).value == 0);
        if (isTrue) return null; // Literally true - don't even add the statement
        if (nowarns.suppress(log.currentSource(), codepos == null ? Position.NOPOS : codepos.getPreferredPosition(), label.toString())) return null;
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
            JCDiagnostic diag = JCDiagnostic.Factory.instance(context).warning(log.currentSource(), codepos, "rac." + label, args);
            String msg = (showRacSource? diag.toString() : diag.noSource()).replace("warning: ", "");
            if (associatedPos != null) {
                diag = JCDiagnostic.Factory.instance(context).warning(new DiagnosticSource(associatedSource,null), associatedPos, "jml.associated.decl");
                String msg2 = (showRacSource? diag.toString() : diag.noSource()).replace("warning: ", "");
                msg = msg + JmlTree.eol + msg2;
            }
            
            if (info == null) {
                info = treeutils.makeStringLiteral(msg,expr.pos);
            }
            // FIXME - if info is not null, we don't get line information
            JCStatement st = assertFailure(info,codepos);
            if (!isFalse) st = M.at(codepos).If(treeutils.makeNot(codepos == null ? Position.NOPOS : codepos.getPreferredPosition(), treeutils.makeIdent(expr.pos,decl.sym)), st, null);
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
     * in which 'codepos' lies. There is no associated position or extra information.
     * The args are arguments for the resource key giving the error message
     * corresponding to the given Label.
     */
    protected JCStatement addAssert(
            DiagnosticPosition codepos, 
            Label label, 
            JCExpression expr, 
            ListBuffer<JCStatement> stats, 
            Object ... args) {
        return addAssert(codepos,label,expr,stats,null,null,null,args);
    }
    
    /** Adds an assertion with the given label and (already translated) expression
     * to the given statement list. 'codepos' is the position within the code where
     * the assertion is triggered; log.currentSource() is used as the sourcefile
     * in which 'codepos' lies. The last two arguments give the file and position
     * within the file of the associated specification that is potentially violated.
     * The args are arguments for the resource key giving the error message
     * corresponding to the given Label.
     */
    protected JCStatement addAssert(
            DiagnosticPosition codepos, 
            Label label, 
            JCExpression expr, 
            ListBuffer<JCStatement> stats, 
            DiagnosticPosition associatedPos, 
            JavaFileObject associatedSource, 
            Object ... args) {
        return addAssert(codepos,label,expr,stats,associatedPos,associatedSource,null,args);
    }
    
    /** Creates an AST for calling a method with the given name from the
     * org.jmlspecs.utils class (that is available at runtime)
     * @param methodName the name of the method 
     * @return the corresponding AST
     */
    protected JCFieldAccess findUtilsMethod(DiagnosticPosition pos, String methodName) {
        JCIdent utilsClassIdent = M.Ident(utilsClass);
        Name n = names.fromString(methodName);
        Scope.Entry e = utilsClass.members().lookup(n);
        Symbol ms = e.sym;
        if (e.sym == null) {
            return null; // Could not find the name
        } else {
            JCFieldAccess m = M.at(pos).Select(utilsClassIdent,n);
            m.sym = ms;
            m.type = m.sym.type;
            return m;
        }
    }
    
    /** Creates an AST for a one-argument call of the given method (from
     * org.jmlspecs.utils).
     * @param methodName the name of the method to call
     * @param translatedArg the AST which is the (already translated) argument
     * @return the resulting AST
     */
    protected JCExpression methodCallUtilsExpression(DiagnosticPosition pos, String methodName, JCExpression translatedArg) {
        JCFieldAccess m = findUtilsMethod(pos,methodName);
        JCExpression c = M.at(pos.getPreferredPosition()).Apply(null,m,List.<JCExpression>of(translatedArg));
        c.setType(((Type.MethodType)m.type).restype);
        return c;
    }

    
    /** Creates a call of org.jmlspecs.utils.Utils.assertionFailure(s), where
     * s is a literal containing the value of the argument, for RAC translations
     * @param sp the string to make into the literal argument of the call
     * @param pos the character position of the created AST
     * @return an assert statement indication an assertion failure
     */
    protected JCStatement assertFailure(JCExpression sp, DiagnosticPosition pos) {
        JCFieldAccess m = findUtilsMethod(pos,"assertionFailure");
        JCExpression c = M.at(pos).Apply(null,m,List.<JCExpression>of(sp));
        c.setType(syms.voidType);
        return M.at(pos).Exec(c);
    }

    
    /** Creates an assumption that two expressions are equal, adding the assumption to the given statement list. */
    protected JmlStatementExpr addAssumeEqual(
            DiagnosticPosition pos, 
            Label label, 
            JCExpression lhs, 
            JCExpression rhs, 
            @Nullable ListBuffer<JCStatement> stats) {
        return addAssume(pos,label,treeutils.makeBinary(pos.getPreferredPosition(),JCTree.EQ,lhs,rhs),stats,null,null,null);
    }
    
    /** Creates an assumption, adding it to the given statement list */
    protected JmlStatementExpr addAssume(
            DiagnosticPosition pos, 
            Label label, 
            JCExpression ex, 
            @Nullable ListBuffer<JCStatement> stats) {
        return addAssume(pos,label,ex,stats,null,null,null);
    }
    
    /** Creates an assumption with an associated declaration (perhaps in a different file), 
     * adding it to the given statement list (does nothing if esc and rac are false)*/
    protected JmlStatementExpr addAssume(
            DiagnosticPosition pos, 
            Label label, 
            JCExpression ex, 
            @Nullable ListBuffer<JCStatement> stats, 
            @Nullable DiagnosticPosition associatedPos, 
            @Nullable JavaFileObject associatedSource) {
        return addAssume(pos,label,ex,stats,associatedPos,associatedSource,null);
    }
    
    /** Creates an assumption with an associated declaration (perhaps in a different file), adding it to the given statement list */
    protected JmlStatementExpr addAssume(
            DiagnosticPosition pos, 
            Label label, 
            JCExpression ex, 
            @Nullable ListBuffer<JCStatement> stats, 
            @Nullable DiagnosticPosition associatedPosition, 
            @Nullable JavaFileObject associatedSource, 
            @Nullable JCExpression info) {
        JmlStatementExpr st = null;
        if (esc) {
            st = treeutils.makeAssume(pos,label,ex);
            st.source = log.currentSourceFile();
            st.declPos = associatedPosition == null ? Position.NOPOS : associatedPosition.getPreferredPosition();
            st.associatedSource = associatedSource;
            st.optionalExpression = info;
            if (stats != null) stats.add(st);
        }
        if (rac && racCheckAssumeStatements) {
            addAssert(pos,label,ex,stats,associatedPosition,associatedSource,info);
        }
        return st;
    }

    /** Creates a declaration for a unique temporary name with the given type and position,
     * with no initialization. */
    protected JCIdent newTemp(DiagnosticPosition pos, Type t) {
        Name n = M.Name(Strings.tmpVarString + (++count));
        JCVariableDecl d = treeutils.makeVarDef(t, n, esc ? null : methodDecl.sym , pos.getPreferredPosition()); // FIXME - see note below
        // We mark all temporaries as final, as an inidcation that they will
        // be used only one.
        d.mods.flags |= Flags.FINAL;
        d.sym.flags_field |= Flags.FINAL;
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
        // We mark all temporaries as final, as an inidcation that they will
        // be used only one.
        d.mods.flags |= Flags.FINAL;
        d.sym.flags_field |= Flags.FINAL;
        currentStatements.add(d);
        JCIdent id = treeutils.makeIdent(expr.pos,d.sym);
        return id;
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

    /** Returns true if the given symbol has a Helper annotation */
    public boolean isHelper(Symbol symbol) {
        return symbol.attribute(attr.tokenToAnnotationSymbol.get(JmlToken.HELPER))!=null;

    }
    
    /** Returns true if the given symbol has a Model annotation */
    public boolean isModel(Symbol symbol) {
        return symbol.attribute(attr.tokenToAnnotationSymbol.get(JmlToken.MODEL))!=null;
    }
    


    /** Computes and adds checks for all the pre and postcondition clauses. */
    // FIXME - review this
    protected void addPrePostConditions(JCMethodDecl decl, 
            ListBuffer<JCStatement> initialStats, 
            ListBuffer<JCStatement> finalizeStats,
            boolean isConstructor) {
        if (decl.sym == null) {
            log.warning("jml.internal.notsobad", "Unexpected null symbol for " + decl.getName());
        }
        JmlMethodSpecs denestedSpecs = decl.sym == null ? null : JmlSpecs.instance(context).getDenestedSpecs(decl.sym);
        // Add a precondition that the parameter != null on each formal parameter, if needed
        // Not adding these because the nonnull conditions are part of the deNestedSpecs.
        // However it would be nice to use these and leave them out of the  combinedPrecondition
        // because we get more accurate error messages.
        // Added  back - appears to be needed for ESC - FIXME
        if (esc) {
            for (JCVariableDecl d: decl.params) {
                if (specs.isNonNull(d.sym, (Symbol.ClassSymbol)d.sym.owner.owner)) {
                    addAssume(d.pos(),Label.NULL_CHECK,treeutils.makeNeqObject(d.pos,treeutils.makeIdent(d.pos, d.sym), treeutils.nulllit), 
                            initialStats);
                }
                JCVariableDecl dd = treeutils.makeVariableDecl(M.Name("PRE_"+d.name.toString()), d.type, 
                        M.Ident(d.sym), decl.pos);
                if (rac) dd.sym.owner = d.sym.owner;
                preparams.put(d.sym,dd);
                addStat(initialStats,dd);
            }
        }
        
        DiagnosticPosition p = methodDecl.pos();
        JCExpression cond = treeutils.makeEqObject(p.getPreferredPosition(),
                treeutils.makeIdent(p.getPreferredPosition(), exceptionSym),treeutils.nulllit);
        
        boolean methodIsStatic = methodDecl.sym.isStatic();
        JmlSpecs.TypeSpecs tspecs = specs.get(classDecl.sym);
        // FIXME - iterate over parent classes and interfaces
        for (JmlTypeClause clause : tspecs.clauses) {
            JmlTypeClauseExpr t;
            try {
                switch (clause.token) {
                    case INVARIANT:
                        if (!methodIsStatic || Utils.instance(context).hasAny(clause.modifiers,Flags.STATIC)) {
                            if (!isHelper(decl.sym)) {
                                t = (JmlTypeClauseExpr)clause;
                                addAssume(methodDecl.pos(),Label.INVARIANT_ENTRANCE,
                                        scanJML(t.expression),initialStats,
                                        clause.pos(),clause.source);
                            }
                        }
                        break;
                    case AXIOM:
                        if (rac) {
                            notImplemented(clause.pos(), "axiom clause");
                        } else if (esc) {
                            t = (JmlTypeClauseExpr)clause;
                            addAssume(methodDecl.pos(),Label.AXIOM,
                                    scanJML(t.expression),initialStats,
                                    clause.pos(),clause.source);
                        }
                        break;
                    default:
                        // Skip

                }
            } catch (JmlNotImplementedException e) {
                notImplemented(clause.token.internedName() + " clause containing ", e);
            }
        }
        ListBuffer<JCStatement> saved = currentStatements;
        JCExpression combinedPrecondition = null;
        ListBuffer<JCStatement> ensureStats = new ListBuffer<JCStatement>();
        ListBuffer<JCStatement> exsureStats = new ListBuffer<JCStatement>();
        for (JmlSpecificationCase scase : denestedSpecs.cases) {
            JCIdent preident = null;
            JCExpression preexpr = null;
            currentStatements = initialStats;
            for (JmlMethodClause clause : scase.clauses) {
                switch (clause.token) {
                    case REQUIRES:
                        JCExpression ex = ((JmlMethodClauseExpr)clause).expression;
                        if (preexpr == null) preexpr = ex;
                        else preexpr = treeutils.makeAnd(preexpr.pos, preexpr, ex);
                        break;
                    default:
                }
            }
            if (preexpr == null) {
                preexpr = treeutils.trueLit;
            } else {
                try {
                    preexpr = scanJML(preexpr);
                } catch (JmlNotImplementedException e) {
                    notImplemented("requires clause containing ",e);
                    continue;
                }
            }
            precount++;
            Name prename = names.fromString(Strings.prePrefix + precount);
            JCVariableDecl d = treeutils.makeVarDef(syms.booleanType, prename, decl.sym, preexpr);
            preident = treeutils.makeIdent(scase.pos, d.sym);
            addStat(initialStats,d);
            preconditions.put(scase, preident);
            if (combinedPrecondition == null || preexpr == treeutils.trueLit) {
                combinedPrecondition = preident;
            } else {
                combinedPrecondition = treeutils.makeOr(combinedPrecondition.pos, combinedPrecondition, preident);
            }
            
            for (JmlMethodClause clause : scase.clauses) {
                try {
                    switch (clause.token) {
                        // FIXME - would be nice if RAC postconditions could refer to the last return that was executed
                        case ENSURES:
                        {
                            currentStatements = ensureStats;
                            pushBlock();
                            JCExpression ex = ((JmlMethodClauseExpr)clause).expression;
                            ex = scanJML(ex,preident,true);
                            ex = treeutils.makeImplies(clause.pos, preident, ex);
                            // FIXME - if the clause is synthetic, the source file may be null, and for signals clause
                            addAssert(esc ? null :methodDecl.pos(),Label.POSTCONDITION,ex,currentStatements,clause.pos(),clause.sourcefile);
                            addStat(popBlock(0,Position.NOPOS));
                            break;
                        }

                        case SIGNALS: // FIXME - need to check exception type of the exception
                        {
                            currentStatements = exsureStats;
                            pushBlock();
                            JCVariableDecl vd = ((JmlMethodClauseSignals)clause).vardef;
                            JCIdent exceptionId = treeutils.makeIdent(clause.pos,exceptionSym);
                            JCTypeCast tc = M.TypeCast(vd.type, exceptionId);
                            vd.init = tc;
                            addStat(vd);
                            //JCVariableDecl evar = treeutils.makeVarDef(vd.type, vd.name, decl.sym, tc); // FIXME - needs a unique name
                            //addStat(evar);
                            JCExpression ex = ((JmlMethodClauseSignals)clause).expression;
                            ex = scanJML(ex,preident,true);
                            ex = treeutils.makeImplies(clause.pos, preident, ex);
                            addAssert(esc ? null :methodDecl.pos(),Label.SIGNALS,ex,currentStatements,clause.pos(),clause.sourcefile);
                            addStat(popBlock(0,Position.NOPOS));
                            break;
                        }

                        case SIGNALS_ONLY:
                        {
                            currentStatements = exsureStats;
                            pushBlock();
                            JCIdent exceptionId = treeutils.makeIdent(clause.pos,exceptionSym);
                            JCExpression condd = treeutils.falseLit;
                            for (JCExpression t: ((JmlMethodClauseSignalsOnly)clause).list) {
                                JCExpression tc = M.at(t.pos()).TypeTest(exceptionId, t).setType(syms.booleanType);
                                condd = treeutils.makeOr(clause.pos, condd, tc);
                            }
                            addAssert(esc ? null :methodDecl.pos(),Label.SIGNALS_ONLY,condd,currentStatements,clause.pos(),clause.sourcefile);
                            addStat(popBlock(0,Position.NOPOS));
                            break;
                        }

                        case DIVERGES:
                        {
                            // FIXME _ implement
                            currentStatements = exsureStats;
                            pushBlock();
                            JCExpression ex = ((JmlMethodClauseExpr)clause).expression;
                            ex = scanJML(ex,preident,true);
                            ex = treeutils.makeImplies(clause.pos, preident, ex);
                            //addAssert(esc ? null :methodDecl.pos(),Label.SIGNALS,ex,currentStatements,clause.pos(),clause.sourcefile);
                            popBlock(0,Position.NOPOS);
                            notImplemented(clause.pos(),clause.token.internedName() + " clause");
                            break;
                        }
                        case DURATION:
                        case WORKING_SPACE:
                        {
                            // FIXME - implement
                            currentStatements = exsureStats;
                            pushBlock();
                            JCExpression ex = ((JmlMethodClauseConditional)clause).expression;
                            ex = scanJML(ex,preident,true);
                            ex = treeutils.makeImplies(clause.pos, preident, ex);
                            //addAssert(esc ? null :methodDecl.pos(),Label.SIGNALS,ex,currentStatements,clause.pos(),clause.sourcefile);
                            popBlock(0,Position.NOPOS);
                            notImplemented(clause.pos(),clause.token.internedName() + " clause");
                            break;
                        }


                        // FIXME - more clauses to implement?

                        case REQUIRES:
                            break;
                        default:
                    }
                } catch (JmlNotImplementedException e) {
                    notImplemented(clause.token.internedName() + " clause containing ",e);
                    continue;
                }
            }
        }

        // FIXME - iterate over parent classes and interfaces
        currentStatements = ensureStats;
        for (JmlTypeClause clause : tspecs.clauses) {
            JmlTypeClauseExpr t;
            try {
                switch (clause.token) {
                    // FIXME - add in assert of non-null fields - check staticness
                    case INVARIANT:
                        if (!methodIsStatic || Utils.instance(context).hasAny(clause.modifiers,Flags.STATIC)) {
                            if (!isHelper(decl.sym)) {
                                pushBlock();
                                t = (JmlTypeClauseExpr)clause;
                                addAssert(methodDecl.pos(),Label.INVARIANT_EXIT,
                                        scanJML(t.expression),
                                        currentStatements,
                                        clause.pos(),clause.source);
                                addStat( popBlock(0,Position.NOPOS));
                            }
                        }
                        break;
                    case CONSTRAINT:
                        // FIXME - need to check the list of method signatures
                        if (!isConstructor && (!methodIsStatic || Utils.instance(context).hasAny(clause.modifiers,Flags.STATIC))) {
                            pushBlock();
                            JmlTypeClauseConstraint tt = (JmlTypeClauseConstraint)clause;
                            addAssert(methodDecl.pos(),Label.CONSTRAINT,
                                    scanJML(tt.expression),
                                    currentStatements,
                                    clause.pos(),
                                    clause.source);
                            addStat( popBlock(0,Position.NOPOS));
                        }
                        break;
                    case INITIALLY:
                        if (isConstructor && !isHelper(decl.sym)) {
                            pushBlock();
                            t = (JmlTypeClauseExpr)clause;
                            addAssert(methodDecl.pos(),Label.INITIALLY,
                                    scanJML(t.expression),
                                    currentStatements,
                                    clause.pos(),clause.source);
                            addStat( popBlock(0,Position.NOPOS));
                        }
                        break;
                    default:
                        // Skip

                }
            } catch (JmlNotImplementedException e) {
                notImplemented(clause.token.internedName() + " clause containing ",e);
                continue;
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
    
    // FIXME - should we implement?
    @Override
    public void visitTopLevel(JCCompilationUnit that) {
        // OpenJML should never call this, because JCCompilationUnit nodes should be
        // replaced by JmlCompilationUnit nodes. We implement this just in case, but
        // always produce a JmlCompilationUnit node
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitTopLevel while translating JML: " + that.getClass());
            return;
        }
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
//        n.setType(that.type);
//        n.sourcefile = that.sourcefile;
//        n.starImportScope = that.starImportScope;
//        n.specsCompilationUnit = that.specsCompilationUnit;
//        n.specsTopLevelModelTypes = that.specsTopLevelModelTypes;
//        result = n;
    }

    @Override
    public void visitImport(JCImport that) {
        // OpenJML should never call this, because JCImport nodes should be
        // replaced by JmlImport nodes. We implement this just in case, but
        // always produce a JmlImport node
        
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitImport while translating JML: " + that.getClass());
            return;
        }
        // FIXME - rewrite the qualid; this produces a JmlImport instead of an Import
        JCTree qualid = that.qualid;
        //if (fullTranslation) qualid = treeutils.makeQualid(qualid);
        result = M.at(that.pos()).Import(qualid, that.staticImport);
    }

    @Override
    public void visitClassDef(JCClassDecl that) {
        // OpenJML should never call this, because JCClassDecl nodes should be
        // replaced by JmlClassDecl nodes. We implement this just in case, but
        // always produce a JmlClassDecl node. FIXME - do we?

        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.viksitClassDef while translating JML: " + that.getClass());
            return;
        }
        error(that.pos, "Unexpectedly calling JmlAssertionAdder.visitClassDef: " + that.getClass());
    }

    @Override
    public void visitMethodDef(JCMethodDecl that) {
        // In OpenJML, we expect to always have JmlMethodDecl nodes, and so 
        // never to call this visit class
        // However, just in case a user creates one, we translate it
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitMethodDef while translating JML: " + that.getClass());
            return;
        }
        // FIXME - implement
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitMethodDef: " + that.getClass());
    }

    @Override
    public void visitVarDef(JCVariableDecl that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitVarDef while translating JML: " + that.getClass());
            return;
        }
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitVarDef: " + that.getClass());
        
        // FIXME - is this ever called? duplicates code from JmlVariableDecl
        JCExpression init = scanExpr(that.init);
        if (init != null) init = addImplicitConversion(that.pos(),that.type,init);
        
        if (init != null && !init.type.isPrimitive() && specs.isNonNull(that.sym,that.sym.enclClass())) {
            // FIXME _ fix this back at the declaration of $$values$...
            //if (!that.getName().toString().startsWith("$$values$")) 
            JCExpression nn = treeutils.makeNeqObject(init.pos,  init, treeutils.nulllit);
            if (init instanceof JCLiteral) {
                // FIXME - potential optimizations, but they need testing, particularly the second one
                if (init.type.tag == TypeTags.BOT) nn = treeutils.falseLit;
                if (init.type.tag == TypeTags.CLASS) nn = treeutils.trueLit;
            } 
            // FIXME - should have an associated position
            addAssert(that.pos(),Label.POSSIBLY_NULL_INITIALIZATION,nn,currentStatements);
        }
        
        // FIXME - need to make a unique symbol
        JCVariableDecl stat = M.at(that.pos()).VarDef(that.sym,init);
        result = addStat(stat);
    }

    //OK
    @Override
    public void visitSkip(JCSkip that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitSkip while translating JML: " + that.getClass());
            return;
        }
        result = addStat(M.at(that.pos()).Skip());
        // Caution - JML statements are subclasses of JCSkip
    }

    //OK
    @Override
    public void visitBlock(JCBlock that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitBlock while translating JML: " + that.getClass());
            return;
        }
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
        JCBlock bl;
        if (that == null) {
            bl = null;
        } else {
            pushBlock();
            scan(that.stats);
            bl = popBlock(that.flags,that.pos);
            if (currentStatements != null) {
                addStat(bl);
            } else {
                classDefs.add(bl);
                methodDecl = null;
            }
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
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitLabelled while translating JML: " + that.getClass());
            return;
        }
        if (!pureCopy) addStat(comment(that.pos,"label:: " + that.label + ": ..."));
        // Note that the labeled statement will turn into a block
        // FIXME - the block may have introduced declarations that are then used after the block?
        JCBlock block = translateIntoBlock(that.pos,that.body);
        JCLabeledStatement stat = M.at(that.pos()).Labelled(that.label, block);
        result = addStat(stat);
    }

    //OK
    @Override
    public void visitSwitch(JCSwitch that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitSwitch while translating JML: " + that.getClass());
            return;
        }
        try {
            JCExpression selector = scanExpr(that.selector);
            JCSwitch sw = M.at(that.pos()).Switch(selector, null);
            treeMap.put(that,sw);
            ListBuffer<JCCase> cases = new ListBuffer<JCCase>();
            for (JCCase c: that.cases) {
                JCExpression pat = scanExpr(c.pat);
                JCBlock b = translateIntoBlock(c.pos,c.stats);
                JCCase cc = M.at(c.pos).Case(pat,b.stats);
                cases.add(cc);
            }
            sw.cases = cases.toList();
            result = addStat(sw.setType(that.type));
        } finally {
            treeMap.remove(that);
        }
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
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitSynchronized while translating JML: " + that.getClass());
            return;
        }
        JCExpression lock = scanExpr(that.lock);
        if (that.lock instanceof JCParens && ((JCParens)that.lock).expr instanceof JCIdent && ((JCIdent)((JCParens)that.lock).expr).name.toString().equals("this")) {
            // Don't need to check that 'this' is not null
            // FIXME - the above is complicated - I expect it will fail in anything but the trivial case
        } else if (rac || esc) {
            JCExpression e = treeutils.makeNeqObject(that.lock.pos, lock, treeutils.nulllit);
            addAssert(that.lock.pos(), Label.POSSIBLY_NULL, e, currentStatements);
        }
        JCBlock block = convertBlock(that.body);
        result = addStat(M.at(that.pos()).Synchronized(lock, block).setType(that.type));
        // FIXME - need to add concurrency checks
    }

    // OK
    // FIXME - review for both esc and rac
    @Override
    public void visitTry(JCTry that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitTry while translating JML: " + that.getClass());
            return;
        }
        JCBlock body = convertBlock(that.body);

        if (!esc) {
            List<JCCatch> catchers = null;
            if (that.catchers != null) {
                ListBuffer<JCCatch> ncatchers = new ListBuffer<JCCatch>();
                for (JCCatch catcher: that.catchers) {
                    JCBlock block = convertBlock(catcher.getBlock());
                    JCVariableDecl odecl = catcher.getParameter();  
                    JmlVariableDecl decl = M.at(odecl.pos()).VarDef(odecl.sym,  null); // Catcher declarations have no initializer
                    JCCatch ncatcher = M.at(catcher.pos()).Catch(decl,block);
                    ncatcher.setType(catcher.type);
                    ncatchers.add(ncatcher);
                }
                catchers = ncatchers.toList();
            }
            JCBlock finalizer = convertBlock(that.finalizer);
            // FIXME - nothing is done about that.resources
            JCTry st =  M.at(that.pos()).Try(body, catchers, finalizer);
            st.resources = that.resources;
            st.setType(that.type);
            result = addStat(st);
            return;
        }

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
                id = M.at(that.pos()).Ident(exceptionSym);  // FIXME - should this have a type cast?
                JCVariableDecl vd = treeutils.makeVarDef(catcher.param.type, catcher.param.name, catcher.param.sym.owner, id);
                stats.add(vd);

                // EXCEPTION = null
                id = treeutils.makeIdent(that.pos,exceptionSym);
                stats.add(treeutils.makeAssignStat(that.pos, id, treeutils.nulllit));

                // TERMINATION = 0
                id = treeutils.makeIdent(that.pos,terminationSym);
                stats.add(treeutils.makeAssignStat(that.pos,id, treeutils.zero));

                // FIXME - need to put in the instanceof operation

                // add statements from the catch block
                JCBlock catchblock = convertBlock(catcher.body);
                stats.addAll(catchblock.stats);

                M.at(catcher.pos());
                JCIf ifstatc = M.If(treeutils.trueLit, M.Block(catcher.body.flags, stats.toList()), null);
                ifstat.elsepart = ifstatc;
                ifstat = ifstatc;
            }
        }

        if (that.finalizer != null) {
            JCBlock finalizer = convertBlock(that.finalizer);
            finalizerstats.add(finalizer);
        }

//        // if (TERMINATION > 0) return ...
//        JCIdent id = treeutils.makeIdent(that.pos, terminationSym);
//        JCBinary cond = treeutils.makeBinary(that.pos,JCTree.GT, id, treeutils.zero );
//        JCIf ifstat = M.If(cond,  M.Return(resultSym == null ? null : M.Ident(resultSym)), null);
//        finalizerstats.add(ifstat);
//
//        // if (TERMINATION < 0) throw ...
//        id = treeutils.makeIdent(that.pos, terminationSym);
//        cond = treeutils.makeBinary(that.pos,JCTree.LT, id, treeutils.zero );
//        ifstat = M.If(cond,  M.Throw(M.Ident(exceptionSym)), null);
//        finalizerstats.add(ifstat);
        
        
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
        if (translatingJML || pureCopy ) {
            JCExpression cond = scanExpr(that.cond);
            JCExpression prev = condition;
            try {
                // Note if !(esc||rac) we are doing a strict copy.
                // Although we compute 'condition' here, it should not be used
                // anywhere.
                condition = treeutils.makeAnd(that.pos, prev, cond);
                JCExpression truepart = scanExpr(that.truepart);
                condition = treeutils.makeAnd(that.pos, prev, treeutils.makeNot(that.falsepart.pos, cond));
                JCExpression falsepart = scanExpr(that.falsepart);
                result = eresult = M.at(that.pos()).Conditional(cond,truepart,falsepart).setType(that.type);
            } finally {
                condition = prev;
            }
            return;
        }
        
        addStat(comment(that.pos," ... conditional ..."));
        
        JCExpression cond = scanExpr(that.cond);
        Name ifname = names.fromString("conditionalResult" + (++count));
        JCVariableDecl vdecl = treeutils.makeVarDef(that.type, ifname, null, that.pos);
        addStat(vdecl);
        pushBlock();

        scan(that.truepart);
        addAssumeEqual(that.truepart.pos(), Label.ASSIGNMENT, 
                treeutils.makeIdent(that.truepart.pos, vdecl.sym), eresult, currentStatements);
        JCBlock trueblock = popBlock(0,that.truepart.pos);
        pushBlock();

        scan(that.falsepart);
        addAssumeEqual(that.falsepart.pos(), Label.ASSIGNMENT, 
                treeutils.makeIdent(that.falsepart.pos, vdecl.sym), eresult, currentStatements);
        JCStatement stat = M.If(cond, trueblock, popBlock(0,that.falsepart.pos));
        
        currentStatements.add(stat);
        result = eresult = treeutils.makeIdent(that.pos, vdecl.sym);
    }

    // OK
    @Override
    public void visitIf(JCIf that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitIf while translating JML: " + that.getClass());
            return;
        }
        addStat(comment(that.pos," ... if ..."));
        JCExpression cond = scanExpr(that.cond);

        // The scanned result of the then and else parts must always be a block
        // because multiple statements might be produced, even from a single
        // statement in the branch. The following implementation has the 
        // disadvantage that if the original branch was a block, the result is
        // a nested block.
        
        pushBlock();
        scan(that.thenpart);
        JCBlock thenpart = popBlock(0,that.thenpart.pos);
        
        pushBlock();
        if (that.elsepart != null) scan(that.elsepart);
        JCBlock elsepart = popBlock(0,that.elsepart != null ? that.elsepart.pos : that.cond.pos);

        result = addStat( M.at(that.pos()).If(cond,thenpart,elsepart).setType(that.type) );
    }

    @Override
    public void visitExec(JCExpressionStatement that) {
        // Applies whether translatingJML or not
        addStat(comment(that));
        JCExpression arg = scanExpr(that.getExpression());
        
        // For rac and esc, assignments become an initialization of a variable,
        // so no exec statement is needed, and arg is then an ident.
        
        // A raw copy will still need creation of an Exec statement
        
        // FIXME - what about method invocations?

        if (arg != null && (arg instanceof JCMethodInvocation || arg instanceof JCAssign || arg instanceof JCAssignOp)) {
            result = addStat( M.at(that.pos()).Exec(arg).setType(that.type) );
        }
    }

    // OK
    @Override
    public void visitBreak(JCBreak that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitBreak while translating JML: " + that.getClass());
            return;
        }
        JCBreak st = M.at(that.pos()).Break(that.label);
        st.target = treeMap.get(that.target);
        if (st.target == null) {
        	error(that.pos,"Unknown break target");
        }
        st.setType(that.type);
        result = addStat(st);
    }

    // OK
    @Override
    public void visitContinue(JCContinue that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitContinue while translating JML: " + that.getClass());
            return;
        }
        JCContinue st = M.at(that.pos()).Continue(that.label);
        st.target = treeMap.get(that.target);
        if (st.target == null) {
            error(that.pos,"Unknown continue target");
        }
        st.setType(that.type);
        result = addStat(st);
    }
    

    // OK
    @Override
    public void visitReturn(JCReturn that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitReturn while translating JML: " + that.getClass());
            return;
        }
        addStat(comment(that));
        JCExpression arg = null;
        JCExpression retValue = that.getExpression();
        if (retValue != null) {
            arg = scanExpr(retValue);
            if (!pureCopy) {
                JCIdent resultid = M.at(that.pos()).Ident(resultSym);
                JCStatement stat = treeutils.makeAssignStat(that.pos,resultid,arg);
                addStat(stat);
                arg = resultid;
            }
        }
        // Record the value of the termination location
        if (!pureCopy) {
            JCIdent id = treeutils.makeIdent(that.pos,terminationSym);
            JCLiteral intlit = treeutils.makeIntLiteral(that.pos,that.pos);
            JCStatement stat = treeutils.makeAssignStat(that.pos,id,intlit);
            addStat(stat);
        }
        // If the return statement is in a finally block, there may have been an exception
        // in the process of being thrown - so we set EXCEPTION to null.
        JCIdent id = treeutils.makeIdent(that.pos,exceptionSym);
        JCStatement stat = treeutils.makeAssignStat(that.pos,id,treeutils.nulllit);
        addStat(stat);
        
        stat = M.at(that.pos()).Return(arg).setType(that.type);
        result = addStat(stat);
    }

    // OK
    // FIXME - review for esc
    @Override
    public void visitThrow(JCThrow that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitThrow while translating JML: " + that.getClass());
            return;
        }
        
        if (!esc) {
            JCExpression expr = scanExpr(that.getExpression());
            if (rac) {
                JCIdent id = treeutils.makeIdent(that.pos,exceptionSym);
                JCStatement assign = M.at(that.pos()).Exec(treeutils.makeAssign(that.pos,id,expr));
                addStat(assign);
            }
            result = addStat(M.at(that.pos()).Throw(expr).setType(that.type));
            return;
        }
        
        addStat(comment(that));
        // assert expr != null;
        pushBlock();
        JCExpression e = treeutils.makeNeqObject(that.expr.pos, scanExpr(that.expr), treeutils.nulllit);
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
        result = addStat(block);
    }

    // OK - this is a Java assert statement
    @Override
    public void visitAssert(JCAssert that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitAssert while translating JML: " + that.getClass());
            return;
        }
        // FIXME - in esc we may want to treat this as an exceptino throwing Java statement
        
        // ESC will eventually convert this to a Jml assertion, but RAC wants
        // it left as a Java assertion statement
        addStat(comment(that));
        JCExpression cond = scanExpr(that.getCondition());
        JCExpression info = scanExpr(that.getDetail());
        
        if (esc && !pureCopy) {
            result = addAssert(that.pos(),Label.EXPLICIT_ASSERT,cond,currentStatements,null,null,info);
        } else {
            result = addStat( M.at(that.pos()).Assert(cond, info).setType(that.type) );
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
                            scanJML(pfa.selected)); // FIXME - needs check for not implemented
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
                JCExpression result = treeutils.makeEqObject(pos, fa.selected, scanJML(pfa.selected));
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
                    JCExpression result = treeutils.makeEqObject(pos, fa.selected, scanJML(pfa.selected));
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
            JCExpression result = treeutils.makeEqObject(pos, a1, scanJML(paa.expression));
            if (aa.index == null) {
                if (paa.lo == null && paa.hi == null) return result;
                if (paa.hi == null) return treeutils.makeAnd(pos, result, treeutils.makeBinary(pos, JCTree.EQ, treeutils.inteqSymbol, scanJML(paa.lo),treeutils.zero));
                
                // FIXME - compare paa.hi to array.length, paa.lo to zero if not null
                return treeutils.falseLit;
            } else {
                JCExpression aat = isjml ? scanJML(aa.index) : (aa.index);
                result = treeutils.makeAnd(pos,result,
                        treeutils.makeAnd(pos,
                                treeutils.makeBinary(pos,JCTree.LE,treeutils.intleSymbol,
                                        paa.lo == null ? treeutils.zero : scanJML(paa.lo),aat),
                                treeutils.makeBinary(pos,JCTree.LE,treeutils.intleSymbol,
                                                aat, paa.hi == null ? null /* FIXME - need length of array */ : scanJML(paa.hi))
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
            JCExpression result = treeutils.makeEqObject(pos, scanJML(aa.expression), scanJML(paa.indexed));
            if (paa.index == null) return result;
            JCExpression paat = scanJML(paa.index);
            result = treeutils.makeAnd(pos, result, treeutils.makeBinary(pos,JCTree.EQ,treeutils.inteqSymbol, 
                    aa.lo == null ? treeutils.zero : scanJML(aa.lo), paat));
//            result = treeutils.makeAnd(pos, result, treeutils.makeBinary(pos,JCTree.EQ,treeutils.inteqSymbol, 
//                    aa.hi == null ? /* FIXME - array length -1 */ : jmlrewriter.translate(aa.hi), paat));
            return result;
        } else if (pstoreref instanceof JmlStoreRefArrayRange) {
            JmlStoreRefArrayRange paa = (JmlStoreRefArrayRange)pstoreref;
            JCExpression result = treeutils.makeEqObject(pos, scanJML(aa.expression), scanJML(paa.expression));
            JCExpression a1 = aa.lo == null ? treeutils.zero : scanJML(aa.lo);
            JCExpression a2 = paa.lo == null ? treeutils.zero : scanJML(paa.lo);
            result = treeutils.makeAnd(pos, result, treeutils.makeBinary(pos,JCTree.LE,treeutils.intleSymbol, 
                    a2, a1));

            // FIXME - in the null case we want array length - 1
            a1 = aa.hi == null ? treeutils.zero : scanJML(aa.hi);
            a2 = paa.hi == null ? treeutils.zero : scanJML(paa.hi);
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
        pre = treeutils.makeIdent(pre.pos, pre.sym); // a new id for the same symbol
        boolean anyAssignableClauses = false;
        JCExpression asg = treeutils.falseLit;
        for (JmlMethodClause mclause : c.clauses) {
            try {
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
                        anyAssignableClauses = true;
                        break;
                    default:
                        break;
                }
            } catch (JmlNotImplementedException e) {
                notImplemented("assignable clause containing ",e);
            }
        }
        // If there are no assignable clauses at all, the default is
        // \everything - so the result of the check is then true.
        if (!anyAssignableClauses) asg = treeutils.trueLit;
        if (asg != treeutils.trueLit) {
            return treeutils.makeImplies(storeref.pos, pre, asg);
        } else {
            return asg;
        }
    }
    
    protected void checkAgainstCallerSpecs(JCExpression scannedItem, JCExpression pre) {
        List<JmlSpecificationCase> cases = specs.getDenestedSpecs(methodDecl.sym).cases;
        for (JmlSpecificationCase c : cases) {
            JCExpression condition = checkAssignable(false,scannedItem,c);
            if (condition != treeutils.trueLit) {
                condition = treeutils.makeImplies(scannedItem.pos, pre, condition);
                addAssert(scannedItem.pos(),Label.ASSIGNABLE,condition,currentStatements,c.pos(),c.sourcefile);
            }
        }
    }

    // FIXME - needs work
    @Override
    public void visitApply(JCMethodInvocation that) {
        // FIXME - needs result set - needs proper handling of pure methods etc.
        if (translatingJML || pureCopy) {
            // FIXME - need to check definedness by testing preconditions
            List<JCExpression> typeargs = scanExprList(that.typeargs);
            JCExpression meth = scanExpr(that.meth);
            List<JCExpression> args = scanExprList(that.args);
            JCMethodInvocation app = M.at(that.pos()).Apply(typeargs, meth, args).setType(that.type);
            app.varargsElement = that.varargsElement; // a Type
            result = eresult = app;
            return;
        }
        JCExpression now;
        MethodSymbol calleeMethodSym = null;
        Symbol savedSym = resultSym;
        
        Map<VarSymbol,JCIdent> prevArgsMap = currentArgsMap;
        Map<Symbol,JCExpression> savedParamActuals = paramActuals; // restore in a finall block FIXME

        try {
            // Translate the method name, and determine the thisid for the
            // method call
            
            List<JCExpression> trArgs;
            JCMethodInvocation trExpr = null;
            if (that.meth instanceof JCIdent) {
                now = scanExpr(that.meth);
                List<JCExpression> typeargs = convert(that.typeargs);
                trArgs = scanExprList(that.args);;
                if (now instanceof JCIdent &&  ((JCIdent)now).sym instanceof MethodSymbol) {

                    calleeMethodSym = (MethodSymbol)((JCIdent)now).sym;
                    //                if (msym.isStatic()) obj = null;
                    //                else obj = currentThisId;
                } else if (now instanceof JCFieldAccess &&  ((JCFieldAccess)now).sym instanceof MethodSymbol) {

                    calleeMethodSym = (MethodSymbol)((JCFieldAccess)now).sym;
                    //                if (msym.isStatic()) obj = null;
                    //                else obj = currentThisId;

                } else { calleeMethodSym=null; } // FIXME - this shouldn't really happen - there is a mis translation in creating makeTYPE expressions

                trExpr = M.at(that.pos()).Apply(typeargs,now,trArgs);
                trExpr.setType(that.type);
                trExpr.varargsElement = that.varargsElement;

            } else if (that.meth instanceof JCFieldAccess) {
                // FIXME - need assertions
                JCFieldAccess fa = (JCFieldAccess)that.meth;
                JCExpression sel = scanExpr(fa.selected);
                List<JCExpression> typeargs = convert(that.typeargs);
                trArgs = scanExprList(that.args);

                JCFieldAccess meth = M.at(that.meth.pos).Select(sel, fa.name);
                meth.sym = fa.sym;
                meth.type = fa.type;
                calleeMethodSym = (MethodSymbol)fa.sym;
//                if (fa instanceof JCIdent &&  ((JCIdent)fa).sym instanceof MethodSymbol) {
//                    msym = (MethodSymbol)((JCIdent)fa).sym;
//                } else if (fa instanceof JCFieldAccess &&  ((JCFieldAccess)fa).sym instanceof MethodSymbol) {
//                    msym = (MethodSymbol)((JCFieldAccess)fa).sym;
//                } else { msym=null; obj = null; } // FIXME - this shouldn't really happen - there is a mis translation in creating makeTYPE expressions
                
                trExpr = M.at(that.pos()).Apply(typeargs,meth,trArgs);
                trExpr.setType(that.type);
                trExpr.varargsElement = that.varargsElement; // a Type
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
                result = eresult = treeutils.trueLit;
                return;
            }
            
            boolean isVoid = ((Type.MethodType)calleeMethodSym.type).restype.tag == TypeTags.VOID;
            

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
            

            JmlMethodSpecs calleeSpecs = specs.getDenestedSpecs(calleeMethodSym);
            if (calleeSpecs == null) {
                // This happens for a binary class with no specs for the given method.
                //log.noticeWriter.println("NO SPECS FOR METHOD CALL(A) " + sym.owner + "." + sym);
                calleeSpecs = JmlSpecs.defaultSpecs(that.pos).cases;
            } 

            java.util.List<JCExpression> preExpressions = new LinkedList<JCExpression>();
            
            if (calleeSpecs.decl != null) {
                paramActuals = new HashMap<Symbol,JCExpression>();
                Iterator<JCVariableDecl> iter = calleeSpecs.decl.params.iterator();
                for (JCExpression arg: trArgs) {
                    paramActuals.put(iter.next().sym, arg);
                }

                if (!calleeSpecs.cases.isEmpty()) {
                    // For each specification case, we accumulate the precondition
                    // and we create a block that checks the assignable statements
                    
                    // FIXME - invariants unless helper

                    JCExpression combinedPre = treeutils.falseLit;
                    JmlMethodClause mc = null;
                    pushBlock();
                    for (JmlSpecificationCase cs : calleeSpecs.cases) {
                        JCExpression pre = treeutils.trueLit;
                        for (JmlMethodClause clause : cs.clauses) {
                            try {
                                switch (clause.token) {
                                    case REQUIRES:
                                        if (mc == null) mc = clause;
                                        JCExpression e = scanJML(((JmlMethodClauseExpr)clause).expression,pre,false);
                                        pre = pre == treeutils.trueLit ? e : treeutils.makeAnd(pre.pos, pre, e);
                                        break;
                                    default:
                                }
                            } catch (JmlNotImplementedException e) {
                                notImplemented("requires clause containing ",e);
                            }
                        }
                        preExpressions.add(pre); // Add to the list of spec cases, in order of declaration
                        combinedPre = combinedPre == treeutils.falseLit ? pre : treeutils.makeOr(combinedPre.pos, combinedPre, pre);
                        pushBlock();
                        boolean anyAssignableClauses = false;
                        for (JmlMethodClause clause : cs.clauses) {
                            // We iterate over each storeref item in each assignable clause
                            // of each specification case - for each item we check
                            // that assigning to it (under the appropriate preconditions)
                            // is allowed by each of the specification cases of the caller specs.
                            try {
                                switch (clause.token) {
                                    case ASSIGNABLE:
                                        List<JCExpression> storerefs = ((JmlMethodClauseStoreRef)clause).list;
                                        for (JCExpression item: storerefs) {
                                            checkAgainstCallerSpecs(scanJML(item),pre);
                                        }
                                        anyAssignableClauses = true;
                                        break;
                                    default:
                                }
                            } catch (JmlNotImplementedException e) {
                                notImplemented("assignable clause containing ",e);
                            }
                        }
                        if (!anyAssignableClauses) {
                            // If there are no assignable clauses in the spec case,
                            // the default is \\everything
                            checkAgainstCallerSpecs(M.at(cs.pos()).JmlStoreRefKeyword(JmlToken.BSEVERYTHING),pre);
                        }
                        JCBlock bl = popBlock(0,cs.pos);
                        addStat( M.at(cs.pos()).If(pre, bl, null) );
                    }
                    if (mc != null) addAssert(that.pos(),Label.PRECONDITION,combinedPre,currentStatements,
                            mc.pos(),mc.source());
                    addStat( popBlock(0,Position.NOPOS) );
                }
            }
            
            JCIdent result = null;
            if (rac) {
                if (isVoid) {
                    addStat( M.at(that.pos()).Exec(trExpr) );
                    resultSym = null;
                } else {
                    result = newTemp(trExpr);
                    resultSym = result.sym;
                }
            }
            if (esc) {
                addStat( comment(that) );
            }
            
            eresult = result;

            if (!calleeSpecs.cases.isEmpty()) {
                paramActuals = new HashMap<Symbol,JCExpression>();
                Iterator<JCVariableDecl> iter = calleeSpecs.decl.params.iterator();
                for (JCExpression arg: trArgs) {
                    paramActuals.put(iter.next().sym, arg);
                }
                    // FIXME - we should set condition
                pushBlock();
                for (JmlSpecificationCase cs : calleeSpecs.cases) {
                    JCExpression pre = preExpressions.remove(0);
                    pushBlock();
                    condition = pre; // FIXME - is this right? what about the havoc statement?
                    for (JmlMethodClause clause : cs.clauses) {
                        try {
                            switch (clause.token) {
                                case REQUIRES: 
                                    break;
                                case ENSURES:
                                    JCExpression e = scanJML(((JmlMethodClauseExpr)clause).expression, condition, true);
                                    addAssert(that.pos(),Label.POSTCONDITION,e,currentStatements,clause.pos(),clause.sourcefile);
                                    break;
                                case ASSIGNABLE:
                                    if (esc) {
                                        JCStatement havoc = M.at(clause.pos).JmlHavocStatement(
                                                scanJML(((JmlMethodClauseStoreRef)clause).list));
                                        addStat(havoc);
                                    }
                                    break;
                                default:
                                    // FIXME - implement others
                                    break;
                            }
                        } catch (JmlNotImplementedException e) {
                            notImplemented(clause.token.internedName() + " clause containing ",e);
                        }

                    }
                    JCBlock b = popBlock(0,cs.pos+1);
                    // The +1 is so that the position of this if statement
                    // and hence the names of the BRANCHT and BRANCHE variables
                    // is different from the if prior to the apply
                    addStat( M.at(cs.pos+1).If(pre,b,null) );
                }
                
                // FIXME - invariants unless helper

                addStat( popBlock(0,Position.NOPOS) );
                // FIXME - the source must be handled properly

            }
        
        } finally {
            paramActuals = savedParamActuals;
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
//        e.setType(that.type);
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

        // FIXME - need to check definedness by testing preconditions when translatingJML

        ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
        for (JCExpression arg: that.args) {
            args.add(scanExpr(arg));
        }
        // FIXME - need to call the constructor; need an assertion about the type of the result; about allocation time

        
        if (!esc || translatingJML) {
            // FIXME - copy the rest of the stuff
            JCNewClass expr = M.at(that.pos()).NewClass(that.encl, that.typeargs, that.clazz, args.toList(), that.def);
            expr.constructor = that.constructor;
            expr.constructorType = that.constructorType;
            expr.varargsElement = that.varargsElement;
            expr.setType(that.type);
            result = eresult =(!translatingJML && (rac || esc)) ? newTemp(expr) : expr;
        } else {
            JCVariableDecl id = treeutils.makeVarDef(that.type,names.fromString(Strings.newObjectVarString + that.pos), null, 0);
            addStat(id);
            result = eresult = treeutils.makeIdent(that.pos, id.sym);
            addAssume(that.pos(),Label.NULL_CHECK,treeutils.makeNeqObject(that.pos, eresult, treeutils.nulllit), currentStatements);
        }
    }

    // OK
    @Override
    public void visitNewArray(JCNewArray that) {
        // Note that a JCNewArray can be the full new array expression: new Type[]{...}
        // But in a multi-dimensional initializer, each nested {...} is itself
        // a JCNewArray, though now with a null elemtype. 

        // FIXME - need to check definedness by testing preconditions when translatingJML

        ListBuffer<JCExpression> dims = new ListBuffer<JCExpression>();
        for (JCExpression dim: that.dims) {
            dims.add(scanExpr(dim));
        }
        
        ListBuffer<JCExpression> elems = new ListBuffer<JCExpression>();
        if (that.elems != null) {
            for (JCExpression elem: that.elems) {
                elems.add(scanExpr(elem));
            }
        } else {
            elems = null;
        }

        // FIXME - this will end up with new array expressions in translated JML for esc???
        
        if (!esc || translatingJML) {
            // This will create a fully-qualified version of the type name
            JCExpression elemtype = that.elemtype == null ? null : treeutils.makeType(that.elemtype.pos, that.elemtype.type);
            result = eresult = M.at(that.pos()).NewArray(elemtype, dims.toList(), elems == null ? null: elems.toList()).setType(that.type);
            if (!translatingJML && !pureCopy) result = eresult =newTemp(eresult);
        } else {
            JCVariableDecl id = treeutils.makeVarDef(that.type,names.fromString(Strings.newArrayVarString + that.pos), null, 0);
            addStat(id);
            result = eresult = treeutils.makeIdent(that.pos, id.sym);
            addAssume(that.pos(),Label.NULL_CHECK,treeutils.makeNeqObject(that.pos, eresult, treeutils.nulllit), currentStatements);
            // FIXME - need assertions about size of array and about any known array elements; about allocation time
            // also about type of the array
        }
        
    }

    // OK
    @Override
    public void visitParens(JCParens that) {
        JCExpression arg = scanExpr(that.getExpression());
        result = eresult = M.at(that.pos()).Parens(arg).setType(that.type);
    }
    
    // FIXME - need endpos in the above, and presumably nearly everywhere else???
    
    // FIXME - check this; document this
    protected JCExpression addImplicitConversion(DiagnosticPosition pos, Type lhstype, JCExpression rhs) {
        if (types.isSameType(lhstype,rhs.type)) return rhs;
        if (lhstype.isPrimitive() && !rhs.type.isPrimitive()) {
            // int = Integer and the like
            eresult = newTemp(rhs.pos(), lhstype);
            // assert TValue(rhs) == eresult
            JCIdent id = M.Ident(names.fromString("intValue"));
            JCExpression e = treeutils.makeEquality(rhs.pos,
                    M.JmlMethodInvocation(id, List.<JCExpression>of(rhs)),
                    eresult);
            addAssume(rhs.pos(),Label.EXPLICIT_ASSUME,e,currentStatements); // FIXME - these EXPLICIT_ASSUME are not explicit - check others
        } else if (!lhstype.isPrimitive() && rhs.type.isPrimitive()) {
            // Integer = int and the like
            eresult = newTemp(rhs.pos(), lhstype);
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
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitAssign while translating JML: " + that.getClass());
            return;
        }
        if (pureCopy) {
            JCExpression lhs = scanExpr(that.lhs);
            JCExpression rhs = scanExpr(that.rhs);
            // FIXME - am not doing RAC for the checks implemented below - nonnull receiver, index out of range
            // nor for null assignment
            JCExpression assign = treeutils.makeAssign(that.pos,  lhs, rhs);
            result = eresult = assign;
            return;
        }
        if (that.lhs instanceof JCIdent) {
            JCIdent id = (JCIdent)that.lhs;
            JCExpression lhs = scanExpr(that.lhs);
            JCExpression rhs = scanExpr(that.rhs);
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
                    // FIXME - this is not necessarily the right pos
                    for (JmlMethodClause m : c.clauses) {
                        if (m.token == JmlToken.ASSIGNABLE) { pos = m.pos(); break; }
                    }
                    addAssert(that.pos(),Label.ASSIGNABLE,check,currentStatements,pos,c.sourcefile);
                }
            }
            
            addStat( treeutils.makeAssignStat(that.pos,  lhs, rhs) );
            result = eresult = lhs;
            
        } else if (that.lhs instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)(that.lhs);
            JCFieldAccess newfa;
            if (!fa.sym.isStatic()) {
                JCExpression obj = scanExpr(fa.selected);
                JCExpression e = treeutils.makeNeqObject(obj.pos, obj, treeutils.nulllit);
                addAssert(that.lhs.pos(), Label.POSSIBLY_NULL, e, currentStatements);
                newfa = treeutils.makeSelect(that.pos, obj, fa.sym);
            } else {
                // We must evaluate the fa.lhs if it is an expression and not a type,
                // even though the value is not used (and might even be null)
                if (!isATypeTree(fa.selected)) {
                    scan(fa.selected);
                }
                // If the field is static, substitute the type tree
                
                JCExpression obj = treeutils.makeType(fa.pos, fa.sym.owner.type);
                newfa = treeutils.makeSelect(that.pos, obj, fa.sym);
                
            }
            JCExpression rhs = scanExpr(that.rhs);
            if (specs.isNonNull(fa.sym,methodDecl.sym.enclClass())) {
                JCExpression e = treeutils.makeNeqObject(fa.pos, rhs, treeutils.nulllit);
                // FIXME - location of nnonnull declaration?
                addAssert(that.pos(), Label.POSSIBLY_NULL_ASSIGNMENT, e, currentStatements);
            }
            addStat( treeutils.makeAssignStat(that.pos, newfa, rhs) );
            result = eresult = newTemp(newfa);
               
        } else if (that.lhs instanceof JCArrayAccess) {
            // that.lhs.getPreferredPosition() is the position of the [ in 
            // the array access expression
            JCArrayAccess aa = (JCArrayAccess)(that.lhs);
            JCExpression array = scanExpr(aa.indexed);
            JCExpression e = treeutils.makeNeqObject(array.pos, array, treeutils.nulllit);
            addAssert(that.lhs.pos(), Label.POSSIBLY_NULL, e, currentStatements);

            JCExpression index = scanExpr(aa.index);
            e = treeutils.makeBinary(index.pos, JCTree.GE, index, treeutils.zero);
            addAssert(that.lhs.pos(), Label.POSSIBLY_NEGATIVEINDEX, e, currentStatements);
            JCFieldAccess newfa = M.at(array.pos).Select(array, syms.lengthVar.name);
            newfa.type = syms.intType;
            newfa.sym = syms.lengthVar;
            e = treeutils.makeBinary(index.pos, JCTree.LT, index, newfa);
            addAssert(that.lhs.pos(), Label.POSSIBLY_TOOLARGEINDEX, e, currentStatements);
            
            JCExpression rhs = scanExpr(that.rhs);
            JCArrayAccess lhs = new JmlBBArrayAccess(null,array,index);
            lhs.pos = aa.pos;
            lhs.type = aa.type;
            addStat( treeutils.makeAssignStat(that.pos,lhs,rhs) );
            result = eresult = newTemp(lhs);
            
        } else {
            error(that.pos,"An unknown kind of assignment seen in JmlAssertionAdder: " + that.lhs.getClass());
        }
    }
    
    // OK
    @Override
    public void visitAssignop(JCAssignOp that) {
        // FIXME - needs pureCopy
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitAssignop while translating JML: " + that.getClass());
            return;
        }
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
            
            lhs = scanned ? lhs : scanExpr(lhs); // This may no longer be a JCIdent
            rhs = scanned ? rhs : scanExpr(rhs);
            addBinaryChecks(that, op, lhs, rhs);

            rhs = treeutils.makeBinary(that.pos,op ,lhs,rhs);

            checkAssignable(methodDecl, lhs, that);

            // Note that we need to introduce the temporary since the rhs contains
            // identifiers that may be captured by the lhs.
            JCIdent id = newTemp(rhs);
            addStat(M.at(that.pos()).Exec(treeutils.makeAssign(that.pos, lhs, id))); // type not set
            if (lhs instanceof JCIdent) result = eresult =treeutils.makeIdent(lhs.pos,((JCIdent)lhs).sym);
            else {
                result = eresult =newTemp(lhs);
            }
            
        } else if (lhs instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)lhs;
            if (fa.sym.isStatic()) {
                // FIXME - if fa.selected is actually an expression, we need to evaluate and discard it
                JCExpression tree = treeutils.makeType(fa.selected.pos, fa.sym.owner.type);
                JCFieldAccess newfa = treeutils.makeSelect(fa.selected.pos, tree, fa.sym);
                newfa.name = fa.name;
                lhs = newfa;
                rhs = scanned ? rhs : scanExpr(rhs);
                
            } else {
                lhs = scanned ? fa.selected : scanExpr(fa.selected);
                JCExpression e = treeutils.makeNeqObject(lhs.pos, lhs, treeutils.nulllit);
                addAssert(that.pos(), Label.POSSIBLY_NULL, e, currentStatements);

                rhs = scanned ? rhs : scanExpr(rhs);
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
            result = eresult =lhs;
        } else if (lhs instanceof JCArrayAccess) {
            JCArrayAccess aa = (JCArrayAccess)lhs;
            JCExpression array = scanned ? aa.indexed : scanExpr(aa.indexed);
            JCExpression e = treeutils.makeNeqObject(array.pos, array, treeutils.nulllit);
            // FIXME - location of nnonnull declaration?
            addAssert(that.pos(), Label.POSSIBLY_NULL, e, currentStatements);

            JCExpression index = scanned ? aa.index: scanExpr(aa.index);
            e = treeutils.makeBinary(index.pos, JCTree.GE, index, treeutils.zero);
            addAssert(that.pos(), Label.POSSIBLY_NEGATIVEINDEX, e, currentStatements);
            JCFieldAccess newfa = M.at(array.pos).Select(array, syms.lengthVar.name);
            newfa.type = syms.intType;
            newfa.sym = syms.lengthVar;
            e = treeutils.makeBinary(index.pos, JCTree.LT, index, newfa);
            addAssert(that.pos(), Label.POSSIBLY_TOOLARGEINDEX, e, currentStatements);

            rhs = scanned ? rhs : scanExpr(rhs);
            lhs = new JmlBBArrayAccess(null,array,index);
            lhs.pos = aa.pos;
            lhs.type = aa.type;

            addBinaryChecks(that,op,lhs,rhs);
            checkAssignable(methodDecl, lhs, that);
            
            // Note that we need to introduce the temporary since the rhs contains
            // identifiers that will be captured by the lhs.
            rhs = treeutils.makeBinary(that.pos,op ,lhs,rhs);
            JCIdent id = newTemp(rhs);
            
            result = eresult =treeutils.makeAssign(that.pos, lhs, id);
        } else {
            error(that.pos,"Unexpected kind of AST in jmlAssertionAdder.visitAssignOp: " + that.getClass());
        }
    }

    /** This translates Java unary operations: ++ -- ! ~ - + */
    // OK
    @Override
    public void visitUnary(JCUnary that) {
        int tag = that.getTag();
        if (translatingJML || pureCopy) {
            JCExpression arg = scanExpr(that.getExpression());
            result = eresult = treeutils.makeUnary(that.pos,tag,that.getOperator(),arg);
        } else if (tag == JCTree.PREDEC) {
            JCAssignOp b = M.at(that.pos()).Assignop(JCTree.MINUS_ASG,that.getExpression(),treeutils.one);
            b.setType(that.type);
            visitAssignop(b);
            result = eresult; // FIXME - redundant?
            return;
        } else if (tag == JCTree.PREINC) {
            JCAssignOp b = M.at(that.pos()).Assignop(JCTree.PLUS_ASG,that.getExpression(),treeutils.one);
            b.setType(that.type);
            visitAssignop(b);
            result = eresult;
            return;
        } else if (tag == JCTree.POSTDEC){
            JCExpression arg = scanExpr(that.getExpression());
            JCIdent id = newTemp(arg);
            JCAssignOp b = M.at(that.pos()).Assignop(JCTree.MINUS_ASG,arg,treeutils.one);
            b.setType(that.type);
            visitAssignopHelper(b,true);
            result = eresult = id;
        } else if (tag == JCTree.POSTINC){
            JCExpression arg = scanExpr(that.getExpression());
            JCIdent id = newTemp(arg);
            JCAssignOp b = M.at(that.pos()).Assignop(JCTree.PLUS_ASG,arg,treeutils.one);
            b.setType(that.type);
            visitAssignopHelper(b,true);
            result = eresult = id;
        } else {
            JCExpression arg = scanExpr(that.getExpression());
            addUnaryChecks(that,tag,arg);
            JCExpression expr = treeutils.makeUnary(that.pos,tag,that.getOperator(),arg);
            result = eresult = newTemp(expr);
        }
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
    
    // FIXME - check that condition is never used when !(esc||rac)

    // OK
    @Override
    public void visitBinary(JCBinary that) {
        if (translatingJML || pureCopy) {
            JCExpression lhs = scanExpr(that.lhs);
            JCExpression rhs;
            int tag = that.getTag();
            if (tag == JCTree.AND) {
                JCExpression prev = condition;
                try {
                    condition = treeutils.makeAnd(that.lhs.pos, condition, lhs);
                    rhs = scanExpr(that.rhs);
                } finally {
                    condition = prev;
                }
            } else if (tag == JCTree.OR) { 
                JCExpression prev = condition;
                try {
                    condition = treeutils.makeAnd(that.lhs.pos, condition, treeutils.makeNot(that.lhs.pos,lhs));
                    rhs = scanExpr(that.rhs);
                } finally {
                    condition = prev;
                }
            } else if (tag == JCTree.DIV || tag == JCTree.MOD) {
                rhs = scanExpr(that.rhs);
                JCExpression nonzero = treeutils.makeBinary(that.pos, JCTree.NE, rhs, treeutils.makeIntLiteral(that.rhs.pos, 0));
                addAssert(that.pos(),Label.UNDEFINED_DIV0,treeutils.makeImplies(that.pos, condition, nonzero),currentStatements);
            } else {
                rhs = scanExpr(that.rhs);
//                JCExpression bin = treeutils.makeBinary(that.pos,that.getTag(),lhs,rhs);
//                ejmlresult = bin;
//                return;
            }
            // FIXME - add checks for numeric overflow - PLUS MINUS MUL - what about SL SR USR
            result = eresult = treeutils.makeBinary(that.pos,that.getTag(),lhs,rhs);
        } else {
            if (that.getTag() == JCTree.OR) {
                JCConditional cond = M.at(that.pos()).Conditional(that.lhs,treeutils.trueLit,that.rhs);
                cond.setType(that.type);
                visitConditional(cond);
                return;
            }
            if (that.getTag() == JCTree.AND) {
                JCConditional cond = M.at(that.pos()).Conditional(that.lhs,that.rhs,treeutils.falseLit);
                cond.setType(that.type);
                visitConditional(cond);
                return;
            }
            JCExpression lhs = scanExpr(that.getLeftOperand());
            JCExpression rhs = scanExpr(that.getRightOperand());
            addBinaryChecks(that,that.getTag(),lhs,rhs);
            JCBinary bin = treeutils.makeBinary(that.pos,that.getTag(),that.getOperator(),lhs,rhs);
            result = eresult = newTemp(bin);
        }
    }

    @Override
    public void visitTypeCast(JCTypeCast that) {
        JCExpression lhs = scanExpr(that.getExpression());
        JCTree type = that.getType();
        JCTree clazz = treeutils.makeType(that.pos, type.type);
        
        JCTypeCast e = M.at(that.pos()).TypeCast(clazz,lhs);
        e.setType(that.type);
        treeutils.copyEndPosition(e,that);
        // Check that expression is either null or the correct type
        JCExpression eqnull = treeutils.makeEqObject(that.pos,lhs,treeutils.makeNullLiteral(that.pos));

        // FIXME - need to adjust condition and check for undefinedness
        
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
                    addAssert(that.pos(),Label.POSSIBLY_BADCAST,cond,currentStatements,
                            lhs.type, clazz.type);
                }
                
            }
            
        }
        result = eresult = (translatingJML || pureCopy) ? e: newTemp(e);
    }

    /** This translates the instanceof operation */
    @Override
    public void visitTypeTest(JCInstanceOf that) {
        JCExpression lhs = scanExpr(that.getExpression());
        JCTree type = that.getType();
        JCTree clazz = treeutils.makeType(type.pos, type.type);
        
        // No checks needed - Java allows (null instanceof type)
        // The value is always false
        if (esc) {
            // FIXME - not yet implemented as an assertion
        }
        if (!esc) { // rac or nothing
            JCInstanceOf e = M.at(that.pos()).TypeTest(lhs,clazz);
            e.setType(that.type);
            treeutils.copyEndPosition(e,that);
            result = eresult = (translatingJML || pureCopy) ? e : newTemp(e);
        }
    }

    // OK
    @Override
    public void visitIndexed(JCArrayAccess that) {
        boolean addAsserts = esc || rac;

        JCExpression indexed = scanExpr(that.indexed);

        if (addAsserts) {
            JCExpression nonnull = treeutils.makeNeqObject(that.indexed.pos, indexed, 
                    treeutils.nulllit);
            if (translatingJML) {
                nonnull = treeutils.makeImplies(that.pos, condition, nonnull);
                addAssert(that.pos(),Label.UNDEFINED_NULL,nonnull,currentStatements);
            } else {
                addAssert(that.pos(),Label.POSSIBLY_NULL,nonnull,currentStatements);
            }
        }

        JCExpression index = scanExpr(that.index);
        if (addAsserts) {
            JCExpression compare = treeutils.makeBinary(that.index.pos, JCTree.LE, treeutils.zero, 
                    index);
            if (translatingJML) {
                compare = treeutils.makeImplies(that.pos, condition, compare);
                addAssert(that.pos(),Label.UNDEFINED_NEGATIVEINDEX,compare,currentStatements);
            } else {
                addAssert(that.pos(),Label.POSSIBLY_NEGATIVEINDEX,compare,currentStatements);
            }
        }
        
        JCExpression length = treeutils.makeLength(that.indexed.pos,indexed);
        if (addAsserts) {
            JCExpression compare = treeutils.makeBinary(that.pos, JCTree.LT, index, 
                    length);
            if (translatingJML) {
                compare = treeutils.makeImplies(that.pos, condition, compare);
                addAssert(that.pos(),Label.UNDEFINED_TOOLARGEINDEX,compare,currentStatements);
            } else {
                addAssert(that.pos(),Label.POSSIBLY_TOOLARGEINDEX,compare,currentStatements);
            }
        }

        //JCArrayAccess aa = M.at(that.pos()).Indexed(indexed,index);
        JmlBBArrayAccess aa = new JmlBBArrayAccess(null,indexed,index); // FIXME - switch to factory
        aa.pos = that.pos;
        aa.setType(that.type);
        
        result = eresult = (translatingJML || pureCopy) ? aa : newTemp(aa);
    }

    // OK
    @Override
    public void visitSelect(JCFieldAccess that) {
        JCExpression selected;
        if (that.sym.isStatic()) {
            // This is the type name, so the tree should be copied, but without inserting temporary assignments
            // makeType creates a fully-qualified name
            selected = treeutils.makeType(that.selected.pos,that.selected.type);
        } else {
            selected = scanExpr(that.selected);
            if (esc || rac) {
                JCExpression nonnull = treeutils.makeNeqObject(that.pos, selected, 
                        treeutils.nulllit);
                addAssert(that.pos(),
                        translatingJML? Label.UNDEFINED_NULL : Label.POSSIBLY_NULL,
                        nonnull,
                        currentStatements);
            }
        }
        JCFieldAccess fa = treeutils.makeSelect(that.pos,selected,that.sym);
        result = eresult = (translatingJML || pureCopy || fa.type.tag == TypeTags.PACKAGE || fa.type.tag == TypeTags.CLASS) ? fa : newTemp(fa);
    }
    
    // OK
    // FIXME - need to test this, document this
    @Override
    public void visitIdent(JCIdent that) {
        if (translatingJML) {
            // FIXME - do we need formal parameter lookup?
            JCVariableDecl decl;
            Symbol symToUse;
            if (isPostcondition && (decl=preparams.get(that.sym)) != null) { // FIXME - what is this?
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
                fa.setType(that.type);
                result = eresult =fa;
            } else {
                // local variable or a static class field - just leave it as 
                // an ident
                JCExpression actual = paramActuals == null ? null : paramActuals.get(symToUse);
                if (actual != null) {
                    result = eresult = actual;
                } else {
                    id = treeutils.makeIdent(that.pos, symToUse);
                    result = eresult = id;
                }
            }
            return;
        }
        JCIdent id = currentArgsMap.get(that.sym);
        if (id != null) {
            // If the symbol is in the currentArgsMap it is an argument and
            // may have been renamed
            id = treeutils.makeIdent(that.pos, id.sym);
            result = eresult =id;
           // The symbol is not an argument
        } else if (!(that.sym.owner instanceof Symbol.ClassSymbol)) {
            // local variable  - just leave it as 
            // an ident
            id = treeutils.makeIdent(that.pos, that.sym);
            result = eresult =id;

            // FIXME - can compare against symbols, or names?
        } else if (that.sym.name.toString().equals("this")) {
            // 'this' - leave it as it is
            id = treeutils.makeIdent(that.pos, that.sym);
            result = eresult =id;
        } else if (that.sym.name.toString().equals("super")) {
            // 'super' - leave it as it is
            id = treeutils.makeIdent(that.pos, that.sym);
            result = eresult =id;

        } else if (!that.sym.isStatic()) {
            // It is a non-static class field, so we prepend 'this'
            // FIXME - do we need to use the current this?
            id = treeutils.makeIdent(that.pos,classDecl.thisSymbol);
            JCFieldAccess fa = treeutils.makeSelect(that.pos,id,that.sym);
            result = eresult =fa;
        } else {
            // static class field - add the qualified name
            JCExpression typetree = treeutils.makeType(that.pos,that.sym.owner.type);
            JCFieldAccess fa = treeutils.makeSelect(that.pos,typetree,that.sym);
            result = eresult =fa;
        }
    }

    // OK
    @Override
    public void visitLiteral(JCLiteral that) {
        result = eresult = fullTranslation ? treeutils.makeDuplicateLiteral(that.pos, that) : that;
    }

    // OK
    @Override
    public void visitTypeIdent(JCPrimitiveTypeTree that) {
        // This is a simple primitive type
        eresult = that;
        if (fullTranslation) {
            eresult = M.at(that.pos()).TypeIdent(that.typetag).setType(that.type);
        }
        result = eresult;
    }

    @Override
    public void visitTypeArray(JCArrayTypeTree that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitTypeArray while translating JML: " + that.getClass());
            return;
        }
        error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitTypeArray: " + that.getClass());
    }

    @Override
    public void visitTypeApply(JCTypeApply that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitTypeApply while translating JML: " + that.getClass());
            return;
        }
        error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitTypeApply: " + that.getClass());
    }

    @Override
    public void visitTypeParameter(JCTypeParameter that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitTypeParameter while translating JML: " + that.getClass());
            return;
        }
        error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitTypeParameter: " + that.getClass());
    }

    @Override
    public void visitWildcard(JCWildcard that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitWildcard while translating JML: " + that.getClass());
            return;
        }
        error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitWildcard: " + that.getClass());
    }

    @Override
    public void visitTypeBoundKind(TypeBoundKind that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitTypeBoundKind while translating JML: " + that.getClass());
            return;
        }
        error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitTypeBoundKind: " + that.getClass());
    }

    @Override
    public void visitAnnotation(JCAnnotation that) {
        // Only needed for a full tree copy
        // A JCAnnotation is a kind of JCExpression
        if (fullTranslation) {
            // FIXME - is there a currentStatements to put the result of scanning into?
            JCTree aType = treeutils.makeType(that.annotationType.pos, that.annotationType.type);
            List<JCExpression> args = that.args; //scanexprlist(that.args);
            JCAnnotation a = M.at(that.pos()).Annotation(aType,args);
            a.setType(a.annotationType.type);
            treeutils.copyEndPosition(a,that);
            result = eresult = a;
        } else {
            result = eresult = that;
        }
    }

    @Override
    public void visitModifiers(JCModifiers that) {
        if (fullTranslation) {
            ListBuffer<JCAnnotation> annotations = new ListBuffer<JCAnnotation>();
            for (JCAnnotation a: that.annotations) {
                annotations.add((JCAnnotation)scanExpr(a));
            }
            JCModifiers mods = M.at(that.pos()).Modifiers(that.flags, annotations.toList());
            result = mods;
        } else {
            result = that;
        }
    }

    // OK
    @Override
    public void visitErroneous(JCErroneous that) {
        List<? extends JCTree> errs = fullTranslation ? scanCopy(that.errs) : that.errs;
        result = eresult = M.at(that.pos()).Erroneous(errs).setType(that.type);
    }

    @Override
    public void visitLetExpr(LetExpr that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitLetExpr while translating JML: " + that.getClass());
            return;
        }
        // TODO Auto-generated method stub
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitLetExpr: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlBinary(JmlBinary that) {
        if (!translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlBinary: " + that.getClass());
            return;
        }
        JCExpression lhs = scanExpr(that.lhs);
        JCExpression rhs,t;
        switch (that.op) {
            case IMPLIES:
                condition = treeutils.makeAnd(that.pos, condition, lhs);
                rhs = scanExpr(that.rhs);
                t = treeutils.makeNot(lhs.pos, lhs);
                t = treeutils.makeOr(that.pos, t, rhs);
                eresult = t;
                break;
                
            case EQUIVALENCE:
                rhs = scanExpr(that.rhs);
                t = treeutils.makeBinary(that.pos, JCTree.EQ, lhs, rhs);
                eresult = t;
                break;
                
            case INEQUIVALENCE:
                rhs = scanExpr(that.rhs);
                t = treeutils.makeBinary(that.pos, JCTree.NE, lhs, rhs);
                eresult = t;
                break;
                
            case REVERSE_IMPLIES:
                t = treeutils.makeNot(lhs.pos, lhs);
                condition = treeutils.makeAnd(that.pos, condition, t);
                rhs = scanExpr(that.rhs);
                rhs = treeutils.makeNot(that.rhs.pos, rhs);
                t = treeutils.makeOr(that.pos, lhs, rhs);
                eresult = t;
                break;
                
             // FIXME - need <: operator
             case SUBTYPE_OF:   
             default:
                 error(that.pos,"Unexpected token in JmlAssertionAdder.visitJmlBinary: " + that.op);
                
        }
        result = eresult;
    }

    @Override
    public void visitJmlChoose(JmlChoose that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlChoose while translating JML: " + that.getClass());
            return;
        }
        // TODO Auto-generated method stub
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlChoose: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlClassDecl while translating JML: " + that.getClass());
            return;
        }
        JmlClassDecl prev = this.classDecl;
        ListBuffer<JCTree> prevlist = this.classDefs;
        try {
            this.classDecl = that;

            this.classDefs = new ListBuffer<JCTree>();
            for (JCTree t: that.defs) {
                scan(t);
            }

            List<JCTree> defs = this.classDefs.toList();
            // FIXME - replicate all the other AST nodes
            JmlClassDecl n = M.at(that.pos()).ClassDef(convert(that.mods),that.name,that.typarams,scanExpr(that.extending),scanExprList(that.implementing),defs);
            n.sym = that.sym;
            n.setType(that.type);
            n.superSymbol = that.superSymbol;
            n.thisSymbol = that.thisSymbol;
            n.toplevel = that.toplevel;  // FIXME - translate to new top level
            n.docComment = that.docComment;
            n.env = that.env; // FIXME - translate?
            n.specsDecls = that.specsDecls; // FIXME - these may be self-references - and I think there are now only one
            n.typeSpecs = that.typeSpecs; // not copied - FIXME? here and elsewhere
            n.typeSpecsCombined = that.typeSpecsCombined; // not copied
            result = n;
        } finally {
            this.classDecl = prev;
            this.classDefs = prevlist;
        }
    }

    // OK
    @Override
    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlCompilationUnit while translating JML: " + that.getClass());
            return;
        }
        // esc does not get here, but rac does
        if (esc) error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitCompilationUnit: " + that.getClass());
        List<JCTree> defs = convert(that.defs);
        // FIXME - replicate all the other AST nodes
        JmlCompilationUnit n = M.at(that.pos()).TopLevel(that.packageAnnotations,that.pid,defs);
        n.docComments = that.docComments;
        n.endPositions = that.endPositions;
        n.flags = that.flags;
        n.mode = that.mode;
        n.lineMap = that.lineMap;
        n.namedImportScope = that.namedImportScope;
        n.packge = that.packge;
        n.setType(that.type);
        n.parsedTopLevelModelTypes = that.parsedTopLevelModelTypes;
        n.sourcefile = that.sourcefile;
        n.starImportScope = that.starImportScope;
        n.specsCompilationUnit = that.specsCompilationUnit;
        n.specsTopLevelModelTypes = that.specsTopLevelModelTypes;
        result = n;
    }

    @Override
    public void visitJmlConstraintMethodSig(JmlConstraintMethodSig that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlConstraintMethodSig while translating JML: " + that.getClass());
            return;
        }
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlDoWhileLoop while translating JML: " + that.getClass());
            return;
        }
      
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

            JCExpression test = scanExpr(that.cond);
            JCExpression ne = treeutils.makeNot(that.cond.pos, test);

            //JmlStatementExpr as = addAssume(that.cond.pos(),Label.BRANCHT,ne,null);
            JCStatement br = M.at(that.cond.pos).Break(null);
            JCBlock bl = M.at(that.cond.pos).Block(0,List.<JCStatement>of(br));
            JCStatement ifs = M.at(that.cond.pos).If(ne,bl,null);
            ifs.type = Type.noType;
            addStat(ifs);

            //addAssume(that.cond.pos(),Label.BRANCHE,test,currentStatements);

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
            st.type = that.type;
            st.loopSpecs = null;
            addStat(st);
        }
    }

    // FIXME - need to do for rac
    @Override
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlEnhancedForLoop while translating JML: " + that.getClass());
            return;
        }
        // FIXME Need to add specifications; also index and values variables
        JCVariableDecl v = M.at(that.var.pos).VarDef(that.var.sym,null);
        v.setType(that.var.type);
        JCExpression e = scanExpr(that.expr);
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
        // result?
    }

    @Override
    public void visitJmlForLoop(JmlForLoop that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlForLoop while translating JML: " + that.getClass());
            return;
        }
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
                JCExpression e = scanExpr(that.cond);
                JCExpression notcond = treeutils.makeNot(e.pos,e);
                pushBlock();
                ///addAssume(e.pos(),Label.BRANCHT,notcond,currentStatements);
                addStat(M.Break(null));
                JCBlock thenBlock = popBlock(0,e.pos);
                pushBlock();
                //addAssume(e.pos(),Label.BRANCHE,e,currentStatements);
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
        // result?
    }

    @Override
    public void visitJmlGroupName(JmlGroupName that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlGroupName while translating JML: " + that.getClass());
            return;
        }
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    // OK - should never encounter this when processing method bodies
    @Override
    public void visitJmlImport(JmlImport that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlImport while translating JML: " + that.getClass());
            return;
        }
        // FIXME - need to rewrite qualid - might have a *; might have a method name
        result = M.at(that.pos()).Import(that.qualid, that.staticImport).setType(that.type);
    }

    // OK
    @Override
    public void visitJmlLblExpression(JmlLblExpression that) {
        if (!translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlLblExpression: " + that.getClass());
            return;
        }
        JCExpression expr = scanExpr(that.expression);
        if (pureCopy) {
            result = eresult = M.at(that.pos()).JmlLblExpression(that.token, that.label, expr).setType(that.type);
            return;
        }
        // The format of this string is important in interpreting it in JmlEsc
        String nm = Strings.labelVarString + that.token.internedName().substring(1) + "_" + that.label;
        JCIdent id = newTemp(nm,expr);
        labels.add(nm);
        result = eresult = id;
        if (rac) {
            JCExpression lit = treeutils.makeLit(that.getPreferredPosition(),syms.stringType,that.label.toString());
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
                JCFieldAccess m = findUtilsMethod(that.pos(),name);
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
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlMethodClauseCallable while translating JML: " + that.getClass());
            return;
        }
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlMethodClauseConditional while translating JML: " + that.getClass());
            return;
        }
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlMethodClauseDecl while translating JML: " + that.getClass());
            return;
        }
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlMethodClauseExpr while translating JML: " + that.getClass());
            return;
        }
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlMethodClauseGroup while translating JML: " + that.getClass());
            return;
        }
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlMethodClauseSignals while translating JML: " + that.getClass());
            return;
        }
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlMethodClauseSigOnly while translating JML: " + that.getClass());
            return;
        }
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    @Override
    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlMethodClauseStoreRef while translating JML: " + that.getClass());
            return;
        }
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlMethodDecl while translating JML: " + that.getClass());
            return;
        }
        // FIXME - implemente constructors - need super calls.
//        if (that.restype == null) { classDefs.add(that); return; } // FIXME - implement constructors
        JCBlock body = convertMethodBody(that,classDecl);
        // FIXME - replicate other ASTs - may be things that refer to parameter and method declarations
        JmlMethodDecl m = M.at(that.pos()).MethodDef(convert(that.mods), that.name, that.restype, that.typarams, that.params, scanExprList(that.thrown), body, scanExpr(that.defaultValue));
        m.sym = that.sym;
        m.setType(that.type);
        m._this = that._this;
        m.sourcefile = that.sourcefile;
        m.owner = that.owner; // FIXME - new class decl?
        m.docComment = that.docComment;
        m.cases = scanCopy(that.cases);
        m.methodSpecsCombined = that.methodSpecsCombined; // FIXME - copy?
        m.specsDecl = that.specsDecl; // FIXME - needs new reference
        classDefs.add(m);
        result = m;
    }

    // OK
    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        if (!translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlMethodInvocation: " + that.getClass());
            return;
        }
        if (pureCopy) {
            JmlMethodInvocation m = M.at(that.pos()).JmlMethodInvocation(that.token, scanExprList(that.args));
            m.setType(that.type);
            m.label = that.label;
            m.startpos = that.startpos;
            m.varargsElement = that.varargsElement;
            result = eresult = m;
            return;
        }
        switch (that.token) {
            case BSOLD:
            case BSPRE:
            {
                // FIXME _ this implementation is not adequate for checking postconditions with \old from callers
                // FIXME - also it does not work for rac at labelled locations
                if (rac) {
                    ListBuffer<JCStatement> saved = currentStatements;
                    try {
                        currentStatements = initialStatements;
                        JCExpression arg = scanExpr(that.args.get(0));
                        String s = "_JML___old_" + (++count); // FIXME - Put string in Strings
                        Name nm = names.fromString(s);
                        JCVariableDecl v = treeutils.makeVarDef(arg.type,nm,methodDecl.sym,arg);
                        v.mods.flags |= Flags.FINAL;
                        addStat(v);
                        JCIdent id = treeutils.makeIdent(arg.pos,v.sym);
                        eresult = id;
                    } finally {
                        currentStatements = saved;
                    }
                } else {
                    JCExpression m = scanExpr(that.meth);
                    JCExpression arg = scanExpr(that.args.get(0));
                    JmlMethodInvocation meth;
                    if (that.args.size() == 1) {
                        meth = M.JmlMethodInvocation(that.token,arg);
                    } else {
                        // The second argument is a label, not an expression
                        meth = M.JmlMethodInvocation(that.token,arg,that.args.get(1));
                    }
                    meth.setType(that.type);
                    meth.pos = that.pos;
                    meth.startpos = that.startpos;
                    meth.varargsElement = that.varargsElement;
                    meth.meth = m;
                    meth.label = that.label;
                    meth.typeargs = that.typeargs; // FIXME - do these need translating?
                    eresult = meth;
                }
            }
            break;
            
            case BSNONNULLELEMENTS :
            if (rac) {
                int n = that.args.size();
                if (n == 0) {
                    result = eresult = treeutils.trueLit;
                } else {
                    JCExpression conj = null;
                    for (JCExpression arg : that.args) {
                        JCExpression e = methodCallUtilsExpression(arg.pos(),"nonnullElementCheck",arg);
                        conj = conj == null? e :
                            treeutils.makeAnd(arg.pos, conj, e);
                    }
                    result = eresult = scanExpr(conj);
                }
            } else {
                throw new JmlNotImplementedException(that.pos(),that.token.internedName());
            }
            break;
            
            case BSTYPELC:
//            {
//                JCTree type = that.args.get(0);
//                result = eresult = treeutils.trType(that.pos, type);
//            }
            
            case BSTYPEOF :
            case BSELEMTYPE :
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
                throw new JmlNotImplementedException(that.pos(),that.token.internedName());

            default:
                Log.instance(context).error("esc.internal.error","Unknown token in JmlAssertionAdder: " + that.token.internedName());
                eresult = treeutils.trueLit; // FIXME - may not even be a boolean typed result
        }
        result = eresult;
    }

    @Override
    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        if (!pureCopy) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlMethodSpecs: " + that.getClass());
            return;
        }
        
        List<JmlSpecificationCase> cases = scanCopy(that.cases);
        JmlMethodSpecs ms = M.at(that.pos()).JmlMethodSpecs(cases);
        ms.setType(that.type);
        ms.decl = that.decl; // FIXME - copy
        ms.deSugared = that.deSugared; // FIXME - copy
        ms.forExampleCases = that.forExampleCases; // FIXME - copy
        ms.impliesThatCases = that.impliesThatCases; // FIXME - copy
        result = ms;
    }

    @Override
    public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlModelProgramStatement while translating JML: " + that.getClass());
            return;
        }
        // TODO Auto-generated method stub
        error(that.pos, "Unexpected visit call in JmlAssertionAdder.visitJmlModelProgramStatement: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        result = eresult =  M.at(that.pos()).JmlPrimitiveTypeTree(that.token).setType(that.type);
        // FIXME - for rac or esc need to do some translating
    }

    // OK
    @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        if (!translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlQuantifiedExpr: " + that.getClass());
            return;
        }
        if (that.racexpr != null) {
            result = eresult = scanExpr(that.racexpr);
        } else {
            log.note(that.pos(),"rac.not.implemented.quantified");
            result = eresult = treeutils.makeZeroEquivalentLit(that.pos,that.type);
        }
    }

    // OK
    @Override
    public void visitJmlSetComprehension(JmlSetComprehension that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlSetComprehension while translating JML: " + that.getClass());
            return;
        }
        // should be using jmlrewriter
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlSetComprehension: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlSingleton(JmlSingleton that) {
        if (!translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlSingleton: " + that.getClass());
            return;
        }
        switch (that.token) {
            case BSRESULT:
                if (resultSym == null) {
                    error(that.pos, "It appears that \\result is used where no return value is defined"); // FIXME - not an internal error
                } else {
                    eresult = treeutils.makeIdent(that.pos, resultSym);
                }
                break;

            case INFORMAL_COMMENT:
                eresult = treeutils.makeBooleanLiteral(that.pos,true);
                break;
                
            case BSEXCEPTION:
                if (exceptionSym == null) {
                    error(that.pos,"It appears that \\exception is used where no exception value is defined" ); // FIXME - not an internal error
                } else {
                    eresult = treeutils.makeIdent(that.pos,exceptionSym);
                }
                break;
//
//            case BSINDEX:
//            case BSVALUES:
//                if (that.info == null) {
//                    log.error(that.pos,"esc.internal.error","No loop index found for this use of " + that.token.internedName());
//                    result = null;
//                } else {
//                    result = newIdentUse((VarSymbol)that.info,that.pos);
//                }
//                break;
//            
//            case BSLOCKSET:
//            case BSSAME:
               

            case BSNOTSPECIFIED:
            case BSNOTHING:
            case BSEVERYTHING:
                error(that.pos, "Should not be attempting to translate this construct in JmlAssertion Adder's JML rewriter: " + that.token.internedName()); // FIXME - ???
                break;

            default:
                Log.instance(context).error(that.pos, "jml.unknown.construct",that.token.internedName(),"BasicBlocker.visitJmlSingleton");
            // FIXME - recovery possible?
                break;
        }
        result = eresult;
    }
    

    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlSpecificationCase while translating JML: " + that.getClass());
            return;
        }
        if (!pureCopy) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlSpecificationCase: " + that.getClass());
            return;
        }
        
        JmlSpecificationCase sc = M.at(that.pos()).JmlSpecificationCase(
                convert(that.modifiers),
                that.code,
                that.token,
                that.also,
                that.clauses);
        sc.sourcefile = that.sourcefile;
        sc.block = that.block == null ? null : convertBlock(that.block); // model program
        sc.setType(that.type);
        result = sc;
    }

    @Override
    public void visitJmlStatement(JmlStatement that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlStatement while translating JML: " + that.getClass());
            return;
        }
        result = null;
        switch (that.token) {
            case DEBUG:
                // FIXME - resolve what sort of constructs are actually allowed in a debug and set statement
                Set<String> keys = Utils.instance(context).commentKeys;
                if (!keys.contains("DEBUG")) return;
                //$FALL-THROUGH$
            case SET:
                JCStatement st = that.statement;
                JCExpression ex = ((JCExpressionStatement)st).expr;
                try {
                    if (ex instanceof JCAssign) {
                        JCAssign asg = (JCAssign)ex;
                        JCExpression lhs = scanJML(asg.lhs);
                        JCExpression rhs = scanJML(asg.rhs);
                        result = addStat (treeutils.makeAssignStat(st.pos, lhs, rhs));

                    } else if (ex instanceof JCAssignOp) {
                        JCAssignOp asg = (JCAssignOp)ex;
                        JCExpression lhs = scanJML(asg.lhs);
                        JCExpression rhs = scanJML(asg.rhs);
                        JCAssignOp asgop = M.at(asg.pos()).Assignop(asg.getTag(),lhs,rhs);
                        asgop.operator = asg.operator;
                        asgop.setType(asg.type);
                        result = addStat (treeutils.makeAssignStat(st.pos, lhs, rhs));

                    } else if (ex instanceof JCMethodInvocation) {
                        JCMethodInvocation m = (JCMethodInvocation)ex;
                        result = addStat( M.at(that.pos()).Exec(scanJML(m)) );
                        
                    } else {
                        String msg = "Unknown token in JmlAssertionAdder.visitJmlStatement: " + that.token.internedName();
                        error(that.pos, msg);
                    }
                } catch (JmlNotImplementedException e) {
                    notImplemented(that.token.internedName() + " statement containing ",e);
                    result = null;
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
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlStatementDecls while translating JML: " + that.getClass());
            return;
        }
        for (JCStatement stat: that.list) {
            stat.accept(this);
        }
        // FIXME - result = ?
    }

    // OK
    @Override
    public void visitJmlStatementExpr(JmlStatementExpr that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlStatementExpr while translating JML: " + that.getClass());
            return;
        }
        try {
          switch (that.token) {
            case ASSERT:
                addStat(comment(that));
                JCExpression e = scanJML(that.expression);
                result = addAssert(that.pos(),Label.EXPLICIT_ASSERT,e,currentStatements,null,null,that.optionalExpression);
                break;
            case ASSUME:
                addStat(comment(that));
                JCExpression ee = scanJML(that.expression);
                result = addAssume(that.pos(),Label.EXPLICIT_ASSUME,ee,currentStatements,null,null,that.optionalExpression);
                break;
            case COMMENT:
                JCExpression expr = fullTranslation ? scanJML(that.expression) : that.expression;
                {
                    JmlStatementExpr st = M.at(that.pos()).JmlExpressionStatement(that.token,that.label,expr);
                    st.setType(that.type);
                    st.associatedSource = that.associatedSource;
                    st.declPos = that.declPos;
                    st.optionalExpression = scanExpr(that.optionalExpression);
                    st.source = that.source;
                    result = addStat(st);
                }
                break;
            case UNREACHABLE:
                if (pureCopy) {
                    JmlStatementExpr st = M.at(that.pos()).JmlExpressionStatement(that.token,that.label,null);
                    st.setType(that.type);
                    st.associatedSource = that.associatedSource;
                    st.declPos = that.declPos;
                    st.optionalExpression = scanExpr(that.optionalExpression);
                    st.source = that.source;
                    result = addStat(st);
                } else {
                    addStat(comment(that));
                    result = addAssert(that.pos(),Label.UNREACHABLE,treeutils.falseLit,currentStatements);
                }
                break;
            case HENCE_BY:
                // FIXME - implement HENCE_BY
                notImplemented(that.pos(),"hence_by statement");
                result = null;
                break;
            default:
                error(that.pos,"Unknown token type in JmlAssertionAdder.visitJmlStatementExpr: " + that.token.internedName());
                break;
          }
        } catch (JmlNotImplementedException e) {
            notImplemented(that.token.internedName() + " statement containing ",e);
        }
    }

    // OK
    @Override
    public void visitJmlStatementHavoc(JmlStatementHavoc that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlStatementHavoc while translating JML: " + that.getClass());
            return;
        }
        try {
            result = addStat( M.at(that.pos()).JmlHavocStatement(scanJML(that.storerefs)).setType(that.type));
        } catch (JmlNotImplementedException e) {
            notImplemented("havoc statement containing ",e);
        }
    }

    @Override
    public void visitJmlStatementLoop(JmlStatementLoop that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlStatementLoop while translating JML: " + that.getClass());
            return;
        }
        // TODO Auto-generated method stub
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlStatementLoop: " + that.getClass());
    }

    @Override
    public void visitJmlStatementSpec(JmlStatementSpec that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlStatementSpec while translating JML: " + that.getClass());
            return;
        }
        // TODO Auto-generated method stub
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlStatementSpec: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlStoreRefArrayRange while translating JML: " + that.getClass());
            return;
        }
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlStoreRefArrayRange: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        if (!translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlStoreRefKeyword: " + that.getClass());
            return;
        }
        eresult = that;
        if (fullTranslation) eresult = M.at(that.pos()).JmlStoreRefKeyword(that.token);
        result = eresult;
    }

    // OK
    @Override
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlStoreRefListExpression while translating JML: " + that.getClass());
            return;
        }
        error(that.pos,"Unexpected visit call in JmlAssertionAdder.visitJmlStoreRefListExpression: " + that.getClass());
    }

    // OK
    @Override
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        // This is only called when making a direct copy of the AST
        if (!pureCopy) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlTypeClauseConditional: " + that.getClass());
            return;
        }
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JCExpression expr = scanExpr(that.expression);
        JCIdent id = treeutils.makeIdent(that.identifier.pos,that.identifier.sym);
        JmlTypeClauseConditional cl = M.at(that.pos()).JmlTypeClauseConditional(mods, that.token, id, expr);
        cl.setType(that.type);
        cl.source = that.source;
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        // This is only called when making a direct copy of the AST
        if (!pureCopy) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlTypeClauseConstraint: " + that.getClass());
            return;
        }
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JCExpression expr = scanExpr(that.expression);
        JmlTypeClauseConstraint cl = M.at(that.pos()).JmlTypeClauseConstraint(mods, expr, convert(that.sigs));
        cl.setType(that.type);
        cl.source = that.source;
        cl.token = that.token;
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        // This is only called when making a direct copy of the AST
        // FIXME - copy decl
        if (!pureCopy) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlTypeClauseDecl: " + that.getClass());
            return;
        }
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JmlTypeClauseDecl cl = M.at(that.pos()).JmlTypeClauseDecl(that.decl);
        cl.setType(that.type);
        cl.source = that.source;
        cl.modifiers = mods;
        cl.token = that.token;
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        // This is only called when making a direct copy of the AST
        if (!pureCopy) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlTypeClauseExpr: " + that.getClass());
            return;
        }
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JCExpression expr = scanExpr(that.expression);
        JmlTypeClauseExpr cl = M.at(that.pos()).JmlTypeClauseExpr(mods, that.token, expr);
        cl.setType(that.type);
        cl.source = that.source;
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        // This is only called when making a direct copy of the AST
        
        if (!pureCopy) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlTypeClauseIn: " + that.getClass());
            return;
        }
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JmlTypeClauseIn cl = M.at(that.pos()).JmlTypeClauseIn(convert(that.list));
        cl.modifiers = mods;
        cl.setType(that.type);
        cl.source = that.source;
        cl.token = that.token;
        cl.parentVar = that.parentVar; // FIXME - need to convert declaration
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        // This is only called when making a direct copy of the AST
        // FIXME - copy specs; make sure this is a direct copy of the specs
        if (!pureCopy) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlTypeClauseInitializer: " + that.getClass());
            return;
        }
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JmlTypeClauseInitializer cl = M.at(that.pos()).JmlTypeClauseInitializer(that.token);
        cl.modifiers = mods;
        cl.specs = that.specs; // FIXME - copy
        cl.setType(that.type);
        cl.source = that.source;
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        // This is only called when making a direct copy of the AST
        if (!pureCopy) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlTypeClauseMaps: " + that.getClass());
            return;
        }
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JCExpression expr = scanExpr(that.expression);
        JmlTypeClauseMaps cl = M.at(that.pos()).JmlTypeClauseMaps(expr,convert(that.list));
        cl.modifiers = mods;
        cl.setType(that.type);
        cl.source = that.source;
        cl.token = that.token;
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        // This is only called when making a direct copy of the AST
        // FIXME - copy list; make sure this is a direct copy of the list
        if (!pureCopy) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlTypeClauseMonitorsFor: " + that.getClass());
            return;
        }
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JCIdent id = treeutils.makeIdent(that.identifier.pos,that.identifier.sym);
        JmlTypeClauseMonitorsFor cl = M.at(that.pos()).JmlTypeClauseMonitorsFor(mods, id, that.list);
        cl.setType(that.type);
        cl.source = that.source;
        cl.token = that.token;
        classDefs.add(cl);
        result = cl;
    }

    // OK
    @Override
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        // This is only called when making a direct copy of the AST
        if (!pureCopy) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlTypeClauseRepresents: " + that.getClass());
            return;
        }
        JCModifiers mods = fullTranslation ? convert(that.modifiers) : that.modifiers;
        JCIdent id = treeutils.makeIdent(that.ident.pos,null); // that.ident.sym); // FIXME - is the ident a JCIdent or an expression?
        JCExpression expr = scanExpr(that.expression);
        JmlTypeClauseRepresents cl = M.at(that.pos()).JmlTypeClauseRepresents(mods, id, that.suchThat, expr);
        cl.setType(that.type);
        cl.source = that.source;
        cl.token = that.token;
        classDefs.add(cl);
        result = cl;
    }

    @Override
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlVariableDecl while translating JML: " + that.getClass());
            return;
        }
        if (JmlAttr.instance(context).isGhost(that.mods)) {
            try {
                JCExpression init = null;
                if (currentStatements == null) pushBlock();
                
                init = scanJML(that.init);
                // FIXME - implicit conversion?
                JmlVariableDecl stat = M.at(that.pos()).VarDef(that.sym,init);
                JCStatement nnStatement = null;
                JCExpression nn = null;
                if (init != null && !init.type.isPrimitive() && specs.isNonNull(that.sym,that.sym.enclClass())) {
                    nn = treeutils.makeNeqObject(init.pos, init, treeutils.nulllit);
                    if (init instanceof JCLiteral) {
                        // FIXME - potential optimizations, but they need testing, particularly the second one
                        if (init.type.tag == TypeTags.BOT) nn = treeutils.falseLit;
                        else if (init.type.tag == TypeTags.CLASS) nn = treeutils.trueLit;
                    } 
                    // FIXME - should have an associated position in assert
                }
                if (statementStack.get(0) == null) {
                    if (nn != null) addAssert(that.pos(),Label.POSSIBLY_NULL_INITIALIZATION,nn,currentStatements,that.name);
                    addStat(stat);
                    JCBlock bl = popBlock(0,that.pos);
                    classDefs.add(bl);
                } else {
                    if (nn != null) addAssert(that.pos(),Label.POSSIBLY_NULL_INITIALIZATION,nn,currentStatements,that.name);
                    addStat(stat);
                }
                result = stat;
            } catch (JmlNotImplementedException e) {
                notImplemented("ghost declaration containing ",e);
            }
        } else if (that.init == null) {
            JmlVariableDecl stat = M.at(that.pos()).VarDef(that.sym,that.init);
            // type, vartype, sym, name, mods, init are filled in
            stat.mods = that.mods;
            stat.sourcefile = that.sourcefile;
            stat.docComment = that.docComment;
            stat.fieldSpecs = that.fieldSpecs;
            stat.fieldSpecsCombined = that.fieldSpecsCombined;
            stat.specsDecl = that.specsDecl;
            if (currentStatements == null) classDefs.add(stat);
            else addStat(stat);
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
            
            JCExpression init = scanExpr(that.init);
            if (init != null) init = addImplicitConversion(init.pos(),that.type,init);

            JCExpression nn = null;
            if (init != null && !init.type.isPrimitive() && specs.isNonNull(that.sym,that.sym.enclClass())) {
                nn = treeutils.makeNeqObject(init.pos, init, treeutils.nulllit);
                if (init instanceof JCLiteral) {
                    // FIXME - potential optimizations, but they need testing, particularly the second one
                    if (init.type.tag == TypeTags.BOT) nn = treeutils.falseLit;
                    else if (init.type.tag == TypeTags.CLASS) nn = treeutils.trueLit;
                } 
                // FIXME - should have an associated position
            }
            

            if (statementStack.get(0) == null) {
                // Class definition
                if (currentStatements.isEmpty() && nn == null) {
                    // Just a simple initialization since there is no nonnull check
                    // and the init expression did not create any new statements
                    popBlock(0,0); // Nothing present - just ignore the empty block
                    stat.init = init;
                    classDefs.add(stat);
                } else {
                    // Create a initializer block
                    if (nn != null) addAssert(that.pos(),Label.POSSIBLY_NULL_INITIALIZATION,nn,currentStatements,that.name);
                    addStat(treeutils.makeAssignStat(that.pos, treeutils.makeIdent(that.pos, stat.sym), init));
                    JCBlock bl = popBlock(that.mods.flags & Flags.STATIC,that.pos);
                    this.classDefs.add(stat);
                    classDefs.add(bl);
                }
            } else {
                // Regular method body
                JCBlock bl = popBlock(0,that.pos);
                currentStatements.addAll(bl.stats);
                if (nn != null) addAssert(that.pos(),Label.POSSIBLY_NULL_INITIALIZATION,nn,currentStatements,that.name);
                stat.init = init;
                addStat(stat);
            }
            result = stat;
        }
    }

    @Override
    public void visitJmlWhileLoop(JmlWhileLoop that) {
        if (translatingJML) {
            error(that.pos,"Unexpected call of JmlAssertionAdder.visitJmlWhileLoop while translating JML: " + that.getClass());
            return;
        }
        // FIXME - need to add specs; 
        if (esc) {
            pushBlock();

            // Now havoc any variables changed in the loop
            ListBuffer<JCExpression> targets = TargetFinder.findVars(that.getStatement(),null);
            TargetFinder.findVars(that.getCondition(),targets);
            // synthesize a modifies list
            JmlStatementHavoc st = M.at(that.body.pos).JmlHavocStatement(targets.toList());
            addStat(st);

            JCExpression test = scanExpr(that.cond);
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
            //JmlStatementExpr as = addAssume(pos,Label.BRANCHT,ne,null);
            JCStatement br = M.at(pos).Break(null);
            JCBlock bl = M.at(pos).Block(0,List.<JCStatement>of(br));
            JCStatement ifs = M.at(pos).If(ne,bl,null);
            ifs.type = Type.noType;
            addStat(ifs);

            //addAssume(that.cond.pos(),Label.BRANCHE,test,currentStatements);

            scan(that.body);



            bl = popBlock(0,that.cond.pos);
            JmlWhileLoop stw = M.at(that.pos()).WhileLoop(treeutils.trueLit, bl);
            stw.setType(that.type);
            stw.loopSpecs = null;
            result = addStat(stw);
        }

        if (rac) {
            // FIXME - need to translate the conditional - be careful of labels on the loop
            JCStatement bl = translateIntoBlock(that.body.pos, that.body);
            JmlWhileLoop st = M.at(that.pos()).WhileLoop(that.cond, bl);
            st.setType(that.type);
            st.loopSpecs = null;
            result = addStat(st);
        }
// TODO- optimization - if there are no extra statements produced, we can keep the (translated) expression in the while condition        
//        else {
        // Something like this;
//            addStat(M.at(that.pos()).WhileLoop(e, b));
//        }
    }
}

