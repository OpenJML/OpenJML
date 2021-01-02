/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;


import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.BasicProgram;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;

import static org.jmlspecs.openjml.ext.FunctionLikeExpressions.*;
import static org.jmlspecs.openjml.ext.FrameExpressions.*;
import static org.jmlspecs.openjml.ext.MiscExpressions.*;
import static org.jmlspecs.openjml.ext.StateExpressions.*;
import static org.jmlspecs.openjml.ext.SingletonExpressions.*;
import static org.jmlspecs.openjml.ext.StatementExprExtensions.*;
import static org.jmlspecs.openjml.ext.ReachableStatement.*;
import static org.jmlspecs.openjml.ext.MiscExtensions.*;
import static org.jmlspecs.openjml.ext.Functional.*;
import org.jmlspecs.openjml.ext.EndStatement;
import org.jmlspecs.openjml.ext.Operators;
import org.jmlspecs.openjml.ext.QuantifiedExpressions;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCArrayTypeTree;
import com.sun.tools.javac.tree.JCTree.JCAssert;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCAssignOp;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCConditional;
import com.sun.tools.javac.tree.JCTree.JCErroneous;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
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
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCSynchronized;
import com.sun.tools.javac.tree.JCTree.JCTypeApply;
import com.sun.tools.javac.tree.JCTree.JCTypeCast;
import com.sun.tools.javac.tree.JCTree.JCTypeParameter;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.JCWildcard;
import com.sun.tools.javac.tree.JCTree.LetExpr;
import com.sun.tools.javac.tree.JCTree.TypeBoundKind;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;

/** This class converts a Java AST into basic block form (including DSA and
 * passification). All Java (and JML) statements are rewritten into assume and
 * assert statements, with basic blocks being created to represent the control
 * flow. In addition, note the following:
 * <UL>
 * <LI> No assertions to represent Java or JML semantics are added, except for those
 * needed to convert control flow into basic blocks
 * <LI> The name field of JCIdent nodes are rewritten in place to
 * convert the program to single-assignment form. Note that this means that 
 * expressions and subexpressions of the input tree may not be shared across statements or 
 * within expressions, at least where the sharing would mix different incarnations
 * of the variable.
 * <LI> The JML \\old and \\pre expressions are recognized and translated to use
 * the appropriate single-assignment identifiers.
 * </UL>
 * <P>
 * The input tree must consist of (FIXME)
 * <UL>
 * <LI> A valid Java program (with any Java constructs):
 * <UL>
 * <LI> assignOp expressions are not allowed
 * <LI> Java let expressions are allowed
 * </UL>
 * <LI> JML assume, assert, comment statements, with JML expressions.
 * <LI> The JML expressions contain only
 * <UL>
 * <LI> Java operators (omitting assignment-operator combinations)
 * <LI> JML quantified expressions
 * <LI> set comprehension expressions
 * <LI> \\old and \\pre expressions
 * <LI> [ FIXME ??? JML type literals, subtype operations, method calls in specs?]
 * </UL
 * </UL>
 *
 * <P>
 * Basic block output form contains only this subset of AST nodes: (FIXME)
 * <UL>
 * <LI> JML assume, assert, comment statements
 * <LI> JCLiteral - numeric (all of them? FIXME), null, boolean, class (String?, character?)
 * <LI> JCIdent
 * <LI> JCParens
 * <LI> JCUnary
 * <LI> JCBinary
 * <LI> JCConditional
 * <LI> JmlBBFieldAccess
 * <LI> JmlBBArrayAccess
 * <LI> JmlBBFieldAssign
 * <LI> JmlBBArrayAssign
 * <LI> JCMethodInvocation - only pure methods within specifications
 * <LI> JmlMethodInvocation - old, typeof
 * <LI> JmlQuantifiedExpr - only forall and exists
 * <LI> JCTypeCast - but the clazz element now has a JCLiteral (which is a type literal)
 * <LI> [JCInstanceOf - not present - use a typeof and a subtype operation]
 * </UL>
 * <P>
 * FIXME - comment on the special use of comment statements for tracing
 * <P>
 * @author David Cok
 */
public class BasicBlocker2 extends BasicBlockerParent<BasicProgram.BasicBlock,BasicProgram>  {

    /** Creates an empty new BasicProgram */
    @Override
    public BasicProgram newProgram(Context context) {
        return new BasicProgram(context);
    }
    
    /** Creates an empty new BasicBlock */
    @Override
    public BasicProgram.BasicBlock newBlock(JCIdent id){
        return new BasicProgram.BasicBlock(id);
    }
    
    // THE FOLLOWING ARE ALL FIXED STRINGS
    
    //-----------------------------------------------------------------
    // Names for a bunch of synthetic variables 
    
    /** Standard name for the variable that represents the heap (which excludes local variables) */
    public static final @NonNull String HEAP_VAR = "_heap__"; // FIXME cf JmlAssertionAdder for same string
    
    //-----------------------------------------------------------------
    // Names for various basic blocks
    
    /** Standard name for the block that starts the body */
    public static final @NonNull String BODY_BLOCK_NAME = "bodyBegin";
    
    /** Standard name for the starting block of the program (just has the preconditions) */
    public static final @NonNull String START_BLOCK_NAME = "Start";
    
    // Other somewhat arbitrary identifier names or parts of names
    
    /** Prefix for the names of the N-dimensional arrays used to model Java's heap-based arrays */
    public static final @NonNull String ARRAY_BASE_NAME = "arrays_";
    
    // THE FOLLOWING FIELDS ARE EXPECTED TO BE CONSTANT FOR THE LIFE OF THE OBJECT
    // They are either initialized in the constructor or initialized on first use
    
    /** General utilities */
    final protected @NonNull Utils utils;
    
    /** The factory used to create AST nodes, initialized in the constructor */
    final protected JmlTree.@NonNull Maker factory;

    // Caution - the following are handy, but they are shared, so they won't
    // have proper position information - which is OK for esc at this point
    
    /** Holds an AST node for a boolean true literal, initialized in the constructor */
    final protected @NonNull JCLiteral trueLiteral;
    
    /** Holds an AST node for a boolean false literal, initialized in the constructor */
    final protected @NonNull JCLiteral falseLiteral;
    
    /** Identifier of a synthesized object field holding the length of an array object, initialized in the constructor */
    final protected @NonNull JCIdent lengthIdent;

    /** Symbol of a synthesized object field holding the length of an array object, initialized in the constructor */
    final protected @NonNull VarSymbol lengthSym;
    
    // THE FOLLOWING FIELDS ARE USED IN THE COURSE OF DOING THE WORK OF CONVERTING
    // TO BASIC BLOCKS.  They are fields of the class because they need to be
    // shared across the visitor methods.
    
    /** Place to put new definitions, such as the equalities defining auxiliary variables */
    protected List<BasicProgram.Definition> newdefs;
    
    /** Place to put new background assertions, such as axioms and class predicates */
    protected List<JCExpression> background;
    
    protected Set<Symbol> methodsSeen;
    
    /** This is an integer that rises monotonically on each use and is used
     * to make sure new identifiers are unique.
     */
    protected int unique;
    
    /** This map records the map from the input JCTree elements to the
     * rewritten value - or at least the value which designates the value of the
     * input JCTree.
     */
    @NonNull final BiMap<JCTree,JCExpression> bimap = new BiMap<JCTree,JCExpression>();
    
    // FIXME - document - I think this can go away
    @NonNull final BiMap<JCTree,JCTree> pathmap = new BiMap<JCTree,JCTree>();
    
    /** A mapping from BasicBlock to the sym->incarnation map giving the map that
     * corresponds to the state at the exit of the BasicBlock.
     */
    @NonNull final public Map<BasicBlock,VarMap> blockmaps = new HashMap<BasicBlock,VarMap>();
    
    /** A mapping from labels to the sym->incarnation map operative at the position
     * of the label.
     */
    @NonNull final protected Map<Name,VarMap> labelmaps = new HashMap<Name,VarMap>();
        
    /** Contains names for which a declaration has been issued. */
    final protected Set<Name> isDefined = new HashSet<Name>();

    // THESE VARIABLES ARE SET (AND RESET) IN THE COURSE OF COMPUTATION
    // (so they do not need initialization)
    
    /** The map from symbol to incarnation number in current use */
    @NonNull public VarMap currentMap;
    
    /** The map immediately after declaration of method parameters; this is
        the mapping of variables to incarnations to use when in the scope of 
        a \pre (or an \old without a label) */
    @NonNull protected VarMap premap;
    
    /** The variable that keeps track of heap incarnations */
    protected JCIdent heapVar;
    
    /** The constructor - a new instance of this class is needed for each
     * Java program being converted to basic blocks. Some class level fields are
     * only initialized on construction and are not necessarily cleaned up if 
     * there is an exceptional exit.
     * @param context the compilation context
     */
    public BasicBlocker2(@NonNull Context context) {
        super(context);

        // Since we are not registering a tool or reusing singleton tool
        // instances we don't self register the instance in the context:
        // context.put(key, this);
        
        // Note - some fields are initialized here, others in the initialize() method
        
        this.factory = JmlTree.Maker.instance(context);
        this.utils = Utils.instance(context);
        this.scanMode = AST_JAVA_MODE;
        
        trueLiteral = treeutils.trueLit;
        falseLiteral = treeutils.falseLit;
        
        // This is the symbol to access the length of an array 
        lengthSym = syms.lengthVar;
        lengthIdent = treeutils.makeIdent(0,lengthSym);
        
    }

    /** Helper routine to initialize the object before starting its task of
     * converting to a basic program; if this object is to be reused, all 
     * fields must be appropriately initialized here - do not rely on cleanup
     * on an exceptional exit from a previous use.
     */
    @Override
    protected void initialize(@NonNull JCMethodDecl methodDecl, 
            @NonNull JCClassDecl classDecl, @NonNull JmlAssertionAdder assertionAdder) {
        super.initialize(methodDecl,classDecl,assertionAdder);
        this.arrayBaseSym.clear();
        this.localVars.clear();
        this.isDefined.clear();
        this.unique = 0;
        this.newdefs = new LinkedList<BasicProgram.Definition>();
        this.background = new LinkedList<JCExpression>();
        this.blockmaps.clear();
        this.labelmaps.clear();
        this.bimap.clear();
        this.pathmap.clear();
        this.heapVar = treeutils.makeIdent(0,assertionAdder.heapSym);
        this.methodsSeen = new HashSet<Symbol>();
        this.continuation = Continuation.CONTINUE;
        // currentMap is set when starting a block
        // premap is set during execution
    }
    

    // METHODS
    
    /** Visits the argument, returning the result as the value of 'result',
     * and records the mapping from old to new JCTree in the bimap.
     * @param tree
     */
    @Override
    public void scan(JCTree tree) {
        result = null;
        super.scan(tree);
        if (tree instanceof JCExpression && !(tree instanceof JCAssign)) {
            bimap.put(tree, result);
        }
    }

    /** Scans all items in the list, replacing the list element with the result of the scan. */
    public void scanList(com.sun.tools.javac.util.List<JCExpression> trees) {
        if (trees != null) {
            for (com.sun.tools.javac.util.List<JCExpression> l = trees; l.nonEmpty(); l = l.tail) {
                scan(l.head);
                l.head = result;
            }
        }
        result = null; // Defensive
    }
    
    /** Scans the argument and returns the rewritten result. */
    public JCExpression convertExpr(JCExpression expr) {
        scan(expr);
        return result;
    }

    /** Should not need this when everything is implemented */
    protected void notImpl(JCTree that) {
        log.getWriter(WriterKind.NOTICE).println("NOT IMPLEMENTED: BasicBlocker2 - " + that.getClass());
        result = trueLiteral;
    }
    
    /** Called by visit methods that should never be called. */
    protected void shouldNotBeCalled(JCTree that) {
        log.error("esc.internal.error","Did not expect to be calling a " + that.getClass() + " within BasicBlocker2");
        throw new JmlInternalError();
    }
    

    /** Creates an encoded name from a symbol and an incarnation position and the
     * current value of unique - so each call of this method returns a different
     * name, even with the same arguments.
     * If the symbol has a null owner (which is illegal if being compiled for RAC),
     * the symbol is considered to be a one-time-use temporary and the name is
     * not encoded.
     * If the symbol has a negative declaration position, that value is not included in the string
     * @param sym the symbol being given a logical name
     * @param incarnationPosition the position (character position in
     * the source file) at which the symbol is used - note that incarnation positions
     * are not necessarily unique, but can be used for debugging
     * @return the new name
     */
    protected Name encodedName(VarSymbol sym, long incarnationPosition) {
        Symbol own = sym.owner;
        // No uniqueness information is attached if any one of the following is true
        // a) the position information provided is NOPOS
        // b) there is no owner (i.e. it is a generated, single-use temporary)
        // c) it is final and not in a constructor (so it will only ever have one instantiation)
        // d) it is in a constructor but static and final (so it will only ever have one instantiation)
        if (incarnationPosition == Position.NOPOS || own == null || (!isConstructor && (sym.flags() & Flags.FINAL) != 0) || (isConstructor && (sym.flags() & (Flags.STATIC|Flags.FINAL)) == (Flags.STATIC|Flags.FINAL))) { 
            //Name n = utils.isJMLStatic(sym) ? sym.getQualifiedName() : sym.name;
            Name n = sym.name;
            if (sym.pos >= 0 && (sym.flags() & Flags.FINAL) == 0 && !n.toString().equals(Strings.THIS)) {
                n = names.fromString(n.toString() + ("_" + sym.pos));
            }
            if (own != null && (utils.isJMLStatic(sym) || own != methodDecl.sym.owner) && own instanceof TypeSymbol) {
                Name s = own.getQualifiedName();
                n = names.fromString(s.toString() + "_" + n.toString());
            }
            return n;
        } else
            return names.fromString(
                    //sym.getQualifiedName() 
                    sym.name 
                    + (sym.pos < 0 ? "_" : ("_" + sym.pos + "_")) // declaration position
                    + incarnationPosition // new definition position
                    + "___" 
                    + (++unique) // unique suffix
                    );
    }
    
    /** A new name for an array name */ // FIXME ??
    protected Name encodedArrayName(VarSymbol sym, int incarnationPosition) {
        Name n;
        if (incarnationPosition == 0) {
            n = sym.getQualifiedName();
        } else {
            n = names.fromString(sym.getQualifiedName() 
                    + (sym.pos < 0 ? "_" : ("_" + sym.pos + "_")) 
                    + incarnationPosition 
                    + "___" 
                    + (++unique)
                    );
        }
        if (isDefined.add(n)) {
            JCIdent id = treeutils.makeIdent(0, sym);
            id.name = n;
            addDeclaration(id);
        }
        return n;
    }
    
    /** Creates an encoded name for a Type variable.
     * @param sym
     * @param declarationPosition
     * @return the new name
     */
    protected Name encodedTypeName(TypeSymbol sym, int declarationPosition) {
        return names.fromString(sym.flatName() + 
                (declarationPosition < 0 ? "_" : "_" + declarationPosition) + 
                "__" + (++unique));
    }
    

    /** Creates a new Ident node, but in this case we supply the nam
     * rather than using the name from the current incarnation map. 
     * This is just used for DSA assignments.
     */
    protected JCIdent newIdentUse(VarMap map, VarSymbol sym, int useposition) {
        Name name = map.getCurrentName(sym); // Creates a name if one has not yet been created
        JCIdent n = factory.at(useposition).Ident(name);
        n.sym = sym;
        n.type = sym.type;
        return n;
    }
    
    /** Creates an identifier node for a use of a variable at a given source code
     * position; the current SA version is used.
     * @param sym the underlying symbol (which gives the declaration location)
     * @param useposition the source position of its use
     * @return the new JCIdent node
     */
    protected JCIdent newIdentUse(VarSymbol sym, int useposition) {
        Name name = currentMap.getCurrentName(sym);
        JCIdent n = factory.at(useposition).Ident(name);
        n.sym = sym;
        n.type = sym.type;
        return n;
    }
    
    /** Creates an identifier node for a use of a type variable at a given source code
     * position; the current SA version is used. */
    protected JCIdent newTypeIdentUse(TypeSymbol sym, int useposition) {
        Name name = currentMap.getCurrentName(sym);
        JCIdent n = factory.at(useposition).Ident(name);
        n.sym = sym;
        n.type = sym.type;
        return n;
    }
    
    /** Creates an identifier nodes for a new SA version of the variable, that is,
     * when the variable is assigned to.
     * @param id the old identifier, giving the root name, symbol and type
     * @param incarnationPosition the position (and incarnation number) of the new variable
     * @return the new identifier
     */
    protected JCIdent newIdentIncarnation(JCIdent id, int incarnationPosition) {
        return newIdentIncarnation((VarSymbol)id.sym,incarnationPosition);
    }
    
    /** Creates a new incarnation of a variable */
    protected JCIdent newIdentIncarnation(VarSymbol vsym, int incarnationPosition) {
        JCIdent n = factory.at(incarnationPosition).Ident(encodedName(vsym,incarnationPosition));
        n.type = vsym.type;
        n.sym = vsym;
        currentMap.putSAVersion(vsym,n.name,unique); // unique is used as the new version number
        if (isDefined.add(n.name)) addDeclaration(n);
        return n;
    }
    
    // FIXME - review and document
    protected JCIdent newArrayIdentIncarnation(VarSymbol vsym, int incarnationPosition) {
        JCIdent n = factory.at(incarnationPosition).Ident(encodedArrayName(vsym,incarnationPosition));
        n.type = vsym.type;
        n.sym = vsym;
        currentMap.putSAVersion(vsym,n.name, unique); // unique is used as the new version number
        if (isDefined.add(n.name)) addDeclaration(n);
        return n;
    }

    // FIXME - document
    protected JCIdent newArrayIncarnation(Type indexType, Type componentType, int usePosition) {
        JCIdent id = getArrayIdent(indexType,componentType,usePosition);
        id = newArrayIdentIncarnation((VarSymbol)id.sym,usePosition);
        return id;
    }
    

    // FIXME - review and document - not used now, but should be for generics
    protected JCIdent newTypeVarIncarnation(TypeSymbol vsym, int incarnationPosition) {
        JCIdent n = factory.at(incarnationPosition).Ident(encodedTypeName(vsym,incarnationPosition));
        n.type = JmlTypes.instance(context).TYPE;
        n.sym = vsym;
        currentMap.putSAVersion(vsym,n.name);
        return n;
    }
    

    /** Sets all the variables that are supposed to stay in synch with the value of
     * currentBlock
     * @param b the new currentBlock
     */
    @Override
    protected void setCurrentBlock(BasicBlock b) {
        super.setCurrentBlock(b);
        currentMap = blockmaps.get(b);
        if (currentMap == null) currentMap = initMap(currentBlock);
        else log.error("jml.internal","The currentMap is unexpectedly already defined for block " + b.id.name);
        // The check above is purely defensive
    }
    
    /** Files away a completed block, adding it to the blocksCompleted list and
     * to the lookup Map.
     * @param b the completed block
     */
    @Override
    protected void completeBlock(@NonNull BasicBlock b) {
        super.completeBlock(b);
        currentMap = null; // Defensive - so no inadvertent assignments
    }
    
    /** Converts the top-level block of a method into the elements of a BasicProgram;
     * this is the entry point to the object; note that most of the work is done 
     * in place, modifying the tree that is the 'block' argument as needed.
     * 
     * @param methodDecl the method to convert to to a BasicProgram
     * @param denestedSpecs the specs of the method
     * @param classDecl the declaration of the containing class
     * @return the completed BasicProgram
     */
    public @NonNull BasicProgram convertMethodBody(JCBlock block, @NonNull JmlMethodDecl methodDecl, 
            JmlMethodSpecs denestedSpecs, @NonNull JmlClassDecl classDecl, @NonNull JmlAssertionAdder assertionAdder) {
        initialize(methodDecl,classDecl,assertionAdder);
        
        // Get the set of field symbols mentioned in the method body
        Set<VarSymbol> vsyms = GetSymbols.collectSymbols(block,assertionAdder.classBiMap.getf(classDecl));
        
        // Define the start block
        BasicBlock startBlock = newBlock(START_BLOCK_NAME,methodDecl.pos);

        // Handle the start block a little specially
        // It does not have any statements in it
        startBlock(startBlock); // Start it so the currentMap, currentBlock, remainingStatements are defined

        // Add mappings for the method parameters
        for (JCVariableDecl d: methodDecl.params) {
            currentMap.putSAVersion(d.sym, 0);
        }

        // Add mappings for all fields mentioned in the body of the method
        for (VarSymbol v: vsyms) {
            Name n = currentMap.putSAVersion(v,0); // Makes a name with incarnation 0
            JCIdent id = treeutils.makeIdent(v.pos, n, v);
            addDeclaration(id);
        }

        // Save the initial mappings
        premap = currentMap.copy();
        labelmaps.put(null,premap);

        // Define the body block
        BasicBlock bodyBlock = newBlock(BODY_BLOCK_NAME,methodDecl.body.pos);
        follows(startBlock,bodyBlock);

        completeBlock(currentBlock); // End of the start block

        // Add declarations of method parameters
        for (JCVariableDecl d: methodDecl.params) {
            // We reset this with a location of 0 so that the name does not get
            // changed. This is only because the premap does not know these names.
            // And will probably have to change when encodedName is made more robust. FIXME
            JCVariableDecl dd = treeutils.makeVarDef(d.type,d.name,d.sym.owner,0);
            bodyBlock.statements.add(dd);
        }
        
        // Put all the program statements in the Body Block
        bodyBlock.statements.addAll(block.getStatements());
        todo.push(bodyBlock);
        processBlocks(); // Iteratively creates and processes following blocks
        
        // Finished processing all the blocks
        // Complete the BasicProgram
        program.startId = startBlock.id;
        program.definitions = newdefs;
        program.background = background;
        return program;
    }
    
    
    /** Adds an assert statement into the given statement list; no 
     * translation is performed (the input expression must already be transformed)
     * @param label the label for the assert statement
     * @param trExpr the expression which must be true
     * @param declpos the associated position (e.g. of the declaration that causes the assertion)
     * @param statements the statement list to which to add the new assert statement
     * @param usepos the source position at which the expression is asserted
     * @param source the source file corresponding to usepos
     * @param statement
     */
    protected void addAssert(Label label, JCExpression trExpr, int declpos, List<JCStatement> statements, int usepos, JavaFileObject source, JCTree statement) {
        JmlTree.JmlStatementExpr st = factory.at(statement.pos()).JmlExpressionStatement(assertID, assertClause,label,trExpr);
        st.optionalExpression = null;
        st.source = source; // source file in which st.pos resides
        //st.line = -1; 
        st.associatedPos = declpos;
        st.associatedSource = null; // OK - always same as source
        st.type = null; // no type for a statement
        copyEndPosition(st,trExpr);
        statements.add(st);
    }
    
    
//    /** Adds a new assume statement to the end of the currentBlock; the assume statement is
//     * given the declaration pos and label from the arguments; it is presumed the input expression is
//     * translated, as is the produced assume statement.
//     * @param pos the declaration position of the assumption
//     * @param label the kind of assumption
//     * @param expr the (translated) expression being assumed
//     */
//    protected JmlStatementExpr addAssume(int pos, Label label, JCExpression expr) {
//        return addAssume(pos,label,expr,currentBlock.statements);
//    }
//    
    /** Adds a new assume statement to the end of the given statements list; the assume statement is
     * given the declaration pos and label from the arguments; it is presumed the input expression is
     * translated, as is the produced assume statement.
     * @param pos the declaration position of the assumption
     * @param label the kind of assumption
     * @param that the (translated) expression being assumed
     * @param statements the list to add the new assume statement to
     */
    protected JmlStatementExpr addAssume(int pos, Label label, JCExpression that, List<JCStatement> statements) {
        return super.addAssume(pos,label,that,statements);
    }
    
    /** Adds an assumption to the given statement list */ 
    protected JmlStatementExpr addAssume(int startpos, JCTree endpos, Label label, JCExpression that, List<JCStatement> statements) {
        return super.addAssume(startpos,endpos,label,that,statements);
    }
    
    
    /** Adds an axiom to the axiom set */
    protected void addAxiom(int pos, Label label, JCExpression that, List<JCStatement> statements) {
        background.add(that);
    }
 
    /** Adds a (copy of) a JCIdent in the list of declarations of the BasicProgram being produced */
    protected void addDeclaration(JCIdent that) {
        JCIdent t = treeutils.makeIdent(0,that.name,that.sym);
        t.type = that.type;
        program.declarations.add(t);
    }
    

    // FIXME - REVIEW and document
    static protected String encodeType(Type t) {   // FIXME String? char? void? unsigned?
        TypeTag tag = t.getTag();
        if (t instanceof ArrayType) {
            return "refA$" + encodeType(((ArrayType)t).getComponentType());
        } else if (!t.isPrimitive()) {
            return "REF";
        } else if (tag == TypeTag.INT || tag == TypeTag.SHORT || tag == TypeTag.LONG || tag == TypeTag.BYTE) {
            return tag.toString();
        } else if (tag == TypeTag.BOOLEAN) {
            return "bool";
        } else if (tag == TypeTag.FLOAT || tag == TypeTag.DOUBLE) {
            return "real";
        } else if (tag == TypeTag.CHAR) {
            return "char";
        } else {
            return "unknown";
        }
    }
    
    /** This is a cache of VarSymbols so that there is a unique instance for
     * each array component type used in the program.
     */
    private Map<String,VarSymbol> arrayBaseSym = new HashMap<String,VarSymbol>();
    
    /** Returns a VarSymbol for the heap array that manages all the arrays of
     * the given component type; this VarSymbol is unique to the type (within
     * this instance of BasicBlocker2).
     */
    protected VarSymbol getArrayBaseSym(Type indexType, Type componentType) {
        if (JmlTypes.instance(context).isAnyIntegral(indexType)) {
            String s = ARRAY_BASE_NAME + encodeType(componentType);
            VarSymbol vsym = arrayBaseSym.get(s);
            if (vsym == null) {
                Name n = names.fromString(s);
                Type t = new ArrayType(componentType,syms.arrayClass);
                vsym = new VarSymbol(0,n,t,null); // null -> No owner
                vsym.pos = 0;
                arrayBaseSym.put(s,vsym);
            }
            return vsym;
        } else {
            String s = ARRAY_BASE_NAME + encodeType(indexType) + "_" + encodeType(componentType);
            VarSymbol vsym = arrayBaseSym.get(s);
            if (vsym == null) {
                Name n = names.fromString(s);
                Type t = new Array2Type(indexType,componentType);
                vsym = new VarSymbol(0,n,t,null); // null -> No owner
                vsym.pos = 0;
                arrayBaseSym.put(s,vsym);
            }
            return vsym;
        }
    }
    
    public static class Array2Type extends Type {
        public Type indexType;
        public Type componentType;
        public Array2Type(Type i, Type c) { super(null); indexType = i; componentType = c; }
        @Override
        public TypeTag getTag() {
            // TODO Auto-generated method stub
            return null;
        }
        public String toString() {
            return "map<"+encodeType(indexType)+","+encodeType(componentType)+">";
        }
    }

    /** Return an identifier for the heap array that manages the given component type. */
    protected JCIdent getArrayIdent(Type indexType, Type componentType, int pos) {
        VarSymbol vsym = getArrayBaseSym(indexType, componentType);
        return newIdentUse(vsym,pos);
    }
    
    
    // FIXME - review the following with havoc \everything in mind.
    /** Returns the initial VarMap of the given block; the returned map is a combination
     * of the maps from all preceding blocks, with appropriate DSA assignments added.
     * @param block
     * @return the VarMap for the given block
     */
    protected VarMap initMap(BasicBlock block) {
        VarMap newMap = new VarMap();
        currentMap = newMap;
//        System.out.println("CREATING BLOCK " + block.id);
//        for (BasicBlock b: block.preceders()) {
//            System.out.println("INPUT " + b.id);
//            System.out.println(blockmaps.get(b));
//        }
        if (block.preceders().size() == 0) {
            // keep the empty one
        } else if (block.preceders().size() == 1) {
            newMap.putAll(blockmaps.get(block.preceders().get(0))); 
        } else {
            // Here we do the DSA step of combining the results of the blocks that precede
            // the block we are about to process. The situation is this: a particular symbol,
            // sym say, may have been modified in any of the preceding blocks. In each case
            // a new incarnation and a new identifier Name will have been assigned. A record
            // of that current Identifier Name is in the VarMap for the block. But we need a single
            // Name to use in this new block.  So we pick a new Name to use in the new block,
            // and for each preceding block we add an assumption of the form newname = oldname.
            // This assumption is added to the end of the preceding block.
            // In this version, we use the maximum incarnation as the new name.
            int pos = block.id.pos;
            List<VarMap> all = new LinkedList<VarMap>();
            VarMap combined = new VarMap();
            for (BasicBlock b : block.preceders()) {
                VarMap m = blockmaps.get(b);
                all.add(m);
                combined.putAll(m);
            }
            //combined.everythingSAversion = maxe;
            for (VarSymbol sym: combined.keySet()) {
                if (sym.owner instanceof Symbol.ClassSymbol) {
                    // If the symbol is owned by a class, then it is implicitly part of each VarMap,
                    // even if it is not explicitly listed.
                    
                    Name maxName = null;
                    long max = -1;
                    //int num = 0;
                    for (VarMap m: all) {
                        Long i = m.getSAVersionNum(sym);
                        //if (i != max) num++;
                        if (i > max) {
                            max = i;
                            maxName = m.getName(sym);
                        }
                    }
                    Name newName = maxName;
//                    if (num > 1) {
//                        JCIdent id = newIdentIncarnation(sym,block.id.pos); // relies on the uniqueness value to be different
//                        // Need to declare this before all relevant blocks, so we do it at the very beginning
//                        program.declarations.add(id);
//                        newName = id.name;
//                    }
                    newMap.putSAVersion(sym,newName,max);

                    for (BasicBlock b: block.preceders) {
                        VarMap m = blockmaps.get(b);
                        Long i = m.getSAVersionNum(sym);
                        if (i < max) {
                            // Type information ? - FIXME 
                            JCIdent pold = newIdentUse(m,sym,pos);
                            JCIdent pnew = newIdentUse(newMap,sym,pos);
                            if (pold.name != pnew.name) { 
                                JCBinary eq = treeutils.makeEquality(pos,pnew,pold);
                                addAssume(pos,Label.DSA,eq,b.statements);
                            }
                        }
                    }
                } else {
                    // If the symbol is owned by the method, then if it is not 
                    // in every inherited map,
                    // then it has gone out of scope and need not be repeated. Also
                    // it is not subject to havoc \everything
                    Name maxName = null;
                    Long max = -1L;
                    boolean skip = false;
                    boolean diff = false;
                    for (VarMap m: all) {
                        Name n = m.getName(sym);
                        if (n == null) { skip = true; break; }
                        Long i = m.getSAVersionNum(sym);
                        if (max >= 0 && max != i) diff = true;
                        if (i > max) {
                            max = i;
                            maxName = n;
                        }
                    }
                    if (skip) continue;
                    Name newName = maxName;
//                    boolean different = false;
//                    for (VarMap m: all) {
//                        Name n = m.getName(sym);
//                        if (!newName.equals(n)) { different = true; break; }
//                    }
//                    if (different) {
//                        max++;
//                        JCIdent id = newIdentIncarnation(sym,pos); // relies on the uniqueness value to be different
//                        // Need to declare this before all relevant blocks, so we do it at the very beginning
//                        //program.declarations.add(id);
//                        newName = id.name;
//                    }
                    newMap.putSAVersion(sym,newName,max);
                    if (!diff) continue;
                    //if (different) {
                        for (BasicBlock b: block.preceders) {
                            VarMap m = blockmaps.get(b);
                            Long i = m.getSAVersionNum(sym);
                            if (i < max) {
                                // No position information for these nodes
                                // Type information put in, though I don't know that we need it
                                JCIdent pold = newIdentUse(m,sym,pos);
                                JCIdent pnew = newIdentUse(newMap,sym,pos);
                                if (pold.name != pnew.name) { 
                                    JCBinary eq = treeutils.makeEquality(pos,pnew,pold);
                                    addAssume(pos,Label.DSA,eq,b.statements);
                                }
                            }
                        }
                    //}
                }
            }
            JCIdent sourceId = M.Ident(block.id().toString() + "_source");
            sourceId.setType(syms.intType);
            addDeclaration(sourceId);
            for (BasicBlock b: block.preceders) {
                JCLiteral lit = treeutils.makeIntLiteral(Position.NOPOS,b.unique);
                JCBinary eq = treeutils.makeEquality(pos,sourceId,lit);
                addAssume(pos,Label.SOURCEBLOCK,eq,b.statements);
            }
       }
        // Note - this is the map at the start of processing a block
//        log.noticeWriter.println("MAP FOR BLOCK " + block.id + JmlTree.eol + newMap.toString());
        blockmaps.put(block,newMap);
        return newMap;
    }
    

    // FIXME - review this
    /** Creates a translated expression whose value is the given type;
     * the result is a JML type, e.g. a representation of an instantiated generic.*/
    protected JCExpression makeTypeLiteral(Type type, int pos) {
        return treeutils.trType(pos,type);
    }
    
    /** Makes the equivalent of an instanceof operation: \typeof(e) <: \type(type) */
    protected JCExpression makeNNInstanceof(JCExpression e, int epos, Type type, int typepos) {
        JCExpression e1 = treeutils.makeTypeof(e);
        JCExpression e2 = makeTypeLiteral(type,typepos);
        JCExpression ee = treeutils.makeJmlBinary(epos,Operators.subtypeofKind,e1,e2);
        return ee;
    }
    
    // FIXME - review and document
    protected JCExpression makeSignalsOnly(JmlMethodClauseSignalsOnly clause) {
        JCExpression e = treeutils.makeBooleanLiteral(clause.pos,false);
        JmlSingleton id = factory.at(0).JmlSingleton(exceptionKind);
        id.kind = org.jmlspecs.openjml.ext.SingletonExpressions.exceptionKind;
        for (JCExpression typetree: clause.list) {
            int pos = typetree.getStartPosition();
            e = treeutils.makeBinary(pos, 
                    JCTree.Tag.OR, makeNNInstanceof(id, pos, typetree.type, pos), e);
        }
        return e;
    }


    // STATEMENT NODES
    
    // OK
    @Override
    public void visitJmlLabeledStatement(JmlLabeledStatement that) {
        VarMap map = currentMap.copy();
        if (that.label.toString().equals(Strings.preLabelBuiltin)) premap = map;
        labelmaps.put(that.label,map); // if that.label is null, this is the premap
        super.visitJmlLabeledStatement(that);
    }
    
    // FIXME - REVIEW
    public void visitExec(JCExpressionStatement that)    { 
        // This includes assignments and stand-alone method invocations
        scan(that.expr);
    }
        
    // FIXME - needs review - al;ready converted to a BasicBlock assert?
    public void visitAssert(JCAssert that) { // This is a Java assert statement
        currentBlock.statements.add(comment(that));
        JCExpression cond = convertExpr(that.cond);
        JCExpression detail = convertExpr(that.detail);
        //JCExpression detail = (that.detail);
        // FIXME - what to do with detail
        // FIXME - for now turn cond into a JML assertion
        // FIXME - need a label for the assert statement
        // FIXME - set line and source
        addAssert(Label.EXPLICIT_ASSERT, cond, that.cond.getStartPosition(), currentBlock.statements, that.cond.getStartPosition(),log.currentSourceFile(),that);
    }
    
    // FIXME - needs review
    public void visitApply(JCMethodInvocation that) { 
        JCExpression now;
        JCExpression obj;
        MethodSymbol msym;
        Type.ForAll tfa = null;
        if (that.meth instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)that.meth;
            msym = (MethodSymbol)(fa.sym);
            if (msym == null || utils.isJMLStatic(msym)) obj = null; // msym is null for injected methods such as box and unbox
            else {
                fa.selected = convertExpr(fa.selected);
                // FIXME - should do better than converting to String
                //if (!fa.selected.type.toString().endsWith("JMLTYPE")) checkForNull(obj,fa.pos,trueLiteral,null);
            }
            if (msym != null && msym.type instanceof Type.ForAll) tfa = (Type.ForAll)msym.type;
            
        } else if (that.meth instanceof JCIdent) {
            // This is a defined function that will be passed on 
            // continue on
        } else {
            // FIXME - not implemented
            log.warning("esc.not.implemented","BasicBlocker2.visitApply for " + that);
            msym = null;
            obj = null;
            result = trueLiteral;
            return;
        }

        // FIXME - what does this translation mean?
        //        ListBuffer<JCExpression> newtypeargs = new ListBuffer<JCExpression>();
        //        for (JCExpression arg: that.typeargs) {
        //            JCExpression n = trExpr(arg);
        //            newtypeargs.append(n);
        //        }

        ListBuffer<JCExpression> newargs = new ListBuffer<JCExpression>();
        for (JCExpression arg: that.args) {
            scan(arg);
            newargs.append(result);
        }
        
        that.args = newargs.toList();
        result = that;
        

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

        // FIXME - concerned that the position here is not after the
        // positions of all of the arguments
//        if (inSpecExpression) {
//            result = insertSpecMethodCall(that.pos,msym,obj,that.typeargs,newargs.toList());
//        } else {
//            result = insertMethodCall(that,msym,obj,that.getTypeArguments(),newargs.toList()); // typeargs ? FIXME
//        }

        //popTypeArgs();
//        toLogicalForm.put(that,result);
        return;
    }

    // FIXME - review this
    //boolean extraEnv = false;
    public void visitJmlMethodInvocation(JmlMethodInvocation that) { 
        if (that.name != null) {
            scanList(that.args);
            result = that;
        } else if (that.token == null && that.kind == null) {
            //super.visitApply(that);  // See testBox - this comes from the implicitConversion - should it be a JCMethodInvocation instead?
            scan(that.typeargs);
            scan(that.meth);
            if (that.meth != null) that.meth = result;
            scanList(that.args);
            result = that;


        } else {
            if (that.kind != null) switch (that.kind.keyword) {
                case oldID:
                case preID:
                case pastID:
                {
                    VarMap savedMap = currentMap;
                    try {
                            Name label = ((JmlAssertionAdder.LabelProperties)that.labelProperties).name;
                            //JCIdent label = (JCIdent)that.args.get(1);
                            currentMap = labelmaps.get(label);
                            if (currentMap == null) {
                                // When method axioms are inserted they can appear before the label,
                                // in which case control flow comes here. SO we are counting on proper
                                // reporting of out of scope labels earlier.
                                // This should have already been reported
                                //log.error(label.pos,"jml.unknown.label",label.name.toString());
                                // Just use the current map
                                currentMap = savedMap;
                            }
                            that.args.get(0).accept(this);
                    } finally {
                        currentMap = savedMap;
                    }
                    break;
                }
                case sameID: {
                    scanList(that.args);
                    result = that;
                    break;                        
                }
                case nonnullelementsID: 
                {
                    scan(that.args.get(0));
                    JCExpression arg = result;
                    JCExpression argarrays = getArrayIdent(syms.intType, syms.objectType,that.pos);
                    that.args = com.sun.tools.javac.util.List.<JCExpression>of(arg,argarrays);
                    result = that;
                    break;
                } 
                case typelcID:
                case typeofID:
                case distinctID:
                {
                    //super.visitApply(that);  // See testBox - this comes from the implicitConversion - should it be a JCMethodInvocation instead?
                    scan(that.typeargs);
                    scan(that.meth);
                    if (that.meth != null) that.meth = result;
                    scanList(that.args);
                    result = that;
                    break;
                } 
                case elemtypeID:
                {
                    scan(that.typeargs);
                    scan(that.meth);
                    if (that.meth != null) that.meth = result;
                    scanList(that.args);
                    result = that;
                    break;
                } 
                case erasureID:
                {
                    scan(that.typeargs);
                    scan(that.meth);
                    if (that.meth != null) that.meth = result;
                    scanList(that.args);
                    result = that;
                    break;
                } 
                case concatID: 
                {
                    scan(that.typeargs);
                    scanList(that.args);
                    result = that;
                    break;
                } 
                case bsrequiresID:
                case bsensuresID:
                case bsreadsID:
                case bswritesID:
                {
                    scan(that.typeargs);
                    scan(that.meth);
                    if (that.meth != null) that.meth = result;
                    scanList(that.args);
                    result = that;
                    break;
                } 
                default:
                    log.error(that.pos, "esc.internal.error", "No implementation for this kind of Jml node in BasicBlocker2: " + that.kind.name());
                    
            } else switch (that.token) { 
                case SUBTYPE_OF:
                case JSUBTYPE_OF:
                {
                    scan(that.args.get(0));
                    JCExpression lhs = result;
                    scan(that.args.get(1));
                    JCExpression rhs = result;
                    that.args = com.sun.tools.javac.util.List.<JCExpression>of(lhs,rhs);
                    result = that;
                    break;
                } 
                default:
                    log.error(that.pos, "esc.internal.error", "Did not expect this kind of Jml node in BasicBlocker2: " + that.token.internedName());
                    shouldNotBeCalled(that);
            }
            return;
        }
    }
    
    // FIXME - REVIEW and document
    protected List<Type> allTypeArgs(Type type) {
        ListBuffer<Type> list = new ListBuffer<Type>();
        allTypeArgs(list,type);
        return list.toList();
    }
    
    // FIXME - REVIEW and document
    protected void allTypeArgs(ListBuffer<Type> list, Type type) {
        if (type == Type.noType) return;
        allTypeArgs(list,type.getEnclosingType());
        list.appendList(type.getTypeArguments());
    }
    
    
    // FIXME - review and document
    protected void havoc(JCExpression storeref) {
        if (storeref instanceof JCIdent) {
            newIdentIncarnation((JCIdent)storeref,storeref.pos);

        } else if (storeref instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)storeref;
            if (fa.name == null) {
                    // Should not come here - as a store-ref of the form o.*
                    // should have been expanded into the actual list of 
                    // non-wildcard locations
                    log.error(fa.pos,"jml.internal","Unexpected wildcard store-ref in havoc call");
            } else {
                if (utils.isJMLStatic(fa.sym)) {
                    newIdentIncarnation((VarSymbol)fa.sym, storeref.pos);
                } else {
                    int sp = fa.pos;
                    scan(fa.selected);
                    JCIdent oldfield = newIdentUse((VarSymbol)fa.sym,sp);
                    if (isDefined.add(oldfield.name)) {
                        if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("AddedFF " + oldfield.sym + " " + oldfield.name);
                        addDeclaration(oldfield);
                    }
                    JCIdent newfield = newIdentIncarnation(oldfield,sp);
                    if (isDefined.add(newfield.name)) {
                        if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("AddedFF " + newfield.sym + " " + newfield.name);
                        addDeclaration(newfield);
                    }
                    if (fa.selected != null) {
                        JmlBBFieldAccess acc = new JmlBBFieldAccess(newfield,fa.selected);
                        acc.pos = sp;
                        acc.type = fa.type;
                        JmlBBFieldAssignment expr = new JmlBBFieldAssignment(newfield,oldfield,fa.selected,acc);
                        expr.pos = sp;
                        expr.type = fa.type;
                        addAssume(sp,Label.HAVOC,expr,currentBlock.statements);
                    }
                }
            }
        } else if (storeref instanceof JmlStoreRefKeyword) {
            IJmlClauseKind t = ((JmlStoreRefKeyword)storeref).kind;
            if (t == everythingKind || t == notspecifiedKind) {
                for (VarSymbol vsym: currentMap.keySet()) {
                    // Local variables are not affected by havoc \everything
                    // The owner of a local symbol is a MethodSymbol
                    // Also, final fields are not affected by havoc \everything
                    if (vsym.owner instanceof ClassSymbol &&
                            (vsym.flags() & Flags.FINAL) != Flags.FINAL) {
                        newIdentIncarnation(vsym, storeref.pos);
                    }
                }
                // FIXME - symbols added after this havoc \everything will not have new incarnations???
            }
        } else if (storeref instanceof JCArrayAccess) { // Array Access
            JCArrayAccess aa = (JCArrayAccess)storeref;
            int sp = storeref.pos;
            JCIdent arr = getArrayIdent(syms.intType,aa.type,aa.pos);
            JCExpression ex = aa.indexed;
            JCExpression index = aa.index;
            JCIdent nid = newArrayIncarnation(syms.intType,aa.type,sp);
            
            scan(ex); ex = result;
            scan(index); index = result;
            
            JmlBBArrayAccess rhs = new JmlBBArrayAccess(nid,ex,index);
            rhs.pos = sp;
            rhs.type = aa.type;
            JCExpression expr = new JmlBBArrayAssignment(nid,arr,ex,index,rhs);
            expr.pos = sp;
            expr.type = aa.type;
            treeutils.copyEndPosition(expr, aa);

            // FIXME - set line and source
            addAssume(sp,Label.HAVOC,expr,currentBlock.statements);
            //log.error(storeref.pos,"jml.internal","Ignoring unknown kind of storeref in havoc: " + storeref);
        } else if (storeref instanceof JmlStoreRefArrayRange) { // Array Access
            int sp = storeref.pos;
            JmlStoreRefArrayRange aa = (JmlStoreRefArrayRange)storeref;
            Type indexType = JmlTypes.instance(context).indexType(aa.expression.type);
            if (aa.lo == aa.hi && aa.lo != null) {
                // Single element
                JCIdent arr = getArrayIdent(indexType,aa.type,aa.pos);
                JCExpression ex = aa.expression;
                JCExpression index = aa.lo;
                JCIdent nid = newArrayIncarnation(indexType,aa.type,sp);
                
                scan(ex); ex = result;
                scan(index); index = result;
                
                Name nm = names.fromString("__BBtmp_" + (++unique));
                JCVariableDecl decl = treeutils.makeVarDef(aa.type, nm, null, sp);
                JCIdent id = treeutils.makeIdent(sp,decl.sym);
                addDeclaration(id);
                
                JmlBBArrayAccess rhs = new JmlBBArrayAccess(nid,ex,index);
                rhs.pos = sp;
                rhs.type = aa.type;
                JCExpression expr = new JmlBBArrayAssignment(nid,arr,ex,index,id);
                expr.pos = sp;
                expr.type = aa.type;
                treeutils.copyEndPosition(expr, aa);

                // FIXME - set line and source
                addAssume(sp,Label.HAVOC,expr,currentBlock.statements);
            } else {
                JmlStoreRefArrayRange aaorig = aa;
                JCExpression ex = aa.expression;
                while (ex instanceof JmlStoreRefArrayRange && ((JmlStoreRefArrayRange)ex).lo == null && ((JmlStoreRefArrayRange)ex).hi == null) { 
                    aa = (JmlStoreRefArrayRange)ex; ex = aa.expression;
                }
                if (aa.lo == null && aa.hi == null) {
                    // Entire array
                    JCIdent arr = getArrayIdent(indexType,aa.type,aa.pos);
                    JCIdent nid = newArrayIncarnation(indexType,aa.type,sp);

                    scan(ex); ex = result;

                    JCExpression expr = new JmlBBArrayAssignment(nid,arr,ex,null,null);
                    expr.pos = sp;
                    expr.type = aa.type;
                    treeutils.copyEndPosition(expr, aa);

                    // FIXME - set line and source
                    addAssume(sp,Label.HAVOC,expr,currentBlock.statements);
                } else {
                    // First havoc entire array
                    // Range of array
                    JCIdent arr = getArrayIdent(indexType,aa.type,aa.pos);
                    JCIdent nid = newArrayIncarnation(indexType,aa.type,sp);

                    scan(ex); ex = result;

                    JCExpression expr = new JmlBBArrayAssignment(nid,arr,ex,null,null);
                    expr.pos = sp;
                    expr.type = aa.type;
                    treeutils.copyEndPosition(expr, aa);
                    // FIXME - set line and source
                    addAssume(sp,Label.HAVOC,expr,currentBlock.statements);

                    int p = aa.pos;
                    scan(aa.lo);
                    JCExpression lo = result;
                    JCVariableDecl decl = treeutils.makeVarDef(syms.intType, names.fromString("_JMLARANGE_" + (++unique)), null, p);
                    JCIdent ind = treeutils.makeIdent(p, decl.sym);
                    JCExpression comp = treeutils.makeBinary(p,JCTree.Tag.LT,treeutils.intltSymbol,ind,lo);
                    JCExpression newelem = new JmlBBArrayAccess(nid,ex,ind);
                    newelem.pos = p;
                    newelem.type = aa.type;
                    JCExpression oldelem = new JmlBBArrayAccess(arr,ex,ind);
                    oldelem.pos = p;
                    oldelem.type = aa.type;
                    JCExpression eq = treeutils.makeEquality(p,newelem,oldelem);

                    if (aa.hi != null) {
                        scan(aa.hi);
                        JCExpression hi = result;
                        comp = treeutils.makeOr(p, comp, treeutils.makeBinary(p,JCTree.Tag.LT,treeutils.intltSymbol,hi,ind));
                    }

                    // FIXME - set line and source
                    expr = factory.at(p).JmlQuantifiedExpr(QuantifiedExpressions.qforallKind,com.sun.tools.javac.util.List.<JCVariableDecl>of(decl),comp,eq);
                    expr.setType(syms.booleanType);
                    addAssume(sp,Label.HAVOC,expr,currentBlock.statements);
                    //log.warning(storeref.pos,"jml.internal","Ignoring unknown kind of storeref in havoc: " + storeref);
                }
            }
        } else {
            log.error(storeref.pos,"jml.internal","Ignoring unknown kind of storeref in havoc: " + storeref);
        }

    }
    

    
//    // FIXME - review and document
//    protected void havocEverything(JCExpression preCondition, int newpos) {
//        // FIXME - if the precondition is true, then we do not need to add the 
//        // assumptions - we just need to call newIdentIncarnation to make a new
//        // value in the map.  This would shorten the VC.  How often is this
//        // really the case?  Actually the preCondition does not need to be true,
//        // it just needs to encompass all allowed cases.
//        
//        // FIXME - check on special variables - should they/are they havoced?
//        // this
//        // terminationVar
//        // exceptionVar
//        // resultVar
//        // exception
//        // others?
//        
//        // Change everything in the current map
//        for (VarSymbol vsym : currentMap.keySet()) {
//            if (vsym.owner == null || vsym.owner.type.tag != TypeTag.CLASS) {
//                continue;
//            }
//            JCIdent oldid = newIdentUse(vsym,newpos);
//            JCIdent newid = newIdentIncarnation(vsym,newpos);
//            JCExpression e = factory.at(newpos).Conditional(preCondition,newid,oldid);
//            e.type = vsym.type;
//            e = treeutils.makeEquality(newpos,newid,e);
//            addAssume(newpos,Label.HAVOC,e,currentBlock.statements);
//        }
//        //currentMap.everythingSAversion = newpos; // FIXME - this now applies to every not-yet-referenced variable, independent of the preCondition
//    }

    /** This method is not called for top-level classes, since the BasicBlocker is invoked
     * directly for each method.
     */
    // FIXME - what about for anonymous classes or local classes or nested classes
    @Override
    public void visitClassDef(JCClassDecl that) {
        // Nested classes are found in JmlEsc.  We get to this point if there is a local
        // class declaration within method body.
        
        System.out.println("GOT HERE!");
        JmlEsc.instance(context).visitClassDef(that);
    }

    // FIXME - review this, and compare to the above
    @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        // Nested classes are found in JmlEsc.  We get to this point if there is a local
        // class declaration within method body.
        
        System.out.println("GOT HERE TOO!");
        JmlEsc.instance(context).visitClassDef(that);
    }


    
    // OK
    @Override
    public void visitJmlStatementExpr(JmlStatementExpr that) { 
        if (that.clauseType == commentClause) {
            // Comments are included in the BB program without rewriting
            // This is essential to how counterexample path construction works
            currentBlock.statements.add(that);
        } else if (that.clauseType == assumeClause || that.clauseType == assertClause || that.clauseType == checkClause) {
            JmlStatementExpr st = M.at(that.pos()).JmlExpressionStatement(that.clauseType.name(),that.clauseType,that.label,convertExpr(that.expression));
            st.id = that.id;
            st.optionalExpression = convertExpr(that.optionalExpression);
            st.associatedPos = that.associatedPos;
            st.associatedSource = that.associatedSource;
            st.description = that.description;
            st.source = that.source;
            st.type = that.type;
            st.associatedClause = that.associatedClause;
            copyEndPosition(st,that);
            if (that.clauseType == assertClause && that.label == Label.METHOD_ASSUME) {
                JCExpression expr = that.expression;
                JCMethodInvocation call = (JCMethodInvocation)((JCBinary)expr).rhs;
                Symbol sym = treeutils.getSym(call.meth);
                if (!methodsSeen.add(sym)) {
                    addMethodEqualities(call,currentBlock); // Execute if the method has already been seen
                }
            }
            currentBlock.statements.add(st);
        } else if (that.clauseType == haltClause) {

            continuation = JmlAssertionAdder.Continuation.HALT;

        } else {
            log.error(that.pos,"esc.internal.error","Unknown token in BasicBlocker2.visitJmlStatementExpr: " + that.clauseType.name());
        }
    }
    
    public void visitJmlStatement(JmlStatement that) {
        if (that.clauseType == EndStatement.endClause) {
            // Modeled after vistReturn
            if (!remainingStatements.isEmpty()) {
                JCStatement stat = remainingStatements.get(0);
                if (stat.toString().contains("JMLsaved")) remainingStatements.remove(0);
                if (remainingStatements.get(0).toString().contains("JMLsaved")) remainingStatements.remove(0);
                if (!remainingStatements.isEmpty()) {
//                    // Not fatal, but does indicate a problem with the original
//                    // program, which the compiler may have already identified
//                    log.warning(remainingStatements.get(0).pos,
//                            "esc.internal.error", //$NON-NLS-1$
//                            "Unexpected statements following a END statement are ignored"); //$NON-NLS-1$
                    remainingStatements.clear();
                }
            }

            replaceFollows(currentBlock, new LinkedList<BasicBlock>());

            processCurrentBlock();
        }
        
    }
    
    protected void traceMethod(JCMethodInvocation call) {
        MethodSymbol msym = (MethodSymbol)((JCIdent)call.meth).sym;
        if (JmlAttr.instance(context).isFunction(msym)) return;
        findInBlock(call, currentBlock,msym,new LinkedList<JCStatement>());
    }
    
    protected void findInBlock(JCMethodInvocation call, BasicBlock bl, MethodSymbol msym, List<JCStatement> list) {
        List<JCStatement> stats = bl.statements;
        boolean sourceBlockFound = false;
        ListIterator<JCStatement> iter = stats.listIterator(stats.size());
        try {
        while (iter.hasPrevious()) {
            JCStatement stat = iter.previous();
            if (stat instanceof JmlStatementExpr) {
                Label label = ((JmlStatementExpr)stat).label;
                if (label == Label.METHOD_ASSUME) {
                    JCMethodInvocation prevcall = (JCMethodInvocation)(((JCBinary)((JmlStatementExpr)stat).expression).rhs);
                    MethodSymbol mm = (MethodSymbol)((JCIdent)prevcall.meth).sym;
                    if (mm == msym) {
                        JCExpression ex = treeutils.trueLit;
                        for (JCStatement s: list) {
                            JCBinary bin = ((JCBinary)((JmlStatementExpr)s).expression);
                            ex = treeutils.makeAnd(Position.NOPOS, ex, bin);
                        }
                        JCExpression newrecv = null;
                        if (prevcall.meth instanceof JCIdent) {
                            newrecv = (JCIdent)prevcall.meth;
                            if (((JCIdent)prevcall.meth).name == ((JCIdent)call.meth).name) return;
                        } else if (prevcall.meth instanceof JCFieldAccess) {
                            JCExpression callrecv = ((JCFieldAccess)call.meth).selected;
                            newrecv = M.Select(callrecv, ((JCFieldAccess)prevcall.meth).name);
                            if (((JCFieldAccess)prevcall.meth).name == ((JCFieldAccess)call.meth).name) return;
                        } else {
                            log.error("jml.internal","Call receiver not implemented " + call.meth.toString());
                        }
                        JCExpression eq = M.Apply(call.typeargs,newrecv,call.args);
                        eq.type = call.type;
                        eq = treeutils.makeEquality(Position.NOPOS, call, eq);
                        ex = treeutils.makeImplies(Position.NOPOS, ex, eq);
                        JmlStatementExpr st = M.at(Position.NOPOS).JmlExpressionStatement(assumeID, assumeClause,Label.DSA,ex);
                        currentBlock.statements.add(st);
                        return ;
                    }
                } else if (label == Label.ASSIGNMENT && stat.toString().contains("_heap___")) {
                    return;
                } else if (label == Label.SOURCEBLOCK) {
                    list.add(0,stat);
                    sourceBlockFound = true;
                }
            }
        }
        for (BasicBlock bll: bl.preceders) {
//            System.out.println("LOOKING IN " + bll.id());
            findInBlock(call, bll,msym, list);
//            System.out.println("NOTHING IN " + bll.id());
        }
        } finally {
            if (sourceBlockFound) list.remove(0);
        }
    }
    
    protected void addMethodEqualities(JCMethodInvocation call, BasicBlock bl) {
        if (true || !JmlOption.isOption(context, JmlOption.DETERMINISM)) return;
        MethodSymbol msym = (MethodSymbol)((JCIdent)call.meth).sym;
        if (JmlAttr.instance(context).isFunction(msym)) return;
        summarizeBlock( currentBlock);
        List<BasicProgram.BasicBlock.MethodInfo> list = currentBlock.methodInfoMap.get(msym);
        currentBlock.methodInfoMap = null;
        if (list != null) for (BasicProgram.BasicBlock.MethodInfo info: list) {
            if (msym != treeutils.getSym(info.meth)) continue;
            JCExpression newrecv = null;
            if (info.meth instanceof JCIdent) {
                newrecv = info.meth;
                if (((JCIdent)info.meth).name == ((JCIdent)call.meth).name) continue;
            } else if (info.meth instanceof JCFieldAccess) {
                JCExpression callrecv = ((JCFieldAccess)call.meth).selected;
                newrecv = M.Select(callrecv, ((JCFieldAccess)info.meth).name);
                if (((JCFieldAccess)info.meth).name == ((JCFieldAccess)call.meth).name) continue;
            } else {
                log.error("jml.internal","Call receiver not implemented " + call.meth.toString());
            }
            JCExpression eq = M.Apply(call.typeargs,newrecv,call.args);
            eq.type = call.type;
            eq = treeutils.makeEquality(Position.NOPOS, call, eq);
            JCExpression ex = treeutils.makeImplies(Position.NOPOS, info.path, eq);
            JmlStatementExpr st = M.at(Position.NOPOS).JmlExpressionStatement(assumeID, assumeClause,Label.DSA,ex);
            currentBlock.statements.add(st);
        }
    }
    
   protected void summarizeBlock(BasicBlock bl) {
       // Check for a heap item

       boolean heapAssignFound = false;
       List<JCStatement> stats = bl.statements;
       ListIterator<JCStatement> iter = stats.listIterator(stats.size());
       while (iter.hasPrevious()) {
           JCStatement stat = iter.previous();
           if (stat instanceof JmlStatementExpr) {
               Label label = ((JmlStatementExpr)stat).label;
               if (label == Label.ASSIGNMENT && stat.toString().contains("_heap___")) {
                   heapAssignFound = true;
                   break;
               }
           }
       }

       Map<MethodSymbol,List<BasicProgram.BasicBlock.MethodInfo>> myStartMap = new HashMap<>();
       yy: if (!heapAssignFound) {
           // Combine information from preceders
           for (BasicBlock bll: bl.preceders) {
               if (bll.methodInfoMap == null) summarizeBlock(bll);
           }
           int numpreceders = bl.preceders.size();
           xx: {
               if (numpreceders == 2 && bl.preceders.get(0).preceders.size() == 1 &&
                       bl.preceders.get(1).preceders.size() == 1) {
                   Map<MethodSymbol,List<BasicProgram.BasicBlock.MethodInfo>> map0 = bl.preceders.get(0).methodInfoMap;
                   Map<MethodSymbol,List<BasicProgram.BasicBlock.MethodInfo>> map1 = bl.preceders.get(1).methodInfoMap;
                   if (map0.entrySet().size() != map1.entrySet().size()) break xx;
                   for (MethodSymbol m: map0.keySet()) {
                       if (map0.get(m) != map1.get(m)) break xx;
                   }
                   myStartMap.putAll(map0);
                   break yy;
               }
           }
           if (numpreceders == 1) {
               BasicBlock bll = bl.preceders.get(0);
               myStartMap.putAll(bll.methodInfoMap);
           } else {
               for (BasicBlock bll: bl.preceders) {
                   JCBinary bin = null;
                   JCExpression id = M.at(Position.NOPOS).Ident(bl.id() + "_source").setType(syms.intType);
                   JCExpression lit = M.Literal(bll.unique).setType(syms.intType);
                   bin = M.at(Position.NOPOS).Binary(JCTree.Tag.EQ, id, lit);
                   bin.setType(syms.booleanType);
                   bin.operator = treeutils.inteqSymbol;
                   for (Map.Entry<MethodSymbol,List<BasicProgram.BasicBlock.MethodInfo>> entry: bll.methodInfoMap.entrySet()) {
                       MethodSymbol msym = entry.getKey();
                       if (!myStartMap.containsKey(msym)) myStartMap.put(msym, new LinkedList<BasicProgram.BasicBlock.MethodInfo>());
                       List<BasicProgram.BasicBlock.MethodInfo> mylist = myStartMap.get(msym);
                       for (BasicProgram.BasicBlock.MethodInfo e: entry.getValue()) {
                           JCExpression a = treeutils.makeAnd(Position.NOPOS, e.path, bin);
                           mylist.add(new BasicProgram.BasicBlock.MethodInfo(e.meth, a));
                       }
                   }
               }
           }
           
           iter = stats.listIterator(0);
       }
       
       // Now add in information from current block
         
        while (iter.hasNext()) {
            JCStatement stat = iter.next();
            if (stat instanceof JmlStatementExpr) {
                Label label = ((JmlStatementExpr)stat).label;
                if (label == Label.METHOD_ASSUME) {
                    JCMethodInvocation prevcall = (JCMethodInvocation)(((JCBinary)((JmlStatementExpr)stat).expression).rhs);
                    MethodSymbol msym = (MethodSymbol)treeutils.getSym(prevcall.meth);
                    myStartMap.put(msym, new LinkedList<BasicProgram.BasicBlock.MethodInfo>());
                    BasicProgram.BasicBlock.MethodInfo info = new BasicProgram.BasicBlock.MethodInfo(prevcall.meth,treeutils.trueLit);
                    myStartMap.get(msym).add(info);
                }
            }
        }
        
        bl.methodInfoMap = myStartMap;
    }
    
    // OK
    @Override
    public void visitJmlStatementHavoc(JmlStatementHavoc that) { 
        for (JCExpression item : that.storerefs) {
            havoc(item);
        }
    }
    
    
    protected boolean isFinal(Symbol sym) {
        return (sym.flags() & Flags.FINAL) != 0;
    }
    

    // Visit methods for Expressions for the most part just use the super class's
    // visit methods. These just call visitors on each subexpression.
    // Everything is transformed in place.
    // There are a few nodes that get special treatment:
    //  JCIdent - the name is overwritten with the single-assignment name (note that
    //     the name will be out of synch with the symbol)
    //  \old and \pre expressions - these need to find the correct scope and translate
    //     JCIdent nodes within their scopes using the correct single-assignment names
        
    // OK
    @Override
    public void visitIdent(JCIdent that) {
        if (that.sym instanceof Symbol.VarSymbol){ 
            Symbol.VarSymbol vsym = (Symbol.VarSymbol)that.sym;
            if (localVars.containsKey(vsym)) {
                that.name = localVars.get(vsym).name;
            } else if (currentMap != null) { // FIXME - why would currentMap ever be null?
                Name newname = currentMap.getCurrentName(vsym);
                if (that.name != vsym.name && newname != that.name) {
                    log.warning(that, "jml.internal", "Double rewriting of ident: " + vsym.name + " " + that.name);
                }
                that.name = newname;
                if (isDefined.add(that.name)) {
                    if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("Added " + vsym + " " + that.name);
                    addDeclaration(that);
                }
            }
        } else if (that.sym == null) {
            // Temporary variables that are introduced by decomposing expressions do not have associated symbols
            // They are also only initialized once and only used locally, so we do not track them for DSA purposes
            // Nor do we need to adjust their names.
            // Also, they will have been declared in a declaration, at which time addDeclaration will have been called.
            // Just skip.
            
        } else if (that.sym instanceof Symbol.TypeSymbol) { // Includes class, type parameter, package
            // Type symbols also are never assigned, so we don't need to
            // track their names. So these are left alone also.
        } else {
            log.error(that.pos,"jml.internal","THIS KIND OF IDENT IS NOT HANDLED: " + that + " " + that.sym.getClass());
        }
        result = that;
    }

    // OK
    public void visitLiteral(JCLiteral that) {
        result = that;
    }

    @Override
    public void visitReference(JCTree.JCMemberReference that) {
        result = that;
    }

    @Override
    public void visitLambda(JCTree.JCLambda that) {
        result = that;
    }


    @Override
    public void visitSelect(JCFieldAccess that) {
        if (!(that.sym instanceof Symbol.VarSymbol)) { result = that; return; } // This is a qualified type name 
        VarSymbol vsym = (Symbol.VarSymbol)that.sym;
        if (vsym.name != that.name) {
            result = that;
            return;
        }
        Name n;
        if (isFinal(that.sym) && (!methodDecl.sym.isConstructor() || utils.isJMLStatic(that.sym))) {
            n = labelmaps.get(null).getCurrentName(vsym);
        } else {
            n = currentMap.getCurrentName((Symbol.VarSymbol)that.sym);
        }
        that.name = n;
        
        if (utils.isJMLStatic(that.sym)) {
            JCIdent id = treeutils.makeIdent(that.pos,that.sym);
            id.name = n;
            if (isDefined.add(n)) {
                addDeclaration(id);
            }
            result = id;
        } else {
            if (isDefined.add(n)) {
                JCIdent id = treeutils.makeIdent(that.pos,that.sym);
                id.name = n;
                addDeclaration(id);
            }
            scan(that.selected);
            result = that;
        }
    }
    
    public void visitIndexed(JCArrayAccess that) {
        scan(that.indexed);
        JCExpression indexed = result;
        scan(that.index);
        JCExpression index = result;
        JCIdent arr = getArrayIdent(JmlTypes.instance(context).indexType(that.indexed.type),that.type,that.pos);
        if (that instanceof JmlBBArrayAccess) {
            that.indexed = indexed;
            that.index = index;
            ((JmlBBArrayAccess)that).arraysId = arr;
            result = that;
        } else {
            log.warning(that,"jml.internal","Did not expect a JCArrayAccess node in BasicBlocker2.visitIndexed");
            result = new JmlBBArrayAccess(arr,indexed,index);
        }
    }


    @Override
    public void visitAssignop(JCAssignOp that) {
        // These should be already desugared to assignments.
        shouldNotBeCalled(that);
    }
    
    // FIXME - review
    public void visitAssign(JCAssign that) {
        //scan(that.lhs);
        JCExpression left = that.lhs;
        JCExpression right = convertExpr(that.rhs);
        result = doAssignment(that.type,left,right,that.pos,that);
        bimap.put(left, result);
        bimap.putf(that, result);
        copyEndPosition(result,that);
    }
    
    public void newIncarnations(JCIdent id) {
        
        
    }
//    
    // FIXME - embedded assignments to array elements are not implemented; no warning either
    // FIXME - is all implicit casting handled
    // Note that only the right expression is translated.
    protected JCExpression doAssignment(Type restype, JCExpression left, JCExpression right, int pos, JCExpression statement) {
        int sp = left.getPreferredPosition();
        JCStatement newStatement;
        JCExpression newExpr;
        if (left instanceof JCIdent) {
            JCIdent id = (JCIdent)left;
            JCIdent newid = newIdentIncarnation(id,sp);
            JCBinary expr = treeutils.makeEquality(pos,newid,right);
            //copyEndPosition(expr,right);
            newStatement = addAssume(sp,Label.ASSIGNMENT,expr,currentBlock.statements);
            newExpr = newid;
        } else if (left instanceof JCArrayAccess) {
            Type ctype = left.type;
            Type indexType = JmlTypes.instance(context).indexType(((JCArrayAccess)left).indexed.type);
            JCIdent arr = getArrayIdent(indexType,ctype,right.pos);
            JCExpression ex = ((JCArrayAccess)left).indexed;
            JCExpression index = ((JCArrayAccess)left).index;
            JCIdent nid = newArrayIncarnation(indexType,right.type,sp);
            
            scan(ex); ex = result;
            scan(index); index = result;
            scan(right); right = result;
            
            //JCExpression rhs = makeStore(ex,index,right);
            JCExpression expr = new JmlBBArrayAssignment(nid,arr,ex,index,right); // FIXME - implicit conversion?
            expr.pos = pos;
            expr.type = restype;
            treeutils.copyEndPosition(expr, right);

            // FIXME - set line and source
            newStatement = addAssume(sp,Label.ASSIGNMENT,expr,currentBlock.statements);
            newExpr = left;
        } else if (left instanceof JCFieldAccess) {
            VarSymbol sym = (VarSymbol)selectorSym(left);
            if (utils.isJMLStatic(sym)) {
                JCIdent id = newIdentUse(sym,sp);
                JCIdent newid = newIdentIncarnation(id,sp);
                newIncarnations(id);
                // currentBlock.statements.add(treeutils.makeVarDef(newid.type, newid.name, id.sym.owner, pos));
                JCBinary expr = treeutils.makeEquality(pos,newid,right);
                //copyEndPosition(expr,right);
                newStatement = addAssume(statement.getStartPosition(),Label.ASSIGNMENT,expr,currentBlock.statements);
                newExpr = newid;
            } else {
                JCFieldAccess fa = (JCFieldAccess)left;
                scan(fa.selected);
                JCIdent oldfield = newIdentUse((VarSymbol)fa.sym,sp);
                if (isDefined.add(oldfield.name)) {
                    addDeclaration(oldfield);
                }
                JCIdent newfield = newIdentIncarnation(oldfield,sp);
                newIncarnations(oldfield);
                if (isDefined.add(newfield.name)) {
                    addDeclaration(newfield);
                }
                JCExpression expr = new JmlBBFieldAssignment(newfield,oldfield,fa.selected,right);
                expr.pos = pos;
                expr.type = restype;
                treeutils.copyEndPosition(expr, right);

                // FIXME - set line and source
                newStatement = addAssume(sp,Label.ASSIGNMENT,expr,currentBlock.statements);
                newIdentIncarnation(heapVar,pos);
                JCFieldAccess newfa = (JCFieldAccess)M.at(left.pos).Select(fa.selected, newfield.sym);
                newfa.name = newfield.name;
                newExpr = newfa;
            }
        } else {
            log.error("jml.internal","Unexpected case in BasicBlocker2.doAssignment: " + left.getClass() + " " + left);
            return null;
        }
        pathmap.put(statement,newStatement);
        return newExpr;
    }
    
    protected Symbol selectorSym(JCTree tree) {
        if (tree instanceof JCIdent) return ((JCIdent)tree).sym;
        if (tree instanceof JCFieldAccess) return ((JCFieldAccess)tree).sym;
        log.error("jml.internal","Unexpected case in selectorSym: " + tree.getClass() + " " + tree);
        return null;
    }

    // OK -= except FIXME - review newIdentIncarnation
    public void visitVarDef(JCVariableDecl that) { 
        currentBlock.statements.add(comment(that));
        JCIdent lhs = newIdentIncarnation(that.sym,that.getPreferredPosition());
        isDefined.add(lhs.name);
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.getWriter(WriterKind.NOTICE).println("Added " + lhs.sym + " " + lhs.name);
        if (that.init != null) {
            // Create and store the new lhs incarnation before translating the
            // initializer because the initializer is in the scope of the newly
            // declared variable.  Actually if there is such a situation, it 
            // will likely generate an error about use of an uninitialized variable.
            scan(that.init);
            JCExpression expr = treeutils.makeBinary(that.pos,JCBinary.Tag.EQ,lhs,that.init);
            addAssume(that.getStartPosition(),Label.ASSIGNMENT,expr,currentBlock.statements);
        }
    }

//    public void visitJmlVariableDecl(JmlVariableDecl that) {
//        JCIdent id;
//        if (that.sym == null || that.sym.owner == null) {
////            if (that.init != null) {
////                scan(that.init);
////                that.init = result;
////            }
//            Name n = encodedName(that.sym,0L);
//            that.name = n;
//            id = factory.at(0).Ident(n);
//            id.sym = that.sym;
//            id.type = that.type;
//            if (isDefined.add(n)) {
//                addDeclaration(id);
//            }
//
//            currentMap.putSAVersion(that.sym,n,0);
//            //currentBlock.statements.add(that);
//        } else {
//            // FIXME - why not make a declaration?
//            id = newIdentIncarnation(that.sym,that.getPreferredPosition());
//            isDefined.add(id.name);
//            that.name = id.name;
//        }
//        scan(that.ident); // FIXME - is this needed since we already set the encodedname
//        if (that.init != null) {
//            scan(that.init);
//            that.init = result;
//            JCBinary expr = treeutils.makeBinary(that.pos,JCBinary.EQ, that.ident != null ? that.ident : id,that.init);
//            addAssume(that.getStartPosition(),Label.ASSIGNMENT,expr,currentBlock.statements);
//        }
//    }
    
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        if (that.sym == null || that.sym.owner == null) {
            if (that.init != null) {
                scan(that.init);
                that.init = result;
            }
            Name n = encodedName(that.sym,0L);
            that.name = n;
            if (isDefined.add(n)) {
//                JCIdent id = factory.at(0).Ident(n);
//                id.sym = that.sym;
//                id.type = that.type;
//                addDeclaration(id);
            }

            currentMap.putSAVersion(that.sym,n,0);
            currentBlock.statements.add(that);
            scan(that.ident); // FIXME - is this needed since we already set the encodedname
        } else {
            // FIXME - why not make a declaration?
            JCIdent lhs = newIdentIncarnation(that.sym,that.getPreferredPosition());
            isDefined.add(lhs.name);
            that.name = lhs.name;
            scan(that.ident); // FIXME - is this needed since we already set the encodedname
            if (that.init != null) {
                scan(that.init);
                that.init = result;
                JCExpression expr = treeutils.makeBinary(that.pos,JCBinary.Tag.EQ, that.ident != null ? that.ident : lhs,that.init);
                addAssume(that.getStartPosition(),Label.ASSIGNMENT,expr,currentBlock.statements);
            }
        }
    }

    // OK
    @Override
    public void visitSynchronized(JCSynchronized that)   { 
        super.visitSynchronized(that);
    }
    
    public void visitWildcard(JCWildcard that)           { notImpl(that); }
    public void visitTypeBoundKind(TypeBoundKind that)   { notImpl(that); }
    public void visitAnnotation(JCAnnotation that)       { notImpl(that); }
    public void visitModifiers(JCModifiers that)         { notImpl(that); }
    public void visitErroneous(JCErroneous that)         { notImpl(that); }

    public void visitLetExpr(LetExpr that) { 
        // FIXME - do we need to add these so they are not rewritten?
        for (JCVariableDecl d: that.defs) {
            scan(d.init);
        }
        for (JCVariableDecl d: that.defs) {
            Name n = encodedName(d.sym,0L);
            d.name = n;
            localVars.put(d.sym,d);
        }
        try {
            scan(that.expr);
        } finally {
            result = that;
            for (JCVariableDecl d: that.defs) {
                localVars.remove(d.sym);
            }
        }
    }
    
    @Override
    public void visitTypeIdent(JCPrimitiveTypeTree that) { 
        // A primitive type
        result = that; 
    }
    
    @Override
    public void visitTypeArray(JCArrayTypeTree that)     { 
        // An array type (e.g., A[] )
        result = that; 
    }
    
    @Override
    public void visitTypeApply(JCTypeApply that)         { 
        // This is the application of a generic type to its parameters
        // e.g., List<Integer> or List<T>
        
        // Just skip
        result = that;
    }
    
    @Override
    public void visitTypeParameter(JCTypeParameter that) { 
        // This is a parameter of a generic type definition
        // e.g., T, or T extends X, or T super Y
        notImpl(that); 
    }

    // Note: all control flow statements are handled by the parent class:
    //  Block, Break, Case, Catch, Continue, loops, If
    //  Switch, Try, Throw, Return

    // FIXME _ implement
    @Override public void visitJmlSetComprehension(JmlSetComprehension that) { notImpl(that); }
    
    
    @Override public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) { 
        notImpl(that); 
    }
    @Override public void visitJmlChoose(JmlChoose that)                     { notImpl(that); }
    @Override public void visitJmlMethodSig(JmlMethodSig that)                     { notImpl(that); }
    @Override public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that)                     { notImpl(that); }
    @Override public void visitJmlModelProgramStatement(JmlModelProgramStatement that)                     { notImpl(that); }
    @Override public void visitJmlGroupName(JmlGroupName that)               { notImpl(that); }
    @Override public void visitJmlTypeClauseIn(JmlTypeClauseIn that)         { notImpl(that); }
    @Override public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that)     { notImpl(that); }
    @Override public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that)     { notImpl(that); }
    @Override public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that)     { notImpl(that); }
    @Override public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) { notImpl(that); }
    @Override public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) { notImpl(that); }
    @Override public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) { notImpl(that); }
    @Override public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) { notImpl(that); }
    @Override public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) { notImpl(that); }
    @Override public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) { notImpl(that); }
    @Override public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) { notImpl(that); }
    @Override public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) { notImpl(that); }
    @Override public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) { notImpl(that); }
    @Override public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) { notImpl(that); }
    @Override public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) { notImpl(that); }
    @Override public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) { notImpl(that); }
    @Override public void visitJmlSpecificationCase(JmlSpecificationCase that){ notImpl(that); }
    @Override public void visitJmlMethodSpecs(JmlMethodSpecs that)           { notImpl(that); }
    @Override public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that){ notImpl(that); }
    @Override public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that)   { notImpl(that); }
    @Override public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that){ notImpl(that); }

    // These should all be translated away prior to calling the basic blocker
    @Override public void visitJmlBinary(JmlBinary that)           { shouldNotBeCalled(that); }
    @Override public void visitJmlLblExpression(JmlLblExpression that) { shouldNotBeCalled(that); }    

    // These should not be implemented
    @Override public void visitTopLevel(JCCompilationUnit that)    { shouldNotBeCalled(that); }
    @Override public void visitImport(JCImport that)               { shouldNotBeCalled(that); }
    @Override public void visitJmlCompilationUnit(JmlCompilationUnit that)   { shouldNotBeCalled(that); }
    @Override public void visitJmlImport(JmlImport that)                     { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodDecl(JmlMethodDecl that)  { shouldNotBeCalled(that); }
//    @Override public void visitJmlStatement(JmlStatement that)    { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementSpec(JmlStatementSpec that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementDecls(JmlStatementDecls that) { shouldNotBeCalled(that); }
    @Override public void visitMethodDef(JCMethodDecl that)        { shouldNotBeCalled(that); }
    
    
    final protected Map<Symbol,JCVariableDecl> localVars = new HashMap<>();
    
    @Override public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) { 
        for (JCVariableDecl d: that.decls) {
            localVars.put(d.sym,d);
            //d.name = encodedName(d.sym,0L); // FIXME - why doesn't this work?
        }
        try {
            that.range = convertExpr(that.range);
            that.value = convertExpr(that.value);
            scanList(that.triggers);
            result = that;
        } finally {
            for (JCVariableDecl d: that.decls) {
                localVars.remove(d.sym);
            }
        }
 
    }

    // OK
    @Override public void visitBinary(JCBinary that) {
//        if (that.lhs instanceof JCBinary && that.rhs instanceof JCBinary) {
//            JCBinary lhsb = (JCBinary)that.lhs;
//            JCBinary rhsb = (JCBinary)that.rhs;
//            if (lhsb.rhs == rhsb.lhs) {
//                lhsb.lhs = convertExpr(lhsb.lhs);
//                lhsb.rhs = convertExpr(lhsb.rhs);
//                rhsb.lhs = lhsb.rhs;
//                rhsb.rhs = convertExpr(rhsb.rhs);
//                result = that;
//                return;
//            }
//        }
        that.lhs = convertExpr(that.lhs);
        that.rhs = convertExpr(that.rhs);
        result = that; 
    }
    
    // OK
    @Override public void visitUnary(JCUnary that) { 
        that.arg = convertExpr(that.arg);
        result = that; 
    }
    
    // OK
    @Override public void visitParens(JCParens that) { 
        that.expr = convertExpr(that.expr);
        result = that;
    }
    
    // OK
    @Override public void visitConditional(JCConditional that) { 
        that.cond = convertExpr(that.cond);
        that.truepart = convertExpr(that.truepart);
        that.falsepart = convertExpr(that.falsepart);
        result = that; 
    }
    
    // FIXME - review
    @Override public void visitJmlSingleton(JmlSingleton that) {
        notImpl(that);
    }

    // OK // FIXME - does this expression type appear?
    @Override public void visitTypeTest(JCInstanceOf that) { 
        that.expr = convertExpr(that.expr);
        scan(that.clazz); // FIXME - if the type tree is rewritten, we are not capturing the result
        result = that; 
    }

    // OK // FIXME - does this expression type appear? in REF case it should be a noop
    @Override public void visitTypeCast(JCTypeCast that) { 
        //scan(that.clazz); // FIXME - if the type tree is rewritten, we are not capturing the result
        that.expr = convertExpr(that.expr);
        result = M.TypeCast(that.clazz, result);
        result.type = that.type;
    }
    
    @Override
    public void visitNewClass(JCNewClass that) {
        // This AST node should be transformed away by JmlAssertionAdder
        shouldNotBeCalled(that);
    }

    @Override
    public void visitNewArray(JCNewArray that) {
        // This AST node should be transformed away by JmlAssertionAdder
        shouldNotBeCalled(that);
    }

// Do not need to override these methods
//  @Override public void visitSkip(JCSkip that) { super.visitSkip(that); }
    
    @Override
    public void visitJmlStatementLoopExpr(JmlStatementLoopExpr that) { 
        shouldNotBeCalled(that); // These are the specs for loops - they are handled in the loop visitors
    }
    
    @Override
    public void visitJmlStatementLoopModifies(JmlStatementLoopModifies that) { 
        shouldNotBeCalled(that); // These are the specs for loops - they are handled in the loop visitors
    }
    
    
    // FIXME - what about  AssignOp, NewClass, NewArray

    /** This class implements a map from variable (as a Symbol) to a unique name
     * as used in Single-Assignment form. At any given point in the program there is
     * a current mapping from symbols to names, giving the name that holds the value
     * for the symbol at that location. When a variable is assigned a new value, it
     * gets a new current Single-Assignment name and the map is updated. Copies of 
     * these maps are saved with each block, representing the state of the map at the
     * end of the block.
     * <P>
     * FIXME - explain this better, and the everythingIncarnation
     * Each Symbol also has an incarnation number. The number is incremented as new
     * incarnations happen. The number is used to form the variable's SA name.
     * <P>
     * The everythingIncarnation value is used as the default incarnation number
     * for symbols that have not yet been used. This is 0 in the pre-state. It
     * is needed, for example, for the following circumstance. Some method call
     * havocs everything, then a class field is used (without having been used
     * before and therefore not having an entry in the name maps). That class field
     * must use a SA Version number different than 0. If it is subsequently
     * used in an \old expression, it will use an SA Version number of 0 in that
     * circumstance and must be distinguished from the use after everything has
     * been havoced.
     */
    // The class is intentionally not static - so it can use encodedName
    public class VarMap {
        // The maps allow VarSymbol or TypeSymbol (for TypeVar)
        private Map<VarSymbol,Long> mapSAVersion = new HashMap<VarSymbol,Long>();
        private Map<TypeSymbol,Long> maptypeSAVersion = new HashMap<TypeSymbol,Long>();
        private Map<Symbol,Name> mapname = new HashMap<Symbol,Name>();
        
        /** Returns a copy of the map */
        public VarMap copy() {
            VarMap v = new VarMap();
            v.mapSAVersion.putAll(this.mapSAVersion);
            v.maptypeSAVersion.putAll(this.maptypeSAVersion);
            v.mapname.putAll(this.mapname);
            return v;
        }
        
        /** Returns the name for a variable symbol as stored in this map */
        public /*@Nullable*/ Name getName(VarSymbol vsym) {
            Name s = mapname.get(vsym);
            return s;
        }
        
        /** Returns the name for a variable symbol as stored in this map, creating (and
         * storing) one if it is not present. */
        public /*@NonNull*/ Name getCurrentName(VarSymbol vsym) {
            Name s = mapname.get(vsym);
            if (vsym == syms.lengthVar) return vsym.name;
            if (s == null) {
                // If there was no mapping at all, we add the name to 
                // all existing maps, with an incarnation number of 0.
                // This makes sure that any maps at labels have a definition
                // of the variable.
                // FIXME - this does not handle a havoc between labels, 
                s = encodedName(vsym,vsym.pos);
                for (VarMap map: blockmaps.values()) {
                    if (map.mapname.get(vsym) == null) map.putSAVersion(vsym,s,0L);
                }
                for (VarMap map: labelmaps.values()) {
                    if (map.mapname.get(vsym) == null) map.putSAVersion(vsym,s,0L);
                }

                if (isDefined.add(s)) {
                    JCIdent idd = treeutils.makeIdent(vsym.pos,s,vsym);
                    addDeclaration(idd);
                }

                putSAVersion(vsym,s,unique);
            }
            return s;
        }
        
        /** Returns the name for a type symbol as stored in this map; returns null
         * if no name is stored */
        public /*@ Nullable */ Name getName(TypeSymbol vsym) {
            Name s = mapname.get(vsym);
            return s;
        }
        
        /** Returns the name for a type symbol as stored in this map, creating (and
         * storing) one if it is not present. */
        public /*@NonNull*/ Name getCurrentName(TypeSymbol vsym) {
            Name s = mapname.get(vsym);
            if (s == null) {
                s = encodedTypeName(vsym,0);
                putSAVersion(vsym,s);
            }
            return s;
        }
        
        /** Returns the incarnation number (single-assignment version
         * number) for the symbol */
        public Long getSAVersionNum(VarSymbol vsym) {
            Long i = mapSAVersion.get(vsym);
            if (i == null) {
                Name n = encodedName(vsym,0L);
                for (VarMap map: blockmaps.values()) {
                    map.putSAVersion(vsym,n,0L);
                }
                for (VarMap map: labelmaps.values()) {
                    map.putSAVersion(vsym,n,0L);
                }
                if (isDefined.add(n)) {
                    JCIdent id = treeutils.makeIdent(vsym.pos,n,vsym);
                    addDeclaration(id);
                }
                i = 0L;
            }
            return i;
        }
        
        /** Returns the incarnation number (single-assignment version
         * number) for the type symbol */
        public Long getSAVersionNum(TypeSymbol vsym) {
            Long i = maptypeSAVersion.get(vsym);
            if (i == null) {
                maptypeSAVersion.put(vsym,(i=0L));
            }
            return i;
        }
        
        /** Stores a new SA version of a symbol, with a custom name */
        public void putSAVersion(VarSymbol vsym, Name s, long version) {
            mapSAVersion.put(vsym,version);
            mapname.put(vsym,s);
        }
        
        /** Stores a new SA version of a symbol */
        public Name putSAVersion(VarSymbol vsym, long version) {
            Name s = encodedName(vsym,version);
            mapSAVersion.put(vsym,version);
            mapname.put(vsym,s);
            return s;
        }
        
        /** Stores a new SA version of a type symbol */
        public void putSAVersion(TypeSymbol vsym, Name s) {
            maptypeSAVersion.put(vsym,0L);
            mapname.put(vsym,s);
        }

        /** Adds everything in the argument map into the receiver's map */
        public void putAll(VarMap m) {
            mapSAVersion.putAll(m.mapSAVersion);
            maptypeSAVersion.putAll(m.maptypeSAVersion);
            mapname.putAll(m.mapname);
        }
        
        /** Removes a symbol from the map, as when it goes out of scope or
         * when a temporary variable is no longer needed. */
        public Long remove(Symbol v) {
            mapname.remove(v);
            return mapSAVersion.remove(v);
        }
        
        /** Returns the Set of all variable Symbols that are in the map;
         * note that variables that are in scope but have not been used
         * will not necessarily be present in the map. */
        public Set<VarSymbol> keySet() {
            return mapSAVersion.keySet();
        }
        
//        public String debug(String s) {
//            String r = "";
//            for (VarSymbol v: keySet()) {
//                if (v.toString().equals(s)) r = r + getCurrentName(v) + " ";
//            }
//            return r;
//        }
        
        /** Returns a debug representation of the map */
        public String toString() {
            StringBuilder s = new StringBuilder();
            s.append("[");
            Iterator<Map.Entry<VarSymbol,Long>> entries = mapSAVersion.entrySet().iterator();
            while (entries.hasNext()) {
                Map.Entry<VarSymbol,Long> entry = entries.next();
                s.append(entry.getKey());
                s.append("=");
                s.append(entry.getValue());
                s.append(",");
            }
            Iterator<Map.Entry<TypeSymbol,Long>> entriest = maptypeSAVersion.entrySet().iterator();
            while (entries.hasNext()) {
                Map.Entry<TypeSymbol,Long> entry = entriest.next();
                s.append(entry.getKey());
                s.append("=");
                s.append(entry.getValue());
                s.append(",");
            }
            s.append("]");
            return s.toString();
        }
    }
    
    
    static class GetSymbols extends JmlTreeScanner {
        
        boolean noMethods = false;
        
        public static Set<VarSymbol> collectSymbols(JCBlock method, JCClassDecl classDecl) {
            GetSymbols gs = new GetSymbols();
            gs.noMethods = false;
            method.accept(gs);
            gs.noMethods = true;
            if (classDecl != null) classDecl.accept(gs); // classDecl can be null when we have not translated the whole class, just the method - e.g. doEsc from the API (FIXME)
            return gs.syms;
        }
        
        private Set<VarSymbol> syms = new HashSet<VarSymbol>();
        
        public GetSymbols() {
            scanMode = JmlTreeScanner.AST_SPEC_MODE;
        }
        
        public void visitClassDef(JCClassDecl that) {
            scan(that.mods);
            scan(that.typarams);
            scan(that.extending);
            scan(that.implementing);
            for (JCTree def: that.defs) {
                if (!noMethods || !(def instanceof JCMethodDecl)) scan(def);
            }
        }
        
        public void visitIdent(JCIdent that) {
            if (that.sym instanceof VarSymbol &&
                   that.sym.owner instanceof ClassSymbol) syms.add((VarSymbol)that.sym);
        }
        
        public void visitSelect(JCFieldAccess that) {
            if (that.sym instanceof VarSymbol &&
                    that.sym.owner instanceof ClassSymbol &&
                    !that.sym.toString().equals("length")) syms.add((VarSymbol)that.sym);
        }
    }

}
