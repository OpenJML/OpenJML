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
import java.util.Map;
import java.util.Set;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAccess;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAssignment;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAccess;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAssignment;
import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlChoose;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlConstraintMethodSig;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlImport;
import org.jmlspecs.openjml.JmlTree.JmlLblExpression;
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
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;

import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.ArrayType;
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
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

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
    public static final @NonNull String HEAP_VAR = "_heap__";
    
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
    
    /** The compilation context */
    @NonNull final protected Context context;
    
    /** The log to which to send error, warning and notice messages */
    @NonNull final protected Log log;
    
    /** The symbol table from the compilation context, initialized in the constructor */
    @NonNull final protected Symtab syms;
    
    /** The Names table from the compilation context, initialized in the constructor */
    @NonNull final protected Names names;
    
    /** The JmlTreeUtils object, holding a bunch of tree-making utilities */
    @NonNull final protected JmlTreeUtils treeutils;
    
    /** General utilities */
    @NonNull final protected Utils utils;
    
    /** The factory used to create AST nodes, initialized in the constructor */
    @NonNull final protected JmlTree.Maker factory;

    // Caution - the following are handy, but they are shared, so they won't
    // have proper position information - which is OK for esc at this point
    
    /** Holds an AST node for a boolean true literal, initialized in the constructor */
    @NonNull final protected JCLiteral trueLiteral;
    
    /** Holds an AST node for a boolean false literal, initialized in the constructor */
    @NonNull final protected JCLiteral falseLiteral;
    
    /** Identifier of a synthesized object field holding the length of an array object, initialized in the constructor */
    @NonNull final protected JCIdent lengthIdent;

    /** Symbol of a synthesized object field holding the length of an array object, initialized in the constructor */
    @NonNull final protected VarSymbol lengthSym;
    
    // THE FOLLOWING FIELDS ARE USED IN THE COURSE OF DOING THE WORK OF CONVERTING
    // TO BASIC BLOCKS.  They are fields of the class because they need to be
    // shared across the visitor methods.
    
    /** Place to put new definitions, such as the equalities defining auxiliary variables */
    protected List<BasicProgram.Definition> newdefs;
    
    /** Place to put new background assertions, such as axioms and class predicates */
    protected List<JCExpression> background;
    
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
    @NonNull final protected Map<BasicBlock,VarMap> blockmaps = new HashMap<BasicBlock,VarMap>();
    
    /** A mapping from labels to the sym->incarnation map operative at the position
     * of the label.
     */
    @NonNull final protected Map<Name,VarMap> labelmaps = new HashMap<Name,VarMap>();
        
    /** Contains names for which a declaration has been issued. */
    final protected Set<Name> isDefined = new HashSet<Name>();

    // THESE VARIABLES ARE SET (AND RESET) IN THE COURSE OF COMPUTATION
    // (so they do not need initialization)
    
    /** The map from symbol to incarnation number in current use */
    @NonNull protected VarMap currentMap;
    
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
        
        this.context = context;
        this.log = Log.instance(context);
        this.factory = JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.syms = Symtab.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
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
        // heapVar is initialized later
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
        log.noticeWriter.println("NOT IMPLEMENTED: BasicBlocker2 - " + that.getClass());
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
        if (incarnationPosition <= 0 || own == null) {
            Name n = sym.getQualifiedName();
            if (sym.pos >= 0 && !n.toString().equals(Strings.thisName)) n = names.fromString(n.toString() + ("_" + sym.pos));
            if (own != null && own != methodDecl.sym.owner && own instanceof TypeSymbol) {
                Name s = own.getQualifiedName();
                n = names.fromString(s.toString() + "." + n.toString());
            }
            return n;
        } else
            return names.fromString(
                    sym.getQualifiedName() 
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
    protected JCIdent newArrayIncarnation(Type componentType, int usePosition) {
        JCIdent id = getArrayIdent(componentType,usePosition);
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

        // FIXME - are these needed or not?
        heapVar = treeutils.makeIdent(0,HEAP_VAR,syms.intType);
        newIdentIncarnation(heapVar,0);

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
        
        processBlock(bodyBlock); // Iteratively creates and processes following blocks
        
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
        JmlTree.JmlStatementExpr st = factory.at(statement.pos()).JmlExpressionStatement(JmlToken.ASSERT,label,trExpr);
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
        JCIdent t = treeutils.makeIdent(0,that.sym);
        t.name = that.name;
        program.declarations.add(t);
    }
    

    // FIXME - REVIEW and document
    static protected String encodeType(Type t) {   // FIXME String? char? void? unsigned?
        if (t instanceof ArrayType) {
            return "refA$" + encodeType(((ArrayType)t).getComponentType());
        } else if (!t.isPrimitive()) {
            return "REF";
        } else if (t.tag == TypeTags.INT || t.tag == TypeTags.SHORT || t.tag == TypeTags.LONG || t.tag == TypeTags.BYTE) {
            return "int";
        } else if (t.tag == TypeTags.BOOLEAN) {
            return "bool";
        } else if (t.tag == TypeTags.FLOAT || t.tag == TypeTags.DOUBLE) {
            return "real";
        } else if (t.tag == TypeTags.CHAR) {
            return "int";
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
    protected VarSymbol getArrayBaseSym(Type componentType) {
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
    }

    /** Return an identifier for the heap array that manages the given component type. */
    protected JCIdent getArrayIdent(Type componentType, int pos) {
        VarSymbol vsym = getArrayBaseSym(componentType);
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
                            JCBinary eq = treeutils.makeEquality(pos,pnew,pold);
                            addAssume(pos,Label.DSA,eq,b.statements);
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
                    for (VarMap m: all) {
                        Name n = m.getName(sym);
                        if (n == null) { skip = true; break; }
                        Long i = m.getSAVersionNum(sym);
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
                    //if (different) {
                        for (BasicBlock b: block.preceders) {
                            VarMap m = blockmaps.get(b);
                            Long i = m.getSAVersionNum(sym);
                            if (i < max) {
                                // No position information for these nodes
                                // Type information put in, though I don't know that we need it
                                JCIdent pold = newIdentUse(m,sym,pos);
                                JCIdent pnew = newIdentUse(newMap,sym,pos);
                                JCBinary eq = treeutils.makeEquality(pos,pnew,pold);
                                addAssume(pos,Label.DSA,eq,b.statements);
                            }
                        }
                    //}
                }
            }
        }
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
        JCExpression ee = treeutils.makeJmlBinary(epos,JmlToken.SUBTYPE_OF,e1,e2);
        return ee;
    }
    
    // FIXME - review and document
    protected JCExpression makeSignalsOnly(JmlMethodClauseSignalsOnly clause) {
        JCExpression e = treeutils.makeBooleanLiteral(clause.pos,false);
        JCExpression id = factory.at(0).JmlSingleton(JmlToken.BSEXCEPTION);
        for (JCExpression typetree: clause.list) {
            int pos = typetree.getStartPosition();
            e = treeutils.makeBinary(pos, 
                    JCTree.OR, makeNNInstanceof(id, pos, typetree.type, pos), e);
        }
        return e;
    }


    // STATEMENT NODES
    
    // OK
    @Override
    public void visitLabelled(JCLabeledStatement that) {
        VarMap map = currentMap.copy();
        labelmaps.put(that.label,map);
        super.visitLabelled(that);
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
                obj = ( fa.selected );
                // FIXME - should do better than converting to String
                //if (!fa.selected.type.toString().endsWith("JMLTYPE")) checkForNull(obj,fa.pos,trueLiteral,null);
            }
            
        } else if (that.meth instanceof JCIdent) {
            log.error(that.pos,"jml.internal","Did not expect a JCIdent here: " + that);
            result = treeutils.makeZeroEquivalentLit(that.pos, that.type);
            return;
        } else {
            // FIXME - not implemented
            log.warning("esc.not.implemented","BasicBlocker2.visitApply for " + that);
            msym = null;
            obj = null;
            result = trueLiteral;
            return;
        }
        if (msym != null && msym.type instanceof Type.ForAll) tfa = (Type.ForAll)msym.type;

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
        if (that.token == JmlToken.BSOLD || that.token == JmlToken.BSPRE || that.token == JmlToken.BSPAST) {
            VarMap savedMap = currentMap;
            try {
                if (that.args.size() == 1) {
                    currentMap = premap;
                    that.args.get(0).accept(this);
                } else {
                    JCIdent label = (JCIdent)that.args.get(1);
                    currentMap = labelmaps.get(label.name);
                    if (currentMap == null) {
                        // This should have already been reported
                        log.error(label.pos,"jml.unknown.label",label.name.toString());
                        // Use premap, just to keep going, though that may
                        // cause other errors
                        currentMap = premap;
                    }
                    that.args.get(0).accept(this);
                    that.args = com.sun.tools.javac.util.List.<JCExpression>of(that.args.get(0));
                }
                that.token = JmlToken.BSSAME; // A no-op // TODO - Review this
            } finally {
                currentMap = savedMap;
            }
        } else if (that.token == JmlToken.SUBTYPE_OF) {
            scan(that.args.get(0));
            JCExpression lhs = result;
            scan(that.args.get(1));
            JCExpression rhs = result;
            that.args = com.sun.tools.javac.util.List.<JCExpression>of(lhs,rhs);
            result = that;
        } else if (that.token == JmlToken.BSNONNULLELEMENTS) {
            scan(that.args.get(0));
            JCExpression arg = result;
            JCExpression argarrays = getArrayIdent(syms.objectType,that.pos);
            that.args = com.sun.tools.javac.util.List.<JCExpression>of(arg,argarrays);
            result = that;
        } else if (that.token == null || that.token == JmlToken.BSTYPELC || that.token == JmlToken.BSTYPEOF) {
            //super.visitApply(that);  // See testBox - this comes from the implicitConversion - should it be a JCMethodInvocation instead?
            scan(that.typeargs);
            scan(that.meth);
            if (that.meth != null) that.meth = result;
            scanList(that.args);
            result = that;
        } else if (that.token == JmlToken.BSSAME) {
            // In this context, BSSAME is a noop
            scanList(that.args);
            result = that;
        } else {
            log.error(that.pos, "esc.internal.error", "Did not expect this kind of Jml node in BasicBlocker2: " + that.token.internedName());
            shouldNotBeCalled(that);
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
                        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("AddedFF " + oldfield.sym + " " + oldfield.name);
                        addDeclaration(oldfield);
                    }
                    JCIdent newfield = newIdentIncarnation(oldfield,sp);
                    if (isDefined.add(newfield.name)) {
                        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("AddedFF " + newfield.sym + " " + newfield.name);
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
            JmlToken t = ((JmlStoreRefKeyword)storeref).token;
            if (t == JmlToken.BSEVERYTHING) {
                for (VarSymbol vsym: currentMap.keySet()) {
                    // Local variables are not affected by havoc \everything
                    // The owner of a local symbol is a MethodSymbol
                    if (vsym.owner instanceof ClassSymbol) newIdentIncarnation(vsym, storeref.pos);
                }
                // FIXME - symbols added after this havoc \everything will not have new incarnations???
            }
        } else if (storeref instanceof JCArrayAccess) { // Array Access
            JCArrayAccess aa = (JCArrayAccess)storeref;
            int sp = storeref.pos;
            JCIdent arr = getArrayIdent(aa.type,aa.pos);
            JCExpression ex = aa.indexed;
            JCExpression index = aa.index;
            JCIdent nid = newArrayIncarnation(aa.type,sp);
            
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
            if (aa.lo == aa.hi && aa.lo != null) {
                // Single element
                JCIdent arr = getArrayIdent(aa.type,aa.pos);
                JCExpression ex = aa.expression;
                JCExpression index = aa.lo;
                JCIdent nid = newArrayIncarnation(aa.type,sp);
                
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
            } else if (aa.lo == null && aa.hi == null) {
                // Entire array
                JCIdent arr = getArrayIdent(aa.type,aa.pos);
                JCExpression ex = aa.expression;
                JCIdent nid = newArrayIncarnation(aa.type,sp);
                
                scan(ex); ex = result;
                
                JCExpression expr = new JmlBBArrayAssignment(nid,arr,ex,null,null);
                expr.pos = sp;
                expr.type = aa.type;
                treeutils.copyEndPosition(expr, aa);

                // FIXME - set line and source
                addAssume(sp,Label.HAVOC,expr,currentBlock.statements);
            } else {
                // Range of array
                JCIdent arr = getArrayIdent(aa.type,aa.pos);
                JCExpression ex = aa.expression;
                JCIdent nid = newArrayIncarnation(aa.type,sp);
                
                scan(ex); ex = result;
                
                JCExpression expr = new JmlBBArrayAssignment(nid,arr,ex,null,null);
                expr.pos = sp;
                expr.type = aa.type;
                treeutils.copyEndPosition(expr, aa);
                
                int p = aa.pos;
                scan(aa.lo);
                JCExpression lo = result;
                JCVariableDecl decl = treeutils.makeVarDef(syms.intType, names.fromString("_JMLARANGE_" + (++unique)), null, p);
                JCIdent ind = treeutils.makeIdent(p, decl.sym);
                JCExpression comp = treeutils.makeBinary(p,JCTree.LT,treeutils.intltSymbol,ind,lo);
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
                    comp = treeutils.makeOr(p, comp, treeutils.makeBinary(p,JCTree.LT,treeutils.intltSymbol,hi,ind));
                }
                
                // FIXME - set line and source
                expr = factory.at(p).JmlQuantifiedExpr(JmlToken.BSFORALL,com.sun.tools.javac.util.List.<JCVariableDecl>of(decl),comp,eq);
                expr.setType(syms.booleanType);
                addAssume(sp,Label.HAVOC,expr,currentBlock.statements);
                //log.warning(storeref.pos,"jml.internal","Ignoring unknown kind of storeref in havoc: " + storeref);
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
//            if (vsym.owner == null || vsym.owner.type.tag != TypeTags.CLASS) {
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
        if (that.token == JmlToken.COMMENT) {
            // Comments are included in the BB program without rewriting
            // This is essential to how counterexample path construction works
            currentBlock.statements.add(that);
        } else if (that.token == JmlToken.ASSUME || that.token == JmlToken.ASSERT) {
            JmlStatementExpr st = M.at(that.pos()).JmlExpressionStatement(that.token,that.label,convertExpr(that.expression));
            st.id = that.id;
            st.optionalExpression = convertExpr(that.optionalExpression);
            st.associatedPos = that.associatedPos;
            st.associatedSource = that.associatedSource;
            st.description = that.description;
            st.source = that.source;
            st.type = that.type;
            copyEndPosition(st,that);
            currentBlock.statements.add(st);
        } else {
            log.error(that.pos,"esc.internal.error","Unknown token in BasicBlocker2.visitJmlStatementExpr: " + that.token.internedName());
        }
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
            if (localVars.contains(vsym)) {
                // no change to local vars (e.g. quantifier and let decls)
            } else {
                that.name = currentMap.getCurrentName(vsym);
                if (isDefined.add(that.name)) {
                    if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("Added " + vsym + " " + that.name);
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
    public void visitSelect(JCFieldAccess that) {
        if (!(that.sym instanceof Symbol.VarSymbol)) { result = that; return; } // This is a qualified type name 
        VarSymbol vsym = (Symbol.VarSymbol)that.sym;
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
                if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("AddedF " + that.sym + " " + that.name);
                addDeclaration(id);
            }
            result = id;
        } else {
            if (isDefined.add(n)) {
                if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("AddedF " + that.sym + " " + that.name);
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
        JCIdent arr = getArrayIdent(that.type,that.pos);
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
        // These should be desugared to assignments.
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
//    
    // FIXME - embedded assignments to array elements are not implemented; no warning either
    // FIXME - is all implicit casting handled
    // Note that only the right expression is translated.
    protected JCExpression doAssignment(Type restype, JCExpression left, JCExpression right, int pos, JCExpression statement) {
        int sp = left.getStartPosition();
        JCStatement newStatement;
        JCExpression newExpr;
        if (left instanceof JCIdent) {
            JCIdent id = (JCIdent)left;
            JCIdent newid = newIdentIncarnation(id,sp);
            //currentBlock.statements.add(treeutils.makeVarDef(newid.type, newid.name, id.sym.owner, pos));
            JCBinary expr = treeutils.makeEquality(pos,newid,right);
            //copyEndPosition(expr,right);
            newStatement = addAssume(sp,Label.ASSIGNMENT,expr,currentBlock.statements);
            newExpr = newid;
        } else if (left instanceof JCArrayAccess) {
            Type ctype = left.type;
            JCIdent arr = getArrayIdent(ctype,right.pos);
            JCExpression ex = ((JCArrayAccess)left).indexed;
            JCExpression index = ((JCArrayAccess)left).index;
            JCIdent nid = newArrayIncarnation(right.type,sp);
            
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
                    if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("AddedFF " + oldfield.sym + " " + oldfield.name);
                    addDeclaration(oldfield);
                }
                JCIdent newfield = newIdentIncarnation(oldfield,sp);
                if (isDefined.add(newfield.name)) {
                    if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("AddedFF " + newfield.sym + " " + newfield.name);
                    addDeclaration(newfield);
                }
                JCExpression expr = new JmlBBFieldAssignment(newfield,oldfield,fa.selected,right);
                expr.pos = pos;
                expr.type = restype;
                treeutils.copyEndPosition(expr, right);

                // FIXME - set line and source
                newStatement = addAssume(sp,Label.ASSIGNMENT,expr,currentBlock.statements);
                newIdentIncarnation(heapVar,pos);
                newExpr = left;
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
        if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("Added " + lhs.sym + " " + lhs.name);
        if (that.init != null) {
            // Create and store the new lhs incarnation before translating the
            // initializer because the initializer is in the scope of the newly
            // declared variable.  Actually if there is such a situation, it 
            // will likely generate an error about use of an uninitialized variable.
            scan(that.init);
            JCBinary expr = treeutils.makeBinary(that.pos,JCBinary.EQ,lhs,that.init);
            addAssume(that.getStartPosition(),Label.ASSIGNMENT,expr,currentBlock.statements);
        }
    }

    public void visitJmlVariableDecl(JmlVariableDecl that) {
        if (that.sym == null || that.sym.owner == null) {
            if (that.init != null) {
                scan(that.init);
                that.init = result;
            }
            Name n = encodedName(that.sym,0L);
            that.name = n;
            isDefined.add(n);
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
                JCBinary expr = treeutils.makeBinary(that.pos,JCBinary.EQ, that.ident != null ? that.ident : lhs,that.init);
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
        scan(that.expr);
        result = that;
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
    @Override public void visitJmlConstraintMethodSig(JmlConstraintMethodSig that)                     { notImpl(that); }
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
    @Override public void visitJmlStatement(JmlStatement that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementSpec(JmlStatementSpec that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementDecls(JmlStatementDecls that) { shouldNotBeCalled(that); }
    @Override public void visitMethodDef(JCMethodDecl that)        { shouldNotBeCalled(that); }
    
    
    final protected List<Symbol> localVars = new LinkedList<Symbol>();
    
    @Override public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) { 
        for (JCVariableDecl d: that.decls) {
            localVars.add(d.sym);
        }
        try {
            scan(that.range);
            JCExpression range = result;
            scan(that.value);
            JCExpression value = result;
            that.range = range;
            that.value = value;
            result = that;
        } finally {
            for (JCVariableDecl d: that.decls) {
                localVars.remove(d.sym);
            }
        }
 
    }

    // OK
    @Override public void visitBinary(JCBinary that) {
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
        scan(that.clazz); // FIXME - if the type tree is rewritten, we are not capturing the result
        that.expr = convertExpr(that.expr);
        result = that; 
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
    public void visitJmlStatementLoop(JmlStatementLoop that) { 
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
