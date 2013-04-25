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
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCArrayTypeTree;
import com.sun.tools.javac.tree.JCTree.JCAssert;
import com.sun.tools.javac.tree.JCTree.JCAssign;
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
 * within expressions.
 * <LI> The JML \\old and \\pre expressions are recognized and translated to use
 * the appropriate single-assignment identifiers.
 * </UL>
 * <P>
 * The input tree must consist of (FIXME)
 * <UL>
 * <LI> A valid Java program (with any Java constructs)
 * <LI> JML assume and assert statements, with JML expressions
 * <LI> The JML expressions contain only
 * <UL>
 * <LI> Java operators
 * <LI> quantified expressions
 * <LI> set comprehension expressions
 * <LI> \\old and \\pre expressions
 * <LI> [ FIXME ??? JML type literals, subtype operations, method calls in specs?]
 * </UL
 * </UL>
 *
 * <P>
 * Basic block output form contains only this subset of AST nodes: (FIXME)
 * <UL>
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
 * 
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
    
    
    /////// To have a unique BasicBlocker2 instance for each method translated
    // In the initialization of tools, call  BasicBlocker2.Factory.preRegister(context);
    // Obtain a new BasicBlocker2 when desired with  context.get(BasicBlocker2.class);
        
//    /** Register a BasicBlocker Factory, if nothing is registered yet */
//    public static void preRegister(final Context context) {
//        //if (context.get(key) != null) return;
//        context.put(key, new Context.Factory<BasicBlocker2>() {
//            @Override
//            public BasicBlocker2 make(Context context) {
//                return new BasicBlocker2(context);
//            }
//        });
//    }
//    
//    final public static Context.Key<BasicBlocker2> key =
//        new Context.Key<BasicBlocker2>();
    
    /////// To have one BasicBlocker2 instance per context use this method without the pre-registration
    // Don't need pre-registration since we are not replacing any tool and not using a factory
    // To obtain a reference to the instance of BasicBlocker2 for the current context
    //                                 BasicBlocker2.instance(context);
    
//    /** Get the instance for this context. 
//     * 
//     * @param context the compilation context
//     * @return a (unique for the context) BasicBlocker instance
//     */
//    public static BasicBlocker2 instance(@NonNull Context context) {
//        BasicBlocker2 instance = context.get(key);
//        // This is lazily initialized so that a derived class can preRegister to
//        // replace this BasicBlocker
//        if (instance == null) {
//            instance = new BasicBlocker2(context);
//        }
//        return instance;
//    }
    
    // Options
    
    /** This static field controls whether (user) assume statements are turned into assumptions tracked
     * with the assume count variable; if so, then there is an easy mechanism to test whether 
     * the assumptions are feasible.
     */
    public static boolean useAssumeDefinitions = false;
    

    // THE FOLLOWING ARE ALL FIXED STRINGS
    
    //-----------------------------------------------------------------
    // Names for a bunch of synthetic variables 
    
    /** Standard name for the variable that represents the heap (which excludes local variables) */
    public static final @NonNull String HEAP_VAR = "_heap__";
    
    /** Standard name for the variable that tracks allocations */
    public static final @NonNull String ALLOC_VAR = "_alloc__";
    
    /** Prefix for assumptions defined in the basic block */
    public static final String ASSUMPTION_PREFIX = "assumption";
    
//    /** Name of the encoded this variable */
//    public static final String THIS = "THIS_";
//    
//    /** The prefix of the variables used in checking assumptions */
//    public static final String ASSUME_CHECK_PREFIX = "ASSUMECHECK_";
//    
    /** A variable name used in checking assumptions */
    public static final String ASSUME_CHECK_COUNT = "__assumeCheckCount";
    
//    /** The prefix for names of switch expressions */
//    public static final String SWITCH_EXPR_PREFIX = "__switch_expression__";
    
    /** Name of length field */
    public static final String LENGTH = "length";
    
    /** Name of the SELECT function for arrays. */
    public static final String SELECTString = "SELECT";
    
    /** The Name of the SELECT function for arrays. */
    public final Name SELECT;
    
    /** String of the STORE function for arrays. */
    public static final String STOREString = "STORE";
    
    /** The Name of the STORE function for arrays. */
    public final Name STORE;
    
    //-----------------------------------------------------------------
    // Names for various basic blocks
    
    /** Standard name for the block that starts the body */
    public static final @NonNull String BODY_BLOCK_NAME = "bodyBegin";
    
    /** Standard name for the starting block of the program (just has the preconditions) */
    public static final @NonNull String START_BLOCK_NAME = "Start";
    
    
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
    // have proper position information
    
    /** Holds an AST node for a boolean true literal, initialized in the constructor */
    @NonNull final protected JCLiteral trueLiteral;
    
    /** Holds an AST node for a boolean false literal, initialized in the constructor */
    @NonNull final protected JCLiteral falseLiteral;
    
//    /** Identifier of a synthesized object field holding the allocation time of the object, initialized in the constructor */
//    @NonNull protected JCIdent allocIdent;
//
//    /** Symbol of a synthesized object field holding the allocation time of the object, initialized in the constructor */
//    @NonNull protected VarSymbol allocSym;

    /** Identifier of a synthesized object field holding the length of an array object, initialized in the constructor */
    @NonNull protected JCIdent lengthIdent;

    /** Symbol of a synthesized object field holding the length of an array object, initialized in the constructor */
    @NonNull protected VarSymbol lengthSym;
    
    /** A fixed id for 'this' of the method being translated (see currentThisId
     * for the 'this' of called methods). */
    @NonNull protected JCIdent thisId;

    // THE FOLLOWING FIELDS ARE USED IN THE COURSE OF DOING THE WORK OF CONVERTING
    // TO BASIC BLOCKS.  They are fields of the class because they need to be
    // shared across the visitor methods.
    
    /** Place to put new definitions, such as the equalities defining auxiliary variables */
    protected List<BasicProgram.Definition> newdefs;
    
    /** Place to put new background assertions, such as axioms and class predicates */
    protected List<JCExpression> background;
    
    /** The variable name that is currently the 'this' variable */
    protected JCIdent currentThisId;
    
    /** The variable that keeps track of heap incarnations */
    protected JCIdent heapVar;
    
    /** This is an integer that rises monotonically on each use and is used
     * to make sure new identifiers are unique.
     */
    protected int unique;
    
    // FIXME - document
    @NonNull BiMap<JCTree,JCExpression> bimap = new BiMap<JCTree,JCExpression>();
    
    /** A mapping from BasicBlock to the sym->incarnation map giving the map that
     * corresponds to the state at the exit of the BasicBlock.
     */
    @NonNull protected Map<BasicBlock,VarMap> blockmaps = new HashMap<BasicBlock,VarMap>();
    
    /** A mapping from labels to the sym->incarnation map operative at the position
     * of the label.
     */
    @NonNull protected Map<Name,VarMap> labelmaps = new HashMap<Name,VarMap>();
        
    /** The map from symbol to incarnation number in current use */
    @NonNull protected VarMap currentMap;
    
    /** The map immediately after declaration of method parameters; this is
        the mapping of variables to incarnations to use when in the scope of 
        an \old */
    @NonNull protected VarMap premap;
    
    /** Contains names for which a declaration has been issued. */
    final protected Set<Name> isDefined = new HashSet<Name>();

    /** The constructor, but use the instance() method to get a new instance,
     * in order to support extension.  This constructor should only be
     * invoked by a derived class constructor.
     * @param context the compilation context
     */
    protected BasicBlocker2(@NonNull Context context) {
        super(context);
        
//        context.put(key, this);
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
        
//        // This is the field name used to access the allocation time of an object
//        allocSym = newVarSymbol(0,ALLOC_VAR,syms.intType,0);
//        allocIdent = newAuxIdent(allocSym,0);

        // This is the symbol to access the length of an array 
        lengthSym = syms.lengthVar;
        lengthIdent = newAuxIdent(lengthSym,0);
        
        SELECT = names.fromString(SELECTString);
        STORE = names.fromString(STOREString);
    }
    
    /** This tracks single-assignment versions - it is incremented whenever
     * a new version of a variable is needed (globally across all variables).
     */
    protected static long saversion = 0;
    
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
    public class VarMap {
        // The maps allow VarSymbol or TypeSymbol (for TypeVar)
        private Map<VarSymbol,Long> mapSAVersion = new HashMap<VarSymbol,Long>();
        private Map<TypeSymbol,Long> maptypeSAVersion = new HashMap<TypeSymbol,Long>();
        private Map<Symbol,Name> mapname = new HashMap<Symbol,Name>();
        //long everythingSAversion = 0;
        
        /** Makes a checkpoint copy of the map */
        public VarMap copy() {
            VarMap v = new VarMap();
            v.mapSAVersion.putAll(this.mapSAVersion);
            v.maptypeSAVersion.putAll(this.maptypeSAVersion);
            v.mapname.putAll(this.mapname);
            //v.everythingSAversion = this.everythingSAversion;
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
                s = encodedName(vsym,vsym.pos);
                if (isDefined.add(s)) {
                    //System.out.println("AddedC " + sym + " " + n);
                    JCIdent idd = treeutils.makeIdent(0, vsym);
                    idd.name = s;
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
                System.out.println("MISSING SYMBOL " + vsym.getQualifiedName());
                mapSAVersion.put(vsym,(i=0L));
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
        
//        /** Stores a new SA version of a symbol */
//        public void putSAVersion(VarSymbol vsym, Name s) {
//            mapSAVersion.put(vsym,++saversion);
//            mapname.put(vsym,s);
//        }
        
        /** Stores a new SA version of a symbol */
        public void putSAVersion(VarSymbol vsym, Name s, long version) {
            mapSAVersion.put(vsym,version);
            mapname.put(vsym,s);
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
    
    // METHODS
    
    @Override
    public void scan(JCTree tree) {
        result = null;
        super.scan(tree);
        if (tree instanceof JCExpression && !(tree instanceof JCAssign)
                ) bimap.put(tree, result);
    }

    public void scanList(com.sun.tools.javac.util.List<JCExpression> trees) {
        if (trees != null)
        for (com.sun.tools.javac.util.List<JCExpression> l = trees; l.nonEmpty(); l = l.tail) {
            scan(l.head);
            l.head = result;
        }
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
    

    /** Creates an encoded name from a symbol and an incarnation position.
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
    protected Name encodedName(VarSymbol sym, int incarnationPosition) {
        if (incarnationPosition == 0 || sym.owner == null || sym.name.toString().equals("THIS")) { // FIXME _ can we avoid the explicit test for THIS?
            Name n = sym.getQualifiedName();
            return n;
        } else
            return names.fromString(
                    sym.getQualifiedName() 
                    + (sym.pos < 0 ? "_" : ("_" + sym.pos + "_")) // declaration position
                    + incarnationPosition // use position
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
        return names.fromString(sym.flatName() + "_" + declarationPosition + "__" + (++unique));
    }
    
    /** Cached value of the SELECT symbol */
    protected Symbol selectSym = null;
    /** Cached value of the STORE Symbol. */
    protected Symbol storeSym = null;
    
    // FIXME - review and document
    protected JCExpression makeSelect(JCExpression array, JCExpression index) {
        if (selectSym == null) {
            selectSym = new VarSymbol(0,SELECT,null,null); // FIXME - OK to have no type or owner?
        }
        JCMethodInvocation app = factory.Apply(
                com.sun.tools.javac.util.List.<JCExpression>nil(),
                treeutils.makeIdent(Position.NOPOS, selectSym),
                com.sun.tools.javac.util.List.<JCExpression>of(index));
        return app;
    }
    
    // FIXME - review and document
    protected JCExpression makeStore(JCExpression array, JCExpression index, JCExpression value) {
        if (storeSym == null) {
            storeSym = new VarSymbol(0,STORE,null,null);
        }
        JCMethodInvocation app = factory.Apply(
                com.sun.tools.javac.util.List.<JCExpression>nil(),
                treeutils.makeIdent(Position.NOPOS, storeSym),
                com.sun.tools.javac.util.List.<JCExpression>of(array,index,value));
        return app;
    }
    

    /** Creates a new Ident node, but in this case we are not using the name from
     * the current incarnation map - so we supply the name. This is just used for
     * DSA assignments.
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
    
    /** Creates a new incarnation of a variable, with unique id added */
    protected JCIdent newIdentIncarnation(VarSymbol vsym, int incarnationPosition) {
        JCIdent n = factory.at(incarnationPosition).Ident(encodedName(vsym,incarnationPosition));
        n.type = vsym.type;
        n.sym = vsym;
        currentMap.putSAVersion(vsym,n.name,unique); // FIXME - should unique be incremented
        if (isDefined.add(n.name)) addDeclaration(n);
        return n;
    }
    
    // FIXME - review
    /** Creates a newly incarnated variable corresponding to the given declaration.
     * The incarnation number will be the position of the declaration for some
     * declarations, but not, for example, for a formal argument of a method call -
     * then it would be the position of the actual parameter expression.
     * @param id the original declaration
     * @param incarnation the incarnation number to use
     * @return the new variable node
     */
    protected JCIdent newIdentIncarnation(JCVariableDecl id, int incarnation) {
        return newIdentIncarnation(id.sym, incarnation);
    }
    
    // FIXME - review and document
    protected JCIdent newArrayIdentIncarnation(VarSymbol vsym, int incarnationPosition) {
        JCIdent n = factory.at(incarnationPosition).Ident(encodedArrayName(vsym,incarnationPosition));
        n.type = vsym.type;
        n.sym = vsym;
        currentMap.putSAVersion(vsym,n.name, saversion);
        if (isDefined.add(n.name)) addDeclaration(n);
        return n;
    }
    
    // FIXME - review and document
    protected JCIdent newIdentIncarnation(TypeSymbol id, int incarnation) {
        JCIdent n = factory.at(incarnation).Ident(encodedTypeName(id,incarnation));
        n.sym = id;
        n.type = id.type;
        // FIXME - end information?
        currentMap.putSAVersion(id,n.name);
        if (isDefined.add(n.name)) {
            //System.out.println("AddedC " + sym + " " + n);
//            JCIdent idd = treeutils.makeIdent(0, id);
//            idd.name = n.name;
            addDeclaration(n);
        }
        return n;
    }
    
    // FIXME - review and document
    protected JCIdent newTypeVarIncarnation(TypeSymbol vsym, int incarnationPosition) {
        JCIdent n = factory.at(incarnationPosition).Ident(encodedTypeName(vsym,incarnationPosition));
        n.type = JmlAttr.instance(context).TYPE;
        n.sym = vsym;
        currentMap.putSAVersion(vsym,n.name);
        return n;
    }
    
    // FIXME - document
    protected JCIdent newArrayIncarnation(Type componentType, int usePosition) {
        JCIdent id = getArrayIdent(componentType);
        id = newArrayIdentIncarnation((VarSymbol)id.sym,usePosition);
        //currentMap.put((VarSymbol)id.sym,Integer.valueOf(usePosition),id.name);
        return id;
    }
    
    // FIXME - review
    /** Creates an attributed, untranslated JCIdent and accompanying VarSymbol using the given name and type;
     * the given pos is used as the textual position of the JCIdent node; also, if incarnations is
     * true, pos is used as the declaration position of the new identifier, with the implication that
     * additional incarnations will be defined later. The new Symbol has no modifiers and no owner.
     * @param name the Name to use for the new symbol
     * @param type the type of the new symbol
     * @param pos the declaration position of the new symbol, if incarnations is true
     * @param incarnations whether there will be multiple incarnations of this symbol
     * @return a JCIdent tree node representing a use of the new symbol
     */
    protected JCIdent newAuxIdent(@NonNull String name, @NonNull Type type, int pos, boolean incarnations) {
        return newAuxIdent(names.fromString(name),type,pos,incarnations);
    }
    
    // FIXME - review
    /** Creates an attributed, untranslated JCIdent and accompanying VarSymbol using the given name and type;
     * the given pos is used as the textual position of the JCIdent node; also, if incarnations is
     * true, pos is used as the declaration position of the new identifier, with the implication that
     * additional incarnations will be defined later. The new Symbol has no modifiers and no owner.
     * @param name the Name to use for the new symbol
     * @param type the type of the new symbol
     * @param pos the declaration position of the new symbol, if incarnations is true
     * @param incarnations whether there will be multiple incarnations of this symbol
     * @return a JCIdent tree node representing a use of the new symbol
     */
    protected JCIdent newAuxIdent(@NonNull Name name, @NonNull Type type, int pos, boolean incarnations) {
        VarSymbol s = new VarSymbol(0,name,type,null);
        s.pos = incarnations ? pos : Position.NOPOS;
        return newAuxIdent(s,pos);
    }
    
    // FIXME - review - same as treeutils.makeIdent
    /** Creates an attributed JCIdent from the given VarSymbol;
     * the given pos is used as the textual position of the JCIdent node;
     * @param sym a Variable Symbol
     * @param pos the use position of the new tree node
     * @return a JCIdent tree node representing a use of the new symbol
     */
    protected JCIdent newAuxIdent(VarSymbol sym, int pos) {
        JCIdent id = factory.at(pos).Ident(sym.name);
        id.sym = sym;
        id.type = sym.type;
        return id;
    }

    // FIXME - review - change to treeutils.makeVarSymbol
    /** Creates a new VarSymbol with the given name and type and modifier flags (and no owner);
     * the declaration position is 'pos'. */
    protected VarSymbol newVarSymbol(long flags, @NonNull String name, @NonNull Type type, int pos) {
        // We leave the symbol's declaration position as Position.NOPOS (-1).
        VarSymbol v = new VarSymbol(flags,names.fromString(name),type,null);
        v.pos = pos;
        return v;
    }
    

    /** Sets all the variables that are supposed to stay in synch with the value of
     * currentBlock
     * @param b the new currentBlock
     */
    @Override
    protected void setCurrentBlock(BasicBlock b) {
        super.setCurrentBlock(b);
        currentMap = blockmaps.get(b);
        if (currentMap == null) currentMap = initMap(currentBlock); // FIXME - under what circumstances is the currentMap already available?
    }
    
    /** Files away a completed block, adding it to the blocksCompleted list and
     * to the lookup Map.
     * @param b the completed block
     */
    @Override
    protected void completeBlock(@NonNull BasicBlock b) {
//        if (super.completed(b)) return true;
        super.completeBlock(b);
        blockmaps.put(b,currentMap);
        currentMap = null; // Defensive - so no inadvertent assignments
        //log.noticeWriter.println("Completed block " + b.id);
//        return false;
    }
    
    /** Converts the top-level block of a method into the elements of a BasicProgram 
     * 
     * @param methodDecl the method to convert to to a BasicProgram
     * @param denestedSpecs the specs of the method
     * @param classDecl the declaration of the containing class
     * @return the completed BasicProgram
     */
    protected @NonNull BasicProgram convertMethodBody(JCBlock block, @NonNull JCMethodDecl methodDecl, 
            JmlMethodSpecs denestedSpecs, @NonNull JCClassDecl classDecl, @NonNull JmlAssertionAdder assertionAdder) {
        initialize(methodDecl,classDecl,assertionAdder);
        this.isDefined.clear();
        unique = 0;
        if (classDecl.sym == null) {
            log.error("jml.internal","The class declaration in BasicBlocker.convertMethodBody appears not to be typechecked");
            return null;
        }

        newdefs = new LinkedList<BasicProgram.Definition>();
        background = new LinkedList<JCExpression>();
        blockmaps.clear();
        labelmaps.clear();
        
        heapVar = newAuxIdent(HEAP_VAR,syms.intType,0,true); // FIXME - would this be better as its own uninterpreted type?
        
        Set<VarSymbol> vsyms = GetSymbols.collectSymbols(methodDecl,classDecl);
//        for (VarSymbol v: vsyms) System.out.print(" " + v.toString());
//        System.out.println("  ENDSYMS");
        
        // Define the start block
        int pos = methodDecl.pos;
        BasicBlock startBlock = newBlock(START_BLOCK_NAME,pos);

        // Define the body block
        // Put all the program statements in the Body Block
        BasicBlock bodyBlock = newBlock(BODY_BLOCK_NAME,methodDecl.body.pos);

        // Add declarations of method parameters
        for (JCVariableDecl d: methodDecl.params) {
            // We reset this with a location of 0 so that the name does not get
            // changed. This is only because the premap does not know these names.
            // And will probably have to change when encodedName is made more robust. FIXME
            JCVariableDecl dd = treeutils.makeVarDef(d.type,d.name,d.sym.owner,0);
            bodyBlock.statements.add(dd);
        }
        
        // Then the program
        bodyBlock.statements.addAll(block.getStatements());
        follows(startBlock,bodyBlock);
        
        // Handle the start block a little specially
        // It does not have any statements in it
        startBlock(startBlock); // Start it so the currentMap, currentBlock, remainingStatements are defined

        // Define the thisId
        if (this.methodDecl._this != null) {
//            currentMap.putSAVersion(this.methodDecl._this, this.methodDecl._this.name, 0);
//            thisId = newAuxIdent(this.methodDecl._this.name.toString(),methodDecl.sym.owner.type,pos,false);
            JCIdent thisId = assertionAdder.thisIds.get(classDecl.sym);
            currentMap.putSAVersion((VarSymbol)thisId.sym, names.fromString("THIS"), 0);
            thisId = newAuxIdent(thisId.name.toString(),methodDecl.sym.owner.type,pos,false);
            currentThisId = thisId;
        }


        // FIXME - these no longer belong here, I think
        newIdentIncarnation(heapVar,0);
//        newIdentIncarnation(allocSym,0);
        currentMap.putSAVersion(syms.lengthVar, names.fromString(LENGTH), 0); // TODO: Some places use 'length' without encoding, so we store an unencoded name

        for (JCVariableDecl d: methodDecl.params) {
            currentMap.putSAVersion(d.sym, d.name, 0);
        }

        for (VarSymbol v: vsyms) {
            currentMap.putSAVersion(v, v.name, 0);
            JCIdent id = treeutils.makeIdent(Position.NOPOS,v);
            addDeclaration(id);
        }
        
        premap = currentMap.copy();
        
        completeBlock(currentBlock);

        processBlock(bodyBlock);
        
        // Finished processing all the blocks
        // Make the BasicProgram
        program.startId = startBlock.id;
        program.definitions = newdefs;
        program.background = background;
//        program.assumeCheckVar = assumeCheckCountVar;
        program.toLogicalForm = toLogicalForm;
        return program;
    }
    
    
    /** Adds an assert statement into the given statement list
     * @param label the label for the assert statement
     * @param that the expression which must be true
     * @param declpos the associated position (e.g. of the declaration that causes the assertion)
     * @param statements the statement list to which to add the new assert statement
     * @param usepos the source position at which the expression is asserted
     * @param source the source file corresponding to usepos
     * @param statement
     */
    protected void addAssert(Label label, JCExpression that, int declpos, List<JCStatement> statements, int usepos, JavaFileObject source, JCTree statement) {
        JmlTree.JmlStatementExpr st = factory.at(statement.pos()).JmlExpressionStatement(JmlToken.ASSERT,label,that);
        st.optionalExpression = null;
        st.source = source;
        //st.line = -1; 
        st.associatedPos = declpos;
        st.associatedSource = null; // OK - always same as source
        st.type = null; // no type for a statement
        copyEndPosition(st,that);
        statements.add(st);
    }
    
    
    /** Adds a new assume statement to the end of the currentBlock; the assume statement is
     * given the declaration pos and label from the arguments; it is presumed the input expression is
     * translated, as is the produced assume statement.
     * @param pos the declaration position of the assumption
     * @param label the kind of assumption
     * @param expr the (translated) expression being assumed
     */
    protected void addAssume(int pos, Label label, JCExpression expr) {
        addAssume(pos,label,expr,currentBlock.statements);
    }
    
    /** Adds a new assume statement to the end of the given statements list; the assume statement is
     * given the declaration pos and label from the arguments; it is presumed the input expression is
     * translated, as is the produced assume statement.
     * @param pos the declaration position of the assumption
     * @param label the kind of assumption
     * @param that the (translated) expression being assumed
     * @param statements the list to add the new assume statement to
     */
    protected JmlStatementExpr addAssume(int pos, Label label, JCExpression that, List<JCStatement> statements) {
        if (useAssumeDefinitions) {
            JCIdent id = factory.at(pos).Ident(names.fromString(ASSUMPTION_PREFIX+(unique++)));
            id.type = syms.booleanType;
            newdefs.add(new BasicProgram.Definition(that.pos,id,that)); // FIXME- end position?
            that = id;
        }
        return super.addAssume(pos,label,that,statements);
    }
    
    /** Adds an assumption to the given statement list */ 
    protected JmlStatementExpr addAssume(int startpos, JCTree endpos, Label label, JCExpression that, List<JCStatement> statements) {
        if (useAssumeDefinitions) {
            if (startpos < 0) startpos = that.pos; 
            JCIdent id = factory.at(startpos).Ident(names.fromString(ASSUMPTION_PREFIX+(unique++)));
            id.type = syms.booleanType;
            newdefs.add(new BasicProgram.Definition(that.pos,id,that)); // FIXME- start, end position?
            that = id;
        }
        return super.addAssume(startpos,endpos,label,that,statements);
    }
    
    
    /** Adds an axiom to the axiom set */
    protected void addAxiom(int pos, Label label, JCExpression that, List<JCStatement> statements) {
        background.add(that);
    }
    
    // FIXME - REVIEW and document
    static public String encodeType(Type t) {   // FIXME String? char? void? unsigned?
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
    
    // FIXME - review and document
    private Map<String,JCIdent> arrayIdMap = new HashMap<String,JCIdent>();
    
    // FIXME - review and document
    protected JCIdent getArrayIdent(Type componentType) {
        String s = "arrays_" + encodeType(componentType);
        JCIdent id = arrayIdMap.get(s);
        if (id == null) {
            id = factory.Ident(names.fromString(s));
            id.pos = 0;
            id.type = new ArrayType(componentType,syms.arrayClass);
            VarSymbol sym = new VarSymbol(0,id.name,id.type,null);
            sym.pos = 0;
            id.sym = sym;
            arrayIdMap.put(s,id);
        }
        id = newIdentUse((VarSymbol)id.sym,0);
        return id;
    }
    
   
    
    
    /** Returns the initial VarMap of the given block; the returned map is a combination
     * of the maps from all preceding blocks, with appropriate DSA assignments added.
     * @param block
     * @return the VarMap for the given block
     */
    protected VarMap initMap(BasicBlock block) {
        VarMap newMap = new VarMap();
        currentMap = newMap;
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
            long maxe = -1;
            for (BasicBlock b : block.preceders()) {
                VarMap m = blockmaps.get(b);
                all.add(m);
                combined.putAll(m);
                //if (maxe < m.everythingSAversion) maxe = m.everythingSAversion;
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
        //log.noticeWriter.println("MAP FOR BLOCK " + block.id + JmlTree.eol + newMap.toString());
        return newMap;
    }
    

    /** Makes a Java parse tree node (attributed) for the this symbol of the methodDecl. */
    protected JCIdent makeThis(int pos) {
        return treeutils.makeIdent(pos,methodDecl._this);
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
    
    /** Makes the equivalent of an instanceof operation: e !=null && \typeof(e) <: \type(type) */
    protected JCExpression makeInstanceof(JCExpression e, int epos, Type type, int typepos) {
        JCExpression e1 = treeutils.makeNeqObject(epos,e,treeutils.nullLit);
        JCExpression e2 = treeutils.makeJmlBinary(epos,JmlToken.SUBTYPE_OF,treeutils.makeTypeof(e),makeTypeLiteral(type,typepos));
        JCExpression ee = treeutils.makeBinary(epos,JCTree.AND,e1,e2);
        return ee;
    }
    
    // FIXME - review and document
    protected MethodSymbol makeFunction(Name name, Type resultType, Type... argTypes) {
        ListBuffer<Type> args = new ListBuffer<Type>().appendArray(argTypes);
        MethodType methodType = new MethodType(args.toList(),resultType,com.sun.tools.javac.util.List.<Type>nil(),syms.methodClass);
        MethodSymbol meth = new MethodSymbol(Flags.STATIC,name,methodType,null); // no owner
        return meth;
    }
    
    // FIXME - review and document
    protected JCExpression makeFunctionApply(int pos, MethodSymbol meth, JCExpression... args) {
        JCIdent methid = factory.at(pos).Ident(meth);
        JCExpression e = factory.at(pos).Apply(null,methid,new ListBuffer<JCExpression>().appendArray(args).toList());
        e.type = meth.getReturnType();
        return e;
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

//    // FIXME - review and document
//    protected int endPos(JCTree t) {
//        if (t instanceof JCBlock) {
//            return ((JCBlock)t).endpos;
//        } else if (t instanceof JCMethodDecl) {
//            return endPos(((JCMethodDecl)t).body);
//        } else {
//            // FIXME - fix this sometime - we don't know the end position of
//            // statements that are not blocks
//            if (JmlEsc.escdebug) log.noticeWriter.println("UNKNOWN END POS");
//            return t.pos;
//        }
//    }


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
        scan(that.cond);
        scan(that.detail);
        JCExpression cond = (that.cond);
        //JCExpression detail = (that.detail);
        // FIXME - what to do with detail
        // FIXME - for now turn cond into a JML assertion
        // FIXME - need a label for the assert statement
        // FIXME - set line and source
        addAssert(Label.EXPLICIT_ASSERT, cond, that.cond.getStartPosition(), currentBlock.statements, that.cond.getStartPosition(),log.currentSourceFile(),that);
    }
    
    // FIXME - needs review
    public void visitApply(JCMethodInvocation that) { 
        // This is an expression so we just use trExpr
        JCExpression now;
        JCExpression obj;
        MethodSymbol msym;
        Type.ForAll tfa = null;
        if (that.meth instanceof JCIdent) {
            now = (that.meth);
            if (  ((JCIdent)now).sym instanceof MethodSymbol) {

                msym = (MethodSymbol)((JCIdent)now).sym;
                if (msym.isStatic()) obj = null;
                else obj = currentThisId;

            } else { msym=null; obj = null; } // FIXME - this shouldn't really happen - there is a mis translation in creating makeTYPE expressions

        } else if (that.meth instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)that.meth;
            msym = (MethodSymbol)(fa.sym);
            if (msym == null || msym.isStatic()) obj = null; // msym is null for injected methods such as box and unbox
            else {
                obj = ( fa.selected );
                // FIXME - should do better than converting to String
                //if (!fa.selected.type.toString().endsWith("JMLTYPE")) checkForNull(obj,fa.pos,trueLiteral,null);
            }
//        } else if (that.token == null) {
//            super.visitApply(that);  // See testBox - this comes from the implicitConversion - should it be a JCMethodInvocation instead?
//            scan(that.typeargs);
//            scan(that.meth);
//            that.meth = result;
//            scanList(that.args);
//            result = that;
        } else {
            // FIXME - not implemented
            log.warning("esc.not.implemented","BasicBlocker.visitApply for " + that.meth.getClass());
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
            JCExpression n = (arg);
            newargs.append(n);
        }

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
        toLogicalForm.put(that,result);
        return;
    }

    // FIXME - review this
    //boolean extraEnv = false;
    public void visitJmlMethodInvocation(JmlMethodInvocation that) { 
        if (that.token == JmlToken.BSOLD || that.token == JmlToken.BSPRE) {
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
        } else if (that.token == null || that.token == JmlToken.BSTYPELC || that.token == JmlToken.BSTYPEOF) {
            //super.visitApply(that);  // See testBox - this comes from the implicitConversion - should it be a JCMethodInvocation instead?
            scan(that.typeargs);
            scan(that.meth);
            if (that.meth != null) that.meth = result;
            scanList(that.args);
            result = that;
        } else {
            log.error(that.pos, "esc.internal.error", "Did not expect this kind of Jml node in BasicBlocker2: " + that.token.internedName());
//            for (JCExpression e: that.args) {
//                e.accept(this);
//            }
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
    
//    // FIXME - REVIEW and document
//    // Generate a (translated) allocation predicate // FIXME - check this out and use it
//    protected void declareAllocated(VarSymbol vsym, int pos) {
//        JCIdent var = newIdentUse(vsym,pos);
//        declareAllocated(var,pos);
//    }
//    
//    // Generate a (translated) allocation predicate // FIXME - check this out and use it
//    protected void declareAllocated(JCExpression e, int pos) {
//        currentBlock.statements.add(comment(pos, e + " != null || " + e + " .alloc < " + allocSym));
//        JCExpression eee = new JmlBBFieldAccess(allocIdent,e);
//        eee.pos = pos;
//        eee.type = syms.intType;
//        eee = treeutils.makeBinary(pos,JCTree.LE,eee,newIdentUse(allocSym,pos));
//        eee = treeutils.makeBinary(pos,JCTree.OR,treeutils.makeEqObject(pos,e,nullLiteral),eee);
//        addAssume(pos,Label.SYN,eee,currentBlock.statements);
//    }
    
//    // Generate a (translated) alloc comparison // FIXME - check this out and use it and docuiment
//    protected JCExpression allocCompare(int pos, JCExpression e) {
//        JCExpression eee = new JmlBBFieldAccess(allocIdent,e);
//        eee.pos = pos;
//        eee.type = syms.intType;
//        eee = treeutils.makeBinary(pos,JCTree.LE,eee,newIdentUse(allocSym,pos));
//        return eee;
//    }
//
//    // Generate a (translated) alloc selection // FIXME - check this out and use it and document
//    protected JCExpression allocSelect(int pos, JCExpression e) {
//        JCExpression eee = new JmlBBFieldAccess(allocIdent,e);
//        eee.pos = pos;
//        eee.type = syms.intType;
//        return eee;
//    }

    
    // FIXME - review and document
    protected void havocAssignables(int pos, JmlMethodInfo mi) {
////        * a store-ref
////        *  is a JCIdent, a JCSelect (potentially with a null field), or a JmlStoreRefArrayRange;
////        *  there may be more than one use of a JmlStoreRefArrayRange, e.g. a[2..3][4..5] or
////        *  a.f[4..5].g[6..7]
//        for (JmlMethodInfo.Entry entry: mi.assignables) {
//            JCExpression preCondition = trSpecExpr(entry.pre,log.currentSourceFile()); // FIXME - fix this
//            for (JCTree sr: entry.storerefs) {
//                if (sr == null) {
//                    log.error(pos,"jml.internal","Unexpected null store-ref in BasicBlocker.havocAssignables");
//                    continue;
//                }
//                int npos = pos*100000 + sr.pos;
//                JCExpression prevCondition = condition;
//                if (sr instanceof JCIdent) {
//                    JCIdent id = (JCIdent)sr;
//                    if (utils.isJMLStatic(id.sym)) {
//                        JCExpression oldid = trSpecExpr(id,log.currentSourceFile()); // FIXME
//                        JCIdent newid = newIdentIncarnation(id,npos); // new incarnation
//                        // newid == precondition ? newid : oldid
//                        JCExpression e = factory.at(pos).Conditional(preCondition,newid,oldid);
//                        e.type = newid.type;
//                        e = treeutils.makeBinary(pos,JCTree.EQ,newid,e);
//                        addAssume(pos,Label.HAVOC,e,currentBlock.statements);
//                    } else {
//                        // Same as for JCFieldAccess except that fa.selected is always 'this' (currentThisId)
//                        Type type = id.type;
//                        checkForNull(currentThisId,id.pos,preCondition,null);
//
//                                JCExpression indexlo = trSpecExpr(ar.lo,log.currentSourceFile()); // FIXME
//                                if (indexlo != null) checkArrayAccess(array,indexlo,sr.pos);
//                                else indexlo = zeroLiteral;
//                                
//                                JCExpression indexhi = trSpecExpr(ar.hi,log.currentSourceFile()); // FIXME
//                                boolean above = false;
//                                if (indexhi != null) checkArrayAccess(array,indexhi,sr.pos);
//                                else {
//                                    //indexhi = factory.at(sr.pos).Select(array,lengthSym);
//                                    indexhi = new JmlBBFieldAccess(lengthIdent,array);
//                                    indexhi.pos = sr.pos;
//                                    indexhi.type = syms.intType;
//                                    above = true;
//                                }
//                                
//                                
//                                JCIdent nid = newArrayIncarnation(sr.type,pos);
//                                JCExpression e = new JmlBBArrayHavoc(nid,arrayId,array,indexlo,indexhi,preCondition,above);
//
//                                addAssume(pos,Label.HAVOC,e,currentBlock.statements);
//
//                            }
//                        } else {
//                            // single element at the top level
//
//                            if (ns.size() > 0) {
//                                // FIXME - this is all wrong
//                                // But wild-cards within the ar.expression
//
////                                JCIdent label = newAuxIdent("havoclabel$"+npos,syms.intType,npos,false);
////                                labelmaps.put(label.name,currentMap.copy());
////                                JCExpression oldaccess = factory.at(npos).JmlMethodInvocation(JmlToken.BSOLD,access,label);
////
////                                JCArrayAccess newaccess = factory.at(access.pos).Indexed(access.indexed,access.index);
////                                newaccess.type = access.type;
////
////                                //                            JCIdent meth = newAuxIdent("arbitrary$",syms.intType,npos);
////                                //                            ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
////                                //                            for (Name n: ns) {
////                                //                                JCIdent id = factory.at(npos).Ident(n);
////                                //                                id.type = syms.intType;
////                                //                                args.append(id);
////                                //                            }
////                                //                            JCMethodInvocation app = factory.at(npos).Apply(null,meth,args.toList());
////                                //                            app.type = ar.type;
////
////                                JCConditional cond = factory.at(sr.pos).Conditional(
////                                        treeutils.makeBinary(JCTree.AND,entry.pre,accumRange,npos),newaccess,oldaccess);
////                                cond.type = access.type;
////
////                                JCExpression assign = treeutils.makeBinary(JCTree.EQ,newaccess,cond,npos);
////
////                                JmlQuantifiedExpr quant = factory.at(sr.pos).JmlQuantifiedExpr(JmlToken.BSFORALL,null,factory.Type(syms.intType),ns,fullRange,assign);
////
////                                JCIdent nid = newArrayIncarnation(sr.type,npos);                            
////                                JmlQuantifiedExpr trQuant = (JmlQuantifiedExpr)trSpecExpr(quant,log.currentSourceFile()); // FIXME
////                                // Now we fix up the expression
////                                JCExpression predicate = trQuant.predicate;
////                                JCBinary bin = (JCBinary)predicate;
////                                cond = (JCConditional)bin.rhs;
////                                JmlBBArrayAccess newaa = (JmlBBArrayAccess)cond.truepart;
////                                JmlBBArrayAccess oldaa = (JmlBBArrayAccess)cond.falsepart;
////
////                                JCExpression expr = new JmlBBArrayAssignment(nid,oldaa.arraysId,oldaa.indexed,oldaa.index,cond);
////                                expr.pos = sr.pos;
////                                expr.type = cond.type;
////
////                                trQuant.predicate = expr;
////
////                                addAssume(pos,Label.HAVOC,trQuant,currentBlock.statements,false);
//
//                            } else {
//                                // single element
//                                // a'[i] = preCondition ? a'[i] : a[i];
//
//                                array = trSpecExpr(array,log.currentSourceFile()); // FIXME
//                                checkForNull(array,sr.pos,trueLiteral,null);
//
//                                JCExpression index = trSpecExpr(ar.lo,log.currentSourceFile()); // FIXME
//                                checkArrayAccess(array,index,sr.pos);
//
//                                JCIdent arrayID = getArrayIdent(sr.type);
//                                JCExpression oldvalue = new JmlBBArrayAccess(arrayID,array,index,sr.pos,sr.type);
//
//                                JCIdent nid = newArrayIncarnation(sr.type,pos);
//                                JCExpression newvalue = new JmlBBArrayAccess(nid,array,index,sr.pos,sr.type);
//
//                                JCExpression condValue = factory.at(sr.pos).Conditional(preCondition,newvalue,oldvalue);
//                                condValue.type = oldvalue.type;
//
//                                JCExpression expr = new JmlBBArrayAssignment(nid,arrayID,array,index,condValue);
//                                expr.pos = sr.pos;
//                                expr.type = oldvalue.type;
//                                addAssume(pos,Label.HAVOC,expr,currentBlock.statements);
//                            }
//                        }
//                    } finally {
//                        condition = prevCondition;
//                    }
//                    
//                } else if (sr instanceof JmlStoreRefKeyword) {
//                    if (((JmlStoreRefKeyword)sr).token == JmlToken.BSNOTHING) {
//                        // OK
//                    } else {
//                        havocEverything(preCondition,sr.pos);
//                    }
//                } else if (sr instanceof JmlSingleton) { // FIXME - why do we get JmlSingleton as a store-ref?
//                    if (((JmlSingleton)sr).token == JmlToken.BSNOTHING) {
//                        // OK
//                    } else {
//                        havocEverything(preCondition,sr.pos);
//                    }
//                } else {
//                    log.error(sr.pos,"jml.internal","Unexpected kind of store-ref in BasicBlocker.havocAssignables: " + sr.getClass());
//                }
//            }
//        }
    }
    
    // FIXME - review and document
    private JCExpression fullRange;
    private JCExpression accumRange;
    protected JCExpression extractQuantifiers(JCExpression expr, ListBuffer<Name> ns) {
        if (expr instanceof JCIdent) {
            accumRange = trueLiteral;
            fullRange = trueLiteral;
            return expr;
        } else if (expr instanceof JmlStoreRefArrayRange) {
            JmlStoreRefArrayRange a = (JmlStoreRefArrayRange)expr;
            JCExpression e = extractQuantifiers(a.expression,ns);
            JCExpression id;
            if (a.lo == a.hi && a.lo != null) {
                id = a.lo;
            } else {
                Name n = names.fromString("i"+(ns.size()+1));
                id = factory.at(expr.pos).Ident(n); // No symbol - FIXME ???
                id.type = syms.intType;
                ns.append(n);
                fullRange = treeutils.makeBinary(a.pos,JCTree.AND,fullRange,treeutils.makeBinary(a.pos,JCTree.LE,treeutils.zero,id));
                //JCExpression len = factory.at(a.pos).Select(a.expression,lengthSym);
                JCExpression len = new JmlBBFieldAccess(lengthIdent,a.expression);
                len.pos = a.pos;
                len.type = syms.intType;
                fullRange = treeutils.makeBinary(a.pos,JCTree.AND,fullRange,treeutils.makeBinary(a.pos,JCTree.LT,id,len));
                if (a.lo != null) accumRange = treeutils.makeBinary(a.lo.pos,JCTree.AND,accumRange,treeutils.makeBinary(a.lo.pos,JCTree.LE,a.lo,id));
                if (a.hi != null) accumRange = treeutils.makeBinary(a.hi.pos,JCTree.AND,accumRange,treeutils.makeBinary(a.hi.pos,JCTree.LE,id,a.hi));
            }
            e = factory.at(expr.pos).Indexed(e,id);
            e.type = expr.type;
            return e;
        } else if (expr instanceof JCFieldAccess) {
            JCFieldAccess a = (JCFieldAccess)expr;
            JCExpression e = extractQuantifiers(a.selected,ns);
            if (e == a.selected) return e;
            e = factory.at(expr.pos).Select(e,a.sym);
            e.type = a.type;
            return e;
        } else {
            return expr;
        }
    }
    
    // FIXME - review and document
    protected void havocField(VarSymbol vsym, JCExpression selected, int pos, int npos, Type type, JCExpression preCondition) {
        JCIdent oldid = newIdentUse(vsym,pos);
        JCFieldAccess oldaccess = new JmlBBFieldAccess(oldid,selected);
        oldaccess.pos = pos;
        oldaccess.type = type;

        JCIdent newid = newIdentIncarnation(oldid,npos);
        JCFieldAccess newaccess = new JmlBBFieldAccess(newid,selected);
        newaccess.pos = pos;
        newaccess.type = type;

        JCExpression right = factory.at(pos).Conditional(preCondition,newaccess,oldaccess);
        right.type = type;
        
        JCExpression expr = new JmlBBFieldAssignment(newid,oldid,selected,right);
        expr.pos = pos;
        expr.type = type;

        addAssume(pos,Label.HAVOC,expr,currentBlock.statements);

    }
    
    // FIXME - review and document
    protected void havoc(JCExpression storeref) {
        if (storeref instanceof JCIdent) {
            JCIdent id = newIdentIncarnation((JCIdent)storeref,storeref.pos);
            //program.declarations.add(id);
            //} else if (e instanceof JCFieldAccess) {
            //} else if (e instanceof JCArrayAccess) {

        } else if (storeref instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)storeref;
            if (fa.name == null) {
                JCExpression e = fa.selected;
                if (e == null) {
                    log.noticeWriter.println("UNIMPLEMENTED HAVOC  " + storeref.getClass());
                    
                } else {
                    Symbol own = e.type.tsym;
                    Symbol s = e instanceof JCIdent ? ((JCIdent)e).sym : e instanceof JCFieldAccess ? ((JCFieldAccess)e).sym : null;
                    if (s instanceof ClassSymbol) {
                        for (VarSymbol vsym: currentMap.keySet()) {
                            if (vsym.owner == own && vsym.isStatic()) {
                                newIdentIncarnation(vsym, storeref.pos);
                            }
                        }
                    } else {
                        for (VarSymbol vsym: currentMap.keySet()) {
                            // FIXME - should we omit vsym.isStatic
                            if (vsym.owner == own && !vsym.name.toString().equals("this")) { // FIXME _ need a better way to avoid 'this'
//                                JCIdent oldid = treeutils.makeIdent(storeref.pos,vsym);
//                                JCIdent id = newIdentIncarnation(vsym, storeref.pos);
////                                JCIdent newfield = newIdentIncarnation(oldfield,pos);
////                                if (isDefined.add(newfield.name)) {
////                                    if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("AddedFF " + newfield.sym + " " + newfield.name);
////                                    addDeclaration(newfield);
////                                }
//                                JCFieldAccess rhs = treeutils.makeSelect(fa.pos,fa.selected,vsym);
//                                rhs.name = id.name;
//                                JCExpression expr = new JmlBBFieldAssignment(id,oldid,fa.selected,rhs);
//                                expr.pos = storeref.pos;
//                                expr.type = id.type;
//
//                                // FIXME - set line and source and position
//                                addAssume(storeref.pos,Label.ASSIGNMENT,expr,currentBlock.statements);
                                newIdentIncarnation(vsym, storeref.pos);

                            }
                        }
                    }
                }
            } else {
                newIdentIncarnation((VarSymbol)fa.sym, storeref.pos);
            }
        } else if (storeref instanceof JmlStoreRefKeyword) {
            JmlToken t = ((JmlStoreRefKeyword)storeref).token;
            if (t == JmlToken.BSEVERYTHING) {
                for (VarSymbol vsym: currentMap.keySet()) {
                    // Local variables are not affected by havoc \everything
                    // The owner of a local symbol is a MethodSymbol
                    if (vsym.owner instanceof ClassSymbol) newIdentIncarnation(vsym, storeref.pos);
                }
            }
        } else {
            // FIXME - havoc in loops
            log.noticeWriter.println("UNIMPLEMENTED HAVOC  " + storeref.getClass());
        }

    }
    

    
    // FIXME - review and document
    protected void havocEverything(JCExpression preCondition, int newpos) {
        // FIXME - if the precondition is true, then we do not need to add the 
        // assumptions - we just need to call newIdentIncarnation to make a new
        // value in the map.  This would shorten the VC.  How often is this
        // really the case?  Actually the preCondition does not need to be true,
        // it just needs to encompass all allowed cases.
        
        // FIXME - check on special variables - should they/are they havoced?
        // this
        // terminationVar
        // exceptionVar
        // resultVar
        // exception
        // others?
        
        // Change everything in the current map
        for (VarSymbol vsym : currentMap.keySet()) {
            if (vsym.owner == null || vsym.owner.type.tag != TypeTags.CLASS) {
                continue;
            }
            JCIdent oldid = newIdentUse(vsym,newpos);
            JCIdent newid = newIdentIncarnation(vsym,newpos);
            JCExpression e = factory.at(newpos).Conditional(preCondition,newid,oldid);
            e.type = vsym.type;
            e = treeutils.makeEquality(newpos,newid,e);
            addAssume(newpos,Label.HAVOC,e,currentBlock.statements);
        }
        //currentMap.everythingSAversion = newpos; // FIXME - this now applies to every not-yet-referenced variable, independent of the preCondition
    }

    /** This method is not called for top-level classes, since the BasicBlocker is invoked
     * directly for each method.
     */
    // FIXME - what about for anonymous classes or local classes or nested classes
    @Override
    public void visitClassDef(JCClassDecl that) {
        // Nested classes are found in JmlEsc.  We get to this point if there is a local
        // class declaration within method body.
        
        JmlEsc.instance(context).visitClassDef(that);
    }

    // FIXME - review this, and compare to the above
    @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        // Nested classes are found in JmlEsc.  We get to this point if there is a local
        // class declaration within method body.
        
        JmlEsc.instance(context).visitClassDef(that);
    }


    
    // OK
    @Override
    public void visitJmlStatementExpr(JmlStatementExpr that) { 
        if (that.token == JmlToken.COMMENT) {
            currentBlock.statements.add(that);
        } else if (that.token == JmlToken.ASSUME || that.token == JmlToken.ASSERT) {
            scan(that.expression);
            //that.expression = result;
            JmlStatementExpr st = M.at(that.pos()).JmlExpressionStatement(that.token,that.label,result);
            st.id = that.id;
            scan(that.optionalExpression);
            st.optionalExpression = result;
            st.associatedPos = that.associatedPos;
            st.associatedSource = that.associatedSource;
            //st.line = that.line;
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
    

//    // We introduce the name 'assumeCheck$<int>$<label>' in order to make
//    // it easy to identify the places where assumptions are being checked.
//    /** Adds (translated) assertions/assumptions that do assumption feasibility checking 
//     * for an assumption that is just added to the currentBlock
//     * @param pos a positive integer different than that used for any other checkAssumption call;
//     *    it should also be the textual location of the assumption being tested
//     * @param label a Label giving the kind of assumption being tested (in order to
//     *    better interpret the implications of the assumptino not being feasible)
//     */
//    
//    protected void checkAssumption(int pos, /*@ non_null*/ Label label, List<JCStatement> statements) {
//        if (!insertAssumptionChecks) return;
//        JCExpression e;
//        JCIdent id;
//        String n = ASSUME_CHECK_PREFIX + pos + "" + label.toString();
//        if (useCountedAssumeCheck) {
//            JCExpression count = treeutils.makeIntLiteral(pos,pos);
//            e = treeutils.makeBinary(pos,JCTree.NE,assumeCheckCountVar,count);
//            id = newAuxIdent(n,syms.booleanType,pos,false);
//            //e = treeutils.makeBinary(pos,JCTree.EQ,id,e);
//            // assume assumeCheck$<int>$<label> == <assumeCheckCountVar> != <int>
//            // To do the coreId method, we need to put this in the definitions list
//            // instead.  And it does not hurt anyway.
//            //addAssume(pos,Label.ASSUME_CHECK,e); // adds to the currentBlock
//            BasicProgram.Definition def = new BasicProgram.Definition(pos,id,e);
//            newdefs.add(def);
//            e = def.expr(context);
//        } else {
//            id = newAuxIdent(n,syms.booleanType,pos,false);
//            e = id;
//            if (assumeCheck == null) assumeCheck = e;
//            else assumeCheck = treeutils.makeBinary(pos,JCTree.AND,e,assumeCheck);
//        }
//        program.assumptionsToCheck.add(new Entry(e,n));
//        // an assert without tracking
//        // assert assumeCheck$<int>$<label>
//        addAssertNoTrack(Label.ASSUME_CHECK,id,statements,pos,null); // FIXME - need the position of the assume, I think
//    }
//
//    protected void checkAssumption(int pos, /*@ non_null*/ Label label) {
//        checkAssumption(pos,label,currentBlock.statements);
//    }

    // Visit methods for Expressions for the most part just use the super class's
    // visit methods. These just call visitors on each subexpression.
    // Everything is transformed in place.
    // There are a few nodes that get special treatment:
    //  JCIdent - the name is overwritten with the single-assignment name (note that
    //     the name will be out of synch with the symbol)
    //  \old and \pre expressions - these need to find the correct scope and translate
    //     JCIdent nodes within their scopes using the correct single-assignment names
        
    
    public Map<JCTree,JCTree> toLogicalForm = new HashMap<JCTree,JCTree>();
//    public Map<JCTree,String> toValue = new HashMap<JCTree,String>();
    
    public void addDeclaration(JCIdent that) {
        JCIdent t = treeutils.makeIdent(0,that.sym);
        t.name = that.name;
        program.declarations.add(t);
    }
    
    // OK
    @Override
    public void visitIdent(JCIdent that) {
        if (that.sym instanceof Symbol.VarSymbol){ 
            if (quantifierSymbols.contains(that.sym)) {
                // no change
            } else {
                Symbol.VarSymbol vsym = (Symbol.VarSymbol)that.sym;
                that.name = currentMap.getCurrentName(vsym);
                if (isDefined.add(that.name)) {
                    if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("Added " + that.sym + " " + that.name);
                    addDeclaration(that);
                }
            }
        } else if (that.sym == null) {
            // Temporary variables that are introduced by decomposing expressions do not have associated symbols
            // They are also only initialized once and only used locally, so we do not track them for DSA purposes
            // Just skip
        } else if (that.sym instanceof Symbol.TypeSymbol) { // Includes class, type parameter, package
            // Just skip
//        } else if (that.sym instanceof Symbol.PackageSymbol) {
//            // Just skip
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
        if (that.sym.isStatic()) {
            that.name = currentMap.getCurrentName((Symbol.VarSymbol)that.sym);
            JCIdent id = treeutils.makeIdent(that.pos,that.sym);
            id.name = that.name;
            if (isDefined.add(that.name)) {
                if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("AddedF " + that.sym + " " + that.name);
                addDeclaration(id);
            }
            result = id;
            
        } else {
            that.name = currentMap.getCurrentName((Symbol.VarSymbol)that.sym);
            if (isDefined.add(that.name)) {
                if (utils.jmlverbose >= Utils.JMLDEBUG) log.noticeWriter.println("AddedF " + that.sym + " " + that.name);
                JCIdent id = treeutils.makeIdent(that.pos,that.sym);
                id.name = that.name;
                addDeclaration(id);
            }
            result = that;
        }
    }
    
    public void visitIndexed(JCArrayAccess that) {
        scan(that.indexed);
        JCExpression indexed = result;
        scan(that.index);
        JCExpression index = result;
        JCIdent arr = getArrayIdent(that.type);
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


    
    
    // FIXME - review
    public void visitAssign(JCAssign that) {
        //scan(that.lhs);
        JCExpression left = that.lhs;
        scan(that.rhs);
        JCExpression right = result;
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
        if (left instanceof JCIdent) {
            JCIdent id = (JCIdent)left;
            JCIdent newid = newIdentIncarnation(id,sp);
            //currentBlock.statements.add(treeutils.makeVarDef(newid.type, newid.name, id.sym.owner, pos));
            JCBinary expr = treeutils.makeEquality(pos,newid,right);
            //copyEndPosition(expr,right);
            addAssume(sp,Label.ASSIGNMENT,expr);
            return newid;
        } else if (left instanceof JCArrayAccess) {
            JCIdent arr = getArrayIdent(right.type);
            JCExpression ex = ((JCArrayAccess)left).indexed;
            JCExpression index = ((JCArrayAccess)left).index;
            JCIdent nid = newArrayIncarnation(right.type,sp);
            
            //JCExpression rhs = makeStore(ex,index,right);
            JCExpression expr = new JmlBBArrayAssignment(nid,arr,ex,index,right);
            expr.pos = pos;
            expr.type = restype;

            // FIXME - set line and source
            addAssume(sp,Label.ASSIGNMENT,expr,currentBlock.statements);
            //newIdentIncarnation(heapVar,pos);
            return left;
        } else if (left instanceof JCFieldAccess) {
            VarSymbol sym = (VarSymbol)selectorSym(left);
            if (sym.isStatic()) {
                JCIdent id = newIdentUse(sym,sp);
                JCIdent newid = newIdentIncarnation(id,sp);
                // currentBlock.statements.add(treeutils.makeVarDef(newid.type, newid.name, id.sym.owner, pos));
                JCBinary expr = treeutils.makeEquality(pos,newid,right);
                //copyEndPosition(expr,right);
                addAssume(statement.getStartPosition(),Label.ASSIGNMENT,expr);
                return newid;
            } else {
                JCFieldAccess fa = (JCFieldAccess)left;
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

                // FIXME - set line and source
                addAssume(sp,Label.ASSIGNMENT,expr,currentBlock.statements);
                newIdentIncarnation(heapVar,pos);
            }
            return left;
        } else {
            log.error("jml.internal","Unexpected case in BasicBlocker.doAssignment: " + left.getClass() + " " + left);
            return null;
        }
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
        JCIdent lhs = newIdentIncarnation(that,that.getPreferredPosition());
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
            isDefined.add(that.name);
            currentMap.putSAVersion(that.sym,that.name,0); // FIXME - should unique be incremented
            currentBlock.statements.add(that);
        } else {
            JCIdent lhs = newIdentIncarnation(that,that.getPreferredPosition());
            isDefined.add(lhs.name);
            if (that.init != null) {
                scan(that.init);
                that.init = result;
                JCBinary expr = treeutils.makeBinary(that.pos,JCBinary.EQ,lhs,that.init);
                addAssume(that.getStartPosition(),Label.ASSIGNMENT,expr,currentBlock.statements);
            }
        }

        
//        if (that.init != null) scan(that.init);
//        if (that.sym != null) currentMap.put(that.sym, currentMap.everythingIncarnation, that.name);
//        currentBlock.statements.add(that);
//        currentBlock.statements.add(comment(that));
//        // FIXME - need to add various field specs tests
//        JCIdent vd = newIdentIncarnation(that,that.pos);
//        toLogicalForm.put(that,vd);
//        if (that.init != null) {
//            int p = that.init.pos;
//            boolean prevInSpecExpression = inSpecExpression;
//            try {
//                if (Utils.instance(context).isJML(that.mods)) inSpecExpression = true;
//                JCExpression ninit = (that.init);
//                addAssume(TreeInfo.getStartPos(that),Label.ASSIGNMENT,treeutils.makeEquality(p,vd,ninit));
//            } finally {
//                inSpecExpression = prevInSpecExpression;
//            }
//        }
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
    public void visitLetExpr(LetExpr that)               { notImpl(that); }
    
    public void visitTypeIdent(JCPrimitiveTypeTree that) { 
        notImpl(that); 
    }
    public void visitTypeArray(JCArrayTypeTree that)     { notImpl(that); }
    public void visitTypeApply(JCTypeApply that)         { 
        // This is the application of a generic type to its parameters
        // e.g., List<Integer> or List<T>
        
        // Just skip
        result = that;
    }
    
    public void visitTypeParameter(JCTypeParameter that) { notImpl(that); }


    // FIXME _ implement
    @Override public void visitJmlSetComprehension(JmlSetComprehension that) { notImpl(that); }
    
    
    @Override public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) { notImpl(that); }
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

    // These do not need to be implemented
    @Override public void visitTopLevel(JCCompilationUnit that)    { shouldNotBeCalled(that); }
    @Override public void visitImport(JCImport that)               { shouldNotBeCalled(that); }
    @Override public void visitJmlCompilationUnit(JmlCompilationUnit that)   { shouldNotBeCalled(that); }
    @Override public void visitJmlImport(JmlImport that)                     { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodDecl(JmlMethodDecl that)  { shouldNotBeCalled(that); }
    @Override public void visitJmlStatement(JmlStatement that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementSpec(JmlStatementSpec that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementDecls(JmlStatementDecls that) { shouldNotBeCalled(that); }
    @Override public void visitMethodDef(JCMethodDecl that)        { shouldNotBeCalled(that); }
    
    List<Symbol> quantifierSymbols = new LinkedList<Symbol>();
    
    @Override public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) { 
        for (JCVariableDecl d: that.decls) {
            quantifierSymbols.add(d.sym);
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
                quantifierSymbols.remove(d.sym);
            }
        }
 
    }

    // OK
    @Override public void visitBinary(JCBinary that) {
        scan(that.lhs);
        that.lhs = result;
        scan(that.rhs);
        that.rhs = result;
        result = that; 
    }
    
    // OK
    @Override public void visitUnary(JCUnary that) { 
        scan(that.arg);
        that.arg = result;
        result = that; 
    }
    
    // OK
    @Override public void visitParens(JCParens that) { 
        scan(that.expr);
        that.expr = result;
        // Leave result = the result of scanning that.expr 
    }
    
    // OK
    @Override public void visitConditional(JCConditional that) { 
        scan(that.cond);
        that.cond = result;
        scan(that.truepart);
        that.truepart = result;
        scan(that.falsepart);
        that.falsepart = result;
        result = that; 
    }

    // OK // FIXME - does this expression type appear?
    @Override public void visitTypeTest(JCInstanceOf that) { 
        scan(that.expr);
        scan(that.clazz); // FIXME - do we scan type names?
        result = that; 
    }

    // OK // FIXME - does this expression type appear? in REF case it should be a noop
    @Override public void visitTypeCast(JCTypeCast that) { 
        scan(that.clazz); // FIXME - do we scan type names?
        scan(that.expr);
        result = that; 
    }

// Do not need to override these methods
//  @Override public void visitSkip(JCSkip that) { super.visitSkip(that); }
        
    public void visitJmlStatementLoop(JmlStatementLoop that) { 
        shouldNotBeCalled(that); // These are the specs for loops - they are handled in the loop visitors
    }
    
    // FIXME - what about Indexed, TypeCast, TypeTest, AssignOp, NewClass, NewArray

    
    static class GetSymbols extends JmlTreeScanner {
        
        boolean noMethods = false;
        
        public static Set<VarSymbol> collectSymbols(JCMethodDecl method, JCClassDecl classDecl) {
            GetSymbols gs = new GetSymbols();
            gs.noMethods = false;
            method.accept(gs);
            gs.noMethods = true;
            classDecl.accept(gs);
            return gs.syms;
        }
        
        private Set<VarSymbol> syms = new HashSet<VarSymbol>();
        
        public GetSymbols() {
            scanMode = this.AST_SPEC_MODE;
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
                    that.sym.owner instanceof ClassSymbol) syms.add((VarSymbol)that.sym);
        }
    }

}
