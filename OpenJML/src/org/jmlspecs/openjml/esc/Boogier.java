/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import static com.sun.tools.javac.code.TypeTag.CLASS;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlInternalError;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.esc.BoogieProgram;
import org.jmlspecs.openjml.esc.BoogieProgram.BoogieBlock;
import org.jmlspecs.openjml.ext.Operators;
import org.jmlspecs.openjml.ext.SingletonExpressions;
import org.jmlspecs.openjml.ext.StatementExprExtensions;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import static org.jmlspecs.openjml.ext.MiscExtensions.*;
import static org.jmlspecs.openjml.ext.FunctionLikeExpressions.*;
import static org.jmlspecs.openjml.ext.StateExpressions.*;
import static org.jmlspecs.openjml.ext.TypeExprClauseExtension.*;
import static org.jmlspecs.openjml.ext.TypeRepresentsClauseExtension.*;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.TypeVariableSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.Type.MethodType;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.comp.Attr;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

/** This class converts a Java AST into a Boogie2 program. It leaves to whatever
 * tool processes the Boogie program the tasks of DSA and passification.
 * All Java (and JML) statements are rewritten into assignment, assume and
 * assert statements, with basic blocks being created to represent the control
 * flow. In addition, note the following:
 * <UL>
 * <LI> No assertions to represent Java or JML semantics are added, except for those
 * needed to convert control flow into basic blocks
 * </UL>
 * <P>
 * The input tree must consist of
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
 * Basic block output form contains only this subset of AST nodes:
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
public class Boogier extends BasicBlockerParent<BoogieProgram.BoogieBlock,BoogieProgram> {

    /////// To have a unique BoogieBlocker2 instance for each method translated
    // In the initialization of tools, call  BoogieBlocker2.Factory.preRegister(context);
    // Obtain a new BoogieBlocker2 when desired with  context.get(BoogieBlocker2.class);
        
//    /** Register a BoogieBlocker Factory, if nothing is registered yet */
//    public static void preRegister(final Context context) {
//        //if (context.get(key) != null) return;
//        context.put(key, new Context.Factory<BoogieBlocker2>() {
//            @Override
//            public BoogieBlocker2 make(Context context) {
//                return new BoogieBlocker2(context);
//            }
//        });
//    }
//    
//    final public static Context.Key<BoogieBlocker2> key =
//        new Context.Key<BoogieBlocker2>();
    
    /////// To have one BoogieBlocker2 instance per context use this method without the pre-registration
    // Don't need pre-registration since we are not replacing any tool and not using a M
    // To obtain a reference to the instance of BoogieBlocker2 for the current context
    //                                 BoogieBlocker2.instance(context);
    
//    /** Get the instance for this context. 
//     * 
//     * @param context the compilation context
//     * @return a (unique for the context) BoogieBlocker instance
//     */
//    public static BoogieBlocker2 instance(@NonNull Context context) {
//        BoogieBlocker2 instance = context.get(key);
//        // This is lazily initialized so that a derived class can preRegister to
//        // replace this BoogieBlocker
//        if (instance == null) {
//            instance = new BoogieBlocker2(context);
//        }
//        return instance;
//    }
    
    // Options
    
    // This implements checking of assumption feasibility.  After an 
    // assumption that is to be checked, we add the assertion
    //       assert assumeCheck$<uniqueint>$<label>
    // and the definition
    //       assume assumeCheck$<uniqueint>$<label> == <assumecheckvar> != <uniqueint>
    // where <uniqueint> is a positive integer not used elsewhere for 
    // this purpose.  Here we use the source code location so that it
    // can be used as well to generate error messages.
    // Then we also add to the VC the assumption
    //       assume <assumecheckvar> == 0
    // That way all the inserted assertions above are true.  However, we
    // can change any one of them to false by replacing the assumption
    // above with
    //       assume <assumecheckvar> == <uniqueid>
    // using the specific <uniqueint> of the assumption we want to test
    
    // FIXME - review and document
    static public boolean insertAssumptionChecks = true;
    
    // FIXME - review and document
    static boolean useCountedAssumeCheck = true;
    // FIXME - review and document
    static JCExpression booleanAssumeCheck;
    // FIXME - review and document
    JCExpression assumeCheck = null;

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
    
    /** Name of the encoded this variable */
    public static final String THIS = "THIS_";
    
    /** The prefix of the variables used in checking assumptions */
    public static final String ASSUME_CHECK_PREFIX = "ASSUMECHECK_";
    
    /** A variable name used in checking assumptions */
    public static final String ASSUME_CHECK_COUNT = "__assumeCheckCount";
    
    /** Name of length field */
    public static final String LENGTH = "length";
    
    
    // THE FOLLOWING FIELDS ARE EXPECTED TO BE CONSTANT FOR THE LIFE OF THE OBJECT
    // They are either initialized in the constructor or initialized on first use
    

    /** Identifier of a synthesized object field holding the length of an array object, initialized in the constructor */
    @NonNull protected JCIdent lengthIdent;

    /** Symbol of a synthesized object field holding the length of an array object, initialized in the constructor */
    @NonNull protected VarSymbol lengthSym;
    
    /** A fixed id for 'this' of the method being translated (see currentThisId
     * for the 'this' of called methods). */
    @NonNull protected JCIdent thisId;


    // FIXME - document the following; check when initialized
    // FIXME - exceptionVar and terminationVar are no longer needed I think
    protected JCIdent exceptionVar = null;
    protected JCIdent heapVar;
    protected JCIdent terminationVar;  // 0=no termination requested; 1=return executed; 2 = exception happening
    
    // THE FOLLOWING FIELDS ARE USED IN THE COURSE OF DOING THE WORK OF CONVERTING
    // TO BASIC BLOCKS.  They are fields of the class because they need to be
    // shared across the visitor methods.
    
    /** Place to put new background assertions, such as class predicates */
    protected List<JCExpression> background;
       
    /** The variable name that is currently the 'this' variable */
    protected JCIdent currentThisId;
    

    /** The jfoMap and jfoArray keep track of a mapping between JavaFileObjects and
     * unique Integers. When position information in an encoded identifier refers to 
     * a file that is not the file containing the implementation of the method being
     * translated and verified, then we have to indicate which file contains the source
     * for the position reference. This indication is an @ followed by an integer included in the identifier,
     * where the integer is a unique positive integer associated with the file. Since
     * these mappings are static, the associations remain constant across different methods
     * and different compilation contexts.
     * <BR>
     * jfoMap is a mapping from JavaFileObject to Integer
     */
    // FIXME - should reconsider whether these mappings should be static
    static Map<JavaFileObject,Integer> jfoMap = new HashMap<JavaFileObject,Integer>();

    /** Maps integers to JavaFileObject, the reverse of the mapping in jfoMap */
    static ArrayList<JavaFileObject> jfoArray = new ArrayList<JavaFileObject>();
    static {
        jfoArray.add(0,null);
    }
    
    /** Returns the int associated with a file, creating it if necessary */
    // FIXME - check what equals and hashmap are being used.
    public static int getIntForFile(JavaFileObject jfo) {
        Integer i = jfoMap.get(jfo);
        int k;
        if (i == null) {
            k = jfoArray.size();
            jfoArray.add(k,jfo);
            jfoMap.put(jfo,k);
        } else {
            k = i;
        }
        return k;
    }
    
    /** Returns the file associated with an int */
    public static JavaFileObject getFileForInt(int i) {
        return jfoArray.get(i);
    }
    
    /** The constructor, but use the instance() method to get a new instance,
     * in order to support extension.  This constructor should only be
     * invoked by a derived class constructor.
     * @param context the compilation context
     */
    protected Boogier(@NonNull Context context) {
        super(context);

        // This is the symbol to access the length of an array 
        lengthSym = syms.lengthVar;
        lengthIdent = treeutils.makeIdent(0,lengthSym);
        
    }
    
    /** Creates an empty new BoogieProgram */
    @Override
    public BoogieProgram newProgram(Context context) {
        return new BoogieProgram(context);
    }
    
    /** Creates an empty new BoogieBlock */
    @Override
    public BoogieBlock newBlock(JCIdent id){
        return new BoogieProgram.BoogieBlock(id);
    }
    
    
    // METHODS

//    @Override
//    public void scan(com.sun.tools.javac.util.List<? extends JCTree> trees) {
//        if (trees != null)
//        for (com.sun.tools.javac.util.List<? extends JCTree> l = trees; l.nonEmpty(); l = l.tail) {
//            scan(l.head);
//        }
//    }

    public void scanList(com.sun.tools.javac.util.List<JCExpression> trees) {
        if (trees != null)
        for (com.sun.tools.javac.util.List<JCExpression> l = trees; l.nonEmpty(); l = l.tail) {
            scan(l.head);
            l.head = result;
        }
    }

    
    // FIXME - use treeutils?
    /** Creates a translated expression whose value is the given type;
     * the result is a JML type, e.g. a representation of an instantiated generic.*/
    protected JCExpression makeTypeLiteral(Type type, int pos) {
        return treeutils.trType(pos,type);
    }
    
    Set<Symbol> isDefined = new HashSet<Symbol>();
    
    // FIXME - review
    /** Creates name for a symbol unique to its declaration
     *    <symbol name>__<declaration position>
     * If the symbol has a negative declaration position, that value is not included in the string
     * @param sym the symbol being given a logical name
     * @param incarnationPosition the incarnation position for which to give a new name
     * @return the new name
     */
    protected Name encodedName(VarSymbol sym) {
//      if (isDefined.add(n)) {
//      //System.out.println("AddedC " + sym + " " + n);
//      JCIdent id = treeutils.makeIdent(0, sym);
//      id.name = n;
//      program.declarations.add(id);
//  }
        return names.fromString(sym.getQualifiedName() + (sym.pos < 0 ? "" : ("__" + sym.pos)));
    }
    
    // FIXME - Review
    protected Name encodedArrayName(VarSymbol sym, int incarnationPosition) {
        Name n;
        if (incarnationPosition == 0) {
            n = sym.getQualifiedName();
        } else {
            n = names.fromString(sym.getQualifiedName() + (sym.pos < 0 ? "" : ("_" + sym.pos)) );
        }
//        if (isDefined.add(n)) {
//            //System.out.println("AddedC " + sym + " " + n);
//            JCIdent id = treeutils.makeIdent(0, sym);
//            id.name = n;
//            program.declarations.add(id);
//        }
        return n;
//return names.fromString(sym.getQualifiedName() + (sym.pos < 0 ? "_" : ("_" + sym.pos + "_")) + incarnationPosition);
    }
    
    // FIXME - review and document
    protected Name encodedName(TypeSymbol tp, int incarnationPosition) {
        return names.fromString(tp.name + "_" + incarnationPosition);
    }
    
    // FIXME - review and document
    protected Name encodedNameNoUnique(VarSymbol sym, int incarnationPosition) {
        return names.fromString(sym.getQualifiedName() + (sym.pos < 0 ? "_" : ("_" + sym.pos + "_")) + incarnationPosition);
    }
    
    // FIXME - review
    /** Creates an encoded name for a Type variable.  There is no incarnation position
     * because type variables are not assigned after initialization.
     * @param sym
     * @param declarationPosition
     * @return the new name
     */
    protected Name encodedTypeName(TypeSymbol sym, int declarationPosition) {
        return names.fromString(sym.flatName() + "_" + declarationPosition);
    }
    
    // FIXME - review
    /** Creates an encoded name from a symbol and an incarnation position of the form
     *    <symbol name>$<declaration position>$<use position>
     * Does not include a unique id
     * If the symbol has a negative declaration position, that value is not included in the string
     * @param sym the symbol being given a logical name
     * @param incarnationPosition the incarnation position for which to give a new name
     * @return the new name
     */
    protected Name encodedName(MethodSymbol sym, int declpos, int incarnationPosition) {
        return names.fromString(sym.getQualifiedName() + (declpos < 0 ? "_" : ("_" + declpos + "_")) + incarnationPosition);
    }
    
    
    // FIXME - review
    /** Creates a new Ident node, but in this case we are not using the name from
     * the current incarnation map - so we supply the name. This is just used for
     * DSA assignments.
     */
    protected JCIdent newIdentUse(VarSymbol sym, Name name) {
        // Boogie does not care about AST position
        JCIdent n = M.Ident(name);
        n.sym = sym;
        n.type = sym.type;
        return n;
    }
    
    
    /** Returns the name to use for a symbol under the current Map. */
    protected Name getCurrentName(VarSymbol sym) {
        return encodedName(sym);
    }
    

    /** Converts the top-level block of a method into the elements of a BasicProgram 
     * 
     * @param methodDecl the method to convert to to a BasicProgram
     * @param denestedSpecs the specs of the method
     * @param classDecl the declaration of the containing class
     * @return the completed BasicProgram
     */
    protected @NonNull BoogieProgram convertMethodBody(JCBlock block, @NonNull JCMethodDecl methodDecl, 
            JmlMethodSpecs denestedSpecs, @NonNull JCClassDecl classDecl, @NonNull JmlAssertionAdder assertionAdder) {
        
        initialize(methodDecl,classDecl,assertionAdder);
//        JmlClassInfo classInfo = getClassInfo(classDecl.sym);
//        if (classInfo == null) {
//            log.error("jml.internal","There is no class information for " + classDecl.sym);
//            return null;
//        }
        background = new LinkedList<JCExpression>();
        
        terminationVar = treeutils.makeIdent(methodDecl.pos,terminationSym);
        exceptionVar = treeutils.makeIdent(methodDecl.pos,assertionAdder.exceptionSymbols.get(methodDecl)); // newAuxIdent(EXCEPTION,syms.exceptionType,0,true);
        heapVar = treeutils.makeIdent(methodDecl.pos,HEAP_VAR,syms.intType); // FIXME - would this be better as its own uninterpreted type?
//        assumeCheckCountVar = treeutils.makeIdent(0,ASSUME_CHECK_COUNT,syms.intType);
//        assumeCheckCount = 0;
        
        // Define the start block
        int pos = methodDecl.pos;
        BoogieBlock startBlock = newBlock(START_BLOCK_NAME,pos);

        // Define the body block
        // Put all the program statements in the Body Block
        BoogieBlock bodyBlock = newBlock(BODY_BLOCK_NAME,methodDecl.body.pos);

        // Then the program
        bodyBlock.statements.addAll(block.getStatements());
        follows(startBlock,bodyBlock);
        
        // Handle the start block a little specially
        // It does not have any statements in it
        startBlock(startBlock); // Start it so the currentMap, currentBlock, remainingStatements are defined

        // Define the thisId
        if (this.methodDecl._this != null) {
            thisId = treeutils.makeIdent(pos,this.methodDecl._this.name.toString(),methodDecl.sym.owner.type);
            currentThisId = thisId;
        }

        // FIXME - have to do static vars of super types also
        // FIXME - and all the model fields
        // FIXME - and all the fields of referenced classes
        // We have to create and store incarnations of class fields so that there is a record of
        // them in the oldMap. Otherwise, if the variables are used within \old later on, a new 
        // identifier will be created, with a new unique number.
//        for (JCTree tree: classInfo.decl.defs ) {
//            if (tree instanceof JCVariableDecl) {
//                JCVariableDecl d = (JCVariableDecl)tree;
//                newIdentIncarnation(d.sym,0);
//            }
//        }

        completeBlock(currentBlock);

        processBlock(bodyBlock);
        
        // Finished processing all the blocks
        // Make the BasicProgram
//        program.startId = startBlock.id;
        //program.blocks.addAll(blocksCompleted);
        if (assumeCheck != null) booleanAssumeCheck = assumeCheck;
        program.background = background;
//        program.assumeCheckVar = assumeCheckCountVar;
//        program.toLogicalForm = toLogicalForm;
        return program;
    }
    
    int assertCount = 0;
    
    // FIXME - REVIEW and document
    protected void addAssert(Label label, JCExpression that, int declpos, List<JCStatement> statements, int usepos, JavaFileObject source, JCTree statement) {
        if (Nowarns.instance(context).suppress(source,usepos,label.toString())) return;
//        if (useAssertDefinitions && label != Label.ASSUME_CHECK) {
//            //if (extraEnv) { usepos++; declpos++; }
//            String n;
//            if (source == log.currentSourceFile()) {
//                n = "assert_" + usepos + "_" + declpos + "_" + label + "_" + (unique++);
//            } else {
//                Integer i = getIntForFile(source);
//                n = "assert_" + usepos + "_" + declpos + "__" + i + "_" + label + "_" + (unique++);
//            }
//             
//            JCIdent id = newAuxIdent(n,syms.booleanType,that.getStartPosition(),false);
//            copyEndPosition(id,that); // FIXME - merge into the call above
//            
//            //JCExpression expr = treeutils.makeBinary(that.pos,JCTree.EQ,id,that);
//                    // FIXME - start and end?
//            BasicProgram.Definition stat = new BasicProgram.Definition(statement.pos,id,that); // FIXME - if we keep this, should use a factory
//            newdefs.add(stat);
//            that = id;
//        }
        JmlTree.JmlStatementExpr st = M.at(statement.pos).JmlExpressionStatement(StatementExprExtensions.assertID, StatementExprExtensions.assertClause, label,that);
        st.optionalExpression = null;
        st.source = source;
        st.associatedPos = declpos;
        st.id = "ASSERT__" + (++assertCount);
        st.type = null; // no type for a statement
        copyEndPosition(st,statement);
        statements.add(st);
    }
    
    // FIXME - REVIEW and document
    public void copyEndPosition(JCTree newnode, JCTree srcnode) {
    }

    
    // FIXME - REVIEW and document
    /** Adds an assertion with an untranslated expression to the given statement list; 
     * it is presumed the statement will be translated later */
    protected void addUntranslatedAssert(Label label, JCExpression that, int declpos, List<JCStatement> statements, int usepos, /*@Nullable*/JavaFileObject source) {
        JmlStatementExpr st;
        st = M.at(usepos).JmlExpressionStatement(StatementExprExtensions.assertID, StatementExprExtensions.assertClause,label,that);
        st.optionalExpression = null;
        st.source = source;
        st.associatedPos = declpos;
        st.id = "ASSERT__" + (++assertCount);
        st.type = null; // no type for a statement
        statements.add(st);
    }
    
    // FIXME - REVIEW and document
    /** Adds an assertion to the given statement list; the expression is presumed translated */
    protected void addAssertNoTrack(Label label, JCExpression that, List<JCStatement> statements, int usepos, /*@Nullable*/JavaFileObject source) {
        JmlStatementExpr st;
        st = M.at(usepos).JmlExpressionStatement(StatementExprExtensions.assertID, StatementExprExtensions.assertClause,label,that);
        st.optionalExpression = null;
        st.type = null; // no type for a statement
        st.source = source;
        st.id = "ASSERT__" + (++assertCount);
        st.associatedPos = usepos;// FIXME - what should this be set to?
        statements.add(st);
    }
    
    // FIXME - REVIEW and document
    /** Adds a new assume statement to the end of the currentBlock; the assume statement is
     * given the declaration pos and label from the arguments; it is presumed the input expression is
     * translated, as is the produced assume statement.
     * @param pos the declaration position of the assumption
     * @param label the kind of assumption
     * @param that the (translated) expression being assumed
     */
    protected void addAssume(int pos, Label label, JCExpression that) {
        addAssume(pos,label,that,currentBlock.statements);
    }
    
    // FIXME - REVIEW and document
    /** Adds a new assume statement to the end of the given statements list; the assume statement is
     * given the declaration pos and label from the arguments; it is presumed the input expression is
     * translated, as is the produced assume statement.
     * @param pos the declaration position of the assumption
     * @param label the kind of assumption
     * @param that the (translated) expression being assumed
     * @param statements the list to add the new assume statement to
     */
    protected JmlStatementExpr addAssume(int pos, Label label, JCExpression that, List<JCStatement> statements) {
        M.at(pos);
        JmlStatementExpr st;
//        if (useAssumeDefinitions) {
//            JCIdent id = M.Ident(names.fromString(ASSUMPTION_PREFIX+(unique++)));
//            id.type = syms.booleanType;
//            newdefs.add(new BasicProgram.Definition(that.pos,id,that)); // FIXME- end position?
//            st = M.JmlExpressionStatement(JmlToken.ASSUME,label,id);
//        } else {
            st = M.JmlExpressionStatement(StatementExprExtensions.assumeID, StatementExprExtensions.assumeClause,label,that);
//        }
//        copyEndPosition(st,that);
        st.type = null; // statements do not have a type
        st.id = "ASSUME__" + (++assertCount);
        statements.add(st);
        return st;
    }
    
    // FIXME - REVIEW and document
    protected JmlStatementExpr addAssume(int startpos, JCTree endpos, Label label, JCExpression that, List<JCStatement> statements) {
        if (startpos < 0) startpos = that.pos; // FIXME - temp 
        M.at(startpos);
        JmlStatementExpr st;
//        if (useAssumeDefinitions) {
//            JCIdent id = M.Ident(names.fromString(ASSUMPTION_PREFIX+(unique++)));
//            id.type = syms.booleanType;
//            newdefs.add(new BasicProgram.Definition(that.pos,id,that)); // FIXME- start, end position?
//            st = M.JmlExpressionStatement(JmlToken.ASSUME,label,id);
//        } else {
            st = M.JmlExpressionStatement(StatementExprExtensions.assumeID, StatementExprExtensions.assumeClause,label,that);
//        }
//        copyEndPosition(st,endpos);
        st.type = null; // statements do not have a type
        st.id = "ASSUME__" + (++assertCount);
        statements.add(st);
        return st;
    }
    
//    // FIXME - REVIEW and document
//    protected JmlStatementExpr addAssumeNoDef(int startpos, JCTree endpos, Label label, JCExpression that, List<JCStatement> statements) {
//        if (startpos < 0) startpos = that.pos; // FIXME - temp 
//        M.at(startpos);
//        JmlStatementExpr st;
//        st = M.JmlExpressionStatement(JmlToken.ASSUME,label,that);
////        copyEndPosition(st,endpos);
//        st.type = null; // statements do not have a type
//        statements.add(st);
//        return st;
//    }
    
//    // FIXME - REVIEW and document
//    /** Adds a new UNTRANSLATED assume statement to the end of the given statements list; the statements list
//     * should be a list of statements that will be processed (and translated) at some later time;
//     * the assume statement is
//     * given the declaration pos and label from the arguments; it is presumed the input expression is
//     * untranslated, as is the produced assume statement.
//     * @param pos the declaration position of the assumption
//     * @param label the kind of assumption
//     * @param that the (untranslated) expression being assumed
//     * @param statements the list to add the new assume statement to
//     */
//    protected JmlStatementExpr addUntranslatedAssume(int pos, Label label, JCExpression that, List<JCStatement> statements) {
//        JmlStatementExpr st = M.at(pos).JmlExpressionStatement(JmlToken.ASSUME,label,that);
//        st.type = null; // statements do not have a type
////        copyEndPosition(st,that);
//        statements.add(st);
//        return st;
//    }
    
//    // FIXME - REVIEW and document
//    protected JmlStatementExpr addUntranslatedAssume(int pos, JCTree posend, Label label, JCExpression that, List<JCStatement> statements) {
//        JmlStatementExpr st = M.at(pos).JmlExpressionStatement(JmlToken.ASSUME,label,that);
//        st.type = null; // statements do not have a type
////        copyEndPosition(st,posend);
//        statements.add(st);
//        return st;
//    }
    
    
    // FIXME - REVIEW and document
    static public String encodeType(Type t) {   // FIXME String? char? void? unsigned?
        TypeTag tag = t.getTag();
        if (t instanceof ArrayType) {
            return "refA$" + encodeType(((ArrayType)t).getComponentType());
        } else if (!t.isPrimitive()) {
            return "REF";
        } else if (tag == TypeTag.INT || tag == TypeTag.SHORT || tag == TypeTag.LONG || tag == TypeTag.BYTE) {
            return "int";
        } else if (tag == TypeTag.BOOLEAN) {
            return "bool";
        } else if (tag == TypeTag.FLOAT || tag == TypeTag.DOUBLE) {
            return "real";
        } else if (tag == TypeTag.CHAR) {
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
            id = M.Ident(names.fromString(s));
            id.pos = 0;
            id.type = new ArrayType(componentType,syms.arrayClass);
            VarSymbol sym = new VarSymbol(0,id.name,id.type,null);
            sym.pos = 0;
            id.sym = sym;
            arrayIdMap.put(s,id);
        }
        id = treeutils.makeIdent(0,id.sym);
        return id;
    }
    
    
    
    
    /** This generates a comment statement (not added to any statement list) whose content is the
     * given String.
     */
    public JmlStatementExpr comment(int pos, String s) {
        return M.at(pos).JmlExpressionStatement(StatementExprExtensions.commentID, StatementExprExtensions.commentClause,null,M.Literal(s));
    }
    
    /** This generates a comment statement (not in any statement list) whose content is the
     * given JCTree, pretty-printed.
     */
    public JmlStatementExpr comment(JCTree t) {
        return comment(t.pos,JmlPretty.write(t,false));
    }
    

    
    // FIXME - do we need this - here?
    /** Makes a JML \typeof expression, with the given expression as the argument */
    protected JCExpression makeTypeof(JCExpression e) {
        JCExpression typeof = M.at(e.pos).JmlMethodInvocation(typeofKind,e);
        typeof.type = syms.classType;
        return typeof;
    }
    
    // FIXME - review and document
    /** Makes a Java this parse tree node (attributed) */
    protected JCIdent makeThis(int pos) {
        return treeutils.makeIdent(pos,methodDecl._this);
    }
    
    // FIXME - review and document
    /** Makes the equivalent of an instanceof operation: \typeof(e) <: \type(type) */
    protected JCExpression makeNNInstanceof(JCExpression e, int epos, Type type, int typepos) {
        JCExpression e1 = makeTypeof(e);
        JCExpression e2 = makeTypeLiteral(type,typepos);
        //if (inSpecExpression) e2 = trSpecExpr(e2,null);
        JCExpression ee = treeutils.makeJmlBinary(epos,Operators.subtypeofKind,e1,e2);
        return ee;
    }
    
    // FIXME - review and document
    /** Makes the equivalent of an instanceof operation: e !=null && \typeof(e) <: \type(type) */
    protected JCExpression makeInstanceof(JCExpression e, int epos, Type type, int typepos) {
        JCExpression e1 = treeutils.makeNeqObject(epos,e,treeutils.nullLit);
        JCExpression e2 = treeutils.makeJmlBinary(epos,Operators.subtypeofKind,makeTypeof(e),makeTypeLiteral(type,typepos));
        //if (inSpecExpression) e2 = trSpecExpr(e2,null);
        JCExpression ee = treeutils.makeBinary(epos,JCTree.Tag.AND,e1,e2);
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
        JCIdent methid = M.at(pos).Ident(meth);
        JCExpression e = M.at(pos).Apply(null,methid,new ListBuffer<JCExpression>().appendArray(args).toList());
        e.type = meth.getReturnType();
        return e;
    }
    
    // FIXME - review and document
    protected JCExpression makeSignalsOnly(JmlMethodClauseSignalsOnly clause) {
        JCExpression e = treeutils.makeBooleanLiteral(clause.pos,false);
        JmlSingleton id = M.at(0).JmlSingleton(SingletonExpressions.exceptionKind);
        id.kind = SingletonExpressions.exceptionKind;
        for (JCExpression typetree: clause.list) {
            int pos = typetree.getStartPosition();
            e = treeutils.makeBinary(pos, 
                    JCTree.Tag.OR, makeNNInstanceof(id, pos, typetree.type, pos), e);
        }
        return e;
    }

    // FIXME - review and document
    protected int endPos(JCTree t) {
        if (t instanceof JCBlock) {
            return ((JCBlock)t).endpos;
        } else if (t instanceof JCMethodDecl) {
            return endPos(((JCMethodDecl)t).body);
        } else {
            // FIXME - fix this sometime - we don't know the end position of
            // statements that are not blocks
            if (JmlEsc.escdebug) log.getWriter(WriterKind.NOTICE).println("UNKNOWN END POS");
            return t.pos;
        }
    }


    // STATEMENT NODES
    
    
    // FIXME - REVIEW
    public void visitExec(JCExpressionStatement that)    { 
        // This includes assignments and stand-alone method invocations
        scan(that.expr);
    }
    
 
    
    // FIXME - needs review - al;ready converted to a BoogieBlock assert?
    public void visitAssert(JCAssert that) { // This is a Java assert statement
        currentBlock.statements.add(comment(that));
        scan(that.cond);
        scan(that.detail);
        JCExpression cond = (that.cond);
        JCExpression detail = (that.detail);
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
        } else {
            // FIXME - not implemented
            log.warning("esc.not.implemented","BoogieBlocker.visitApply for " + that.meth.getClass());
            msym = null;
            obj = null;
            result = treeutils.trueLit;
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

        pushTypeArgs();
        if (tfa != null) {
            // tfa is the declaration of a parameterized method
            // that is the actual call, which may not have explicit parameters
            Iterator<Type> tv = tfa.tvars.iterator();
            Iterator<JCExpression> e = that.typeargs.iterator();
            if (e.hasNext()) {
                while (tv.hasNext()) {
                    typeargs.put(tv.next().tsym,e.next().type);
                }
            } else {
                log.getWriter(WriterKind.NOTICE).println("NOT IMPLEMENTED - parameterized method call with implicit type parameters");
            }
        }

        // FIXME - concerned that the position here is not after the
        // positions of all of the arguments
//        if (inSpecExpression) {
//            result = insertSpecMethodCall(that.pos,msym,obj,that.typeargs,newargs.toList());
//        } else {
//            result = insertMethodCall(that,msym,obj,that.getTypeArguments(),newargs.toList()); // typeargs ? FIXME
//        }

        popTypeArgs();
        toLogicalForm.put(that,result);
        return;
    }

    // FIXME - review this
    //boolean extraEnv = false;
    public void visitJmlMethodInvocation(JmlMethodInvocation that) { 
        if (that.kind == oldKind || that.kind == preKind || that.kind == pastKind) {
                if (that.args.size() == 1) {
                    that.args.get(0).accept(this);
                } else {
                    JCIdent label = (JCIdent)that.args.get(1);
                    that.args.get(0).accept(this);
                    that.args = com.sun.tools.javac.util.List.<JCExpression>of(that.args.get(0));
                }
                that.token = null;
                that.kind = sameKind; // A no-op // TODO - Review this
        } else if (that.token == null) {
            super.visitApply(that);  // See testBox - this comes from the implicitConversion - should it be a JCMethodInvocation instead?
            scan(that.typeargs);
            scan(that.meth);
            that.meth = result;
            scanList(that.args);
            result = that;
        } else {
            log.error(that.pos, "esc.internal.error", "Did not expect this kind of Jml node in BoogieBlocker: " + that.token.internedName());
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
//        JCIdent var = treeutils.makeIdent(pos,vsym);
//        declareAllocated(var,pos);
//    }
//    
//    // Generate a (translated) allocation predicate // FIXME - check this out and use it
//    protected void declareAllocated(JCExpression e, int pos) {
//        currentBlock.statements.add(comment(pos, e + " != null || " + e + " .alloc < " + allocSym));
//        JCExpression eee = new JmlBBFieldAccess(allocIdent,e);
//        eee.pos = pos;
//        eee.type = syms.intType;
//        eee = treeutils.makeBinary(pos,JCTree.LE,eee,treeutils.makeIdent(pos,allocSym));
//        eee = treeutils.makeBinary(pos,JCTree.OR,treeutils.makeEqObject(pos,e,nullLiteral),eee);
//        addAssume(pos,Label.SYN,eee,currentBlock.statements);
//    }
//    
//    // Generate a (translated) alloc comparison // FIXME - check this out and use it and docuiment
//    protected JCExpression allocCompare(int pos, JCExpression e) {
//        JCExpression eee = new JmlBBFieldAccess(allocIdent,e);
//        eee.pos = pos;
//        eee.type = syms.intType;
//        eee = treeutils.makeBinary(pos,JCTree.LE,eee,treeutils.makeIdent(pos,allocSym));
//        return eee;
//    }

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
//                    log.error(pos,"jml.internal","Unexpected null store-ref in BoogieBlocker.havocAssignables");
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
//                        JCExpression e = M.at(pos).Conditional(preCondition,newid,oldid);
//                        e.type = newid.type;
//                        e = treeutils.makeBinary(pos,JCTree.EQ,newid,e);
//                        addAssume(pos,Label.HAVOC,e,currentBlock.statements);
//                    } else {
//                        // Same as for JCFieldAccess except that fa.selected is always 'this' (currentThisId)
//                        Type type = id.type;
//                        checkForNull(currentThisId,id.pos,preCondition,null);
//
//                        JCIdent oldid = newIdentUse((VarSymbol)id.sym,id.pos);
//                        JCFieldAccess oldaccess = new JmlBBFieldAccess(oldid,currentThisId);
//                        oldaccess.pos = id.pos;
//                        oldaccess.type = type;
//
//                        JCIdent newid = newIdentIncarnation(oldid,npos);
//                        JCFieldAccess newaccess = new JmlBBFieldAccess(newid,currentThisId);
//                        newaccess.pos = id.pos;
//                        newaccess.type = type;
//
//                        JCExpression right = M.at(id.pos).Conditional(preCondition,newaccess,oldaccess);
//                        right.type = type;
//                        
//                        JCExpression expr = new JmlBBFieldAssignment(newid,oldid,currentThisId,right);
//                        expr.pos = pos;
//                        expr.type = type;
//
//                        addAssume(pos,Label.HAVOC,expr,currentBlock.statements);
//                    }
//                } else if (sr instanceof JCFieldAccess) {
//                    // FIXME - this duplicates logic in visitSelect and doAssignment
//                    // s.f' = precondition ? s.f' : s.f
//                    JCFieldAccess fa = (JCFieldAccess)sr;
//                    JCExpression selected = fa.selected;
//                    boolean isType = true;
//                    if ((selected instanceof JCIdent) && ((JCIdent)selected).sym instanceof ClassSymbol) {
//                        // do nothing
//                    } else if ((selected instanceof JCFieldAccess) && ((JCFieldAccess)selected).sym instanceof ClassSymbol) {
//                        // do nothing
//                    } else {
//                        //selected = trSpecExpr(fa.selected,log.currentSourceFile()); // FIXME
//                        selected = (fa.selected); // FIXME
//                        isType = false;
//                    }
//
//                    try {
//                        //if (!isType) checkForNull(selected,sr.pos,preCondition,null);
//
//                        if (fa.sym == null) {
//                            Symbol ownerSym = fa.selected.type.tsym;
//                            if (ownerSym instanceof ClassSymbol) {
//                                ClassSymbol csym = (ClassSymbol)ownerSym;
//                                Scope.Entry symentry = csym.members().elems;
//                                while (symentry != null) {
//                                    Symbol sym = symentry.sym;
//                                    symentry = symentry.sibling;
//                                    if (sym instanceof VarSymbol) {
//                                        if (utils.isJMLStatic(sym)) {
//                                            JCIdent newid = newIdentIncarnation((VarSymbol)sym,npos);
//                                            JCExpression e = treeutils.makeEquality(npos,newid,newid);
//                                            addAssume(sr.pos,Label.HAVOC,e,currentBlock.statements);
//                                            
//                                        } else if (!isType) {
//                                            havocField((VarSymbol)sym,selected,fa.pos,npos,sym.type,preCondition);
//                                        }
//                                    }
//                                }
//                            } else {
//                                log.noticeWriter.println("FOUND " + ownerSym.getClass());
//                            }
//
//                        } else {
//                            VarSymbol vsym = (VarSymbol)fa.sym;
//                            havocField(vsym,selected,fa.pos,npos,fa.type,preCondition);
//                        }
//                    } finally {
//                        condition = prevCondition;
//                    }
//                    
//                } else if (sr instanceof JmlStoreRefArrayRange) {
//                    JmlStoreRefArrayRange ar = (JmlStoreRefArrayRange)sr;
//                    
//                    ListBuffer<Name> ns = new ListBuffer<Name>();
//                    JCExpression array = extractQuantifiers(ar.expression,ns);
//
//                    condition = treeutils.makeBinary(sr.pos,JCTree.AND,condition,preCondition);
//                    try {
//                        if (ar.hi != ar.lo || ar.lo == null) {
//                            // wildcard at the top level
//                            if (ns.size() > 0) {
//                                // and wildcards within
//                            } else {
//                                // no wildcards within
//                                
//                                JCIdent arrayId = getArrayIdent(sr.type);
//                                
//                                array = trSpecExpr(array,log.currentSourceFile()); // FIXME
//                                checkForNull(array,sr.pos,trueLiteral,null);
//
//                                JCExpression indexlo = trSpecExpr(ar.lo,log.currentSourceFile()); // FIXME
//                                if (indexlo != null) checkArrayAccess(array,indexlo,sr.pos);
//                                else indexlo = zeroLiteral;
//                                
//                                JCExpression indexhi = trSpecExpr(ar.hi,log.currentSourceFile()); // FIXME
//                                boolean above = false;
//                                if (indexhi != null) checkArrayAccess(array,indexhi,sr.pos);
//                                else {
//                                    //indexhi = M.at(sr.pos).Select(array,lengthSym);
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
////                                JCExpression oldaccess = M.at(npos).JmlMethodInvocation(JmlToken.BSOLD,access,label);
////
////                                JCArrayAccess newaccess = M.at(access.pos).Indexed(access.indexed,access.index);
////                                newaccess.type = access.type;
////
////                                //                            JCIdent meth = newAuxIdent("arbitrary$",syms.intType,npos);
////                                //                            ListBuffer<JCExpression> args = new ListBuffer<JCExpression>();
////                                //                            for (Name n: ns) {
////                                //                                JCIdent id = M.at(npos).Ident(n);
////                                //                                id.type = syms.intType;
////                                //                                args.append(id);
////                                //                            }
////                                //                            JCMethodInvocation app = M.at(npos).Apply(null,meth,args.toList());
////                                //                            app.type = ar.type;
////
////                                JCConditional cond = M.at(sr.pos).Conditional(
////                                        treeutils.makeBinary(JCTree.AND,entry.pre,accumRange,npos),newaccess,oldaccess);
////                                cond.type = access.type;
////
////                                JCExpression assign = treeutils.makeBinary(JCTree.EQ,newaccess,cond,npos);
////
////                                JmlQuantifiedExpr quant = M.at(sr.pos).JmlQuantifiedExpr(JmlToken.BSFORALL,null,M.Type(syms.intType),ns,fullRange,assign);
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
//                                JCExpression condValue = M.at(sr.pos).Conditional(preCondition,newvalue,oldvalue);
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
//                    log.error(sr.pos,"jml.internal","Unexpected kind of store-ref in BoogieBlocker.havocAssignables: " + sr.getClass());
//                }
//            }
//        }
    }
    
    // FIXME - review and document
    private JCExpression fullRange;
    private JCExpression accumRange;
    protected JCExpression extractQuantifiers(JCExpression expr, ListBuffer<Name> ns) {
        if (expr instanceof JCIdent) {
            accumRange = treeutils.trueLit;
            fullRange = treeutils.trueLit;
            return expr;
        } else if (expr instanceof JmlStoreRefArrayRange) {
            JmlStoreRefArrayRange a = (JmlStoreRefArrayRange)expr;
            JCExpression e = extractQuantifiers(a.expression,ns);
            JCExpression id;
            if (a.lo == a.hi && a.lo != null) {
                id = a.lo;
            } else {
                Name n = names.fromString("i"+(ns.size()+1));
                id = M.at(expr.pos).Ident(n); // No symbol - FIXME ???
                id.type = syms.intType;
                ns.append(n);
                fullRange = treeutils.makeBinary(a.pos,JCTree.Tag.AND,fullRange,treeutils.makeBinary(a.pos,JCTree.Tag.LE,treeutils.makeZeroEquivalentLit(a.pos,syms.intType),id));
                //JCExpression len = M.at(a.pos).Select(a.expression,lengthSym);
                JCExpression len = new JmlBBFieldAccess(lengthIdent,a.expression);
                len.pos = a.pos;
                len.type = syms.intType;
                fullRange = treeutils.makeBinary(a.pos,JCTree.Tag.AND,fullRange,treeutils.makeBinary(a.pos,JCTree.Tag.LT,id,len));
                if (a.lo != null) accumRange = treeutils.makeBinary(a.lo.pos,JCTree.Tag.AND,accumRange,treeutils.makeBinary(a.lo.pos,JCTree.Tag.LE,a.lo,id));
                if (a.hi != null) accumRange = treeutils.makeBinary(a.hi.pos,JCTree.Tag.AND,accumRange,treeutils.makeBinary(a.hi.pos,JCTree.Tag.LE,id,a.hi));
            }
            e = M.at(expr.pos).Indexed(e,id);
            e.type = expr.type;
            return e;
        } else if (expr instanceof JCFieldAccess) {
            JCFieldAccess a = (JCFieldAccess)expr;
            JCExpression e = extractQuantifiers(a.selected,ns);
            if (e == a.selected) return e;
            e = M.at(expr.pos).Select(e,a.sym);
            e.type = a.type;
            return e;
        } else {
            return expr;
        }
    }
    
    // FIXME - review and document
    protected void havocField(VarSymbol vsym, JCExpression selected, int pos, int npos, Type type, JCExpression preCondition) {
//        JCIdent oldid = treeutils.makeIdent(pos,vsym);
//        JCFieldAccess oldaccess = new JmlBBFieldAccess(oldid,selected);
//        oldaccess.pos = pos;
//        oldaccess.type = type;
//
//        JCIdent newid = newIdentIncarnation(oldid,npos);
//        JCFieldAccess newaccess = new JmlBBFieldAccess(newid,selected);
//        newaccess.pos = pos;
//        newaccess.type = type;
//
//        JCExpression right = M.at(pos).Conditional(preCondition,newaccess,oldaccess);
//        right.type = type;
//        
//        JCExpression expr = new JmlBBFieldAssignment(newid,oldid,selected,right);
//        expr.pos = pos;
//        expr.type = type;
//
//        addAssume(pos,Label.HAVOC,expr,currentBlock.statements);

    }
    
    // FIXME - review and document
    protected void havoc(JCExpression storeref) {
//        if (storeref instanceof JCIdent) {
//            JCIdent id = newIdentIncarnation((JCIdent)storeref,storeref.pos);
//            program.declarations.add(id);
//            //} else if (e instanceof JCFieldAccess) {
//            //} else if (e instanceof JCArrayAccess) {
//
//        } else {
//            // FIXME - havoc in loops
//            log.noticeWriter.println("UNIMPLEMENTED HAVOC  " + storeref.getClass());
//        }

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
//        for (VarSymbol vsym : currentMap.keySet()) {
//            if (vsym.owner == null || vsym.owner.type.tag != TypeTag.CLASS) {
//                continue;
//            }
//            JCIdent oldid = newIdentUse(vsym,newpos);
//            JCIdent newid = newIdentIncarnation(vsym,newpos);
//            JCExpression e = M.at(newpos).Conditional(preCondition,newid,oldid);
//            e.type = vsym.type;
//            e = treeutils.makeEquality(newpos,newid,e);
//            addAssume(newpos,Label.HAVOC,e,currentBlock.statements);
//        }
//        currentMap.everythingIncarnation = newpos; // FIXME - this now applies to every not-yet-referenced variable, independent of the preCondition
    }

    /** This method is not called for top-level classes, since the BoogieBlocker is invoked
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
        if (that.clauseType == StatementExprExtensions.commentClause) {
            currentBlock.statements.add(that);
        } else if (that.clauseType == StatementExprExtensions.assertClause || that.clauseType == StatementExprExtensions.assumeClause || that.clauseType == StatementExprExtensions.checkClause) {
            scan(that.expression);
            currentBlock.statements.add(that);
        } else {
            log.error(that.pos,"esc.internal.error","Unknown token in BoogieBlocker2.visitJmlStatementExpr: " + that.keyword);
        }
    }
    
    // OK
    @Override
    public void visitJmlStatementHavoc(JmlStatementHavoc that) {
        // TODO - seems a shame to recopy the whole list on the chance that there is a \nothing to remove
        Iterator<JCExpression> iter = that.storerefs.iterator();
        ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
        while (iter.hasNext()) {
            JCExpression x = iter.next();
            if (x instanceof JmlStoreRefKeyword && ((JmlStoreRefKeyword)x).kind == nothingKind)
                {}
            else newlist.add(x);
        }
        that.storerefs = newlist.toList();
        if (!that.storerefs.isEmpty()) currentBlock.statements.add(that); // FIXME - are the targets all OK for Boogie?
    }
    

    // We introduce the name 'assumeCheck$<int>$<label>' in order to make
    // it easy to identify the places where assumptions are being checked.
    /** Adds (translated) assertions/assumptions that do assumption feasibility checking 
     * for an assumption that is just added to the currentBlock
     * @param pos a positive integer different than that used for any other checkAssumption call;
     *    it should also be the textual location of the assumption being tested
     * @param label a Label giving the kind of assumption being tested (in order to
     *    better interpret the implications of the assumptino not being feasible)
     */
    
    // FIXME - REVIEW and document
    protected void checkAssumption(int pos, /*@ non_null*/ Label label, List<JCStatement> statements) {
//        if (!insertAssumptionChecks) return;
//        JCExpression e;
//        JCIdent id;
//        String n = ASSUME_CHECK_PREFIX + pos + "" + label.toString();
//        if (useCountedAssumeCheck) {
//            JCExpression count = treeutils.makeIntLiteral(pos,pos);
//            e = treeutils.makeBinary(pos,JCTree.NE,assumeCheckCountVar,count);
//            id = treeutils.makeIdent(pos,n,syms.booleanType);
//            //e = treeutils.makeBinary(pos,JCTree.EQ,id,e);
//            // assume assumeCheck$<int>$<label> == <assumeCheckCountVar> != <int>
//            // To do the coreId method, we need to put this in the definitions list
//            // instead.  And it does not hurt anyway.
//            //addAssume(pos,Label.ASSUME_CHECK,e); // adds to the currentBlock
//        } else {
//            id = treeutils.makeIdent(pos,n,syms.booleanType);
//            e = id;
//            if (assumeCheck == null) assumeCheck = e;
//            else assumeCheck = treeutils.makeBinary(pos,JCTree.AND,e,assumeCheck);
//        }
//        // an assert without tracking
//        // assert assumeCheck$<int>$<label>
//        addAssertNoTrack(Label.ASSUME_CHECK,id,statements,pos,null); // FIXME - need the position of the assume, I think
    }

    // FIXME - REVIEW and document
    protected void checkAssumption(int pos, /*@ non_null*/ Label label) {
        checkAssumption(pos,label,currentBlock.statements);
    }

    //OK
    public void visitJmlStatementDecls(JmlStatementDecls that) {
        shouldNotBeCalled(that);
    }
    
    // Visit methods for Expressions for the most part just use the super class's
    // visit methods. These just call visitors on each subexpression.
    // Everything is transformed in place.
    // There are a few nodes that get special treatment:
    //  JCIdent - the name is overwritten with the single-assignment name (note that
    //     the name will be out of synch with the symbol)
    //  \old and \pre expressions - these need to find the correct scope and translate
    //     JCIdent nodes within their scopes using the correct single-assignment names
        
    
    public Map<JCTree,JCTree> toLogicalForm = new HashMap<JCTree,JCTree>();
    public Map<JCTree,String> toValue = new HashMap<JCTree,String>();
    
    // OK
    @Override
    public void visitIdent(JCIdent that) {
        if (that.sym instanceof Symbol.VarSymbol){ 
            Symbol.VarSymbol vsym = (Symbol.VarSymbol)that.sym;
            that.name = getCurrentName(vsym);
//            if (isDefined.add(that.name)) {
//                System.out.println("Added " + that.sym + " " + that.name);
//                program.declarations.add(that);
//            }
        } else if (that.sym == null) {
            // Temporary variables that are introduced by decomposing expressions do not have associated symbols
            // They are also only initialized once and only used locally, so we do not track them for DSA purposes
            // Just skip
        } else if (that.sym instanceof Symbol.ClassSymbol) {
            // Just skip
        } else if (that.sym instanceof Symbol.PackageSymbol) {
            // Just skip
        } else {
            log.error(that.pos,"jml.internal","THIS KIND OF IDENT IS NOT HANDLED: " + that + " " + that.sym.getClass());
        }
        result = that;
    }

    public void visitLiteral(JCLiteral tree) {
        result = tree;
    }


    @Override
    public void visitSelect(JCFieldAccess that) {
        if (!(that.sym instanceof Symbol.VarSymbol)) return; // This is a qualified type name 
        if (that.sym.isStatic()) {
            that.name = getCurrentName((Symbol.VarSymbol)that.sym);
            JCIdent id = treeutils.makeIdent(that.pos,that.sym);
            id.name = that.name;
            if (isDefined.add(that.sym)) {
//                System.out.println("AddedF " + that.sym + " " + that.name);
                program.declarations.add(id);
            }
            result = id;
            
        } else {
            that.name = getCurrentName((Symbol.VarSymbol)that.sym);
            scan(that.selected);
            if (isDefined.add(that.sym)) {
//                System.out.println("AddedF " + that.sym + " " + that.name);
                JCIdent id = treeutils.makeIdent(that.pos,that.sym);
                id.name = that.name;
                program.declarations.add(id);
            }
            result = that;
        }
    }
    
    public void visitIndexed(JCArrayAccess that) {
        scan(that.indexed);
        scan(that.index);
        result = that;
        
//        JCIdent arr = getArrayIdent(that.type);
//        
//        if (that instanceof JmlBBArrayAccess) {
//            that.indexed = indexed;
//            that.index = index;
//            ((JmlBBArrayAccess)that).arraysId = arr;
//            result = that;
//        } else {
//            log.warning(that,"jml.internal","Did not expect a JCArrayAccess node in BoogieBlocker2.visitIndexed");
//            result = new JmlBBArrayAccess(arr,indexed,index); // FIXME -= M
//        }
    }


    
    
    // FIXME - review
    public void visitAssign(JCAssign that) {
        scan(that.lhs);
        JCExpression left = result;
        scan(that.rhs);
        JCExpression right = result;
        result = doAssignment(that.type,left,right,that.pos,that);
    }
//    
    // FIXME - embedded assignments to array elements are not implemented; no warning either
    // FIXME - is all implicit casting handled
    // Note that the left and right expressions are translated.
    protected JCExpression doAssignment(Type restype, JCExpression left, JCExpression right, int pos, JCExpression assignExpr) {
//        scan(left);
//        scan(right);
        currentBlock.statements.add(treeutils.makeAssignStat(pos,left,right));
        return assignExpr;
//        if (left instanceof JCIdent) {
////            JCIdent id = (JCIdent)left;
////            JCIdent newid = id;
////            currentBlock.statements.add(treeutils.makeVarDef(newid.type, newid.name, id.sym.owner, pos));
////            JCBinary expr = treeutils.makeEquality(pos,newid,right);
////            copyEndPosition(expr,right);
////            addAssume(TreeInfo.getStartPos(statement),Label.ASSIGNMENT,expr);
//            currentBlock.statements.add(treeutils.makeAssignStat(pos,left,right));
//            return assignExpr;
//        } else if (left instanceof JCArrayAccess) {
////            JCIdent arr = getArrayIdent(right.type);
////            JCExpression ex = ((JCArrayAccess)left).indexed;
////            JCExpression index = ((JCArrayAccess)left).index;
////            JCIdent nid = newArrayIncarnation(right.type,left.pos);
////            
////            //JCExpression rhs = makeStore(ex,index,right);
////            JCExpression expr = new JmlBBArrayAssignment(nid,arr,ex,((JCArrayAccess)left).index,right);
////            expr.pos = pos;
////            expr.type = restype;
////
////            // FIXME - set line and source
//////            JCBinary bin = treeutils.makeEquality(Position.NOPOS,nid,expr);
//////            copyEndPosition(bin,expr);
////            addAssume(TreeInfo.getStartPos(left),Label.ASSIGNMENT,expr,currentBlock.statements);
////            //newIdentIncarnation(heapVar,pos);
//            return right;
//        } else if (left instanceof JCFieldAccess) {
//            VarSymbol sym = (VarSymbol)selectorSym(left);
//            if (sym.isStatic()) {
//                JCIdent id = treeutils.makeIdent(left.pos,sym);
//                JCIdent newid = id;
//                currentBlock.statements.add(treeutils.makeVarDef(newid.type, newid.name, id.sym.owner, pos));
//                JCBinary expr = treeutils.makeEquality(pos,newid,right);
//                copyEndPosition(expr,right);
//                addAssume(TreeInfo.getStartPos(assignExpr),Label.ASSIGNMENT,expr);
//                return newid;
//            } else {
//                JCFieldAccess fa = (JCFieldAccess)left;
//                JCIdent oldfield = treeutils.makeIdent(pos,(VarSymbol)fa.sym);
//                if (isDefined.add(fa.sym)) {
////                    System.out.println("AddedFF " + oldfield.sym + " " + oldfield.name);
//                    program.declarations.add(oldfield);
//                }
//                JCIdent newfield = oldfield;
////                if (isDefined.add(newfield.name)) {
////                    System.out.println("AddedFF " + newfield.sym + " " + newfield.name);
////                    program.declarations.add(newfield);
////                }
//                JCExpression expr = new JmlBBFieldAssignment(newfield,oldfield,fa.selected,right);
//                expr.pos = pos;
//                expr.type = restype;
//
//                // FIXME - set line and source
////                addAssume(TreeInfo.getStartPos(left),Label.ASSIGNMENT,expr,currentBlock.statements);
////                newIdentIncarnation(heapVar,pos);
//            }
//            return left;
//        } else {
//            log.error("jml.internal","Unexpected case in BoogieBlocker.doAssignment: " + left.getClass() + " " + left);
//            return null;
//        }
    }
    
    protected Symbol selectorSym(JCTree tree) {
        if (tree instanceof JCIdent) return ((JCIdent)tree).sym;
        if (tree instanceof JCFieldAccess) return ((JCFieldAccess)tree).sym;
        log.error("jml.internal","Unexpected case in selectorSym: " + tree.getClass() + " " + tree);
        return null;
    }

    // FIXME - this is all wrong -= except FIXME - review newIdentIncarnation
    public void visitVarDef(JCVariableDecl that) { 
        currentBlock.statements.add(comment(that));
        JCIdent lhs = treeutils.makeIdent(that.getPreferredPosition(),that.sym);
        program.declarations.add(lhs);
        if (that.init != null) {
            // Create and store the new lhs incarnation before translating the
            // initializer because the initializer is in the scope of the newly
            // declared variable.  Actually if there is such a situation, it 
            // will likely generate an error about use of an uninitialized variable.
            scan(that.init);
            JCExpression expr = treeutils.makeBinary(that.pos,JCBinary.Tag.EQ,lhs,that.init);
            // FIXME - INITIALIZATION instead of ASSIGNMENT?
            addAssume(that.getStartPosition(),Label.ASSIGNMENT,expr,currentBlock.statements);
        }
    }
    
    // OK
    public void visitSynchronized(JCSynchronized that)   { 
        super.visitSynchronized(that);
    }
    
    // FIXME - review and document
    List<Map<Symbol,Type>> typeargsStack = new LinkedList<Map<Symbol,Type>>();
    // FIXME - review and document
    Map<Symbol,Type> typeargs = new HashMap<Symbol,Type>();
    // FIXME - review and document
    public void pushTypeArgs() {
        typeargsStack.add(0,typeargs);
        typeargs = new HashMap<Symbol,Type>();
    }
    // FIXME - review and document
    public void popTypeArgs() {
        typeargs = typeargsStack.remove(0);
    }
    // FIXME - review and document
    public void pushTypeArgs(Type type) {
        if (type.getTypeArguments() != null && type.getTypeArguments().size() != 0) {
            pushTypeArgs();
            Iterator<Type> args = type.getTypeArguments().iterator();
            Iterator<TypeVariableSymbol> params = type.tsym.getTypeParameters().iterator();
            while (params.hasNext()) {
                typeargs.put(params.next(),args.next());
            }
        }
    }
    // FIXME - review and document
    public void popTypeArgs(Type type) {
        if (type.getTypeArguments() != null && type.getTypeArguments().size() != 0) {
            popTypeArgs();
        }
    }
    
//    // FIXME - review and document
//    public Type trType(Type type) {
//        if (type instanceof Type.TypeVar) {
//            Type t = typeargs.get(type.tsym);
//            type = t != null ? t : ((Type.TypeVar)type).getUpperBound(); // FIXME - what about the other bounds?
//        }
//        return type;
//    }
//    
    public void visitTypeIdent(JCPrimitiveTypeTree that) { notImpl(that); }
    public void visitTypeArray(JCArrayTypeTree that)     { notImpl(that); }
    public void visitTypeApply(JCTypeApply that)         { notImpl(that); }
    public void visitTypeParameter(JCTypeParameter that) { notImpl(that); }
    public void visitWildcard(JCWildcard that)           { notImpl(that); }
    public void visitTypeBoundKind(TypeBoundKind that)   { notImpl(that); }
    public void visitAnnotation(JCAnnotation that)       { notImpl(that); }
    public void visitModifiers(JCModifiers that)         { notImpl(that); }
    public void visitErroneous(JCErroneous that)         { notImpl(that); }
    public void visitLetExpr(LetExpr that)               { notImpl(that); }
    
    // Adds specs to a Java Variable Declaration
    // FIXME - delegate to visitVarDef?
    // FIXME - use a constructed name?
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        if (that.sym == null || that.sym.owner == null) {
            if (that.init != null) {
                scan(that.init);
                that.init = result;
            }
            if (that.init instanceof JCMethodInvocation) {
                that.init = null;
                currentBlock.statements.add(that);
            } else {
                JCIdent lhs = treeutils.makeIdent(that.getPreferredPosition(),that.sym);
                program.declarations.add(lhs);
                if (that.init != null) {
                    JCStatement stat = treeutils.makeAssignStat(that.pos, lhs, that.init);
                    currentBlock.statements.add(stat);
                }
            }
        } else if (that.init == null) {
            JCIdent lhs = treeutils.makeIdent(that.getPreferredPosition(),that.sym);
            scan(lhs);
            program.declarations.add(lhs);
        } else {
            JCIdent lhs = treeutils.makeIdent(that.getPreferredPosition(),that.sym);
            scan(lhs);
            program.declarations.add(lhs);

            scan(that.init);
            that.init = result;
            JCStatement stat = treeutils.makeAssignStat(that.pos, lhs, that.init);
            currentBlock.statements.add(stat);
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
    

    // FIXME - how are these checked for definedness?
    @Override public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        notImpl(that);
//        JmlToken op = that.op;
//        if (op == JmlToken.BSFORALL || op == JmlToken.BSEXISTS) {
//            JCExpression prevCondition = condition;
//            try {
//                ListBuffer<JCVariableDecl> decls = ListBuffer.<JCVariableDecl>lb();
//                for (JCVariableDecl d: that.decls) {
//                    JCIdent id = newIdentUse(d.sym,0);
//                    JCVariableDecl dd = M.at(d.pos).VarDef(d.mods,id.name,d.vartype,null);
//                    dd.type = d.type;
//                    decls.append(dd);
//                }
//                JCExpression range = trExpr(that.range);
//                condition = range == null ? condition : treeutils.makeBinary(condition.pos,JCTree.AND,condition,range);
//                JCExpression predicate = trExpr(that.value);
//                JmlQuantifiedExpr now = M.at(that.pos).JmlQuantifiedExpr(op,decls,range,predicate);
//                now.type = that.type;
//                result = now;
//            } finally {
//                condition = prevCondition;
//            }
//        } else {
//            result = trueLiteral;
//            notImpl(that);
//        }
//        toLogicalForm.put(that,result);
    }

    // FIXME _ implement
    @Override public void visitJmlSetComprehension(JmlSetComprehension that) { notImpl(that); }
    
    
    @Override public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
//        switch (that.token) {
//            case BSNOTMODIFIED:
//                // Allows multiple arguments; they may be store-refs with wildcards (FIXME)
//                JCExpression combined = null;
//                for (JCExpression a : that.list){
//                    // FIXME - there is an issue with condition - how do we evaluate if old(e) is well-defined?
//                    //  defined as  arg == \old(arg)
//                    int pos = that.pos;
//                    JCExpression e = trExpr(a);
//                    VarMap prevMap = currentMap;
//                    currentMap = oldMap;
//                    try {
//                        // FIXME - what happens if not_modifieds are nested, or within an old
//                        //extraEnv = true;
//                        JCExpression ee = trExpr(a);
//                        ee = treeutils.makeEquality(pos,e,ee);
//                        if (combined == null) combined = ee;
//                        else combined = treeutils.makeBinary(pos,JCTree.AND,combined,ee);
//                    } finally {
//                        currentMap = prevMap;
//                        //extraEnv = false;
//                    }
//                }
//                result = combined;
//                break;
//
//            default: notImpl(that);
//        }
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
    @Override public void visitJmlStatement(JmlStatement that) { shouldNotBeCalled(that); }

    // These do not need to be implemented
    @Override public void visitTopLevel(JCCompilationUnit that)    { shouldNotBeCalled(that); }
    @Override public void visitImport(JCImport that)               { shouldNotBeCalled(that); }
    @Override public void visitJmlCompilationUnit(JmlCompilationUnit that)   { shouldNotBeCalled(that); }
    @Override public void visitJmlImport(JmlImport that)                     { shouldNotBeCalled(that); }
    @Override public void visitMethodDef(JCMethodDecl that)        { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodDecl(JmlMethodDecl that)  { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementSpec(JmlStatementSpec that) { shouldNotBeCalled(that); }

    // Expressions just need to set the result field
    @Override public void visitBinary(JCBinary that) {
        scan(that.lhs);
        that.lhs = result;
        scan(that.rhs);
        that.rhs = result;
        result = that; 
    }
    
    @Override public void visitUnary(JCUnary that) { 
        scan(that.arg);
        that.arg = result;
        result = that; 
    }
    
    @Override public void visitParens(JCParens that) { 
        scan(that.expr);
        that.expr = result;
        result = that; 
    }
    
    @Override public void visitConditional(JCConditional that) { 
        scan(that.cond);
        that.cond = result;
        scan(that.truepart);
        that.truepart = result;
        scan(that.falsepart);
        that.falsepart = result;
        result = that; 
    }
    
    @Override public void visitTypeTest(JCInstanceOf that) { 
        result = treeutils.trueLit; // FIXME - fix
    }


// Do not need to override these methods
//  @Override public void visitSkip(JCSkip that) { super.visitSkip(that); }
        
    public void visitJmlStatementLoopExpr(JmlStatementLoopExpr that) { 
        shouldNotBeCalled(that); // These are the specs for loops - they are handled in the loop visitors
    }
    
    public void visitJmlStatementLoopModifies(JmlStatementLoopModifies that) { 
        shouldNotBeCalled(that); // These are the specs for loops - they are handled in the loop visitors
    }
    
    // FIXME - what about Indexed, TypeCast, TypeTest, AssignOp, NewClass, NewArray

    /** This class is a tree walker that finds any references to classes in the
     * tree being walked: types of anything, explicit type literals
     * 
     * @author David Cok
     *
     */
    public static class ClassFinder extends JmlTreeScanner {
        
        private Set<Type> types;
        
        public ClassFinder() {}
        
        public static Set<Type> findS(List<? extends JCTree> that, Set<Type> v) {
            ClassFinder vf = new ClassFinder();
            return vf.find(that,v);
        }
        
        public static Set<Type> findS(JCTree that, Set<Type> v) {
            ClassFinder vf = new ClassFinder();
            return vf.find(that,v);
        }
        
        public Set<Type> find(List<? extends JCTree> that, Set<Type> v) {
            if (v == null) types = new HashSet<Type>();
            else types = v;
            for (JCTree t: that) t.accept(this);
            return types;
        }
        
        public Set<Type> find(JCTree that, Set<Type> v) {
            if (v == null) types = new HashSet<Type>();
            else types = v;
            that.accept(this);
            return types;
        }
        
        // visitAnnotation  - FIXME

        // visitApply - expression: just scan the component expressions
        // visitAssert - statement: just scan the component expressions
        // visitAssign - no new types - just scan the component expressions
        // visitAssignOp - no new types - just scan the component expressions
        // visitBinary - only primitive types
        // visitBlock - statement: just scan the component expressions
        // visitBreak - statement: just scan the component expressions
        // visitCase - statement: just scan the component expressions
        // visitCatch - statement: just scan the component expressions - FIXME - make sure to get the declaration
        // visitClassDef - FIXME ???
        // visitConditional - no new types - just scan the component expressions
        // visitContinue - statement: just scan the component expressions
        // visitDoLoop - statement: just scan the component expressions
        // visitErroneous - statement: just scan the component expressions
        // visitExec - statement: just scan the component expressions
        // visitForEachLoop - statement: just scan the component expressions - FIXME - implied iterator?
        // visitForLoop - statement: just scan the component expressions

        public void visitIdent(JCIdent that) {
            if (!that.type.isPrimitive()) types.add(that.type);
            super.visitIdent(that);
        }
        
        // visitIf - statement: just scan the component expressions
        // visitImport - statement: just scan the component expressions
        // visitIndexed - FIXME
        // visitLabelled - statement: just scan the component expressions
        // visitLetExpr - FIXME
        // visitLiteral - FIXME
        // visitMethodDef - FIXME
        // visitModifiers - no new types
        // visitNewArray - FIXME

        public void visitNewClass(JCNewClass that) {
            types.add(that.type);
        }
        
        // visitParens - no new types - just scan the component expressions
        // visitReturn - statement: just scan the component expressions
        // visitSelect - FIXME
        // visitSkip - statement: just scan the component expressions
        // visitSwitch - statement: just scan the component expressions (FIXME _ might be an Enum)
        // visitSynchronized - statement: just scan the component expressions
        // visitThrow - statement: just scan the component expressions
        // visitTopLevel - statement: just scan the component expressions
        // visitTree
        // visitTry - statement: just scan the component expressions
        // visitTypeApply - FIXME ??
        // visitTypeArray - FIXME ??
        // visitTypeBoundKind - FIXME ??
        // visitTypeCast - FIXME ??

        public void visitTypeIdent(JCPrimitiveTypeTree that) {
            types.add(that.type);
            super.visitTypeIdent(that);
        }
        
        // visitTypeParameter - FIXME ??
        // visitTypeTest (instanceof) - scans the expression and the type
        // visitUnary - only primitive types
        // visitVarDef - FIXME ??
        // visitWhileLoop - statement: just scan the component expressions
        // visitWildcard - FIXME ??
        
        // visitJmlBBArrayAccess - FIXME ?
        // visitJmlBBArrayAssignment - FIXME ?
        // visitJmlBBFieldAccess - FIXME ?
        // visitJmlBBFieldAssignment - FIXME ?
        // visitJmlBinary - no new types - FIXME - subtype?
        // visitJmlClassDecl - FIXME - do specs also
        // visitJmlCompilationUnit - just scan internal components
        // visitJmlConstraintMethodSig - FIXME ?
        // visitJmlDoWhileLoop - FIXME - scan specs
        // visitJmlEnhancedForLoop - FIXME - scan specs
        // visitJmlForLoop - FIXME - scan specs
        // visitJmlGroupName - FIXME??
        // visitJmlImport - no types
        // visitLblExpression - no new types - scan component expressions
        // visitJmlMethodClause... - scan all component expressions - FIXME : watch Decls, Signals, SigOnly
        // visitJmlMethodDecl - FIXME?? - do specs also
        // visitJmlMethodSpecs - FIXME??
        // visitJmlPrimitiveTypeTree - FIXME??
        // visitJmlQuantifiedExpr - FIXME??
        // visitJmlRefines - FIXME??
        // visitJmlSetComprehension - FIXME??
        // visitJmlSingleton - FIXME??
        // visitJmlSpecificationCase - FIXME?? - FIXME??
        // visitJmlStatement - FIXME??
        // visitJmlStatementDecls - FIXME??
        // visitJmlStatementExpr - FIXME??
        // visitJmlStatementLoop - FIXME??
        // visitJmlStatementSpec - FIXME??
        // visitJmlStoreRefArrayRange - FIXME??
        // visitJmlStoreRefKeyword - FIXME??
        // visitJmlStoreRefListExpression - FIXME??
        // visitJmlTypeClause... - scan all components - FIXME - is there more to do?
        // visitJmlVariableDecl - FIXME??
        // visitJmlWhileLoop - FIXME - be sure to scan specs
        
        // FIXME - some things that can probably always be counted on: Object, String, Class
        // FIXME - closure of super types and super interfaces 
    } 
    

    /** This class is a tree walker that finds everything that is the target of
     * a modification in the tree being walked: assignments, assignment-ops, 
     * increment and decrement operators, fields specified as modified by a
     * method call.
     */
    // FIXME - is the tree already in reduced BoogieBlock form?
    public static class TargetFinder extends JmlTreeScanner {
        
        private ListBuffer<JCExpression> vars;
        
        public TargetFinder() {}
        
        /** Finds variables in the given JCTree, adding them to the list that is the 
         * second argument; the second argument is returned.
         */
        public static /*@Nullable*/ListBuffer<JCExpression> findVars(JCTree that, /*@Nullable*/ListBuffer<JCExpression> v) {
            if (that == null) return v;
            TargetFinder vf = new TargetFinder();
            return vf.find(that,v);
        }
        
        /** Finds variables in the given JCTrees, adding them to the list that is the 
         * second argument; the second argument is returned.
         */
        public static ListBuffer<JCExpression> findVars(Iterable<? extends JCTree> list, /*@Nullable*/ListBuffer<JCExpression> v) {
            TargetFinder vf = new TargetFinder();
            return vf.find(list,v);
        }
        
        /** Finds variables in the given JCTrees, adding them to the list that is the 
         * second argument; the second argument is returned.
         */
        public ListBuffer<JCExpression> find(Iterable<? extends JCTree> list, /*@Nullable*/ListBuffer<JCExpression> v) {
            if (v == null) vars = new ListBuffer<JCExpression>();
            else vars = v;
            for (JCTree t: list) t.accept(this);
            return vars;
        }
        
        /** Finds variables in the given JCTrees, adding them to the list that is the 
         * second argument; the second argument is returned.
         */
        public ListBuffer<JCExpression> find(JCTree that, ListBuffer<JCExpression> v) {
            if (that == null) return v;
            if (v == null) vars = new ListBuffer<JCExpression>();
            else vars = v;
            that.accept(this);
            return vars;
        }
        
        public void visitAssign(JCAssign that) {
            vars.add(that.lhs);
        }
        
        public void visitAssignOp(JCAssign that) {
            vars.add(that.lhs);
        }
        
        public void visitUnary(JCUnary that) {
            JCTree.Tag op = that.getTag();
            if (op == JCTree.Tag.POSTDEC || op == JCTree.Tag.POSTINC ||
                    op == JCTree.Tag.PREINC || op == JCTree.Tag.PREDEC)
                vars.add(that.getExpression());
        }
        
        // FIXME - also need targets of method calls, update statements of loops,
        // initialization statements of loops, specs of method calls

    } 

    /** A Map that caches class info for a given class symbol */
    @NonNull protected Map<Symbol,JmlClassInfo> classInfoMap = new HashMap<Symbol,JmlClassInfo>();

    /** Returns the jmlClassInfo structure for a class, computing and caching 
     * it if necessary.
     * @param cls the declaration whose info is desired
     * @return the corresponding JmlClassInfo structure; may be null if the
     *   argument has no associated symbol
     */
    //@ modifies (* contents of the classInfoMap *);
    //@ ensures cls.sym != null <==> \result != null;
    @Nullable JmlClassInfo getClassInfo(@NonNull JCClassDecl cls) {
        JmlClassInfo mi = classInfoMap.get(cls.sym);
        if (mi == null) {
            mi = computeClassInfo(cls.sym);
            classInfoMap.put(cls.sym,mi);
        }
        return mi;
    }
    
    /** Returns the JmlClassInfo structure for the given Class Symbol,
     * computing and caching it if necessary
     * @param sym the Symbol for the class whose JmlClassInfo is wanted
     * @return the corresponding JmlClassInfo structure, null if sym is null
     */
    @Nullable JmlClassInfo getClassInfo(@NonNull Symbol sym) {
        if (sym == null) return null;
        ClassSymbol csym = (ClassSymbol)sym;
        JmlClassInfo mi = classInfoMap.get(sym);
        if (mi == null) {
            mi = computeClassInfo(csym);
            classInfoMap.put(sym,mi);
        }
        return mi;
    }
    
    // FIXME - what about nested classes ($-separated ?)
    /** Returns the JmlClassInfo structure for the given dot-separated,
     * fully-qualified class name,
     * computing and caching it if necessary
     * @param qualifiedName the fully-qualified name of the class
     * @return the corresponding JmlClassInfo structure, null if sym is null
     */
    @Nullable JmlClassInfo getClassInfo(@NonNull String qualifiedName) {
        Name n = Names.instance(context).fromString(qualifiedName);
        Symbol sym = Symtab.instance(context).classes.get(n);
        return getClassInfo(sym);
    }
    
    // TODO - review this
    /** Computes the class information for a given class declaration.
     * @param csym the ClassSymbol for which to get JmlClassInfo
     * @return the corresponding JmlClassInfo
     */
    protected @Nullable JmlClassInfo computeClassInfo(@NonNull ClassSymbol csym) {
        TypeSpecs typeSpecs = specs.get(csym);
        if (typeSpecs == null) {  
            if (csym == syms.arrayClass) {
                // This one is special
                JmlClassInfo classInfo = new JmlClassInfo(null);
                classInfo.typeSpecs = new TypeSpecs(csym);  // FIXME - save this inJmlSpecs?
                classInfo.csym = csym;
                
                Type type = syms.objectType;
                classInfo.superclassInfo = getClassInfo(type.tsym);

                return classInfo;
            }
            // This should not happen - every class referenced is loaded, 
            // even binary files.  If there is no source and no specs, then
            // the typespecs will have essentially null
            // innards, but the object should be there.
            // If this point is reached, some class somehow escaped being loaded.
            log.error("jml.internal","No typespecs for class " + csym);
            return null;
        }
        JCClassDecl tree = typeSpecs.decl;
            // 'tree' may be null if there is a binary class with no specs.
            // So we have to be sure there are default specs, which for
            // a class is essentially empty.

        JmlClassInfo classInfo = new JmlClassInfo(tree);
        classInfo.typeSpecs = typeSpecs;
        classInfo.csym = csym;
        
        Type type = csym.getSuperclass();
        classInfo.superclassInfo = (csym == syms.objectType.tsym || csym.isInterface() ) ? null : getClassInfo(type.tsym);

        // Divide up the various type specification clauses into the various types
        ListBuffer<JmlTypeClauseRepresents> represents = new ListBuffer<JmlTypeClauseRepresents>();
        ListBuffer<JCVariableDecl> modelFields = new ListBuffer<JCVariableDecl>();

        for (JmlTypeClause c: typeSpecs.clauses) {  // FIXME - decls?
            boolean isStatic = c.modifiers != null && (c.modifiers.flags & Flags.STATIC) != 0;
            if (c instanceof JmlTypeClauseDecl) {
                JCTree tt = ((JmlTypeClauseDecl)c).decl;
                if (tt instanceof JCVariableDecl && ((JmlAttr)Attr.instance(context)).isModel(((JCVariableDecl)tt).mods)) {
                    // model field - find represents or make into abstract method
                    modelFields.append((JCVariableDecl)tt);
                } else {
                    // ghost fields, model methods, model classes are used as is
                    //newlist.append(tt);
                }
            } else {
                IJmlClauseKind token = c.clauseType;
                if (token == invariantClause) {
                    JmlTypeClauseExpr copy = (JmlTypeClauseExpr)c.clone();
                    //copy.expression = treetrans.translate(copy.expression);
                    if (isStatic) classInfo.staticinvariants.add(copy);
                    else          classInfo.invariants.add(copy);
                } else if (token == representsClause) {
                    JmlTypeClauseRepresents r = (JmlTypeClauseRepresents)c;
                    represents.append(r);
                } else if (token == constraintClause) {
                    if (isStatic) classInfo.staticconstraints.add((JmlTypeClauseConstraint)c);
                    else          classInfo.constraints.add((JmlTypeClauseConstraint)c);
                } else if (token == initiallyClause) {
                    classInfo.initiallys.add((JmlTypeClauseExpr)c);
                } else if (token == axiomClause) {
                    JmlTypeClauseExpr copy = (JmlTypeClauseExpr)c.clone();
                    //copy.expression = treetrans.translate(copy.expression);
                    classInfo.axioms.add(copy);
                } else {
                    log.warning("esc.not.implemented","JmlEsc does not yet implement (and ignores) " + token.name());
                    // FIXME - readable if, writable if, monitors for, in, maps, initializer, static_initializer, (model/ghost declaration?)
                }
            }
        }
        return classInfo;
    }
    
    // OK
    @Override
    public void visitLabelled(JCLabeledStatement that) {
        super.visitLabelled(that);
    }


//    // FIXME - Review
//    /** This class converts a counterexample into more readable information */
//    public static class Tracer extends JmlTreeScanner {
//        
//        /** The compilation context */
//        @NonNull Context context;
//        
//        /** The counterexample information */
//        @NonNull ICounterexample ce;
//        
//        /** The log for output */
//        @NonNull Log log;
//        
//        @NonNull Writer w;
//        
//        /** A runtime exception used to jump up to a finally block in the visitor calling stack */
//        private static class ReturnException extends RuntimeException {
//            private static final long serialVersionUID = -3475328526478936978L;}
//        
//        /** A runtime exception used to jump up to a finally block in the visitor calling stack */
//        private static class ExException extends RuntimeException {
//            private static final long serialVersionUID = -5610207201211221750L;}
//        
//        /** Outputs the counterexample information in more readable form
//         * @param context the compilation context
//         * @param decl the method declaration 
//         * @param s the counterexample information to translate
//         */
//        public String trace(@NonNull Context context, @NonNull JCMethodDecl decl, @NonNull ICounterexample s) {
//            Tracer t = new Tracer(context,s);
//            try {
//                try {
//                    decl.accept(t);
//                } catch (ReturnException e) {
//                    // ignore
//                } catch (ExException e) {
//                    // ignore
//                } catch (RuntimeException e) {
//                    t.w.append("FAILED : " + e + "\n");
//                }
//                t.w.append("END\n");
//                return t.w.toString();
//            } catch (IOException e) {
//                log.noticeWriter.println("IOException");
//                return "";
//            }
//        }
//
//        /** Translates the given position information into source, line and column information 
//         * @param pos the position information to translate
//         * @return A String containing human-readable source location information
//         */
//        public String getPosition(int pos) { // TODO - check about the second argument of getColumnNumber
//            return log.currentSourceFile().getName() + ":" + log.currentSource().getLineNumber(pos) + " (col " + log.currentSource().getColumnNumber(pos,false) + "): ";
//        }
//        
//        /** The constructor for this class
//         * @param context the compilation context
//         * @param s the counterexample information
//         */
//        protected Tracer(@NonNull Context context, @NonNull ICounterexample s) {
//            this.context = context;
//            ce = s;
//            log = Log.instance(context);
//            w = new StringWriter();
//        }
//        
//        // CAUTION: The Strings in use in these visit methods correspond to the
//        // encoding used in the BoogieBlocker methods.  The BoogieBlocker encodes
//        // variables using combinations of variable name, declaration position,
//        // and incarnation position.  These are reflected in the counterexample 
//        // information and we need to match that as we interpret the counterexample
//        // information in these methods.
//        
//        // FIXME - this implementation needs fleshing out
//        
//        public void visitMethodDef(JCMethodDecl that) {
//            try {
//                w.append("START METHOD " + that.sym + "\n");
//                for (JCVariableDecl param: that.params) {
//                    String s = param.name + "$" + param.pos + "$0";
//                    String value = ce.get(s);
//                    w.append("Parameter value: " + param.name + " = " + (value == null ? "<unused>" : value) + "\n");
//                }
//            } catch (IOException e) {
//                // TODO Auto-generated catch block
//                e.printStackTrace();
//            }
//            super.visitMethodDef(that);
//        }
//        
//        public void visitIf(JCIf that) {
//            String s = "branchCondition_" + that.pos + "_" + 0;
//            String value = ce.get(s);
//            try {
//                if (value == null) w.append(getPosition(that.pos) + "!!!  Could not find value for branch ("+s+")\n");
//                else {
//                    w.append(getPosition(that.pos) + "Branch condition value: " + value + "\n");
//                    if (value.equals("true")) {
//                        if (that.thenpart != null) that.thenpart.accept(this);
//                    } else if (value.equals("false")) {
//                        if (that.elsepart != null) that.elsepart.accept(this);
//                    } else {
//                        w.append("!!! Unknown value: " + value + "\n");
//                    }
//                }
//            } catch (IOException e) {
//                // TODO Auto-generated catch block
//                e.printStackTrace();
//            }
//        }
//        
//        public void visitAssign(JCAssign that) {
//            try {
//                if (that.lhs instanceof JCIdent) {
//                    JCIdent id = (JCIdent)that.lhs;
//                    String s = id.name + "$" + ((VarSymbol)id.sym).pos + "$" + that.pos;
//                    String value = ce.get(s);
//                    if (value == null) w.append(getPosition(that.pos) + "!!!  Could not find value for variable ("+s+")\n");
//                    else w.append(getPosition(that.pos) + "Assignment: " + id.name + " = " + value + "\n");
//                }
//            } catch (IOException e) {
//                // TODO Auto-generated catch block
//                e.printStackTrace();
//            }
//        }
//        
//        public void visitTry(JCTry that) {
//            try {
//                try {
//                    that.body.accept(this);
//                } catch (ReturnException e) {
//                    // do the finally block
//                    if (that.finalizer != null) {
//                        w.append(getPosition(that.finalizer.pos) + "Executing finally block\n");
//                        that.finalizer.accept(this);
//                    }
//                    throw e;
//                } catch (ExException e) {
//                    // FIXME
//                }
//            } catch (IOException e) {
//                // FIXME
//            }
//        }
//        
//        public void visitReturn(JCReturn that) {
//            String s = "RESULT_";  // FIXME - should replace with defined constnat, but this is missing the final $
//            String value = ce.get(s);
//            try {
//                if (that.expr != null) {
//                    if (value == null) w.append(getPosition(that.pos) + "!!!  Could not find return value ("+s+")\n");
//                    else w.append(getPosition(that.pos) + "Executed return: value = " + value + "\n");
//                } else {
//                    w.append(getPosition(that.pos) + "Executed return\n");
//                }
//            } catch (IOException e) {
//                // TODO Auto-generated catch block
//                e.printStackTrace();
//            }
//            throw new ReturnException();
//        }
//    } 
    

//    /** A runtime exception used to jump up to a finally block in the visitor calling stack */
//    private static class ReturnException extends RuntimeException {
//        private static final long serialVersionUID = -3475328526478936978L;}
//
//    /** A runtime exception used to jump up to a finally block in the visitor calling stack */
//    private static class ExException extends RuntimeException {
//        private static final long serialVersionUID = -5610207201211221750L;}
    
    /** Outputs the counterexample information in more readable form
     * @param context the compilation context
     * @param program the program whose counterexample information is to be printed 
     * @param ce the counterexample information to translate
     * @param prover the prover from which the counterexample information came
     */
//    public static String trace(@NonNull Context context, @NonNull BasicProgram program, @NonNull ICounterexample ce, IProver prover) {
//        String s = null;
//        try {
//            s = (new TracerBB(context)).trace(program,ce,prover);
//        } catch (ReturnException e) {
//            // ignore
//        } catch (ExException e) {
//            // ignore
//        } catch (IOException e) {
//            log.noticeWriter.println("ABORTED");
//        } catch (RuntimeException e) {
//            log.noticeWriter.println("ABORTED");
//            throw e;
//        } 
//        return s;
//    }
//    
    
//    // FIXME - Review
//    /** This class converts a counterexample into more readable information;
//     * it uses the basic program form rather than using the Java AST. */
//    public static class TracerBB extends JmlTreeScanner {
//        
//        /** The counterexample information */
//        ICounterexample ce;
//        
//        boolean showSubexpressions;
//        
//        /** The log for output */
//        @NonNull Log log;
//        
//        /** The program being traced */
//        BasicProgram program;
//        
//        /** The compilation context */
//        @NonNull Context context;
//        
//        Map<String,String> values;
//        
//        Writer w;
//        
//        /** The prover that was used to create the counterexample */
//        IProver prover;
//        
//        Symtab syms;
//        
//        List<IProverResult.Span> path = null;
//        
//        /** Translates the given position information into source, line and column information 
//         * @param pos the position information to translate
//         * @return A String containing human-readable source location information
//         */
//        public String getPosition(int pos) {  // TODO - check about the second argument of getColumnNumber
//            return log.currentSourceFile().getName() + ":" + log.currentSource().getLineNumber(pos) + " (col " + log.currentSource().getColumnNumber(pos,false) + "): \t";
//        }
//        
//        /** The constructor for this class
//         * @param context the compilation context
//         */
//        public TracerBB(@NonNull Context context) {
//            this.context = context;
//            log = Log.instance(context);
//            syms = Symtab.instance(context);
//            w = new StringWriter();
//            showSubexpressions = JmlOption.isOption(context,JmlOption.SUBEXPRESSIONS) || true;
//        }
//        
//        // FIXME - DOCUMENT
//        public static String trace(@NonNull Context context, @NonNull BasicProgram program, ICounterexample ce, IProver prover) {
//            try {
//                return new TracerBB(context).trace(program,ce,prover);
//            } catch (IOException e) {
//                return "<IOException: " + e + ">";
//            }
//        }
//        
//        //@ ensures this.program != null && this.ce != null;
//        //@ ensures this.program != program && this.ce != ce;
//        public String trace(@NonNull BasicProgram program, ICounterexample ce, IProver prover) throws IOException {
//            this.ce = ce;
//            this.program = program;
//            this.prover = prover;
//            w = new StringWriter();
//            w.append("COUNTEREXAMPLE TRACE \n\n");
//            values = ce.getMap();
//            this.subexp = new Subexpressor(context,prover,values,w);
//            this.path = new LinkedList<IProverResult.Span>();
//            
//            for (JCVariableDecl vd: program.methodDecl.params) {
//                String n = vd.name + "$" + vd.pos + "$0";
//                String value = ce.get(n);
//                w.append(getPosition(vd.pos) + "Parameter \t" +  n + " \t= " + (value==null?"?":value) + "\n");
//            }
//            
//            if (showSubexpressions) prover.reassertCounterexample(ce);
////            for (Map.Entry<JCTree,String> entry: ((Counterexample)ce).mapv.entrySet()) { // FIXME - hacked to get at map - fix this
////              values.put(entry.getKey(),entry.getValue());
////            }
//            BoogieBlock block = program.startBlock();
//            outer: while (traceBlockStatements(block,ce)) {
//                for (BoogieBlock next: block.succeeding()) {
//                    String s = next.id().toString();
//                    String value = ce.get(s);
//                    if (value.equals("false")) {
//                        block = next;
//                        continue outer;
//                    }
//                }
//                break;
//            }
//            w.append("END\n");
//            ce.putMap(values);
//            ce.putPath(path);
//            return w.toString();
//        }
//        
//
//        
//        // CAUTION: The Strings in use in these visit methods correspond to the
//        // encoding used in the BoogieBlocker methods.  The BoogieBlocker encodes
//        // variables using combinations of variable name, declaration position,
//        // and incarnation position.  These are reflected in the counterexample 
//        // information and we need to match that as we interpret the counterexample
//        // information in these methods.
//        
//        // FIXME - Review
//        protected boolean traceBlockStatements(BoogieBlock b, ICounterexample ce) throws IOException {
//            w.append(" [ block " + b.id() + " ]\n");
//            boolean sawFalseAssert = false;
//            String pos=null, lastpos;
//            for (JCStatement statement: b.statements) {
//                if (!(statement instanceof JmlStatementExpr)) {
//                    log.error(statement.pos,"esc.internal.error","Incorrect statement type in traceBlockStatements: " + statement.getClass());
//                    continue;
//                }
//                JmlStatementExpr s = (JmlStatementExpr)statement;
//                JCExpression expr = s.expression;
//                if (expr instanceof JCIdent) {
//                    Name nm = ((JCIdent)expr).name;
//                    if (nm.toString().startsWith(BoogieBlocker.ASSUMPTION_PREFIX)) {
//                        for (BasicProgram.Definition def : program.definitions) {
//                            if (def.id.name.equals(nm)) {
//                                expr = def.value;
//                                break;
//                            }
//                        }
////                        for (JCExpression e : program.pdefinitions) {
////                            if (e instanceof JCBinary && ((JCBinary)e).lhs instanceof JCIdent && ((JCIdent)((JCBinary)e).lhs).name.equals(nm)) {
////                                expr = ((JCBinary)e).rhs;
////                            }
////                        }
//                    }
//                }
//                lastpos = pos;
//                pos = getPosition(s.pos);
//                Label label = s.label;
//                if (label == Label.ASSUME_CHECK) {
//                    // skip
//                } else if (s.token == JmlToken.ASSUME) {
//                    if (label == Label.ASSIGNMENT) {
//                        // FIXME - array, field assignments
//                        if (expr instanceof JCBinary) {
//                            JCBinary bin = (JCBinary)expr;
//                            if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                            Name n = ((JCIdent)bin.lhs).name;
//                            String v = value((JCIdent)bin.lhs);
//                            w.append(pos + "Assignment " + n + " = " + v
//                                    + "  [" + bin.rhs + "]\n");
//                            record(bin.lhs,v);
//                            showSubexpressions(bin.rhs);
//
//                        } else if (expr instanceof JmlBBArrayAssignment){
//                            JmlBBArrayAssignment asg = (JmlBBArrayAssignment)expr;
//                            JCExpression array = asg.args.get(2);
//                            JCExpression index = asg.args.get(3);
//                            JCExpression value = asg.args.get(4);
//                            
//                            List<String> results = subexp.getValues(array,index,value);
//                            if (results != null) {
//                            w.append(pos + "ArrayAssignment " 
//                                    + results.get(0) + "[" + results.get(1) + "] = " + results.get(2)
//                                    + "  [ (" + array + ")[" + index + "] = " + value + " ]\n");
//                            }
//                            showSubexpressions(array);
//                            showSubexpressions(index);
//                            showSubexpressions(value);
//                        } else if (expr instanceof JmlBBFieldAssignment){
//                            JmlBBFieldAssignment asg = (JmlBBFieldAssignment)expr;
//                            JCExpression obj = asg.args.get(2);
//                            JCIdent field = (JCIdent)asg.args.get(0);
//                            JCExpression value = asg.args.get(3);
//                            
//                            List<String> results = subexp.getValues(obj,value);
//                            w.append(pos + "FieldAssignment " 
//                                    + results.get(0) + "." + field + " = " + results.get(1)
//                                    + "  [ (" + obj + ")." + field + " = " + value + " ]\n");
//                            showSubexpressions(obj);
//                            showSubexpressions(value);
//
//                        } else {
//                            failure(label,expr);
//                        }
//                    } else if (label == Label.ARGUMENT) {
//                        // Called methods and new object (called constructor) calls
//                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
//                        JCBinary bin = (JCBinary)expr;
//                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        Name n = ((JCIdent)bin.lhs).name;
//                        String v = value((JCIdent)bin.lhs);
//                        w.append(pos + "ArgumentEvaluation " + n + " = " + v
//                                + "  [" + bin.rhs + "]\n");
//                        record(bin.lhs,v);
//                        showSubexpressions(bin.rhs);
//
//                    } else if (label == Label.RECEIVER) {
//                        // Called methods and new object (called constructor) calls
//                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
//                        JCBinary bin = (JCBinary)expr;
//                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        Name n = ((JCIdent)bin.lhs).name;
//                        String v = value((JCIdent)bin.lhs);
//                        w.append(pos + "ReceiverEvaluation " + n + " = " + v
//                                + "  [" + bin.rhs + "]\n");
//                        record(bin.lhs,v);
//                        showSubexpressions(bin.rhs);
//                    
//                    } else if (label == Label.BRANCHC) {
//                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
//                        JCBinary bin = (JCBinary)expr;
//                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        String v = value((JCIdent)bin.lhs);
//                        w.append(pos + label + " = " + v
//                                + "  [" + bin.rhs + "]\n");
//                        record(bin.lhs,v);
//                        showSubexpressions(bin.rhs);
//                        
//                    } else if (label == Label.LBL) {
//                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
//                        JCBinary bin = (JCBinary)expr;
//                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        JCIdent id = (JCIdent)bin.lhs;
//                        String lbl = id.toString();
//                        int k = lbl.lastIndexOf('$');
//                        lbl = lbl.substring(k+1);
//                        String v = value(id);
//                        w.append(pos + label + ": " + lbl + " = " + v
//                                + "  [" + bin.rhs + "]\n");
//                        record(id,v);
//                        showSubexpressions(bin.rhs);
//                        
//                    } else if (label == Label.SWITCH_VALUE) {
//                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
//                        JCBinary bin = (JCBinary)expr;
//                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        String v = value((JCIdent)bin.lhs);
//                        w.append(pos + "switch value = " + v
//                                + "  [" + bin.rhs + "]\n");
//                        record(bin.lhs,v);
//                        showSubexpressions(bin.rhs);
//                        
//                    } else if (label == Label.SYN) {  // FIXME - rename the SYN types that are wanted
//                        if (expr instanceof JCBinary) {
//                            JCExpression lhs = ((JCBinary)expr).lhs;
//                            if (lhs instanceof JCIdent) {
//                                String value = ce.get(((JCIdent)lhs).name.toString());
//                                w.append(pos + "Syn " + lhs + " = " + value + "\n");
//                            } else {
//                                w.append(pos + "Syn " + expr + "\n");
//                            }
//                        } else {
//                            w.append(pos + "Syn " + expr + "\n");
//                        }
//                    } else if (label == Label.EXPLICIT_ASSUME) {
//                        if (expr instanceof JCIdent) {
//                            // This will happen for tracked assumptions
//                            Name n = ((JCIdent)expr).name;
//                            String value = ce.get(n.toString());
//                            w.append(pos + label + " " + n + " = " + value + "\n");
//                            JCExpression e = findDefinition(n);
//                            record(expr,value);
//                            if (e != null) showSubexpressions(e);
//                        } else {
//                            w.append(pos + label + " " + expr + "\n");
//                            showSubexpressions(expr);
//                        }
//                    } else if (label == Label.DSA) {
//                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
//                        JCBinary bin = (JCBinary)expr;
//                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        if (!(bin.rhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        w.append(lastpos + label + " = " + value((JCIdent)bin.lhs)
//                                + "  [" + bin.rhs + "]\n");
//                        // no subexpressions
//                    } else if (label == Label.RETURN) {
//                        w.append(pos + "Executing return statement\n");
//                    } else if (label == Label.TERMINATION) {
//                        if (!(expr instanceof JCBinary)) { failure(label,expr); continue; }
//                        JCBinary bin = (JCBinary)expr;
//                        if (!(bin.lhs instanceof JCBinary)) { failure(label,expr); continue; }
//                        bin = (JCBinary)bin.lhs;
//                        if (!(bin.lhs instanceof JCIdent)) { failure(label,expr); continue; }
//                        String v = value((JCIdent)bin.lhs);
//                        if (v.equals("0")) {
//                            String rv = bin.lhs.toString().replace("terminationVar","result");
//                            String vv = valueNull(rv);
//                            w.append(pos + "Called method returned normally [" + bin.lhs + "=" + v +"]"+ (vv==null?"":", return value = " + vv + " ["+rv+"]\n"));
//                        } else {
//                            String rv = bin.lhs.toString().replace("terminationVar","exception");
//                            String vv = subexp.getType(rv);
//                            w.append(pos + "Called method exited with an exception [" + bin.lhs + "=" + v +"]"
//                                    + (vv==null?"":", exception type = "+vv) + "\n");
//                        }
//                    } else if (label == Label.METHODAXIOM) {
//                        // Just print the axiom - don't try to evaluate it
//                        w.append(pos + label + " " + expr + "\n");
//                    } else if (label == Label.ARRAY_INIT) {
//                        // Just print the expression - don't try to evaluate it
//                        w.append(pos + label + " " + expr + "\n");
//                    } else if (label == Label.BRANCHT || label == Label.HAVOC) {
//                        // skip
//                    } else if (label == Label.BRANCHE) {
//                        if (expr instanceof JCUnary) {
//                            JCExpression e = ((JCUnary)expr).getExpression();
//                            if (e instanceof JCIdent) {
//                                String value = value((JCIdent)e);
//                                record(expr,value);
//                            }
//                        }
//                    } else {
//                        w.append(pos + label + " " + expr + "\n");
//                        showSubexpressions(expr);
//                    }
//                } else if (s.token == JmlToken.ASSERT) {
//                    String value = null;
//                    String name = null;
//                    if (expr instanceof JCIdent) {
//                        name = ((JCIdent)expr).toString();
//                        value = ce.get(name);
//                        JCExpression e = findDefinition(((JCIdent)expr).name);
//                        if (e != null) expr = e;
//                    }
//                    w.append(pos + "Assert [" + label + "] "
//                            + (value == null? "" : value)
//                            + "   [" + expr + "]\n");
//                    showSubexpressions(expr);
//                    if ("false".equals(value)) {
//                        sawFalseAssert = true;
//                    }
//                } else if (s.token == JmlToken.COMMENT) {
//                    w.append(pos);
//                    w.append("Comment: // ");
//                    w.append(((JCLiteral)s.expression).value.toString());
//                    w.append("\n");
//                } else {
//                    log.error(pos,"esc.internal.error","Incorrect token type in traceBlockStatements: " + s.token.internedName());
//                }
//                if (label == Label.PRECONDITION) {
////                    int sp = TreeInfo.getStartPos(expr);
////                    int ep = TreeInfo.getEndPos(expr,log.currentSource().getEndPosTable());
////                    int type = IProverResult.Span.NORMAL;
////                    String result = values.get(expr.toString());
////                    type = result == null ? IProverResult.Span.NORMAL : result.equals("true") ? IProverResult.Span.TRUE : result.equals("false") ? IProverResult.Span.FALSE : IProverResult.Span.NORMAL; 
////                    if (sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//                    doLogicalSubExprs(expr);
//                } else if (label == Label.ASSIGNMENT || label == Label.EXPLICIT_ASSERT || label == Label.EXPLICIT_ASSUME
//                        || label == Label.BRANCHT || label == Label.BRANCHE
//                        || label == Label.SWITCH_VALUE) { 
//                    int sp = TreeInfo.getStartPos(s);
//                    int ep = TreeInfo.getEndPos(s,log.currentSource().getEndPosTable());
//                    int type = IProverResult.Span.NORMAL;
//                    if (label != Label.ASSIGNMENT) {
//                        String result = values.get(expr.toString());
//                        type = result == null ? IProverResult.Span.NORMAL : result.equals("true") ? IProverResult.Span.TRUE : result.equals("false") ? IProverResult.Span.FALSE : IProverResult.Span.NORMAL; 
//                    }
//                    if (sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//                } else if (label == Label.CATCH_CONDITION) {
//                    int sp = TreeInfo.getStartPos(s);
//                    int ep = TreeInfo.getEndPos(s,log.currentSource().getEndPosTable());
//                    int type = IProverResult.Span.NORMAL;
//                    type = IProverResult.Span.NORMAL; 
//                    if (sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//                } else if (label == Label.POSTCONDITION || label == Label.SIGNALS) {
//                    JCExpression texpr = expr;
//                    if (label == Label.SIGNALS) {// FIXME - a NPE thrown from here does not produce any visible error
//                        texpr = (texpr instanceof JmlBinary && ((JmlBinary)texpr).op == JmlToken.IMPLIES) ? ((JmlBinary)texpr).rhs : null;
//                        texpr = (texpr instanceof JCBinary && ((JCBinary)texpr).getTag() == JCTree.AND) ? ((JCBinary)texpr).rhs : null;
//                        if (texpr instanceof JmlBinary && ((JmlBinary)texpr).op == JmlToken.IMPLIES) {
//                            JCExpression tt = ((JmlBinary)texpr).rhs;
//                            if (tt instanceof JmlBinary && ((JmlBinary)tt).op == JmlToken.IMPLIES) {
//                                texpr = (JmlBinary)tt;
//                            }
//                        } else {
//                            texpr = null;
//                        }
//                    } else {
//                        texpr = (texpr instanceof JmlBinary && ((JmlBinary)texpr).op == JmlToken.IMPLIES) ? ((JmlBinary)texpr).rhs : null;
//                        texpr = (texpr instanceof JmlBinary && ((JmlBinary)texpr).op == JmlToken.IMPLIES) ? texpr : null;
//                    }
//                    if (texpr instanceof JmlBinary) {
//                        JmlBinary rexpr = (JmlBinary)texpr;
//                        JCExpression lhs = rexpr.lhs;
//                        JCExpression rhs = rexpr.rhs;
//                        int sp = TreeInfo.getStartPos(lhs);
//                        int ep = TreeInfo.getEndPos(lhs,log.currentSource().getEndPosTable());
//                        int type = IProverResult.Span.NORMAL;
//                        String result = values.get(lhs.toString());
//                        type = result == null ? IProverResult.Span.NORMAL : result.equals("true") ? IProverResult.Span.TRUE : result.equals("false") ? IProverResult.Span.FALSE : IProverResult.Span.NORMAL; 
//                        if (sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//                        if (type != IProverResult.Span.FALSE) {
//                            sp = TreeInfo.getStartPos(rhs);
//                            ep = TreeInfo.getEndPos(rhs,log.currentSource().getEndPosTable());
//                            type = IProverResult.Span.NORMAL;
//                            result = values.get(rhs.toString());
//                            type = result == null ? IProverResult.Span.NORMAL : result.equals("true") ? IProverResult.Span.TRUE : result.equals("false") ? IProverResult.Span.FALSE : IProverResult.Span.NORMAL; 
//                            if (sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//                        }
//                    } else {
//                        int sp = TreeInfo.getStartPos(s);
//                        int ep = TreeInfo.getEndPos(s,log.currentSource().getEndPosTable());
//                        int type = IProverResult.Span.NORMAL;
//                        String result = values.get(expr.toString());
//                        type = result == null ? IProverResult.Span.NORMAL : result.equals("true") ? IProverResult.Span.TRUE : result.equals("false") ? IProverResult.Span.FALSE : IProverResult.Span.NORMAL; 
//                        if (sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//                    }
//                } else if (label == Label.TERMINATION) {
//                    int sp = TreeInfo.getStartPos(s);
//                    int ep = TreeInfo.getEndPos(s,log.currentSource().getEndPosTable());
//                    int type = IProverResult.Span.NORMAL;
//                    {
//                        JCExpression e = ((JCBinary)((JCBinary)expr).lhs).lhs;
//                        String result = values.get(e.toString());
//                        int k = result == null ? 0 : Integer.valueOf(result);
//                        type = k < 0 ? IProverResult.Span.EXCEPTION : IProverResult.Span.NORMAL; 
//                    }
//                    if (sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//                }
//                if (sawFalseAssert) break;// Stop reporting the trace if we encounter a false assertion
//            }
//            return !sawFalseAssert;
//        }
//        
//        public int doExpr(JCExpression expr, boolean show) {
//            int sp = TreeInfo.getStartPos(expr);
//            int ep = TreeInfo.getEndPos(expr,log.currentSource().getEndPosTable());
//            int type = IProverResult.Span.NORMAL;
//            String result = values.get(expr.toString());
//            type = result == null ? IProverResult.Span.NORMAL : result.equals("true") ? IProverResult.Span.TRUE : result.equals("false") ? IProverResult.Span.FALSE : IProverResult.Span.NORMAL; 
//            if (show && sp >= 0 && ep >= sp) path.add(new IProverResult.Span(sp,ep,type)); // FIXME - don't think the end position is right for statements
//            return type;
//        }
//        
//        public int doLogicalSubExprs(JCExpression expr) {
//            int r = -10;
//            if (expr instanceof JCBinary) {
//                int op = expr.getTag();
//                JCBinary bin = (JCBinary)expr;
//                if (op == JCTree.OR) {
//                    r = doLogicalSubExprs(bin.lhs);
//                    if (r != IProverResult.Span.TRUE) {
//                        r = doLogicalSubExprs(bin.rhs);
//                    }
//                } else if (op == JCTree.AND) {
//                    r = doLogicalSubExprs(bin.lhs);
//                    if (r != IProverResult.Span.FALSE) {
//                        r = doLogicalSubExprs(bin.rhs);
//                    }
//                } else if (op == JCTree.BITOR) {
//                    r = doLogicalSubExprs(bin.lhs);
//                    int rr = doLogicalSubExprs(bin.rhs);
//                    r = (rr==IProverResult.Span.TRUE) ? rr : r;
//                } else {
//                    r = doExpr(expr,true);
//                }
//            } else if (expr instanceof JmlBinary) {
//                JmlBinary bin = (JmlBinary)expr;
//                JmlToken op = bin.op;
//                if (op == JmlToken.IMPLIES) {
//                    r = doLogicalSubExprs(bin.lhs);
//                    if (r != IProverResult.Span.FALSE) {
//                        r = doLogicalSubExprs(bin.rhs);
//                    }
//                } else if (op == JmlToken.REVERSE_IMPLIES) {
//                    r = doLogicalSubExprs(bin.lhs);
//                    if (r != IProverResult.Span.TRUE) {
//                        r = doLogicalSubExprs(bin.rhs);
//                    }
//                } else {
//                    r = doLogicalSubExprs(bin.rhs);
//                    r = doExpr(expr,false);
//                }
//            } else {
//                r = doExpr(expr,true);
//            }
//
//            // FIXME - also do NOT, conditional expression, boolean ==, EQUIVALENCE, INEQUIVALENCE
//            return r;
//        }
//        
//        public JCExpression findDefinition(Name name) {
//            for (BasicProgram.Definition def: program.definitions()) {
//                JCIdent id = def.id;
//                if (id.name != name) continue;
//                return def.value;
//            }
////            for (JCExpression e: program.pdefinitions) {
////                if (!(e instanceof JCBinary)) continue;
////                JCBinary bin = (JCBinary)e;
////                if (!(bin.lhs instanceof JCIdent)) continue;
////                JCIdent id = (JCIdent)bin.lhs;
////                if (id.name != name) continue;
////                return bin.rhs;
////            }
//            return null;
//        }
//        
//        public String value(JCIdent id) {
//            String v = ce.get(id.name.toString());
//            if (v == null) v = "?";
//            return v;
//        }
//        
//        public String valueNull(JCIdent id) {
//            return ce.get(id.name.toString());
//        }
//        
//        public String valueNull(String id) {
//            return ce.get(id);
//        }
//        
//        public void failure(Label label, JCExpression expr) {
//            log.warning("jml.internal.notsobad","Unable to interpret counterexample trace.  A " + label + " statement has unexpected structure: " + expr);
//        }
//        
//        Subexpressor subexp;
//        
//        public String showSubexpressions(JCExpression expr) {
//            if (showSubexpressions) try { 
//                subexp.walk(expr);
//                return w.toString();
//            } catch (IOException e) {
//                return "<IOException>";
//            }
//            return "";
//        }
//        
//        public void record(JCExpression expr, String value) {
//            subexp.values.put(expr.toString(),value);
//        }
//    }
//    
//    static int count = 1000000;
//
//    /** This class requests values of subexpressions from the prover */
//    public static class Subexpressor extends JmlTreeScanner {
//        
//        Context context;
//        IProver prover;
//        JmlTree.Maker M;
//        Names names;
//        Symtab syms;
//        Writer w;
//        final String prefix = "X$$$";
//        List<JCBinary> exprs = new LinkedList<JCBinary>();
//        Map<String,JCExpression> requests = new HashMap<String,JCExpression>();
//        Map<String,String> values = null;
//        
//        /** Top-level call for the class - puts requests to the prover for each
//         * subexpression of the argument, returning the results in 'requests'.
//         * This method can be reused, but is not thread-safe.
//         */
//        public void walk(JCExpression expr) throws IOException {
//            exprs.clear();
//            requests.clear();
//            scan(expr);
//            IProverResult res = null;
//            try {
//                for (JCExpression e: exprs) {
//                    prover.assume(e);
//                }
//                res = prover.check(true);
//            } catch (ProverException ex) {
//                w.append(ex.toString());  // FIXME - clean up the error reporting here and in the RUntimeExceptions just below.
//                w.append("\n");
//                return;
//            }
//            if (res == null) {
//                throw new RuntimeException("ERROR: no additional information available");
//            } else if (!res.isSat()) {
//                throw new RuntimeException("ERROR: no longer satisfiable");
//            } else {
//                ICounterexample nce = res.counterexample();
//                for (JCBinary bin: exprs) {
//                    JCIdent id = (JCIdent)bin.lhs;
//                    String value = nce.get(id.toString());
//                    if (value != null && id.type.tag == TypeTag.CHAR) {
//                        value = ((Character)(char)Integer.parseInt(value)).toString() + " (" + value + ")";
//                    }
//                    if (value == null) value = "?";
//                    w.append("                                " + value + "\t = " + bin.rhs + "\n");
//                    values.put(bin.rhs.toString(), value);
//                }
//            }
//        }
//        
//        /** Top-level call that returns a list of values (as Strings) corresponding to the list of 
//         * expressions in the argument */
//        public List<String> getValues(JCExpression... exprlist) throws IOException {
//            IProverResult res = null;
//            List<JCIdent> ids = new LinkedList<JCIdent>();
//            try {
//                for (JCExpression e: exprlist) {
//                    JCIdent id = newIdent(e);
//                    JCExpression ex = M.at(Position.NOPOS).Binary(JCTree.EQ,id,e);
//                    ex.type = syms.booleanType;
//                    ids.add(id);
//                    prover.assume(ex);
//                }
//                res = prover.check(true);
//            } catch (ProverException ex) {
//                w.append(ex.toString()); w.append("\n"); // FIXME - better error response here and below
//                return null;
//            }
//            if (res == null) {
//                w.append("ERROR: no additional information available\n");
//            } else if (!res.isSat()) {
//                w.append("ERROR: no longer satisfiable\n");
//            } else {
//                ICounterexample nce = res.counterexample();
//                List<String> out = new LinkedList<String>();
//                int k = 0;
//                for (JCIdent id: ids) {
//                    String value = nce.get(id.name.toString());
//                    if (value == null) value = "?";
//                    out.add(value);
//                    if (values != null) {
//                        JCExpression ee = exprlist[k];
//                        String e = ee.toString();
//                        if (ee.type.tag == TypeTag.CHAR) {
//                            e = ((Character)(char)Integer.parseInt(e)).toString();
//                        }
//                        values.put(e,value);
//                        //System.out.println("MAPPING: " + e + " " + value);
//                        k++; // FIXME - increment inside or outside the if statement
//                    }
//                }
//                prover.reassertCounterexample(nce);
//                return out;
//            }
//            return null;
//        }
//
//        /** Returns the dynamic type of the variable given in the argument */
//        public String getType(String eid) {
//            try {
//                M.at(Position.NOPOS);
//                JCIdent expr = M.Ident(Names.instance(context).fromString(eid));
//                expr.type = syms.objectType;
//                JCExpression e = M.JmlMethodInvocation(JmlToken.BSTYPEOF,expr);
//                e.type = syms.classType;
//                JCIdent id = newIdent(e);
//                JCExpression ex = M.at(Position.NOPOS).Binary(JCTree.EQ,id,e);
//                ex.type = syms.booleanType;
//                prover.assume(ex);
//                IProverResult res = prover.check(true);
//                if (res == null) {
//                    w.append("ERROR: no additional information available\n");
//                } else if (!res.isSat()) {
//                    w.append("ERROR: no longer satisfiable\n");
//                } else {
//                    ICounterexample nce = res.counterexample();
//                    String value = nce.get(id.name.toString());
//                    return value;
//                }
//            } catch (IOException e) {
//                Log.instance(context).noticeWriter.println(e.toString());
//
//            } catch (ProverException e) {
//                Log.instance(context).noticeWriter.println(e.toString());
//            }
//            return null;
//        }
//        
//        public Subexpressor(Context context, IProver prover, Map<String,String> values, Writer w) {
//            this.context = context;
//            this.prover = prover;
//            this.M = JmlTree.Maker.instance(context);
//            this.names = Names.instance(context);
//            this.syms = Symtab.instance(context);
//            this.w = w;
//            this.values = values;
//        }
//        
//        public void request(JCExpression expr) {
//            JCIdent id = newIdent(expr);
//            requests.put(id.name.toString(),expr);
//            JCBinary bin = M.Binary(JCTree.EQ,id,expr);
//            bin.type = syms.booleanType;
//            bin.pos = Position.NOPOS;
//            exprs.add(bin);
//        }
//        
//        /** Creates a unique identifier with the type of the given expression */
//        public JCIdent newIdent(JCExpression expr)  {
//            Type t = expr.type;
//            Name n = names.fromString(prefix + (++count));
//            JCIdent id = M.Ident(n);
//            id.type = t;
//            return id;
//        }
//        
//        /** Scan the given JCTree, issuing a request() call for each subexpression encountered */
//        public void scan(JCTree that) {
//            super.scan(that);
//            if (that instanceof JCExpression &&
//                    !(that instanceof JCParens) &&
//                    !(that instanceof JCLiteral)) request((JCExpression)that);
//        }
//
//        /** Scan the given JCTree, issuing a request() call for each subexpression encountered,
//         * but not for the argument itself */
//        public void scanNoRequest(JCTree that) {
//            super.scan(that);
//        }
//        
//        public void visitLiteral(JCLiteral tree) {
//            String r = tree.toString();
//            values.put(r,r);
//        }
//
//        /** Overridden so that we request the arguments but not the method call itself.*/
//        public void visitApply(JCMethodInvocation tree) {
//            scanNoRequest(tree.meth);
//            scan(tree.args);
//        }
//        
//        /** Don't request values for quantified expressions */
//        public void visitJmlQuantifiedExpr(JmlQuantifiedExpr tree) {
//            // do not scan the subexpressions of a quantified expression
//        }
//        
//        public void visitCatch(JCCatch tree) {
//            super.visitCatch(tree);
//        }
//    }
//    
//    /** This class computes metrics over a BoogieBlock */
//    public static class Counter extends JmlTreeScanner {
//        
//        int nodes = 0;  // nodes
//        int assumes = 0;
//        int asserts = 0;
//        int blocks = 0;
//        int statements = 0;
//        int paths = 0;
//        int maxBlockNodes = 0;
//        
//        public void count(BoogieBlock b) {
//            for (JCTree t: b.statements()) t.accept(this);
//            nodes += b.statements().size();
//        }
//        
//        public static int counts(BoogieBlock b) {
//            return counts(b.statements());
//        }
//        
//        public static int counts(List<JCStatement> sts) {
//            Counter c = new Counter();
//            for (JCTree t: sts) t.accept(c);
//            return c.nodes + sts.size();
//        }
//        
//        static public Counter count(BasicProgram b) {
//            Counter c = new Counter();
//            int max = 0;
//            for (BoogieBlock bb: b.blocks()) {
//                int c1 = c.nodes;
//                c.count(bb);
//                if (c.nodes - c1 > max) max = c.nodes - c1;
//            }
//            c.maxBlockNodes = max;
//            for (BasicProgram.Definition t: b.definitions()) { t.id.accept(c); t.value.accept(c); }
//            for (JCTree t: b.pdefinitions) t.accept(c);
//            for (JCTree t: b.background()) t.accept(c);
//            c.blocks = b.blocks().size();
//            return c;
//        }
//        
//        static public int countx(BasicProgram b) {
//            Counter c = new Counter();
//            for (BasicProgram.Definition t: b.definitions()) { t.id.accept(c); t.value.accept(c); }
//            for (JCTree t: b.pdefinitions) t.accept(c);
//            for (JCTree t: b.background()) t.accept(c);
//            return c.nodes;
//        }
//        
//        static public int countAST(JCTree node) {
//            Counter c = new Counter();
//            node.accept(c);
//            if (node instanceof JCBlock) c.nodes++;
//            return c.nodes;
//        }
//        
//        static public int countASTStatements(JCTree node) {
//            Counter c = new Counter();
//            node.accept(c);
//            if (node instanceof JCBlock) c.statements++;
//            return c.statements;
//        }
//        
//        public Counter() {
//        }
//        
//        public void add(Counter c) {
//            nodes += c.nodes;
//            assumes += c.assumes;
//            asserts += c.asserts;
//            blocks += c.blocks;
//            statements += c.statements;
//            maxBlockNodes = maxBlockNodes < c.maxBlockNodes ? c.maxBlockNodes : maxBlockNodes;
//        }
//        
//        public void scan(JCTree that) {
//            nodes++;
//            if (that instanceof JCStatement) statements++;
//            super.scan(that);
//        }
//        
//        public void visitJmlStatementExpr(JmlStatementExpr that) {
//            if (that.token == JmlToken.ASSUME) assumes++;
//            if (that.token == JmlToken.ASSERT) asserts++;
//            super.visitJmlStatementExpr(that);
//        }
//        
//        public String toString() {
//            return "    " + blocks + " blocks; " + nodes + " nodes; " + maxBlockNodes + " max; " + assumes + " assumes; " + asserts + " asserts; " ;
//        }
//    }

}
