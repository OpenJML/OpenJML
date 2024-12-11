/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.util.*;
import java.util.stream.Collectors;

import static org.jmlspecs.openjml.ext.StatementExprExtensions.*;
import static org.jmlspecs.openjml.ext.FunctionLikeExpressions.*;
import static org.jmlspecs.openjml.ext.MiscExpressions.*;
import static org.jmlspecs.openjml.ext.StateExpressions.*;
import static org.jmlspecs.openjml.ext.Operators.*;

import org.jmlspecs.openjml.*;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.ext.JmlPrimitiveTypes;
import org.jmlspecs.openjml.ext.QuantifiedExpressions;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.smtlib.ICommand;
import org.smtlib.ICommand.IScript;
import org.smtlib.IExpr;
import org.smtlib.IExpr.*;
import org.smtlib.ISort;
import org.smtlib.SMT;
import org.smtlib.SMT.Configuration;
import org.smtlib.command.*;
import org.smtlib.impl.Factory;
import org.smtlib.impl.SMTExpr.Numeral;
import org.smtlib.impl.Script;

import com.sun.tools.javac.code.*;
import com.sun.tools.javac.code.Type.*;
import com.sun.tools.javac.model.JavacTypes;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;

/** This class translates a BasicBlock program into SMTLIB;
 *  a new instance of the class is needed for each BasicBlock program translated.
 *  <P>
 * The input program is a BasicBlock program, which may consist of the
 * following kinds of statements:
 * <UL>
 * <LI>declaration statements with or without initializers (TODO - what kinds of types)
 * <LI>JML assume statements
 * <LI>JML assert statements
 * <LI>JML comment statements
 * </UL>
 * Expressions may include the following:
 * <UL>
 * <LI>Java operators: + - * / % comparisons bit-operations logic-operators
 * <LI>field access - TODO?
 * <LI>array access - TODO?
 * <LI>STORE and SELECT functions using Java method class (JCMethodInvocation)
 * <LI>method calls (TODO - any restrictions?)
 * </UL>
 */
public class SMTBitVector extends JmlTreeScanner {
    
    public static enum BV { NOT_INT, NO_BV, EITHER, OK_BV, MUST_BV }

    // domain is either JCTree and Symbol
    public HashMap<Object, BV> bvmap = new HashMap<>();
    
    BV result;
    BV bv;

    /** The compilation context */
    protected Context context;
    
    /** The error log */
    final protected Log log;
    
    /** The symbol table for this compilation context */
    final protected Symtab syms;
    
    /** The Names table for this compilation context */
    final protected Names names;
    
    /** Cached value of the types tool */
    final protected javax.lang.model.util.Types types;
    
    final protected JmlTypes jmltypes;
    
    /** Cached instance of the JmlTreeUtils tool for the context. */
    final protected JmlTreeUtils treeutils;
    
    /** Cached instance of the org.jmlspecs.openjml.Utils tool for the context. */
    final protected Utils utils;
    
    public boolean useBV;
    public boolean inQuant;
    
    final Symbol REAL;
    final Symbol BIGINT;
    final Symbol STRING;
    final Symbol TYPE;
    
    
    /** The constructor - create a new instance for each Basic Program to be translated */
    public SMTBitVector(Context context) {
        this.context = context;
        // OpenJDK tools
        log = Log.instance(context);
        syms = Symtab.instance(context);
        names = Names.instance(context);
        types = JavacTypes.instance(context);
        treeutils = JmlTreeUtils.instance(context);
        utils = org.jmlspecs.openjml.Utils.instance(context);
        jmltypes = JmlTypes.instance(context);
        
        STRING = JmlPrimitiveTypes.stringTypeKind.getSymbol(context);
        BIGINT = JmlPrimitiveTypes.bigintTypeKind.getSymbol(context);
        REAL = JmlPrimitiveTypes.realTypeKind.getSymbol(context);
        TYPE = JmlPrimitiveTypes.TYPETypeKind.getSymbol(context);

    }

    
    /** This is called by visit methods, and super.scan calls accept methods;
     * clients should call scan instead of accept so that there is a common
     * processing point as well as the type-specific processing in accept methods.
     */
    @Override
    public void scan(JCTree t) {
        result = null;
        if (t != null) {
            super.scan(t);
            if (result != null) {
                // This mapping is used in associating original source code 
                // sub-expressions with SMT expressions that give their values
                // in a counterexample.
                if (t instanceof JCExpression) bvmap.put((JCExpression)t, result);
                else if (t instanceof JmlVariableDecl) {
                    JCIdent id = ((JmlVariableDecl)t).ident;
                    bvmap.put(id, result);
                    bvmap.put(id.sym, result);
                }
            }
        }
    }
        
    public void convert(BasicProgram program, boolean useBV) {
        this.useBV = useBV;
        
        // FIXME - use factory for the commands?
        // set any options

        
        
        
        for (JCIdent id: program.declarations) {
//            addConstant(id);
        }
        
        // add definitions
        for (BasicProgram.Definition e: program.definitions()) {
            try {
                scan(e.value);
            } catch (RuntimeException ee) {
                // skip - error already issued // FIXME - better error recovery?
            }
        }
        
        // Because blocks have forward references to later blocks, but
        // backward references to variables in earlier blocks, we declare
        // all the block variables first
        for (BasicProgram.BasicBlock b: program.blocks()) {
//            ICommand cc = new C_declare_fun(F.symbol(b.id.toString()), emptyList, F.Bool());
//            commands.add(cc);
        }
        
        // add blocks
        for (BasicProgram.BasicBlock b: program.blocks()) {
            convertBasicBlock(b);
        }
        
        {
            // Add an assertion that negates the start block id
//            LinkedList<IExpr> argss = new LinkedList<IExpr>();
//            argss.add(F.symbol(program.startId().name.toString()));
//            IExpr negStartID = F.fcn(notSym, argss);
        }
        
//        if (!functionSymbols.isEmpty()){
//            List<IExpr> dargs = new LinkedList<IExpr>();
//            dargs.addAll(functionSymbols);
//            dargs.add(nullSym);
//            IExpr f = F.fcn(distinctSym, dargs);
//            commands.add(new C_assert(f));
//        }
        
    }
    
//    protected void addConstant(JCIdent id) {
//        if (id.toString().contains("internal")) {
//            Type t = id.type;
//            //System.out.println("ADDCONST " + id + " " + t);
//            //System.out.println("  ADDCTYEPES " + (t==BIGINT.type) + " " + (t.tsym == BIGINT) + " " + BIGINT + " " + t.hashCode() + " " + BIGINT.hashCode());
//        }
//        String nm = makePQBarEnclosedString(id);
//
//        //String nm = makeBarEnclosedString(id.name.toString());
//        if (defined.add(nm)) {
//            try {
//                ISort sort = convertSort(id.type);
//                // FIXME - I don't think 'this' should ever get this far
//                if (id.sym != null && id.sym.owner instanceof Symbol.ClassSymbol && !Utils.instance(context).isJMLStatic(id.sym) && !id.sym.name.toString().equals("this")) {
//                    // The name is a non-static field of a class, so the sort is an SMT Array
//                    sort = F.createSortExpression(arraySym,convertSort(id.sym.owner.type),sort);
//                } else if (id.type instanceof BasicBlocker2.Array2Type) {
//                    sort = convertSort(((BasicBlocker2.Array2Type)id.type).componentType);
//                    ISort index = convertSort(((BasicBlocker2.Array2Type)id.type).indexType);
//                    sort = F.createSortExpression(arraySym,index,sort);
//                    sort = F.createSortExpression(arraySym,refSort,sort);
//                } else if (nm.startsWith(arrays_)) {
//                    // FIXME - review modeling of arrays
//                    sort = convertSort(((Type.ArrayType)id.type).getComponentType());
//                    sort = F.createSortExpression(arraySym,useBV ? bv32Sort : intSort,sort); // The type of the index is Int
//                    sort = F.createSortExpression(arraySym,refSort,sort);
//                }
//                ISymbol sym = F.symbol(nm);
//                ICommand c = new C_declare_fun(sym,emptyList,sort);
//                commands.add(c);
//                bimap.put(id,sym);
//            } catch (RuntimeException ee) {
//                // skip - error already issued// FIXME - better error recovery?
//            }
//        }
//    }
//    
//    protected boolean addConstant(ISymbol sym, ISort sort, JCExpression expr) {
//        String s = sym.toString();
//        boolean isnew = defined.add(s);
//        if (isnew) {
//            ICommand c = new C_declare_fun(sym,emptyList,sort);
//            startCommands.add(c);
//            bimap.put(expr,sym);
//        }
//        return isnew;
//    }
    
    
    
    public void convertBasicBlock(BasicProgram.BasicBlock block) {
        ListIterator<JCStatement> iter = block.statements.listIterator();
        IExpr tail; 
        if (block.followers.isEmpty()) {
//            tail = F.symbol("true");
        } else if (block.followers.size() == 1) {
//            tail = F.symbol(block.followers.get(0).id.name.toString());
        } else {
//            ArrayList<IExpr> args = new ArrayList<IExpr>();
//            for (BasicProgram.BasicBlock bb: block.followers) {
//                args.add(F.symbol(bb.id.name.toString()));
//            }
//            tail = F.fcn(andSym,args);
        }
        
        // First add all declarations
        while (iter.hasNext()) {
            convertDeclaration(iter.next());
        }

        // Then construct the block expression from the end to the start
        
        if (false) {
            // Each block statement is one (potentially very long) assertion

            // This would be an excellent candidate for iterating through the list of 
            // statements in the block in reverse order, since that is the
            // natural way to construct the block expression and avoids having
            // a deep call stack (of the length of a block). However, the statements
            // in the block have to be translated in forward order, or auxiliary
            // commands produced in their translations are added to 'commands' in
            // reverse order.
            //        while (iter.hasPrevious()) {
            //            tail = convertStatement(iter.previous(),tail);
            //        }
//            tail = convertList(block.statements,tail);
            
        } else {

//            tail = convertList2(block.id.toString(),block.statements,tail);

        }

    }
    
    /** If the statement is a variable declaration, converts it to an SMT
     * declare-fun or define-fun of the appropriate sort, depending on whether
     * there is an initializer or not.
     * @param stat
     */
    public void convertDeclaration(JCStatement stat) {
        if (stat instanceof JmlVariableDecl) {
            try {
                JmlVariableDecl decl = (JmlVariableDecl)stat;
                // convert to a declaration or definition
                if (decl.init != null) convertExpr(decl.init);
                
                String s = makeBarEnclosedString(decl.name.toString());
//                ISymbol sym = F.symbol(s);
                // An identifier may be appended to a JmlVariableDecl simply
                // to have an expression with which to associated an SMT value
//                if (decl.ident != null) bimap.put(decl.ident, sym);
//                if (sort == refSort && (decl.type instanceof Type.ClassType)) {
//                    ICommand c = new C_assert(
//                            F.fcn(orSym,F.fcn(eqSym, sym, nullSym),makeInstanceof(sym,decl.type))
//                            );
//                   commands.add(c);
//                }
            } catch (JmlBVException ee) {
                throw ee;
            } catch (RuntimeException ee) {
                // skip - error already issued // FIXME - better recovery
            }
        }
    }
    
    /** An alternate implementation, commented out below, uses recursive calls
     * to assemble the block encoding. That can give quite deep call stacks. 
     * Instead we iterate down the list and back, storing each expression on 
     * a stack. That is we are replacing the call stack with a simple expression stack.
     */
    public IExpr convertList(List<JCStatement> list, IExpr tail) {
        ListIterator<JCStatement> iter = list.listIterator();
        Stack<IExpr> stack = new Stack<IExpr>();
        
        while (iter.hasNext()) {
            JCStatement stat = iter.next();
            try {
                if (stat instanceof JmlVariableDecl) {
                    continue;
                } else if (stat instanceof JmlStatementExpr) {
                    JmlStatementExpr s = (JmlStatementExpr)stat;
                    if (s.clauseType == assumeClause) {
                        if (s.label == Label.METHOD_DEFINITION) {
//                            JCExpression ex = s.expression;
//                            ex = ((JmlQuantifiedExpr)ex).value;
//                            JCExpression lhs = ((JCTree.JCBinary)ex).lhs;
//                            JCTree.JCMethodInvocation mcall = (JCTree.JCMethodInvocation)lhs;
//                            JCExpression nm = mcall.meth;
//                            JCExpression rhs = ((JCTree.JCBinary)ex).rhs;
//                            addFunctionDefinition(nm.toString(),mcall.args,rhs);
                        } else {
                            convertExpr(s.expression);
                        }
                    } else if (s.clauseType == assertClause) {
                        convertExpr(s.expression);
                    } else if (s.clauseType == checkClause) {
                        convertExpr(s.expression);
                    } else if (s.clauseType == commentClause) {
                        convertExpr(treeutils.falseLit);
                    } else {
                        log.error("jml.internal", "Incorrect kind of token encountered when converting a BasicProgram to SMTLIB: " + s.clauseType.keyword());
                        break;
                    }
                } else {
                    log.error("jml.internal", "Incorrect kind of statement encountered when converting a BasicProgram to SMTLIB: " + stat.getClass());
                    break;
                }
            } catch (RuntimeException ee) {
                // There is no recovery from this
                log.error("jml.internal", "Exception while translating block: " + ee);
                break;
            }
        }
        while (iter.hasPrevious()) {
            JCStatement stat = iter.previous();
            try {
                if (stat instanceof JmlVariableDecl) {
                    continue;
                } else if (stat instanceof JmlStatementExpr) {
                    JmlStatementExpr s = (JmlStatementExpr)stat;
                    if (s.clauseType == assumeClause) {
                        if (s.label == Label.METHOD_DEFINITION) {
                            // skip
                        } else {
                        }
                    } else if (s.clauseType == assertClause) {
//                        IExpr exx = stack.pop();
//                        // The first return is the classic translation; the second
//                        // effectively inserts an assume after an assert. I'm not
//                        // sure it makes any difference. TODO - evaluate this sometime.
//                        //return F.fcn(F.symbol("and"), exx, tail);
//                        tail = F.fcn(andSym, exx, F.fcn(impliesSym, exx, tail));
                    } else if (s.clauseType == checkClause) {
//                        IExpr exx = stack.pop();
//                        // The first return is the classic translation; the second
//                        // effectively inserts an assume after an assert. I'm not
//                        // sure it makes any difference. TODO - evaluate this sometime.
//                        //return F.fcn(F.symbol("and"), exx, tail);
//                        tail = F.fcn(andSym, exx, tail);
                    } else if (s.clauseType == commentClause) {
//                        if (s.id == null || !s.id.startsWith("ACHECK")) continue;
//                        int k = s.id.indexOf(" ");
//                        k = Integer.valueOf(s.id.substring(k+1));
//                        if (k != assumeCount) continue;
//                        IExpr exx = stack.pop();
//                        tail = exx;
                    } else {
                        log.error("jml.internal", "Incorrect kind of token encountered when converting a BasicProgram to SMTLIB: " + s.keyword);
                        break;
                    }
                } else {
                    log.error("jml.internal", "Incorrect kind of statement encountered when converting a BasicProgram to SMTLIB: " + stat.getClass());
                    break;
                }
            } catch (RuntimeException ee) {
                // skip - error already issued // FIXME - better recovery
                break;
            }
        }
        return tail;
    }
    

    public IExpr convertList2(String blockid, List<JCStatement> list, IExpr tail) {
        ListIterator<JCStatement> iter = list.listIterator();
        Stack<IExpr> stack = new Stack<IExpr>();
        int count = 0;
        
        while (iter.hasNext()) {
            JCStatement stat = iter.next();
            try {
                if (stat instanceof JmlVariableDecl) {
                    JmlVariableDecl decl = (JmlVariableDecl)stat;
//                    if (!useFcnDef && decl.init != null) {
//                        IExpr exx = convertExpr(decl.init);
//                        exx = F.fcn(F.symbol("="), F.symbol(decl.name.toString()), exx);
//                        ISymbol newsym = F.symbol(blockid + "__A" + (++count));
//                        commands.add(new C_define_fun(newsym,new LinkedList<IDeclaration>(),boolSort,exx));
//                        stack.push(newsym);
//                    }
                    continue;
                } else if (stat instanceof JmlStatementExpr) {
                    JmlStatementExpr s = (JmlStatementExpr)stat;
                    if (s.clauseType == assumeClause) {
                        if (s.label == Label.METHOD_DEFINITION) {
//                            JCExpression ex = s.expression;
//                            ex = ((JmlQuantifiedExpr)ex).value;
//                            JCExpression lhs = ((JCTree.JCBinary)ex).lhs;
//                            JCTree.JCMethodInvocation mcall = (JCTree.JCMethodInvocation)lhs;
//                            JCExpression nm = mcall.meth;
//                            JCExpression rhs = ((JCTree.JCBinary)ex).rhs;
//                            addFunctionDefinition(nm.toString(),mcall.args,rhs);
                        } else {
                            convertExpr(s.expression);
//                            ISymbol newsym = F.symbol(blockid + "__A" + (++count));
//                            commands.add(new C_define_fun(newsym,new LinkedList<IDeclaration>(),boolSort,exx));
//                            stack.push(newsym);
                        }
                    } else if (s.clauseType == assertClause) {
                        convertExpr(s.expression);
                    } else if (s.clauseType == checkClause) {
                        convertExpr(s.expression);
                    } else if (s.clauseType == commentClause) {
//                        if (s.id == null || !s.id.startsWith("ACHECK")) continue;
//                        int k = s.id.indexOf(" ");
//                        k = Integer.valueOf(s.id.substring(k+1));
//                        s.optionalExpression = k != assumeCount ? null : (treeutils.falseLit);;
//                        if (k != assumeCount) continue;
                    } else {
                        log.error("jml.internal", "Incorrect kind of token encountered when converting a BasicProgram to SMTLIB: " + s.clauseType.keyword());
                        break;
                    }
                } else {
                    log.error("jml.internal", "Incorrect kind of statement encountered when converting a BasicProgram to SMTLIB: " + stat.getClass());
                    break;
                }
            } catch (JmlBVException ee) {
                throw ee;
            } catch (RuntimeException ee) {
                // There is no recovery from this
                log.error("jml.internal", "Exception while translating block: " + ee);
                ee.printStackTrace();
                break;
            }
        }
        int n = 0;
        while (iter.hasPrevious()) {
            JCStatement stat = iter.previous();
            try {
                if (stat instanceof JmlVariableDecl) {
                    continue;
                } else if (stat instanceof JmlStatementExpr) {
                    JmlStatementExpr s = (JmlStatementExpr)stat;
                    if (s.clauseType == assumeClause) {
//                        if (s.label == Label.METHOD_DEFINITION) {
//                            // skip
//                        } else {
//                            IExpr exx = stack.pop();
//                            tail = F.fcn(impliesSym, exx, tail);
//                            ++n;
//                        }
                    } else if (s.clauseType == assertClause) {
//                        IExpr exx = stack.pop();
//                        // The first return is the classic translation; the second
//                        // effectively inserts an assume after an assert. I'm not
//                        // sure it makes any difference. TODO - evaluate this sometime.
//                        //return F.fcn(andSym, exx, tail);
//                        tail = F.fcn(andSym, exx, F.fcn(impliesSym, exx, tail));
//                        ++n;
                    } else if (s.clauseType == checkClause) {
//                        IExpr exx = stack.pop();
//                        // The first return is the classic translation; the second
//                        // effectively inserts an assume after an assert. I'm not
//                        // sure it makes any difference. TODO - evaluate this sometime.
//                        //return F.fcn(andSym, exx, tail);
//                        tail = F.fcn(andSym, exx, F.fcn(impliesSym, exx, tail));
//                        ++n;
                    } else if (s.clauseType == commentClause) {
//                        if (s.id == null || !s.id.startsWith("ACHECK")) continue;
//                        int k = s.id.indexOf(" ");
//                        k = Integer.valueOf(s.id.substring(k+1));
//                        if (k != assumeCount) continue;
//                        IExpr exx = stack.pop();
//                        tail = exx;
                    } else {
                        log.error("jml.internal", "Incorrect kind of token encountered when converting a BasicProgram to SMTLIB: " + s.keyword);
                        break;
                    }
//                    if (n > 250) { // 250 is chosen just to make sure there is not a stack overflow if there is a huge basic block
//                        ISymbol nm = F.symbol("|##PTMP_" + (++ptmp)+ "##|");  // Just something that will not be encoutered elsewhere
//                        C_define_fun c = new C_define_fun(nm, new LinkedList<IDeclaration>(), boolSort, tail);
//                        commands.add(c);
//                        tail = nm;
//                        n = 0;
//
//                    }
                } else {
                    log.error("jml.internal", "Incorrect kind of statement encountered when converting a BasicProgram to SMTLIB: " + stat.getClass());
                    break;
                }
            } catch (RuntimeException ee) {
                // skip - error already issued // FIXME - better recovery
                break;
            }
        }
        return tail;
    }
    
    int ptmp = 0;

    /** Converts a basic block statement to an SMT expression, tacking it on
     * the front of tail and returning the composite expression.
     */
    public void convertStatement(JCStatement stat, IExpr tail) {
        try {
            if (stat instanceof JmlVariableDecl) {
                 return ;
            } else if (stat instanceof JmlStatementExpr) {
                JmlStatementExpr s = (JmlStatementExpr)stat;
                if (s.clauseType == assumeClause) {
                    convertExpr(s.expression);
                    return;
                } else if (s.clauseType == assertClause) {
                    convertExpr(s.expression);
                    return;
                } else if (s.clauseType == checkClause) {
                    convertExpr(s.expression);
                    return;
                } else if (s.clauseType == commentClause) {
                    return ;
                } else {
                    log.error("jml.internal", "Incorrect kind of token encountered when converting a BasicProgram to SMTLIB: " + s.keyword);
                }
            } else {
                log.error("jml.internal", "Incorrect kind of statement encountered when converting a BasicProgram to SMTLIB: " + stat.getClass());
            }
        } catch (RuntimeException ee) {
            // skip - error already issued // FIXME - better recovery
        }
        return ;
        
    }
    
    
    
    /** Converts an AST expression into SMT form. */
    public BV convertExpr(JCExpression expr, BV bvmode) {
        BV saved = this.bv;
        bv = bvmode;
        var res = convertExpr(expr);
        bv = saved;
        return res;
    }
    
    public BV convertExpr(JCExpression expr) {
        scan(expr);
        return result;
    }
    
    public void convertExprList(List<JCExpression> list, BV bvmode) {
        BV saved = this.bv;
        bv = bvmode;
        convertExprList(list);
        bv = saved;
    }
    
    public void convertExprList(List<JCExpression> list) {
        List<IExpr> newargs = new LinkedList<IExpr>();
        for (JCExpression e: list) {
            scan(e);
        }
    }
    
    // We need to be able to translate expressions
    
    /** Issues a error message about the AST node not being implemented */
    public void notImpl(JCTree tree) {
    	utils.error(tree, "esc.not.implemented","Not yet supported expression node in bit-vector scanning BasicPrograms: " + tree.getClass());
    }
    
    /** Issues an error message about something not being implemented */
    public void notImpl(DiagnosticPosition pos, String msg) {
    	utils.error(pos, "esc.not.implemented","Not yet supported feature in bit-vector scanning BasicPrograms: " + msg);
    }
    
    public static class JmlBVException extends RuntimeException {
		private static final long serialVersionUID = 1L;
    }
    
    /** Issues an error message about bit-vector operations */
    public void notImplBV(DiagnosticPosition pos, String msg) {
        if ("auto".equals(JmlOption.value(context, JmlOption.ESC_BV))) throw new JmlBVException();
        utils.error(pos, "jml.message","This method uses bit-vector operations and must be run with --esc-bv=true (or auto) [" + msg + "]");
        throw new JmlBVException();
    }
    
    /** Issues an error message about something not being implemented */
    public void notImplWarn(DiagnosticPosition pos, String msg) {
    	utils.warning(pos, "esc.not.implemented","Not yet supported feature in bit-vector scanning BasicPrograms: " + msg);
    }
    
    /** Issues an error message that a particular AST node should not be being used in the input basic block program */
    public void shouldNotBeCalled(JCTree tree) {
    	utils.error(tree, "jml.internal","This node should not be present in converting BasicPrograms to SMTLIB: " + tree.getClass() + " " + tree.toString());
    }
    
    /** A set to hold the names of implicit functions that have been defined so far
     * (so we don't duplicate definitions).
     */
    protected Set<String> fcnsDefined = new HashSet<String>();
    
    /** Adds a function with the given name and a definition if it is not already added. */
    protected void addFcn(String newname, JCMethodInvocation tree) {
        String bnewname = makeBarEnclosedString(newname);
        if (fcnsDefined.add(bnewname)) {
//            var rt = tree.type;
//            if (tree.meth.type != null) rt = tree.meth.type.getReturnType();
//            if (TreeInfo.symbolFor(tree.meth) != null) rt = TreeInfo.symbolFor(tree.meth).type.getReturnType();
//            // Was not already present
//            ISymbol n = F.symbol(bnewname);
//            ISort resultSort = convertSort(rt);
//            List<ISort> argSorts = new LinkedList<ISort>();
//            // Adds an argument for the receiver, if the function is not static
//            if (tree.meth instanceof JCFieldAccess && ((JCFieldAccess)tree.meth).selected != null && !((JCFieldAccess)tree.meth).sym.isStatic()) {  // FIXME _ JML sstatic?
//                argSorts.add(refSort);
//            }
//            for (JCExpression e: tree.args) {
//                argSorts.add(convertSort(e.type));
//            }
        }
        
    }
    
    protected void addFunctionDefinition(String newname, List<JCExpression> args, JCExpression expr) {
        String bnewname = makeBarEnclosedString(newname);
        if (fcnsDefined.add(bnewname)) {
            // Was not already present
//            ISymbol n = F.symbol(bnewname);
//            ISort resultSort = convertSort(expr.type);
//            List<IDeclaration> argDecls = new LinkedList<IDeclaration>();
//            // Adds an argument for the receiver, if the function is not static - TODO: do we ever use this?
//            if (tree.meth instanceof JCFieldAccess && ((JCFieldAccess)tree.meth).selected != null && !((JCFieldAccess)tree.meth).sym.isStatic()) {
//                argSorts.add(refSort);
//            }
            for (JCExpression e: args) {
//                IDeclaration d = F.declaration(F.symbol(e.toString()),convertSort(e.type));
//                argDecls.add(d);
            }
        }
        
    }
    
    // FIXME - review this
    @Override
    public void visitApply(JCMethodInvocation tree) {
        JCExpression m = tree.meth;
        if (m instanceof JCIdent) {
            String name = makeBarEnclosedString(((JCIdent)m).name.toString());
            String newname = name;
            addFcn(newname,tree);
            List<IExpr> newargs = new LinkedList<IExpr>();
            for (JCExpression arg: tree.args) {
                convertExpr(arg);
            }
            return;

        } else if (m == null) {
            if (tree instanceof JmlBBFieldAssignment) {
//                IExpr.IFcnExpr right = F.fcn(F.symbol("store"),
//                        convertExpr(tree.args.get(1)),
//                        convertExpr(tree.args.get(2)),
//                        convertExpr(tree.args.get(3))
//                        );
//                result = F.fcn(eqSym, convertExpr(tree.args.get(0)),right);
                return;
            }
            else if (tree instanceof JmlBBArrayAssignment) {
                if (tree.args.length() <= 3) {
//                    // [0] = store([1],[2], select([0],[2]))
//                    IExpr arg0 = convertExpr(tree.args.get(0));
//                    IExpr arg2 = convertExpr(tree.args.get(2));
//                    IExpr.IFcnExpr sel = F.fcn(selectSym,
//                            arg0,
//                            arg2
//                            );
//
//                    IExpr.IFcnExpr newarray = F.fcn(F.symbol("store"),
//                            convertExpr(tree.args.get(1)),
//                            arg2,
//                            sel
//                            );
//                    result = F.fcn(eqSym, arg0,newarray);
                } else if (tree.args.size() == 4) {
//                    // JML primitive array-like case
//                    // [0] = store([1], [2], [3])
//                    IExpr.IFcnExpr right = F.fcn(F.symbol("store"),
//                            convertExpr(tree.args.get(1)),
//                            convertExpr(tree.args.get(2)),
//                            convertExpr(tree.args.get(3))
//                            );
//                    result = F.fcn(eqSym, convertExpr(tree.args.get(0)),right);
                    
                } else {
//                    // [0] = store([1],[2], store(select([1],[2]),[3],[4]))
//                    IExpr.IFcnExpr sel = F.fcn(selectSym,
//                            convertExpr(tree.args.get(1)),
//                            convertExpr(tree.args.get(2))
//                            );
//                    IExpr.IFcnExpr newarray = F.fcn(F.symbol("store"),
//                            sel,
//                            convertExpr(tree.args.get(3)),
//                            convertExpr(tree.args.get(4))
//                            );
//
//                    IExpr.IFcnExpr right = F.fcn(F.symbol("store"),
//                            convertExpr(tree.args.get(1)),
//                            convertExpr(tree.args.get(2)),
//                            newarray
//                            );
//                    result = F.fcn(eqSym, convertExpr(tree.args.get(0)),right);
                }
                return;
            }
        } else if (m instanceof JCFieldAccess) {
            JCFieldAccess fa = (JCFieldAccess)m;
            String name = fa.name.toString();
            String newname = null;
//            if (Utils.instance(context).isJMLStatic(fa.sym)) {
//                // FIXME The fully qualifiedness should be done in BasicBlocking
//                newname = "_" + m.toString();
//                addFcn(newname,tree);
//            } else {
//                newname = fa.sym.owner.toString() + "." + name;
//                addFcn(newname,tree);
//            }
//            List<IExpr> newargs = new LinkedList<IExpr>();
//            if (!Utils.instance(context).isJMLStatic(fa.sym)) {
//                newargs.add(convertExpr(fa.selected));
//            }
//            for (JCExpression arg: tree.args) {
//                newargs.add(convertExpr(arg));
//            }
//            var sym = F.symbol(makeBarEnclosedString(newname));
//            result = newargs.isEmpty() ? sym : F.fcn(sym,newargs);
            
        }
    }
    
    /** Converts a JML function-like expression: 
     * \type, \typeof, <:, \nonnullelements
     *
     */
    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        if (that.kind == typelcKind) {
//            Type t = that.args.get(0).type;
//            addType(t);
//            result = that.javaType ? javaTypeSymbol(t) : jmlTypeSymbol(t);
            return;
        }
        convertExprList(that.args, bv);
//        if (that.kind == typeofKind) {
//            ISymbol s = that.javaType ? F.symbol("javaTypeOf") : F.symbol("jmlTypeOf");
//            result = F.fcn(s, newargs);
//        } else if (that.kind == nonnullelementsKind) {
//            result = F.fcn(F.symbol(nonnullelements), newargs);
//        } else if (that.kind == elemtypeKind) {
//            result = F.fcn(F.symbol(arrayElemType), newargs);
//        } else if (that.kind == sameKind || that.kind == oldKind) { // old has already been translated
//            result = newargs.get(0);
//        } else if (that.kind == erasureKind) {
//        	if (that.args.get(0).type == com.sun.tools.javac.comp.JmlAttr.instance(context).syms.classType) {
//        		result = F.fcn(F.symbol("erasure_java"), newargs);
//        	} else if (that.args.get(0).type.tsym == TYPE) {
//        		result = F.fcn(F.symbol("erasure"), newargs);
//        	} else {
//        		log.error("jml.internal","Unexpected argument type " + that.args.get(0).type + " " + that);
//        		result = null;
//        	}
//        } else if (that.kind == distinctKind) {
//            result = F.fcn(distinctSym, newargs);
//        } else if (that.kind == concatKind) {
//            if (newargs.size() != 0) {
//               Iterator<IExpr> iter = newargs.iterator();
//               result = iter.next();
//               while (iter.hasNext()) {
//                   result = F.fcn(F.symbol(concat), result, iter.next());
//               }
//            } else {
//                // ERROR - or empty string?
//                result = null;
//            }
//        } else if (that.kind == null) {
//        } else if (that.kind == subtypeofKind) {
//        } else if (that.kind == subtypeofeqKind) {
//            result = F.fcn(F.symbol(JMLSUBTYPE), newargs);
//        } else if (that.kind == jsubtypeofKind) {
//            result = F.fcn(F.symbol(JAVASUBTYPE), newargs);
//        } else if (that.kind == jsubtypeofeqKind) {
//            result = F.fcn(F.symbol(JAVASUBTYPE), newargs);
//        } else if (that.meth != null) {
//            // Built-in methods
//            String n = that.meth.toString();
//            if (n.equals("shortValue") || n.equals("byteValue") || n.equals("charValue") || n.equals("longValue")) n = "intValue";
//            else if (n.equals("floatValue") || n.equals("doubleValue")) n = "realValue";
//            result = F.fcn(F.symbol(n),newargs);
//        } else {
//            result = newargs.get(0); // FIXME - this is needed for \old and \pre but a better solution should be found (cf. testLabeled)
//        }
    }

    @Override
    public void visitNewClass(JCNewClass tree) {
        shouldNotBeCalled(tree);
        super.visitNewClass(tree);
        result = BV.NOT_INT;
    }

    @Override
    public void visitNewArray(JCNewArray tree) {
        shouldNotBeCalled(tree);
        super.visitNewArray(tree);
        result = BV.NOT_INT;
    }

    @Override
    public void visitAssign(JCAssign tree) {
        shouldNotBeCalled(tree);
        super.visitAssign(tree);
    }

    @Override
    public void visitAssignop(JCAssignOp tree) {
        shouldNotBeCalled(tree);
        super.visitAssignop(tree);
    }

    @Override
    public void visitUnary(JCUnary tree) {
        JCTree.Tag op = tree.getTag();
        result = convertExpr(tree.arg);
    }
    
    @Override public void visitParens(JCParens that) {
        // Since SMT-LIB consists of S-expressions, we do not need to 
        // add additional parentheses for resolving precedence
        super.visitParens(that);
    }


    @Override
    public void visitBinary(JCBinary tree) {
    	try {
        JCTree.Tag op = tree.getTag();
//        IExpr lhs = convertExpr(tree.lhs);
//        IExpr rhs = convertExpr(tree.rhs);
        TypeTag tlhs = tree.lhs.type.getTag();
        TypeTag trhs = tree.rhs.type.getTag();
        boolean isReal = false;
        boolean isInt = false;
        boolean isString = tree.lhs.type.tsym == STRING || tree.rhs.type.tsym == STRING;
        if (tree.lhs.type.tsym == REAL || tree.rhs.type.tsym == REAL) {
            isReal = true;
        } else if (tree.lhs.type.tsym == BIGINT || tree.rhs.type.tsym == BIGINT) {
            isInt = true;
        } else if (tlhs == TypeTag.DOUBLE || trhs == TypeTag.DOUBLE ||
                tlhs == TypeTag.FLOAT || trhs == TypeTag.FLOAT) {
            isReal = true;
        }
//        if (useBV) {
//            if (isReal) {
//                // skip
//            } else if (tree.type.getTag() == TypeTag.BOOLEAN) {
//                TypeTag max = bits(tlhs) > bits(trhs) ? tlhs : trhs;
//                lhs = castBV(max,tree.lhs.type.getTag(),lhs);
//                rhs = castBV(max,tree.rhs.type.getTag(),rhs);
//            } else {
//                lhs = castBV(tree.type.getTag(),tlhs,lhs);
//                rhs = castBV(tree.type.getTag(),trhs,rhs);
//            }
//        }
        switch (op) {
            case EQ:
            case NE:
                result = BV.EITHER; // FIXME ???
                break;
            case BITAND:
                if (tree.type.getTag() == TypeTag.BOOLEAN) {
                    result = BV.EITHER;
                } else {
//                    Object val;
//                    IExpr arg = null;
//                    JCLiteral num = null;
//                    result = null;
//                    if (tree.rhs instanceof JCLiteral) {
//                        arg = lhs;
//                        num = (JCLiteral)tree.rhs;
//                    } else if (tree.rhs instanceof JCTypeCast && ((JCTypeCast)tree.rhs).expr instanceof JCLiteral) {
//                        arg = lhs;
//                        num = (JCLiteral)((JCTypeCast)tree.rhs).expr;
//                    } else if (tree.lhs instanceof JCLiteral) {
//                        arg = rhs;
//                        num = (JCLiteral)tree.lhs;
//                    } else if (tree.lhs instanceof JCTypeCast && ((JCTypeCast)tree.lhs).expr instanceof JCLiteral) {
//                        arg = rhs;
//                        num = (JCLiteral)((JCTypeCast)tree.lhs).expr;
//                    }
//                    if (num.getValue() instanceof Number) {
//                        long v = ((Number)num.getValue()).longValue();
//                        if (v > 0 && Long.bitCount(v+1) == 1) {
//                            result = F.fcn(F.symbol("mod"), arg, F.numeral(v+1));
//                        }
//                    }
//                    if (result == null) notImplBV(tree, "Bit-operation " + op);
                }
                break;
            case BITOR:
                if (tree.type.getTag() == TypeTag.BOOLEAN) {
                    var lhs = convertExpr(tree.lhs, bv);
                    var rhs = convertExpr(tree.rhs, lhs);
                    if (lhs != rhs) convertExpr(tree.lhs, rhs);
                    result = rhs;
                } else {
                    var lhs = convertExpr(tree.lhs, BV.MUST_BV);
                    var rhs = convertExpr(tree.rhs, BV.MUST_BV);
                    result = BV.MUST_BV;
                }
                break;
            case BITXOR:
                if (tree.type.getTag() == TypeTag.BOOLEAN) {
                    var lhs = convertExpr(tree.lhs, bv);
                    var rhs = convertExpr(tree.rhs, lhs);
                    if (lhs != rhs) convertExpr(tree.lhs, rhs);
                    result = rhs;
                } else {
                    var lhs = convertExpr(tree.lhs, BV.MUST_BV);
                    var rhs = convertExpr(tree.rhs, BV.MUST_BV);
                    result = BV.MUST_BV;
                }
                break;
            default:
                {
                var lhs = convertExpr(tree.lhs, bv);
                var rhs = convertExpr(tree.rhs, lhs);
                if (lhs != rhs) convertExpr(tree.lhs, rhs);
                result = rhs;
                }
        }
    	} catch (JmlBVException e) {
    	    throw e;
        } catch (Exception e) {
            log.error("jml.internal","Exception while scanning expression for bit-vector: " + JmlPretty.write(tree));
        	System.out.println("EXCEPTION IN SUBEXPR OF " + tree);
        	e.printStackTrace(System.out);
        	throw e;
        }
    }

    @Override
    public void visitTypeCast(JCTypeCast tree) {
        TypeTag tagr = tree.type.getTag();
        TypeTag tage = tree.expr.type.getTag();
        result = convertExpr(tree.expr);
        boolean exprIsPrim = utils.isJavaOrJmlPrimitiveType(tree.expr.type);
        boolean treeIsPrim = utils.isJavaOrJmlPrimitiveType(tree.type);
        //System.out.println("TYPECAST " + tree.expr.type + " TO " + tree.type + " " + exprIsPrim + " " + treeIsPrim);
        Number value = null;
        if (tree.expr instanceof JCLiteral) {
            JCLiteral lit = (JCLiteral)tree.expr;
            if (lit.getValue() instanceof Number) {
                if (tagr == TypeTag.DOUBLE || tagr == TypeTag.FLOAT || ((tagr == TypeTag.NONE || tagr == TypeTag.UNKNOWN) && tree.type.tsym == REAL)) {
                    double d = ((Number)lit.getValue()).doubleValue();
                    result = BV.NOT_INT;
                    return;
                }
            }
        }
//        if (result instanceof Numeral) {
//            if (tree.type.getTag() == TypeTag.REAL) {
//                result = BV.NOT_INT;
//                return;
//            }
//        }
        if (treeIsPrim == exprIsPrim) {
            if (utils.isExtensionValueType(tree.type)) { 
                if (utils.isExtensionValueType(tree.expr.type)) { 
                    if (tree.type.tsym == REAL) {
                        if ( tree.expr.type.tsym == REAL) {
                            // \real to \real -- OK
                        } else if (tree.expr.type.tsym == BIGINT) {
                                // \bigint to \real
                                result = BV.NOT_INT;
                        } else {
                            // FIXME - error
                        }
                    } else if (tree.type.tsym == BIGINT) {
                        if ( tree.expr.type.tsym == REAL) {
                            // \real to \bigint
                            result = BV.NOT_INT;
                        } else if (tree.expr.type.tsym == BIGINT) {
                                // \bigint to \bigint -- OK
                        } else {
                            // FIXME - error
                        }
                    } else {
                        // FIXME - error
                    }
                    
                } else if (treeutils.isIntegral(tage)) {
                    if ( tree.type.tsym == REAL) {
                        // int to \real
                        result = BV.NOT_INT;
                    } else if (tree.type.tsym == BIGINT) {
                        // int to \bigint -- OK
                    } else {
                        // FIXME - error
                    }
                } else {
                    if ( tree.type.tsym == REAL) {
                        // float/double to \real -- OK
                    } else if (tree.type.tsym == BIGINT) {
                        // float/double to \bigint
                        result = BV.NO_BV;
                    } else {
                        // FIXME - error
                    }
                }
            } else if (utils.isExtensionValueType(tree.expr.type)) { 
                if (treeutils.isIntegral(tagr)) {
                    if (tree.expr.type.tsym == REAL) {
                        // \real to int -- FIXME
                        result = BV.NO_BV;
                    } else if (tree.expr.type.tsym == BIGINT) {
                        // \bigint to int -- OK
                    } else {
                        // FIXME - error
                    }
                } else {
                    result = BV.NOT_INT;
                    if (tree.expr.type.tsym == REAL) {
                        // \real to float/double -- OK
                    } else if (tree.expr.type.tsym == BIGINT) {
                        // \bigint to float/double -- FIXME
                    } else {
                        // FIXME - error
                    }
                }
            } else if (!treeIsPrim) {
                // This is a cast from reference type to reference type, we can ignore it
            } else if (tree.expr instanceof JCLiteral) {
                // Cast from one primitive literal to a another primitive type
                // Note that in SMT there is only Int and Real types (or bit-value types)
                // any restrictions on the range of a value must already be stated using assertions 
                Object v = ((JCLiteral)tree.expr).getValue();
                if (tage == tagr) {
                    // OK -- no change in type
                } else if (treeutils.isIntegral(tage) && treeutils.isIntegral(tagr)) {
                    // Both are integral
                	if (useBV && tage != tagr) {
//                	    result = castBV(tagr, tage, result);
                   	}
                } else if (!treeutils.isIntegral(tage) && !treeutils.isIntegral(tagr)) {
                    // Both are floating point
                    // OK -- no change in SMT type
                } else if (treeutils.isIntegral(tage)) {
                    // integral to real literal
                    result = BV.NOT_INT;
                } else if (!treeutils.isIntegral(tage)) {
                    // FIXME - cast from double to integral
                } else if (tagr.ordinal() == TypeTag.DOUBLE.ordinal() || tagr.ordinal() == TypeTag.FLOAT.ordinal()) {
                    // Cast to real FIXME - already done?
                    result = BV.NOT_INT;
                }
            } else {
                // cast from primitive to primitive for an expression
                boolean argIsInt = treeutils.isIntegral(tage);
                boolean resultIsInt = treeutils.isIntegral(tagr);
                if (argIsInt && !resultIsInt) {
                    // Requires int and real logic
                    // integral to real
                    result = BV.NOT_INT;
                } else if (!argIsInt && resultIsInt) {
                    // Requires int and real logic
                    // real to int
                    result = BV.NO_BV;
                } else if (argIsInt && resultIsInt) {
                    if (tage != tagr) {
                        int be = bits(tage);
                        int br = bits(tagr);
                        if (useBV) {
                            if (be > br) {
//                                List<INumeral> args = new LinkedList<>();
//                                args.add(F.numeral(br-1));
//                                args.add(F.numeral(0));
//                                result = F.fcn(F.id(F.symbol("extract"),args),result);
                                result = BV.MUST_BV;
                            } else if (br > be) {
//                                List<INumeral> args = new LinkedList<>();
//                                args.add(F.numeral(br-be));
//                                result = F.fcn(F.id(F.symbol("sign_extend"),args),result);
                                result = BV.MUST_BV;
                            }
                        } else {
//                            if (be > br) {
//                                if (br == 32) result = F.fcn(F.symbol("|#trunc32s#|"), result);
//                                if (br == 16) result = F.fcn(F.symbol("|#trunc16s#|"), result);
//                                if (br == 8) result = F.fcn(F.symbol("|#trunc8s#|"), result);
//                            }
                            result = bv; // FIXME ???
                        }
                    }

                } else {
                    // no change in result
                    result = bv; // FIXME ???
                }
            }
        } else if (!treeIsPrim) {
            // Cast from primitive to object
        	utils.error(tree,"jml.internal","Do not expect casts to reference type in expressions: " + JmlPretty.write(tree));
        } else {
            // unboxing cast from object to primitive
        	utils.error(tree,"jml.internal","Do not expect casts from reference type in expressions: " + JmlPretty.write(tree));
            TypeTag tag = tree.type.getTag();
            switch (tag) {
                case INT:
                case LONG:
                case SHORT:
                case BYTE:
                case CHAR:
                case DOUBLE:
                case FLOAT:
                case BOOLEAN:
                    // FIXME - should this ever happen?
                    break;
                default:
                	utils.error(tree,"jml.internal","Unknown type tag in translating an unboxing cast: " + tag + " " + JmlPretty.write(tree));
                    
            }
        }
    }
    
    public void castBV(TypeTag resulttag, TypeTag exprtag, IExpr expr) {
//        int be = bits(exprtag);
//        int br = bits(resulttag);
//        if (be > br) {
//            if (br == 0) Utils.stop();
//            List<INumeral> args = new LinkedList<>();
//            args.add(F.numeral(br-1));
//            args.add(F.numeral(0));
//            return F.fcn(F.id(F.symbol("extract"),args),expr);
//        } else if (be < br) {
//            List<INumeral> args = new LinkedList<>();
//            args.add(F.numeral(br-be));
//            return F.fcn(F.id(F.symbol("sign_extend"),args),expr);
//        } else {
//            return expr;
//        }
    }
    
    public int bits(TypeTag tag) {
    	switch (tag) {
    	case BYTE: return 8;
    	case INT: return 32;
        case SHORT: return 16;
        case CHAR: return 16;
    	case LONG: return 64;
    	case FLOAT: return 32;
    	case DOUBLE: return 64;
    	default: return 0;
    	}
    }

    @Override
    public void visitTypeTest(JCInstanceOf tree) {
        convertExpr(tree.expr);
    }
    


    @Override
    public void visitIndexed(JCArrayAccess tree) {
        if (tree instanceof JmlBBArrayAccess) {
//            JmlBBArrayAccess aa = (JmlBBArrayAccess)tree;
//            // select(select(arraysId,a).i)
//            String typeString = typeString(aa.indexed.type);
//            //System.out.println("AACCESS " + tree + " " + tree.indexed.type + " " + tree.indexed.type.getClass() + " " + typeString );
//            
//            if (typeString.startsWith("org_jmlspecs_lang_")) { // FIXME - find a way to do better than string checking
//            	result = F.fcn(selectSym,
//            			convertExpr(aa.indexed),
//            			convertExpr(aa.index)
//            			);
//            } else {
//            	IExpr.IFcnExpr sel = F.fcn(selectSym,
//            			convertExpr(aa.arraysId),
//            			convertExpr(aa.indexed)
//            			);
//            	sel = F.fcn(selectSym,
//            			sel,
//            			convertExpr(aa.index)
//            			);
//            	result = sel;
//            }
            return; // FIXME
        }

        shouldNotBeCalled(tree);
    }
    
    @Override 
    public void visitConditional(JCConditional that) { 
//        result = F.fcn(F.symbol("ite"), 
//                convertExpr(that.cond), 
//                convertExpr(that.truepart), 
//                convertExpr(that.falsepart)
//                ); // FIXME
    }


    
    @Override
    public void visitSelect(JCFieldAccess tree) {
        result = convertExpr(tree.selected, BV.EITHER);
        bvmap.put(tree, result);
    }
    
    @Override
    public void visitIdent(JCIdent tree) {
        result = bvmap.get(tree.sym);
        if (result == null) result = BV.EITHER;
    }
    
    @Override
    public void visitLiteral(JCLiteral tree) {
        if (tree.typetag == TypeTag.BOOLEAN) {
           result = BV.EITHER; 
        } else if (tree.typetag == TypeTag.INT || tree.typetag == TypeTag.LONG || tree.typetag == TypeTag.SHORT || tree.typetag == TypeTag.BYTE) {
            result = BV.EITHER; 
        } else if (tree.typetag == TypeTag.CHAR) {
            result = BV.EITHER; 
        } else if (tree.typetag == TypeTag.BOT) {
            result = BV.EITHER;
        } else if (tree.typetag == TypeTag.CLASS) {
            result = BV.NOT_INT;
        } else if (tree.typetag == TypeTag.FLOAT || tree.typetag == TypeTag.DOUBLE) {
            result = BV.NOT_INT;
        } else {
            notImpl(tree);
            super.visitLiteral(tree);
        }
        bvmap.put(tree, result);
    }
    
    
    protected String makeBarEnclosedString(JCTree tree) {
        String s = tree.toString();
        return makeBarEnclosedString(s);
    }
    protected static String makeBarEnclosedString(String s) {
        if (s.startsWith("arrays")) return s;
        if (s.charAt(0) == '|') return s;
        s = s.replace('|','#').replace('\n', ' ').replace("\r","").replace("\\","#");
        if (s.length() > 40) {
            s = s.substring(0, 40) + s.hashCode();
        }
        s = "|" + s + "|";
        return s;
    }
    
    protected String makePQBarEnclosedString(JCIdent id) {
        String nm;
        if (id.sym == null || id.sym.owner == null || !(id.sym.owner instanceof Symbol.ClassSymbol)) {
            // This is the case for generated names or local names
            nm = makeBarEnclosedString(id.name.toString());
        } else if (Utils.instance(context).isJMLStatic(id.sym)) {
            String ostr = id.sym.owner.toString();
            String nstr = id.name.toString();
            // FIXME: SHould not have to do this check -- means that naming is inconsistent in JmlAssertionAdder or BasicBlocker2
            if (!nstr.startsWith(ostr)) nstr = ostr + "_" + nstr;
            nm = makeBarEnclosedString(nstr);
        } else {
            nm = makeBarEnclosedString(id.sym.owner.toString() + "_" + id.name.toString());
        }
        return nm;
    }
    
    @Override
    public void visitReference(JCTree.JCMemberReference that) {
        result = BV.NOT_INT;
        bvmap.put(that, result);
    }
    
    Set<ISymbol> functionSymbols = new HashSet<ISymbol>();
    
    @Override 
    public void visitLambda(JCTree.JCLambda that) {
//        String s = makeBarEnclosedString(that);
//        ISymbol sym = F.symbol(s);
//        functionSymbols.add(sym);
//        addConstant(sym, refSort, that);
////        if (addConstant(sym, refSort, that)) {
////            IExpr e = F.fcn(distinctSym, sym, nullSym);
////            ICommand c = new C_assert(e);
////            commands.add(c);
////        }
        result = BV.NOT_INT;
        bvmap.put(that, result);
   }



    @Override public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) { notImpl(that); } // FIXME - maybe
    @Override public void visitJmlSetComprehension(JmlSetComprehension that)   { notImpl(that); }
    @Override public void visitJmlSingleton(JmlSingleton that)                 { notImpl(that); }
    @Override public void visitJmlRange(JmlRange that) { 
    	convertExpr(that.lo, BV.NO_BV);
    	convertExpr(that.hi, BV.NO_BV);
    	result = BV.NOT_INT;
    	bvmap.put(that, result);
    }

    @Override public void visitLetExpr(LetExpr that) { 
        
//        Iterator<JCStatement> iter = that.defs.iterator();
//        result = doLet(iter,that.expr);
    }
    
    // We need to create nested let expressions because the SMT let expression
    // does parallel bindings of initializers to variables, while Java does
    // sequential bindings. So we also need unique bound identifiers.
    private void doLet(Iterator<JCStatement> iter, JCExpression expr) {
//    	// FIXME
//        if (iter.hasNext()) {
//            JCVariableDecl decl = (JCVariableDecl)iter.next();
//            IExpr.ISymbol sym = F.symbol(makeBarEnclosedString(decl.name.toString()));
//            IExpr e = convertExpr(decl.init);
//            List<IBinding> bindings = new LinkedList<IBinding>();
//            bindings.add(F.binding(sym,e));
//            return F.let(bindings, doLet(iter,expr));
//        } else {
//            return convertExpr(expr);
//        }
    }

    @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        boolean prev = inQuant;
        try {
            IExpr typeConstraint = null;
            inQuant = true;
            List<IDeclaration> params = new LinkedList<IDeclaration>();
//            for (JCVariableDecl decl: that.decls) {
//                IExpr.ISymbol sym = F.symbol(makeBarEnclosedString(decl.name.toString()));
//                ISort sort = convertSort(decl.type);
//                params.add(F.declaration(sym, sort));
//                if (decl.type.isPrimitive() && sort == intSort && !decl.type.toString().contains("\\")) {
//                    IExpr c = makeTypeConstraint(decl.type, sym);
//                    typeConstraint = typeConstraint == null ? c : F.fcn(andSym, typeConstraint, c);
//                }
//            }
            scan(that.range);
            var range = result;
            scan(that.value);
            var value = result;
            switch (that.kind.keyword()) {
            case QuantifiedExpressions.qforallID:
//                if (range != null) value = F.fcn(impliesSym,range,value);
//                if (typeConstraint != null && (that.range == null || treeutils.isTrueLit(that.range))) value = F.fcn(impliesSym, typeConstraint, value);
//                if (that.triggers != null && !that.triggers.isEmpty()) {
//                    List<IExpr> triggers = convertExprList(that.triggers);
//                    result = F.forall(params,value,triggers);
//                } else {
//                    result = F.forall(params,value);
//                }
                result = BV.EITHER;
                break;
            case QuantifiedExpressions.qexistsID:
//                if (range != null) value = F.fcn(andSym,range,value);
//                if (typeConstraint != null && (that.range == null || treeutils.isTrueLit(that.range))) value = F.fcn(andSym, typeConstraint, value);
//                if (that.triggers != null && !that.triggers.isEmpty()) {
//                    List<IExpr> triggers = convertExprList(that.triggers);
//                    result = F.exists(params,value,triggers);
//                } {
//                    result = F.exists(params,value);
//                }
                result = BV.EITHER;
                break;
            default:
//                notImplWarn(that, "JML Quantified expression using " + that.kind.keyword());
//                ISymbol sym = F.symbol(makeBarEnclosedString(that));
//                addConstant(sym,convertSort(that.type),null);
//                result = sym;
            }
            // Can't do this, because then the quantified expression is evaluated
            // in the wrong context (I think)
//            if (false && !prev) {
//                // Because SMTLIB does not allow getValue to have arguments containing
//                // quantifiers, we do the following: as long as the quantified
//                // expression is not nested within another (technically could be
//                // as long as it is closed), we define a temporary variable to
//                // hold its value. We could use named 
//                // SMTLIB expressions, but I'm not sure how widespread support
//                // for that feature is.
//                ISymbol tmp = F.symbol("_JMLSMT_tmp_" + (++uniqueCount));
//                ICommand c = new C_declare_fun(tmp,emptyList,boolSort);
//                commands.add(c);
//                c = new C_assert(F.fcn(eqSym,  tmp, result));
//                commands.add(c);
//                result = tmp;
//            }
        } finally {
            inQuant = prev;
        }
    }

    // FIXME - review and implement all these generic type visit functions,
    // or declare that they should not be called
    
    @Override
    public void visitTypeIdent(JCPrimitiveTypeTree tree) {
        notImpl(tree);
        super.visitTypeIdent(tree);
    }

    @Override
    public void visitTypeArray(JCArrayTypeTree tree) {
        notImpl(tree);
        super.visitTypeArray(tree);
    }

    @Override
    public void visitTypeApply(JCTypeApply tree) {
        notImpl(tree);
        super.visitTypeApply(tree);
    }

    @Override
    public void visitTypeUnion(JCTypeUnion tree) {
        notImpl(tree);
        super.visitTypeUnion(tree);
    }

    @Override
    public void visitTypeParameter(JCTypeParameter tree) {
        notImpl(tree);
        super.visitTypeParameter(tree);
    }

    @Override
    public void visitWildcard(JCWildcard tree) {
        notImpl(tree);
        super.visitWildcard(tree);
    }

    @Override
    public void visitTypeBoundKind(TypeBoundKind tree) {
        notImpl(tree);
        super.visitTypeBoundKind(tree);
    }
    
    // These should all be translated away prior to calling the basic blocker,
    // or should never be called in the first place, because they are not
    // expressions
    // FIXME - what about calls of anonymous classes
    @Override public void visitTopLevel(JCCompilationUnit that)    { shouldNotBeCalled(that); }
    @Override public void visitImport(JCImport that)               { shouldNotBeCalled(that); }
    @Override public void visitMethodDef(JCMethodDecl that)        { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodDecl(JmlMethodDecl that)  { shouldNotBeCalled(that); }
    @Override public void visitJmlBinary(JmlBinary that)           { shouldNotBeCalled(that); }
    @Override public void visitJmlChoose(JmlChoose that)           { shouldNotBeCalled(that); }
    @Override public void visitJmlClassDecl(JmlClassDecl that)           { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodSig(JmlMethodSig that) { shouldNotBeCalled(that); }
    @Override public void visitJmlDoWhileLoop(JmlDoWhileLoop that)  { shouldNotBeCalled(that); }
    @Override public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) { shouldNotBeCalled(that); }
    @Override public void visitJmlForLoop(JmlForLoop that) { shouldNotBeCalled(that); }
    @Override public void visitJmlGroupName(JmlGroupName that) { shouldNotBeCalled(that); }
    @Override public void visitJmlLblExpression(JmlLblExpression that) { shouldNotBeCalled(that); }    
    @Override public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) { shouldNotBeCalled(that); }
    @Override public void visitJmlMethodSpecs(JmlMethodSpecs that)           { shouldNotBeCalled(that); }
    @Override public void visitJmlModelProgramStatement(JmlModelProgramStatement that) { shouldNotBeCalled(that); }
    @Override public void visitJmlSpecificationCase(JmlSpecificationCase that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementDecls(JmlStatementDecls that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementExpr(JmlStatementExpr that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementLoopExpr(JmlStatementLoopExpr that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementLoopModifies(JmlStatementLoopModifies that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStatementSpec(JmlStatementSpec that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) { shouldNotBeCalled(that); }
    @Override public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseIn(JmlTypeClauseIn that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) { shouldNotBeCalled(that); }
    @Override public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) { shouldNotBeCalled(that); }
    @Override public void visitJmlVariableDecl(JmlVariableDecl that) { shouldNotBeCalled(that); }
    @Override public void visitJmlWhileLoop(JmlWhileLoop that) { shouldNotBeCalled(that); }

    @Override public void visitClassDef(JCClassDecl that) { shouldNotBeCalled(that); }
    @Override public void visitVarDef(JCVariableDecl that)  { shouldNotBeCalled(that); }
    @Override public void visitSkip(JCSkip that) { shouldNotBeCalled(that); }
    @Override public void visitBlock(JCBlock that) { shouldNotBeCalled(that); }
    @Override public void visitDoLoop(JCDoWhileLoop that) { shouldNotBeCalled(that); }
    @Override public void visitWhileLoop(JCWhileLoop that) { shouldNotBeCalled(that); }
    @Override public void visitForLoop(JCForLoop that) { shouldNotBeCalled(that); }
    @Override public void visitForeachLoop(JCEnhancedForLoop that) { shouldNotBeCalled(that); }
    @Override public void visitLabelled(JCLabeledStatement that) { shouldNotBeCalled(that); }
    @Override public void visitSwitch(JCSwitch that) { shouldNotBeCalled(that); }
    @Override public void visitCase(JCCase that) { shouldNotBeCalled(that); }
    @Override public void visitSynchronized(JCSynchronized that) { shouldNotBeCalled(that); }
    @Override public void visitTry(JCTry that) { shouldNotBeCalled(that); }
    @Override public void visitCatch(JCCatch that) { shouldNotBeCalled(that); }
    @Override public void visitIf(JCIf that) { shouldNotBeCalled(that); }
    @Override public void visitExec(JCExpressionStatement that) { shouldNotBeCalled(that); }
    @Override public void visitBreak(JCBreak that) { shouldNotBeCalled(that); }
    @Override public void visitContinue(JCContinue that) { shouldNotBeCalled(that); }
    @Override public void visitReturn(JCReturn that) { shouldNotBeCalled(that); }
    @Override public void visitThrow(JCThrow that) { shouldNotBeCalled(that); }
    @Override public void visitAssert(JCAssert that) { shouldNotBeCalled(that); }
    @Override public void visitAnnotation(JCAnnotation that) { shouldNotBeCalled(that); }
    @Override public void visitModifiers(JCModifiers that) { shouldNotBeCalled(that); }
    @Override public void visitErroneous(JCErroneous that) { shouldNotBeCalled(that); }

}
