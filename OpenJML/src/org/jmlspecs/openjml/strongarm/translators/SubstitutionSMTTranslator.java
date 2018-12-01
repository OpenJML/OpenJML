package org.jmlspecs.openjml.strongarm.translators;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.esc.BasicProgram;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;
import org.jmlspecs.openjml.esc.SMTTranslator;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.ISort;
import org.smtlib.SMT;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.command.C_assert;
import org.smtlib.command.C_check_sat;
import org.smtlib.command.C_declare_fun;
import org.smtlib.command.C_declare_sort;
import org.smtlib.command.C_define_fun;
import org.smtlib.command.C_push;
import org.smtlib.command.C_set_logic;
import org.smtlib.command.C_set_option;
import org.smtlib.impl.Script;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.util.Context;

public class SubstitutionSMTTranslator extends SMTTranslator {

    public SubstitutionSMTTranslator(Context context, String source) {
        super(context, source);
    }

    
    /**
     * Write out a proof for proposition equality to reduce redundant preconditions. 
     */
//   z @Override
//    public ICommand.IScript convert(BasicProgram program, SMT smt) {
//        script = new Script();
//        ICommand c;
//        commands = script.commands();
//        
//        // FIXME - use factory for the commands?
//        // set any options
//        c = new C_set_option(F.keyword(":produce-models"),F.symbol("true"));
//        commands.add(c);
//        
//        // set the logic
//        String s = JmlOption.value(context, JmlOption.LOGIC);
//        c = new C_set_logic(F.symbol(s));
//        commands.add(c);
//        
//        // add background statements
//        // declare the sorts we use to model Java+JML
//        // (declare-sort REF 0)
//        c = new C_declare_sort(F.symbol(REF),zero);
//        commands.add(c);
//        // define NULL as a REF: (declare-fun NULL () REF)
//        c = new C_declare_fun(nullSym,emptyList, refSort);
//        commands.add(c);
//        // define THIS as a REF: (declare-fun THIS () REF)
//        c = new C_declare_fun(thisSym,emptyList, refSort);
//        commands.add(c);
//        // define stringConcat: (declare-fun stringConcat (REF,REF) REF)
//        c = new C_declare_fun(F.symbol(concat),Arrays.asList(refSort,refSort), refSort);
//        commands.add(c);
//        // define stringLength: (declare-fun stringLength (REF) Int)
//        c = new C_declare_fun(F.symbol("stringLength"),Arrays.asList(refSort), intSort); // FIXME - not sure this =is used
//        commands.add(c);
//        // THIS != NULL: (assert (distinct THIS NULL))
//        c = new C_assert(F.fcn(distinctSym, thisSym, nullSym)); // SMT defined name
//        commands.add(c);
//        // (assert __JMLlength () (Array REF Int))
//        c = new C_declare_fun(lengthSym,
//                emptyList, 
//                F.createSortExpression(arraySym,refSort,intSort)
//                );
//        commands.add(c);
//
//            // array lengths are always non-negative
//        addCommand(smt,"(assert (forall ((o "+REF+")) (>= (select "+arrayLength+" o) 0)))");
//            // result of string concatenation is always non-null
//        addCommand(smt,"(assert (forall ((s1 "+REF+")(s2 "+REF+")) (distinct ("+concat+" s1 s2) "+NULL+")))");
//
//        // The following functions model aspects of Java+JML;
//        // The strings here are arbitrary except that they must not conflict with 
//        // identifiers from the Java program as mapped into SMT identifiers
//        List<ISort> args = Arrays.asList(refSort); // List of one element 
//        c = new C_declare_fun(F.symbol("asIntArray"),args, F.createSortExpression(arraySym,intSort,intSort));
//        commands.add(c);
//        c = new C_declare_fun(F.symbol("asREFArray"),args, F.createSortExpression(arraySym,intSort,refSort));
//        commands.add(c);
//        c = new C_declare_fun(F.symbol("intValue"),args, intSort);
//        commands.add(c);
//        c = new C_declare_fun(F.symbol("booleanValue"),args, boolSort);
//        commands.add(c);
//        c = new C_declare_fun(lengthSym,
//                Arrays.asList(new ISort[]{refSort}), 
//                intSort);
//        
//        int loc = addTypeModel(smt);
//        
//        // List types that we always want defined in the SMT script, whether
//        // or not they are explicitly used in the input program 
//        addType(syms.objectType);
//        addType(syms.exceptionType);
//        addType(syms.runtimeExceptionType);
//        
//        // Now translate all the programs background assertions
//        for (JCExpression e: program.background()) {
//            try {
//                scan(e);
//                commands.add(new C_assert(result));
//            } catch (RuntimeException ee) {
//                // skip - error already issued // FIXME - better error recovery?
//            }
//        }
//        
//        // The 'defined' set holds all Names that have already had SMT definitions issued
//        // We have already defined some names - record that fact.
//        
//        defined.add(names.fromString(this_));
//        defined.add(names.fromString(arrayLength));
//        
//        // Add the rest that are recorded in the basic block program
//        for (JCIdent id: program.declarations) {
//            if (defined.add(id.name)) {
//                try {
//                    ISort sort = convertSort(id.type);
//                    String nm = id.name.toString();
//                    // FIXME - I don't think 'this' should ever get this far
//                    if (id.sym.owner instanceof Symbol.ClassSymbol && !Utils.instance(context).isJMLStatic(id.sym) && !id.sym.name.toString().equals("this")) {
//                        // The name is a non-static field of a class, so the sort is an SMT Array
//                        sort = F.createSortExpression(arraySym,refSort,sort);
//                    } else if (nm.startsWith(arrays_)) {
//                        // FIXME - review modeling of arrays
//                        sort = convertSort(((Type.ArrayType)id.type).getComponentType());
//                        sort = F.createSortExpression(arraySym,intSort,sort); // The type of the index is Int
//                        sort = F.createSortExpression(arraySym,refSort,sort);
//                    }
//                    ISymbol sym = F.symbol(nm);
//                    c = new C_declare_fun(sym,emptyList,sort);
//                    commands.add(c);
//                    bimap.put(id,sym);
//                } catch (RuntimeException ee) {
//                    // skip - error already issued// FIXME - better error recovery?
//                }
//            }
//        }
//        
//        // add definitions
//        for (BasicProgram.Definition e: program.definitions()) {
//            try {
//                scan(e.value);
//                ISymbol sym = F.symbol(e.id.toString());
//                c = new C_define_fun(sym,
//                        new LinkedList<IDeclaration>(),
//                        convertSort(e.id.type),
//                        result);
//                commands.add(c);
//                bimap.put(e.id,sym);
//            } catch (RuntimeException ee) {
//                // skip - error already issued // FIXME - better error recovery?
//            }
//        }
//        
//        // Because blocks have forward references to later blocks, but
//        // backward references to variables in earlier blocks, we declare
//        // all the block variables first
//        for (BasicProgram.BasicBlock b: program.blocks()) {
//            ICommand cc = new C_declare_fun(F.symbol(b.id.toString()), emptyList, F.Bool());
//            commands.add(cc);
//        }
//        
//        // add blocks
//        for (BasicProgram.BasicBlock b: program.blocks()) {
//            convertBasicBlock(b);
//        }
//        
//        {
//            // Add an assertion that negates the start block id
//            LinkedList<IExpr> argss = new LinkedList<IExpr>();
//            argss.add(F.symbol(program.startId().name.toString()));
//            IExpr negStartID = F.fcn(F.symbol("not"), argss);
//            ICommand cc = new C_assert(negStartID);
//            commands.add(cc);
//        }
//        
//        // (push 1)
//        ICommand cc = new C_push(F.numeral(1));
//        commands.add(cc);
//        // (assert (= __JML_AssumeCheck 0)) 
//        cc = new C_assert(F.fcn(eqSym,F.symbol(JmlAssertionAdder.assumeCheckVar),zero));
//        commands.add(cc);
//        // (push 1)
//        cc = new C_push(F.numeral(1));
//        commands.add(cc);
//        // (check-sat)
//        cc = new C_check_sat();
//        commands.add(cc);
//        
//        addTypeRelationships(loc,smt);
//        
//        return script;
//
//    }

}
