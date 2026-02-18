/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;
// FIXME- NEEDS REVIEW; use an interface?

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.smtlib.IExpr.*;
import org.smtlib.ISort.*;
import org.smtlib.impl.SMTExpr;
import org.smtlib.sexpr.ISexpr;
import org.smtlib.sexpr.ISexpr.ISeq;

/** This class is a visitor that type-checks a formula */
public class TypeChecker extends IVisitor.NullVisitor</*@Nullable*/ ISort> {

	/** Compilation of errors */
	public List<IResponse> result = new LinkedList<IResponse>();

	/** A reference to the current symbol table */
	private SymbolTable symTable;

	/** A reference to the current configuration */
	private SMT.Configuration smtConfig;
	
	/** A reference to the map in which to keep type information */
	private /*@Nullable*/ Map<IExpr,ISort> typemap;
	
	private ISymbol isClosed = null;

	/** Constructs a formula typechecker from the current
	 * symbol table and type map
	 */
	private TypeChecker(SymbolTable symTable, Map<IExpr,ISort> typemap) {
		this.symTable = symTable;
		this.smtConfig = symTable.smtConfig;
		this.typemap = typemap;
	}
	
	/** Constructs a type checker without keeping a type map */
	public TypeChecker(SymbolTable symTable) {
		this(symTable,null);
	}
	
	/** Utility method for recording an error */
	protected void error(String msg, IPos pos) {
		result.add(smtConfig.responseFactory.error(msg,pos));
	}
	
	/** Utility method for printing an expression, using the default printer */
	protected String pr(IExpr e) {
		return smtConfig.defaultPrinter.toString(e);
	}

	/** Utility method for printing a sort, using the default printer */
	protected String pr(ISort e) {
		return smtConfig.defaultPrinter.toString(e);
	}

	/** The main entry point for type-checking an ISort.*/
	public static List<IResponse> checkSort(SymbolTable symTable, ISort expr) {
		TypeChecker f = new TypeChecker(symTable,null);
		try {
			expr.accept(f);
		} catch (IVisitor.VisitorException e) {
			f.error("Visitor Exception: " + e.getMessage(), e.pos());
		}
		return f.result;
	}

	public static List<IResponse> checkSortAbbreviation(SymbolTable symTable, IIdentifier id, List<ISort.IParameter> params, ISort expr) {
		TypeChecker f = new TypeChecker(symTable,null); // FIXME - we should use a factory
		symTable.push();
		boolean errors = false;
		try {
            symTable.logicInUse.checkSortDeclaration(id,params,expr);
			if (params != null) for (ISort.IParameter p : params) {
				boolean b = symTable.addSortParameter(p.symbol());
				if (!b) {
					f.error("Duplicate sort parameters: " + p.symbol(),p.pos());
					errors = true;
				}
			}
			if (!errors && expr != null) expr.accept(f);
		} catch (IVisitor.VisitorException e) {
			f.error("Error while checking sort abbreviation: " + e.getMessage(),id.pos());
		} catch (Exception e) {
			f.error("INTERNAL ERROR: Exception while checking sort abbreviation: " + e.getMessage(),expr.pos());
		} finally {
			symTable.pop();
		}
		return f.result;
	}
	
	public static List<IResponse> checkFcn(SymbolTable symTable, IIdentifier id, List<ISort> sorts, ISort result, IPos pos) {
		TypeChecker f = new TypeChecker(symTable,null);
		try {
			for (ISort p : sorts) {
				p.accept(f);
			}
			ISort newresult = result.accept(f);
			try {
				symTable.logicInUse.checkFcnDeclaration(id,sorts,newresult,null);
			} catch (IVisitor.VisitorException e) {
				f.error(e.getMessage(), e.pos());
			}
		} catch (IVisitor.VisitorException e) {
			f.error("INTERNAL ERROR: Exception while checking sort abbreviation: " + e.getMessage(), pos);
		} catch (Exception e) {
			f.error("INTERNAL ERROR: Exception while checking sort abbreviation: " + e.getMessage(), null);
		}
		return f.result;
		
	}

	public static List<IResponse> checkFcn(SymbolTable symTable, Map<IExpr,ISort> typemap, IIdentifier id, List<IDeclaration> params, ISort result, IExpr expr, IPos pos) {
		TypeChecker f = new TypeChecker(symTable,typemap);
		symTable.push();
		try {
			for (IDeclaration p : params) {
				if (p.sort().accept(f) != null) {
					ISort.IFcnSort fs = symTable.smtConfig.sortFactory.createFcnSort(new ISort[0],p.sort());
					SymbolTable.Entry entry = new SymbolTable.Entry(p.parameter(),fs,null);
					symTable.add(entry,true);
				}
			}
			if (f.result.isEmpty()) {
				ISort res = result.accept(f);
				if (res != null) {
					res = expr.accept(f);
				}
				if (res != null && !res.equals(result)) {
					f.error("Declared sort of the result does not match the sort of the expression: "
							+ symTable.smtConfig.defaultPrinter.toString(result) + " vs. " 
							+ symTable.smtConfig.defaultPrinter.toString(res),result.pos());
				}
			}
			try {
				List<ISort> sorts = new LinkedList<ISort>(); 
				for (IDeclaration p : params) sorts.add(p.sort());
				symTable.logicInUse.checkFcnDeclaration(id,sorts,result,expr);
				symTable.logicInUse.validExpression(expr);
			} catch (IVisitor.VisitorException e) {
				f.error(e.getMessage(), e.pos());
			}
		} catch (IVisitor.VisitorException e) {
			f.error("INTERNAL ERROR: Exception while checking sort abbreviation: " + e.getMessage(),expr.pos());
		} catch (Exception e) {
			f.error("INTERNAL ERROR: Exception while checking sort abbreviation: " + e.getMessage(),expr.pos());
		} finally {
			symTable.pop();
		}
		return f.result;
		
	}

	/** The main entry point for type-checking an IExpr (expected to be a Bool)*/
	public static List<IResponse> check(SymbolTable symTable, IExpr expr) {
		TypeChecker f = new TypeChecker(symTable,null);
		try {
			ISort topsort = expr.accept(f);
			if (topsort != null && !topsort.isBool()) {
				f.error("Expected an expression with Bool sort, not " + topsort, expr.pos());
			}
			try {
				symTable.logicInUse.validExpression(expr);
			} catch (IVisitor.VisitorException e) {
				f.error(e.getMessage(), e.pos());
			}
		} catch (IVisitor.VisitorException e) {
			f.error("Visitor Exception: " + e.getMessage(), e.pos());
		} catch (Exception e) {
			f.error("INTERNAL ERROR: Exception while checking sort abbreviation: " + e.getMessage(),expr.pos());
		}
		return f.result;
	}
	
	/** The main entry point for type-checking an IExpr (expected to be a Bool)*/
	public static List<IResponse> check(SymbolTable symTable, IExpr expr, Map<IExpr,ISort> typemap) {
		TypeChecker f = new TypeChecker(symTable,typemap);
		symTable.push();
		try {
			ISort topsort = expr.accept(f);
			if (topsort != null && !topsort.isBool()) {
				f.error("Expected an expression with Bool sort, not " + topsort, expr.pos());
			}
			try {
				symTable.logicInUse.validExpression(expr);
			} catch (IVisitor.VisitorException e) {
				f.error(e.getMessage(), e.pos());
			}
			if (f.result.isEmpty()) symTable.merge();
		} catch (IVisitor.VisitorException e) {
			f.error("Visitor Exception: " + e.getMessage(), e.pos());
		} catch (Exception e) {
			f.error("INTERNAL ERROR: Exception while checking sort abbreviation: " + e.getMessage(),expr.pos());
		} finally {
			if (!f.result.isEmpty()) symTable.pop();
		}
		return f.result;
	}

	public static List<IResponse> check(SymbolTable symTable, IExpr expr, Map<IExpr,ISort> typemap, List<IExpr.IDeclaration> decls) {
		TypeChecker f = new TypeChecker(symTable,typemap);
		try {
			for (IExpr.IDeclaration d: decls) {
				f.currentScope.put(d.parameter(),new Variable(d.parameter(),d.sort(),null));
			}
			ISort topsort = expr.accept(f);
			if (topsort != null && !topsort.isBool()) {
				f.error("Expected an expression with Bool sort, not " + topsort, expr.pos());
			}
			try {
				symTable.logicInUse.validExpression(expr);
			} catch (IVisitor.VisitorException e) {
				f.error(e.getMessage(), e.pos());
			}
		} catch (IVisitor.VisitorException e) {
			f.error("Visitor Exception: " + e.getMessage(), e.pos());
		} catch (Exception e) {
			f.error("INTERNAL ERROR: Exception while checking sort abbreviation: " + e.getMessage(),expr.pos());
		}
		return f.result;
	}

	public /*@Nullable*/ ISort save(/*@NonNull*/IExpr e, /*@Nullable*/ISort s) {
		if (typemap != null) typemap.put(e,s);
		return s;
	}
	
	@Override
	public /*@Nullable*/ ISort visit(INumeral e) {
		IFcnSort sort = symTable.lookup(0,smtConfig.exprFactory.symbol("NUMERAL"));
		if (sort == null) error("No sort specified for numeral",e.pos());
		return save(e,sort == null ? null : sort.resultSort());
	}

	@Override
	public /*@Nullable*/ ISort visit(IFcnExpr e) throws IVisitor.VisitorException {
		if (e.args().size() == 0) {
			// Error message already given on parsing
			// but we'll defensively program
			error("Unexpected function with no arguments: " + pr(e.head()),e.pos());
			return null; 
		}

		// Type check all the arguments
		boolean anyErrors = false;
		List<ISort> argSorts = new LinkedList<ISort>();
		java.util.Iterator<IExpr> iter = e.args().iterator();
		while (iter.hasNext()) {
			IExpr sx = iter.next();
			ISort argSort = sx.accept(this);
			anyErrors = anyErrors || (argSort == null);
			if (argSort != null) argSorts.add(argSort); 
		}
		if (anyErrors) return null;

		// Now lookup the head in the context of these arguments
		IQualifiedIdentifier qhead = e.head();
		IIdentifier head;
		ISort resultSort = null;
		if (qhead instanceof IAsIdentifier) {
			resultSort = qhead.accept(this);
			if (resultSort == null) return null;
			head = ((IAsIdentifier)qhead).head();
		} else {
			head = (IIdentifier)qhead;
		}
		boolean bvperhaps = symTable.bitVectorTheorySet && head.toString().startsWith("bv");
		String name = head.toString();
		if (name.equals("=") || name.equals("distinct")) {
			// FIXME - this is just here until we get par types implemented
			// FIXME - /= is not part of SMT - put it in relax?
			ISort ss = null;
			for (ISort s: argSorts) {
				if (ss == null) ss = s;
				else if (!ss.equals(s)) {
					if (symTable.realsIntsTheorySet &&
							(ss.toString().equals("Real") && s.toString().equals("Int"))) {
						// OK
					} else if (symTable.realsIntsTheorySet &&
								(s.toString().equals("Real") && ss.toString().equals("Int"))) {
						ss = s;
					} else {
						String msg = "Mismatched sorts of arguments: " + 
						smtConfig.defaultPrinter.toString(ss) + " vs. " +
						smtConfig.defaultPrinter.toString(s);
						error(msg,e.pos());
						return null;
					}
				}
			}
			ISort b = smtConfig.sortFactory.Bool();
			b.accept(this);
			return save(e,b);
		} else if (name.equals("ite")) {
			// FIXME - this is just here until we get par types implemented
			if (!argSorts.get(0).isBool()) {
				error("The first argument of ite must have sort Bool",e.pos());
				return null;
			}
			if (!argSorts.get(1).equals(argSorts.get(2))) {
				error("The last two arguments of ite have different sorts",e.pos());
				return null;
			}
			return save(e,argSorts.get(1));
		} else if (symTable.arrayTheorySet && name.equals("store")) {
			if (argSorts.size() != 3) {
				error(" The store function should have three arguments",head.pos());
				return null;
			}
			// FIXME - this needs to be fully expanded of all definitions
			ISort sort1 = argSorts.get(0);
			if (sort1 instanceof ISort.IApplication) {
				ISort.IApplication asort = (ISort.IApplication)sort1;
				if (!(asort.family().headSymbol().toString().equals("Array"))) {
					error("The first argument of the store function should be an Array sort, not " + sort1,e.pos());
					return null;
				}
				if (!asort.parameters().get(0).equals(argSorts.get(1))) {
					error("The second argument of the store function must match the array index sort: " + argSorts.get(1) + " vs. " + asort.parameters().get(0), e.pos() );
					return null;
				}
				if (!asort.parameters().get(1).equals(argSorts.get(2))) {
					error("The third argument of the store function must match the array value sort: " + argSorts.get(2) + " vs. " + asort.parameters().get(1), e.pos() );
					return null;
				}
			} else {
				error("The first argument of the store function should be an Array sort, not " + sort1,e.pos());
				return null;
			}
			// FIXME - this is just here until we get par types implemented; it also should depend on which theories are installed
			return save(e,argSorts.get(0));
		}
		if (symTable.arrayTheorySet && name.equals("select")) {
			// FIXME - this is just here until we get par types implemented; it also should depend on which theories are installed
			if (argSorts.size() != 2) {
				error(" The select function should have two arguments",head.pos());
				return null;
			}
			// FIXME - this needs to be fully expanded of all definitions
			ISort sort1 = argSorts.get(0);
			if (sort1 instanceof ISort.IApplication) {
				ISort.IApplication asort = (ISort.IApplication)sort1;
				if (!(asort.family().headSymbol().toString().equals("Array"))) {
					error("The first argument of the select function should be an Array sort, not " + sort1,e.pos());
					return null;
				}
				if (!asort.parameters().get(0).equals(argSorts.get(1))) {
					error("The second argument of the select function must match the array index sort: " + argSorts.get(1) + " vs. " + asort.parameters().get(0), e.pos() );
					return null;
				}
			} else {
				error("The first argument of the select function should be an Array sort, not " + sort1,e.pos());
				return null;
			}
			// FIXME - this is just here until we get par types implemented; it also should depend on which theories are installed
			sort1 = ((ISort.IApplication)sort1).parameters().get(1);
			return save(e,sort1);
		} 
		boolean useext = true;
		if (bvperhaps) {
			if (name.equals("bvnot") || name.equals("bvneg")) {
				if (argSorts.size() != 1) {
					error(" The " + name + " function should have one argument",head.pos());
					return null;
				}
				ISort s = argSorts.get(0);
				if (!isBitVec(s)) {
					error("The argument must have a BitVec sort, not " + smtConfig.defaultPrinter.toString(s),e.args().get(0).pos());
					return null;
				}
				return save(e,s);
				
			} else if (name.equals("bvand") || name.equals("bvor") 
					|| name.equals("bvadd") || name.equals("bvmul")
					|| name.equals("bvudiv") || name.equals("bvurem")
					|| name.equals("bvshl") || name.equals("bvlshr") ||
					(useext && (name.equals("bvnand") || name.equals("bvnor") || name.equals("bvxor") || name.equals("bvxnor")
							|| name.equals("bvsub") || name.equals("bvsdiv") || name.equals("bvsrem") || name.equals("bvsmod")
							|| name.equals("bvashr") || name.equals("bvcomp") 
					))
					) {
				if (argSorts.size() != 2) {
					error(" The " + name + " function should have two arguments",head.pos());
					return null;
				}
				ISort s = argSorts.get(0);
				if (!isBitVec(s)) {
					error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
					return null;
				}
				ISort ss = argSorts.get(1);
				if (!isBitVec(ss)) {
					error("The argument must have a BitVec sort, not " + pr(ss),e.args().get(1).pos());
					return null;
				}
				if (!s.equals(ss)) {
					error("The sorts must match: " + pr(s) + " vs. " + pr(ss),e.pos());
					return null;
				}
				if (name.equals("bvcomp")) {
					s = makeBitVec(1);
					return save(e,s);
				}
				return save(e,s);
			} else if (name.equals("bvult") || (useext && (name.equals("bvule") || name.equals("bvugt") || name.equals("bvuge")
					|| name.equals("bvslt") || name.equals("bvsle") || name.equals("bvsgt") || name.equals("bvsge")
					)
					)) {
				if (argSorts.size() != 2) {
					error(" The " + name + " function should have two arguments",head.pos());
					return null;
				}
				ISort s = argSorts.get(0);
				if (!isBitVec(s)) {
					error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
					return null;
				}
				ISort ss = argSorts.get(1);
				if (!isBitVec(ss)) {
					error("The argument must have a BitVec sort, not " + pr(ss),e.args().get(1).pos());
					return null;
				}
				if (!s.equals(ss)) {
					error("The sorts must match: " + pr(s) + " vs. " + pr(ss),e.pos());
					return null;
				}
				ISort b = smtConfig.sortFactory.Bool(); // FIXME - get something from the symbol table?
				b.accept(this);
				return save(e,b);
			}
					
		}
		if (symTable.bitVectorTheorySet && name.equals("concat")) {
			if (argSorts.size() != 2) {
				error(" The " + name + " function should have two arguments",head.pos());
				return null;
			}
			ISort s = argSorts.get(0);
			if (!isBitVec(s)) {
				error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
				return null;
			}
			ISort ss = argSorts.get(1);
			if (!isBitVec(ss)) {
				error("The argument must have a BitVec sort, not " + pr(ss),e.args().get(1).pos());
				return null;
			}
			s = makeBitVec(bitvecSize(s)+bitvecSize(ss));
			return save(e,s);
		}
		String pname = null;
		if (head instanceof IParameterizedIdentifier) pname = ((IParameterizedIdentifier)head).headSymbol().toString();
		if (symTable.bitVectorTheorySet && 
				head instanceof IParameterizedIdentifier &&
				pname.equals("extract")) {
			if (argSorts.size() != 1) {
				error(" The " + name + " function should have one argument",head.pos());
				return null;
			}
			ISort s = argSorts.get(0);
			if (!isBitVec(s)) {
				error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
				return null;
			}
			IParameterizedIdentifier pid = (IParameterizedIdentifier)head;
			if (pid.numerals().size() != 2) {
				error("Expected exactly two numerals in an extract identifier",pid.pos());
				return null;
			}
			int end = pid.numerals().get(0).intValue();
			int start = pid.numerals().get(1).intValue();
			if (end < start) {
				error("The end index is less than the starting index",pid.numerals().get(1).pos());
				return null;
			}
			int len = bitvecSize(s);
			if (end >= len) {
				error("The end index must be less than the length of the argument sort: " + end + " vs. " + len, pid.numerals().get(1).pos());
				return null;
			}
			s = makeBitVec(end-start+1);
			return save(e,s);

		}
		if (useext && symTable.bitVectorTheorySet && 
				head instanceof IParameterizedIdentifier &&
				(pname.equals("repeat")
				)) {
			if (argSorts.size() != 1) {
				error(" The " + name + " function should have one argument",head.pos());
				return null;
			}
			ISort s = argSorts.get(0);
			if (!isBitVec(s)) {
				error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
				return null;
			}
			IParameterizedIdentifier pid = (IParameterizedIdentifier)head;
			if (pid.numerals().size() != 1) {
				error("Expected exactly one numeral in a repeat identifier",pid.pos());
				return null;
			}
			int val = pid.numerals().get(0).intValue();
			if (val == 0) {
				error("The numeral may not be 0 in a repeat",pid.numerals().get(0).pos());
				return null;
			}
			s = makeBitVec(val*bitvecSize(s));
			return save(e,s);

		}
		
		if (useext && symTable.bitVectorTheorySet && 
				head instanceof IParameterizedIdentifier &&
				(pname.equals("zero_extend") || pname.equals("sign_extend")
				)) {
			if (argSorts.size() != 1) {
				error(" The " + name + " function should have one argument",head.pos());
				return null;
			}
			ISort s = argSorts.get(0);
			if (!isBitVec(s)) {
				error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
				return null;
			}
			IParameterizedIdentifier pid = (IParameterizedIdentifier)head;
			if (pid.numerals().size() != 1) {
				error("Expected exactly one numeral in a repeat identifier",pid.pos());
				return null;
			}
			int val = pid.numerals().get(0).intValue();
			s = makeBitVec(val+bitvecSize(s));
			return save(e,s);

		}
		if (useext && symTable.bitVectorTheorySet && 
				head instanceof IParameterizedIdentifier &&
				(pname.equals("rotate_left") || pname.equals("rotate_right")
				)) {
			if (argSorts.size() != 1) {
				error(" The " + name + " function should have one argument",head.pos());
				return null;
			}
			ISort s = argSorts.get(0);
			if (!isBitVec(s)) {
				error("The argument must have a BitVec sort, not " + pr(s),e.args().get(0).pos());
				return null;
			}
			IParameterizedIdentifier pid = (IParameterizedIdentifier)head;
			if (pid.numerals().size() != 1) {
				error("Expected exactly one numeral in a repeat identifier",pid.pos());
				return null;
			}
			return save(e,s);

		}
		
		SymbolTable.Entry entry = symTable.lookup(head,argSorts,resultSort);
		if (entry == null && symTable.realsIntsTheorySet) {
			ISort realSort = null;
			for (ISort sort: argSorts) {
				if (sort.toString().equals("Real")) realSort = sort; 
			}
			if (realSort != null) {
				List<ISort> newargs = new LinkedList<ISort>();
				for (ISort sort: argSorts) {
					if (sort.toString().equals("Int")) {
						newargs.add(realSort);
					} else {
						newargs.add(sort);
					}
				}
				entry = symTable.lookup(head,newargs,resultSort);
			}
		}
		if (entry == null) {
			String msg = "Unknown predicate symbol " + name + " with argument types";
			for (ISort s: argSorts) {
				msg = msg + " " + smtConfig.defaultPrinter.toString(s);
			}
			error(msg,e.pos());
			return null;
		} else {
			return save(e,entry.sort.resultSort());
		}
	}
	
	private boolean isBitVec(ISort s) {
		if (!(s instanceof ISort.IApplication)) return false;
		ISort.IApplication se = (ISort.IApplication)s;
		if (!(se.family() instanceof IParameterizedIdentifier)) return false;
		IParameterizedIdentifier pid = (IParameterizedIdentifier)se.family();
		return pid.headSymbol().toString().equals(Utils.BITVEC); // FIXME - compare against a stored symbol?
	}

	private int bitvecSize(ISort s) {
		if (!(s instanceof ISort.IApplication)) return -1;
		ISort.IApplication se = (ISort.IApplication)s;
		if (!(se.family() instanceof IParameterizedIdentifier)) return -1;
		IParameterizedIdentifier pid = (IParameterizedIdentifier)se.family();
		if (pid.numerals().size() != 1) return -1;
		return pid.numerals().get(0).intValue();
	}
	
	private ISort makeBitVec(int length) throws IVisitor.VisitorException {
		List<INumeral> nums = new LinkedList<INumeral>();
		nums.add(smtConfig.exprFactory.numeral(length));
		// FIXME - use a pre-constructed symbol for BitVec when it does not have a position?
		IIdentifier id = smtConfig.exprFactory.id(smtConfig.exprFactory.symbol(Utils.BITVEC),nums);
		ISort s = smtConfig.sortFactory.createSortExpression(id, new ISort[0]);
		s.accept(this);
		return s;
	}

	@Override
	/*@checkers.igj.quals.ReadOnly*/
	public /*@Nullable*/ ISort visit(ISymbol e) {
		IFcnSort sort = null;
		String value = e.value();
		if (Utils.TRUE.equals(value) || Utils.FALSE.equals(value)) { 
			return save(e,symTable.smtConfig.sortFactory.Bool()); 
		} else {
			Variable v = currentScope.get(e);
			if (v != null) {
				if (isClosed == null && v.expression == null) isClosed = e; // FIXME - need to check if v.expression is closed or not
				return save(e,v.sort);
			}
			if ((sort=symTable.lookup(0,e))==null) {
				result.add(smtConfig.responseFactory.error("Unknown constant symbol " + value, e.pos()));
				return null;
			} else {
				return save(e,sort.resultSort());
			}
		}
	}


	@Override
	public /*@Nullable*/ISort visit(IDecimal e) {
		IFcnSort sort = symTable.lookup(0,smtConfig.exprFactory.symbol("DECIMAL")); // FIXME - don't recreate this every time it is used
		if (sort == null) result.add(smtConfig.responseFactory.error("No sort specified for decimal literal",e.pos()));
		return save(e,sort == null ? null : sort.resultSort());
	}

	@Override
	public /*@Nullable*/ISort visit(IBinaryLiteral e) throws IVisitor.VisitorException {
		if (!symTable.bitVectorTheorySet) result.add(smtConfig.responseFactory.error("No sort specified for a binary literal",e.pos()));
		ISort s = makeBitVec(e.length());
		s.accept(this);
		return save(e,s);
	}

	@Override
	public /*@Nullable*/ ISort visit(IHexLiteral e) throws IVisitor.VisitorException {
		if (!symTable.bitVectorTheorySet) result.add(smtConfig.responseFactory.error("No sort specified for a hex literal",e.pos()));
		List<INumeral> nums = new LinkedList<INumeral>();
		nums.add(smtConfig.exprFactory.numeral(e.length()*4));
		IIdentifier id = smtConfig.exprFactory.id(smtConfig.exprFactory.symbol(Utils.BITVEC),nums);
		ISort s = smtConfig.sortFactory.createSortExpression(id, new ISort[0]);
		s.accept(this);
		return save(e,s);
	}

	@Override
	public /*@Nullable*/ ISort visit(IStringLiteral e) {
		IFcnSort sort = symTable.lookup(0,smtConfig.exprFactory.symbol("STRING")); // FIXME - don't recreate this everytime it is used
		if (sort == null) result.add(smtConfig.responseFactory.error("No sort specified for string-literal",e.pos()));
		return save(e,sort == null ? null : sort.resultSort());
	}

	@Override
	public /*@Nullable*/ ISort visit(IKeyword e) {
		// Should never be called
		result.add(smtConfig.responseFactory.error("INTERNAL ERROR: Did not expect to be type-checking a keyword",e.pos()));
		return null;
	}

	@Override
	public /*@Nullable*/ ISort visit(IError e) {
		return null;
	}

	@Override
	public /*@Nullable*/ ISort visit(IParameterizedIdentifier e) throws IVisitor.VisitorException {
		IFcnSort sort = null;
		boolean useext = true;
		String pname = e.headSymbol().toString();
		if (useext && symTable.bitVectorTheorySet && 
				(pname.matches("bv(0|[1-9][0-9]*)") // TODO - allow leading zeros?
				)) {
			if (e.numerals().size() != 1) {
				error("Expected exactly one numeral in a bv identifier",e.pos());
				return null;
			}
			int size = e.numerals().get(0).intValue();
			BigInteger value = new BigInteger(pname.substring(2));
			if (value.bitLength() > size) {
				error("The value of the bitvector constant is too large for the given size (" + value.bitLength() + " vs. " + size + "bits)",e.pos());
				return null;
			}
			ISort s = makeBitVec(size);
			return save(e,s);
		}

		if ((sort=symTable.lookup(0,e))==null) {
			result.add(smtConfig.responseFactory.error("No sort known for identifier: " + smtConfig.defaultPrinter.toString(e),e.pos()));
			return null;
		} else {
			return save(e,sort.resultSort());
		}
	}

	@Override
	public /*@Nullable*/ ISort visit(IAsIdentifier e) throws IVisitor.VisitorException {
		// Check the sort
		ISort s = e.qualifier().accept(this);
		// We do the rest of the checking in the parent (IFcnExpr)
		return s;
	}

	@Override
	public /*@Nullable*/ ISort visit(IAttributedExpr e) throws IVisitor.VisitorException {
		ISymbol savedIsClosed = isClosed;
		isClosed = null;
		boolean errors = false;
		ISort resultSort = null;
		try {
			resultSort = save(e,e.expr().accept(this));
			for (IAttribute<?> a: e.attributes()) {
				String name = a.keyword().value();
				if (name.equals(":named")) { // FIXME - use a canonical representation
					IAttributeValue v = a.attrValue();
					if (!(v instanceof ISymbol)) {
						result.add(smtConfig.responseFactory.error("Expected a symbol after :named",v==null?a.keyword().pos():v.pos()));
						errors = true;
					}
					ISort.IFcnSort fcnSort = smtConfig.sortFactory.createFcnSort(new ISort[0],resultSort);
					SymbolTable.Entry entry = new SymbolTable.Entry((ISymbol)v,fcnSort,null);
					if (!symTable.add(entry,false)) { 
						result.add(smtConfig.responseFactory.error("Symbol " + v.toString() + " is already defined",v.pos())); // FIXME - encode name
						errors = true;
					}
					if (isClosed != null) {
						result.add(smtConfig.responseFactory.error("The expression being named is not closed - this symbol is a variable: " + smtConfig.defaultPrinter.toString(isClosed),isClosed.pos()));
						errors = true;
					}
				} else if (name.equals(":pattern")) {
					IAttributeValue v = a.attrValue();
					if (!(v instanceof ISeq)) {
						result.add(smtConfig.responseFactory.error("Expected a sequence after :pattern",v==null?a.keyword().pos():v.pos()));
						errors = true;
					} else {
						for (ISexpr ee: ((ISeq)v).sexprs()) {
							IExpr ex = convert(ee);
							ex.accept(this);
						}
					}
				}
			}
		} finally {
			isClosed = isClosed == null ? savedIsClosed : isClosed;
		}
		if (errors) return null;
		return resultSort;
	}
	
	public IExpr convert(ISexpr s) { // FIXME - use a factory? do typechecking here?
		if (s instanceof ISexpr.ISeq) {
			Iterator<ISexpr> sexprs = ((ISeq)s).sexprs().iterator();
			ISexpr first = sexprs.next();
			List<IExpr> args = new LinkedList<IExpr>();
			while (sexprs.hasNext()) {
				IExpr arg = convert(sexprs.next());
				args.add(arg);
			}
			ISymbol id = (ISymbol)first;
			return new SMTExpr.FcnExpr(id,args);
		} else if (s instanceof ISymbol) {
			return (ISymbol)s;
		} else {
			throw new RuntimeException();
		}
	}

	protected Map<ISymbol,Variable> currentScope = new HashMap<ISymbol,Variable>();
	protected List<Map<ISymbol,Variable>> parameters = new LinkedList<Map<ISymbol,Variable>>();

	@Override
	public /*@Nullable*/ ISort visit(IForall e) throws IVisitor.VisitorException {
		Map<ISymbol,Variable> saved = new HashMap<ISymbol,Variable>();
		saved.putAll(currentScope);
		parameters.add(0,saved);
		boolean errors = false;
		for (IExpr.IDeclaration decl : e.parameters()) {
			ISort res = decl.sort().accept(this);
			if (res == null) errors = true;
			else currentScope.put(decl.parameter(),new Variable(decl.parameter(),decl.sort(),null));
		}
		try {
			if (errors) return null;
			ISort s = e.expr().accept(this);
			return save(e,s);
		} finally {
			currentScope = parameters.remove(0);
		}
	}

	@Override
	public /*@Nullable*/ ISort visit(IExists e) throws IVisitor.VisitorException {
		Map<ISymbol,Variable> saved = new HashMap<ISymbol,Variable>();
		saved.putAll(currentScope);
		parameters.add(0,saved);
		boolean errors = false;
		for (IExpr.IDeclaration decl : e.parameters()) {
			ISort res = decl.sort().accept(this);
			if (res == null) errors = true;
			else currentScope.put(decl.parameter(),new Variable(decl.parameter(),decl.sort(),null));
		}
		try {
			if (errors) return null;
			ISort s = e.expr().accept(this);
			return save(e,s);
		} finally {
			currentScope = parameters.remove(0);
		}
	}

	@Override
	public /*@Nullable*/ ISort visit(ILet e) throws IVisitor.VisitorException {
		Map<ISymbol,Variable> newdecls = new HashMap<ISymbol,Variable>();
		Map<ISymbol,Variable> saved = new HashMap<ISymbol,Variable>();
		saved.putAll(currentScope);
		parameters.add(0,saved);
		try {
			boolean anyErrors = false;
			for (IExpr.IBinding decl : e.bindings()) {
				IExpr expr = decl.expr();
				ISort s = expr.accept(this);
				if (s == null) anyErrors = true;
				else {
					newdecls.put(decl.parameter(),new Variable(decl.parameter(),s,expr));
				}
			}
			if (anyErrors) return null;
			currentScope.putAll(newdecls);
			ISort s = e.expr().accept(this);
			return save(e,s);
		} finally {
			currentScope = parameters.remove(0);
		}
	}
	
	@Override
	public /*@Nullable*/ ISort visit(ISort.IApplication s) throws IVisitor.VisitorException {
		IIdentifier f = s.family();
		List<ISort> args = s.parameters();
		IDefinition def = symTable.lookupSort(f);
		if (def instanceof ISort.ErrorDefinition) {
			ISort.ErrorDefinition ed = (ISort.ErrorDefinition)def;
			error(ed.error,ed.pos);
			return null;
		}
		s.definition(null);
		boolean errors = false;
		List<ISort> newargs = new LinkedList<ISort>();
		for (ISort ss : args) {
			ISort result = ss.accept(this);
			if (result == null) errors = true;
			else newargs.add(result);
		}
		if (def == null) {
			error("No such sort symbol declared: " + pr(f),f.pos());
			return null;
		}
		if (args.size() != def.intArity()) {
			error("The sort symbol " + pr(f) + " expects " + def.intArity()
					+ " arguments, not " + args.size(), s.pos());
			return null;
		}
		if (errors) return null;
		s.definition(def);
		return def.eval(newargs);
	}
	
	@Override
	public /*@Nullable*/ ISort visit(ISort.IFamily s) throws IVisitor.VisitorException {
		error("INTERNAL ERROR - unexpected type-checking of a ISort.IFamily " + s, null);
		return null;
	}
	
	@Override
	public /*@Nullable*/ ISort visit(ISort.IParameter s) throws IVisitor.VisitorException {
		return s;
	}
	
	@Override
	public /*@Nullable*/ ISort visit(ISort.IAbbreviation s) throws IVisitor.VisitorException {
		error("INTERNAL ERROR - unexpected type-checking of a ISort.IAbbreviation " + s, null);// FIXME - check sort
		return null;
	}

	@Override
	public /*@Nullable*/ ISort visit(ISort.IFcnSort s) throws IVisitor.VisitorException {
		error("INTERNAL ERROR - unexpected type-checking of a ISort.IFcnSort " + s, s.pos());// FIXME - check sort
		return null;
	}
	
	public static class Variable {
		public ISymbol symbol;
		public ISort sort;
		public /*@Nullable*/IExpr expression;
		public Variable(ISymbol sym, ISort sort, IExpr expr) {
			this.symbol = sym;
			this.sort = sort;
			this.expression = expr;
		}
	}

}