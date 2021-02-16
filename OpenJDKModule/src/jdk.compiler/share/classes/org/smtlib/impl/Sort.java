/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.impl;

import java.util.*;

import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.INumeral;
import org.smtlib.*;
import org.smtlib.impl.SMTExpr.Symbol;

/** This class implements the abstract ISort interface */
public abstract class Sort extends Pos.Posable implements ISort {
	
//	/** Declared abstract so the derived classes are reminded to implement it */
//	abstract public boolean equals(Object o);
//	
//	/** Declared abstract so the derived classes are reminded to implement it */
//	abstract public int hashCode();
	
	/** Returns true iff the receiver is a Sort expression designating the pre-defined Bool sort */
	@Override
	public boolean isBool() {
		return this == Bool || ((this instanceof IApplication) &&  ((IApplication)this).family().toString().equals(BOOL));
	}

	/** Returns the pre-defined Bool sort */
	static public ISort.IApplication Bool() {
		return Bool;
	}
	
	/** Concrete syntax for the pre-defined Bool sort */  // FIXME - do we want concrete syntax here?
	static final private String BOOL = "Bool";
	
	/** A cached instance of the pre-defined Bool sort */
	static final private Sort.Application Bool = new Sort.Application(new Symbol(BOOL), new LinkedList<ISort>());

	/** Represents a new sort symbol, with a given identifier and arity */
	static public class Family implements IFamily {
		private IIdentifier identifier;
		private INumeral arity;
		public Family(IIdentifier identifier, INumeral arity) {
			this.identifier = identifier;
			this.arity = arity;
		}
		@Override
		public IIdentifier identifier() { return identifier; }
		
		@Override
		public INumeral arity() { return arity; }

		@Override
		public int intArity() { return arity().intValue(); }

		@Override
		public IApplication eval(List<ISort> sorts) {
			if (sorts.size() != arity().intValue()) {
				throw new SMT.InternalException("Incorrect number of arguments: " + sorts.size() + "vs. " +  arity().intValue());
			}
			Application e = new Application(this.identifier(),sorts);
			e.definition(this);
			return e;
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IFamily)) return false;
			return identifier().equals(((IFamily)o).identifier());  // FIXME - is this sufficient in the presence of overriding symbols?
		}

		@Override
		public int hashCode() {
			return identifier.hashCode();
		}
		
		/** Use this just for debugging - proper conversion to a String is performed by an IPrinter */
		@Override
		public String toString() {
			return identifier.toString();
		}
		
		@Override
		public </*@Nullable*/T> /*@Nullable*/T accept(IVisitor</*@Nullable*/T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
	}
	
	/** Implements a Sort abbreviation (parameterized definition) */
	static public class Abbreviation implements IAbbreviation {
		
		private IIdentifier identifier;
		private List<IParameter> parameters;
		private ISort sortExpression;
		
		public Abbreviation(IIdentifier identifier, List<IParameter> parameters, ISort sortExpression) {
			this.identifier = identifier;
			this.parameters = parameters;
			this.sortExpression = sortExpression;
		}
		
		@Override
		public IIdentifier identifier() { return identifier; }
		
		@Override
		public List<IParameter> parameters() { return parameters; }
		
		@Override
		public ISort sortExpression() { return sortExpression; }

		@Override
		public int intArity() { return parameters().size(); }
		
		@Override
		public ISort eval(List<ISort> sorts) {
			if (sorts.size() != parameters().size()) {
				throw new SMT.InternalException("Incorrect number of arguments: " + sorts.size() + " instead of " + parameters().size());
			}
			Map<IParameter,ISort> map = new HashMap<IParameter,ISort>();
			int i = 0;
			for (IParameter p: parameters) {
				if (map.put(p,sorts.get(i))!=null) {
					throw new SMT.InternalException("Duplicate parameter: " + p);
				}
				i++;
			}
			return sortExpression.substitute(map);
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IAbbreviation)) return false;
			return identifier().equals(((IAbbreviation)o).identifier());
		}
		
		@Override
		public int hashCode() {
			// The identifier is supposed to be unique across all in-scope definitions
			return identifier().hashCode(); 
		}
		
		/** Use this just for debugging - proper conversion to a String is performed by an IPrinter */
		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append("(");
			sb.append(identifier.toString());
			sb.append(" (");
			for (IParameter p : parameters) {
				sb.append(" ");
				sb.append(p.toString());
			}
			sb.append(") ");
			sb.append(sortExpression.toString());
			sb.append(")");
			return sb.toString();
		}

		@Override
		public </*@Nullable*/T> /*@Nullable*/T accept(IVisitor</*@Nullable*/T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
	}
	
	/** Represents a sort expression consisting of a sort symbol or sort abbreviation symbol applied to a
	 * corresponding number of sort arguments 
	 */
	static public class Application extends Sort implements IApplication {
		protected IIdentifier sortID;
		protected List<ISort> sortParameters;
		
		/** Reference to definition; filled in during type-checking */
		private ISort.IDefinition definition;  
		
		/** Cached value for expanded() */
		private ISort expanded = null;
		
		public Application(IIdentifier sortID, List<ISort> sortParameters) {
			this.sortID = sortID;
			this.sortParameters = sortParameters;
		}
		
		public Application(IIdentifier sortID, ISort... sortParameters) {
			this.sortID = sortID;
			this.sortParameters = Arrays.asList(sortParameters);
		}
		
		@Override
		public IIdentifier family() { return sortID; }
		
		@Override
		public ISort param(int i) { return sortParameters.get(i); }
		
		@Override
		public List<ISort> parameters() { return sortParameters; }
		
		@Override
		public IDefinition definition() { return definition; }
		
		@Override
		public IDefinition definition(IDefinition definition) {
			this.definition = definition;
			return definition;
		}
		
		@Override
		public ISort expand() {
			// Note we could call definition().eval(sortParameters) always, but that 
			// creates a duplicate object in Family.eval
			
			if (expanded == null) {
				boolean changed = false;
				ISort ss = this;
				for (ISort param: parameters()) {
					ISort p = param.expand();
					if (p != param) changed = true;
				}
				while (ss instanceof Application) {
					if (((Application)ss).definition() instanceof IFamily) return ss;
					ss = definition().eval(sortParameters);
				}
				expanded = ss;
			}
			return expanded;
		}
		
// TODO _ review all the equals implementations
		@Override
		public boolean equals(Object sort) {
			if (this == sort) return true;
			if (!(sort instanceof ISort)) return false;
			return expand().equalsNoExpand( ((ISort)sort).expand());
//			Object esort = sort;
//			if (sort instanceof IApplication) {
//				IApplication e = (IApplication)sort;
//				if (e.family().equals(this.family())) {
//					boolean matches = true;
//					int i = 0;
//					for (ISort p: this.parameters()) {
//						if (!p.equals(e.param(i++))) { matches = false; break; }
//					}
//					if (matches) return true;
//				}
//				esort = e.expand();
//			}
//			// Substitute abbreviations
//			ISort ethis = expand();
//			// If either one was expanded, call equals recursively
//			if (this != ethis || sort != esort) return ethis.equals(esort);
//			return false;
		}
		
		@Override
		public boolean equalsNoExpand(ISort sort) {
			if (this == sort) return true;
			if (!(sort instanceof IApplication)) return false;
			IApplication esort = (IApplication)sort;
			if (esort.family().equals(this.family())) {
				// If the family() is equal, the arity must be equal
				int i = 0;
				for (ISort p: this.parameters()) {
					if (!p.equalsNoExpand(esort.param(i++))) return false;
				}
				return true;
			} else {
				return false;
			}
		}	
		
		@Override
		public boolean equals(Map<IParameter,ISort> leftmap, ISort sort, Map<IParameter,ISort> rightmap, SymbolTable symTable) {
			//if (this == sort) return true; // Only the case if the maps are the same
			Object esort = sort;
			if (sort instanceof IApplication) {
				IApplication e = (IApplication)sort;
				if (e.family().equals(this.family())) {
					boolean matches = true;
					int i = 0;
					for (ISort p: this.parameters()) {
						if (!p.equals(leftmap,e.param(i++),rightmap,symTable)) { matches = false; break; }
					}
					if (matches) return true;
				}
				esort = e.expand();
			}
			// Substitute abbreviations
			ISort ethis = expand();
			// If either one was expanded, call equals recursively
			if (this != ethis || sort != esort) return ethis.equals(esort);
			return false;
			
			
			
// TODO _ delete when tests are successful			
//			if (this == sort) return true;
//			if (!(sort instanceof IApplication)) return false;
//			IApplication e = (IApplication)sort;
//			if (!(e.family().equals(sortFamily))) {
//				IDefinition leftdef = symTable.lookupSort(sortFamily);
//				if (!(leftdef instanceof IAbbreviation)) return sort.equals(rightmap,this,leftmap,symTable);
//				IAbbreviation leftabbrev = (IAbbreviation)leftdef;
//				if (leftabbrev.intArity() != e.parameters().size()) {
//					return false; // FIXME - actually a problem - mismatched aritities?
//				}
//				Map<IIdentifier,ISort> newmap = new HashMap<IIdentifier,ISort>();
//				newmap.putAll(leftmap);
//				for (int i = 0; i<leftdef.intArity(); ++i) {
//					newmap.put(leftabbrev.parameters().get(i).symbol(),
//							e.parameters().get(i));
//				}
//				return leftabbrev.sortExpression().equals(newmap,sort,rightmap,symTable);
//			}
//			// If the family() is equal, the arity must be equal
//			int i = 0;
//			for (ISort p: sortParameters) {
//				if (!p.equals(e.param(i++))) return false;
//			}
//			return true;
		}

		@Override
		public int hashCode() {
			int hash = sortID.hashCode();
			for (ISort s: sortParameters) {
				hash += s.hashCode();
			}
			return hash;
		}
		
		@Override
		public ISort substitute(Map<IParameter,ISort> map) {
			IIdentifier id = family();
			List<ISort> params = new LinkedList<ISort>();
			for (ISort s: sortParameters) {
				params.add(s.substitute(map));
			}
			ISort s = map.get(id);
			if (s != null) return s;
			Application e = new Application(id,params);
			e.definition(this.definition());
			return e;
		}
		
		/** Use this just for debugging - proper conversion to a String is performed by an IPrinter */
		@Override
		public String toString() {
			if (sortParameters.size() == 0) return sortID.toString();
			StringBuilder sb = new StringBuilder();
			sb.append("(");
			sb.append(sortID.toString());
			for (ISort s: sortParameters) {
				sb.append(" ");
				sb.append(s.toString());
			}
			sb.append(")");
			return sb.toString();
		}

		@Override
		public </*@Nullable*/T> /*@Nullable*/T accept(IVisitor</*@Nullable*/T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
	}
	
	/** Represents the class of the sort of a function symbol.  This is not a 
	 * sort that can be expressed in SMT-LIB sort grammar, except implicitly 
	 * when function ids are defined in define-fun and declare-fun
	 * commands and in theory definitions.
	 */
	static public class FcnSort extends Sort implements IFcnSort {
		static private ISort[] noargs = new ISort[0];
		private ISort resultSort;
		private ISort[] argSorts;
		
		public FcnSort(ISort[] argSorts, ISort resultSort) {
			this.argSorts = argSorts;
			this.resultSort = resultSort;
		}
		
		public FcnSort(ISort resultSort) {
			this.argSorts = noargs;
			this.resultSort = resultSort;
		}
		
		@Override
		public ISort expand() { return this; } // TODO: Fix this?
		
		@Override
		public ISort resultSort() { return resultSort; }
		
		@Override
		public ISort[] argSorts() { return argSorts; }
		
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IFcnSort)) return false;
			IFcnSort fs = (IFcnSort)o;
			if (!(fs.resultSort().equals(resultSort))) return false;
			if (fs.argSorts().length != argSorts.length) return false;
			for (int i=0; i<argSorts.length; ++i) {
				if (!(fs.argSorts()[i].equals(argSorts[i]))) return false;
			}
			return true;
		}
		
		@Override
		public boolean equalsNoExpand(ISort sort) {
			if (this == sort) return true;
			if (!(sort instanceof IFcnSort)) return false;
			IFcnSort fs = (IFcnSort)sort;
			if (!(fs.resultSort().equals(resultSort))) return false;
			if (fs.argSorts().length != argSorts.length) return false;
			for (int i=0; i<argSorts.length; ++i) {
				if (!(fs.argSorts()[i].equalsNoExpand(argSorts[i]))) return false;
			}
			return true;
		}


		@Override
		public boolean equals(Map<IParameter,ISort> leftmap, ISort sort, Map<IParameter,ISort> rightmap, SymbolTable symTable) {
			// FcnSorts are not parameterized
			return equals(sort);
		}

		@Override
		public int hashCode() {
			int hash = resultSort.hashCode();
			for (ISort s: argSorts) {
				hash += s.hashCode();
			}
			return hash;
		}
		
		@Override
		public ISort substitute(Map<IParameter, ISort> map) {
			// Actually, do not expect a FcnSort to have any substitutable parameters
			ISort newResult = resultSort.substitute(map);
			ISort[] newArgs = new ISort[argSorts.length];
			for (int i = 0; i<argSorts.length; ++i) {
				newArgs[i] = ((Sort)argSorts[i]).substitute(map);
			}
			return new FcnSort(newArgs,newResult);
		}
		
		/** Use this just for debugging - proper conversion to a String is performed by an IPrinter */
		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append("(");
			for (ISort s: argSorts) {
				sb.append(s.toString());
				sb.append(" ");
			}
			sb.append(resultSort.toString());
			sb.append(")");
			return sb.toString();
		}
		
		@Override
		public </*@Nullable*/T> /*@Nullable*/T accept(IVisitor</*@Nullable*/T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
	}
	
	/** Represents a Sort parameter, such as in either the parameter list or the expression of a Sort abbreviation */
	static public class Parameter extends Sort implements IParameter {
		private IExpr.ISymbol symbol;
		
		public Parameter(IExpr.ISymbol symbol) {
			this.symbol = symbol;
		}
		
		@Override
		public IExpr.ISymbol symbol() { return symbol; }
		
		@Override
		public ISort substitute(Map<IParameter,ISort> map) {
			ISort s = map.get(this);
			return s == null ? this : s;
		}
		
		@Override
		public ISort expand() { return this; } // TODO: Fix this?
		
		@Override
		public boolean equals(Object o) {
			// Parameters are equal only under object equality
			// Two parameters with the same name in different scopes are not equal
			return this == o;
		}
		
		@Override
		public boolean equalsNoExpand(ISort sort) {
			return this == sort;
		}


		@Override
		public boolean equals(Map<IParameter,ISort> leftmap, ISort sort, Map<IParameter,ISort> rightmap, SymbolTable symTable) {
			ISort s = leftmap.get(this);
			if (s != null) {
				return sort.equals(rightmap,s,leftmap,symTable);
			} else if (sort instanceof IParameter) {
				ISort ss = rightmap.get(sort);
				if (ss == null) return this == sort;
				return ss.equals(rightmap,this,leftmap,symTable);
			} else {
				if (s == null) s = this;
				return sort.equals(rightmap,s,leftmap,symTable);
			}
		}
		
		@Override
		public int hashCode() {
			return super.hashCode(); // Should use Object hashCode
		}
		
		/** Use this just for debugging - proper conversion to a String is performed by an IPrinter */
		@Override
		public String toString() {
			return symbol.value().toString();
		}

		@Override
		public </*@Nullable*/T> /*@Nullable*/T accept(IVisitor</*@Nullable*/T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
		
		@Override
		public IIdentifier identifier() {
			return symbol;
		}
		
		@Override
		public ISort eval(List<ISort> sorts) {
			// Do nothing to evaluate a parameter that does not have arguments
			if (!sorts.isEmpty()) throw new SMT.InternalException("May not call eval on an IParameter with arguments");
			return this;
		}
		
		@Override
		public int intArity() {
			return 0;
		}
	}

}
