/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IParameterizedIdentifier;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.ISort.IFcnSort;
import org.smtlib.ISort.IParameter;

// FIXME - define an interface for symbol table?

/** This class manages a symbol table used for storing definitions and looking up ids in expressions.
 *  The table maps names to Entry objects that hold information about the defined symbol. */
public class SymbolTable {

	/** true if the Array theory has been set */
	// Used only while we have store and select built in
	public boolean arrayTheorySet = false;
	
	/** true if the bit-vector theory has been set */
	// Used only while we have BitVec built in
	public boolean bitVectorTheorySet = false;
	
	/** true if the RealsInts theory is set (which allows implicit promotion of ints to reals) */
	public boolean realsIntsTheorySet = false;
	
	/** The logic that is being used - this value is used to check that 
	 * expressions, etc., conform to the language restrictions of the current
	 * logic.
	 */
	public ILogic logicInUse = null;
	
	/** A reference to the Configuration for this instance of SMT. */
	public SMT.Configuration smtConfig;
	
	/* The tops of the stack are at the beginning of the lists.  The table 
	 * manages a stack of scopes, each stack element holds a scope.  
	 * Within a scope, a symbol can be defined with various different arities 
	 * (and multiple mappings for a given arity) and different sort arguments. 
	 */
	
	//@ private invariant sorts = sortStack.get(0);
	/** The stack of Sort declaration scopes */
	private List<Map<IIdentifier,ISort.IDefinition>> sortStack;
	/** The top-most Sort scope */
	private Map<IIdentifier,ISort.IDefinition> sorts;
	
	//@ private invariant names == symStack.get(0);
	/** The stack of Symbol scopes */
	private List<Map<IIdentifier,Map<Integer,List<Entry>>>> symStack;
	/** The top-most Symbol scope */
	private Map<IIdentifier,Map<Integer,List<Entry>>> names;
	
	/** An object that holds all the information about the defined symbol (or aliased definition). */
	public static class Entry {
		
		/** Constructs a symbol table entry */
		public Entry(IIdentifier name, ISort.IFcnSort sort, /*@Nullable*/ List<IExpr.IAttribute<?>> attrs) {
			this.name = name;
			this.sort = sort;
			this.attributes = attrs;
			this.definition = null;
		}
		
		/** The identifier */ 
		public IIdentifier name;
		/** The Sort of the identifier */ // FIXME _ what about parameter names ?
		public ISort.IFcnSort sort;
		/** Any attributes (null if none), e.g. :left-assoc */
		public /*@Nullable*/ List<IExpr.IAttribute<?>> attributes;
		/** The definition of the symbol, if any */
		public /*@Nullable*/ IExpr definition;
	}
	
	/** An iterator over all of the Symbols in the symbol scope stack from the top-most scope
	 * on down.
	 * @author David R. Cok
	 */
	public static class Iterator implements java.util.Iterator<Entry> {
		private java.util.Iterator<Map<IIdentifier,Map<Integer,List<Entry>>>> stackIter;
		private /*@Nullable*/ java.util.Iterator<Map<Integer,List<Entry>>> arityIter = null;
		private /*@Nullable*/ java.util.Iterator<List<Entry>> symIter = null;
		private /*@Nullable*/ java.util.Iterator<Entry> entryIter = null;
		
		/** Constructs a new iterator, initialized at the beginning */
		public Iterator(SymbolTable sym) {
			stackIter = sym.symStack.iterator();
		}
		
		/*@AssertNonNullIfTrue({"symIter"})*/
		@Override
		public boolean hasNext() {
			while (entryIter == null || !entryIter.hasNext()) {
				while (symIter == null || !symIter.hasNext()) {
					while (arityIter == null || !arityIter.hasNext()) {
						if (!stackIter.hasNext()) return false;
						arityIter = stackIter.next().values().iterator();
					}
					symIter = arityIter.next().values().iterator();
				}
				entryIter = symIter.next().iterator();
			}
			return true;
		}
		
		@Override
		public Entry next() {
			if (!hasNext()) throw new NoSuchElementException();
			return entryIter.next();
		}
		
		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}
	}
	
	/** Constructs an empty symbol table */
	public SymbolTable(SMT.Configuration smtConfig) {
		this.smtConfig = smtConfig;
		clear(false);
	}
	
	/** Makes a copy of the symbol table */
	public SymbolTable(SymbolTable s) {
		clear(false);
		this.smtConfig = s.smtConfig;
		sortStack = new LinkedList<Map<IIdentifier,ISort.IDefinition>>();
		symStack = new LinkedList<Map<IIdentifier,Map<Integer,List<Entry>>>>();
		sortStack.addAll(s.sortStack);
		symStack.addAll(s.symStack);
		names = symStack.get(0);
		sorts = sortStack.get(0);
	}
	
	/** Returns a fresh iterator over the symbol table's contents */
	public Iterator iterator() {
		return new Iterator(this);
	}
	
	/** Initializes the symbol table with an empty background frame and one empty frame. */
	public void clear(boolean keepBackground) {
		if (keepBackground) {
			while (sortStack.size() > 1) sortStack.remove(0);
			while (symStack.size() > 1) symStack.remove(0);
		} else {
			sortStack = new LinkedList<Map<IIdentifier,ISort.IDefinition>>();
			symStack = new LinkedList<Map<IIdentifier,Map<Integer,List<Entry>>>>();
			push(); // an empty background frame
			push(); // an empty primary frame
		}
	}

	/** Adds a new empty frame on the top of the symbol table stack. */
	public void push() {
		sortStack.add(0,sorts=new HashMap<IIdentifier,ISort.IDefinition>());
		symStack.add(0,names=new HashMap<IIdentifier,Map<Integer,List<Entry>>>());
	}
	
	/** Combines the top two symbol scopes, removing the current top scope; presumes that there
	 * is no shadowing of symbols; the top sort scope is discarded.
	 */ // TODO - say more about why this is used/needed; also review this
	public void merge() {
		Map<IIdentifier,Map<Integer,List<SymbolTable.Entry>>> oldnames = names;
		pop();
		// Put everything in oldnames into the current top
		for (Map<Integer,List<SymbolTable.Entry>> e: oldnames.values()) {
			for (List<SymbolTable.Entry> ee: e.values()) {
				for (SymbolTable.Entry entry: ee) {
					// We have already checked that there is no shadowing
					add(entry);
				}
			}
		}
	}
	
	/** Removes the top frame from the symbol table stack. 
	 * The symbol table must have at least one non-background scope or an 
	 * InternalException will be thrown.
	 */
	public void pop() {
		// The comparison is <= 1 since there is always also the background scope
		if (symStack.size() <= 1) {
			// We throw an InternalException (that is, a bug), since pop should not be called if
			// there are no scopes to pop.
			throw new SMT.InternalException("Invalid pop - no more symbol table scopes to pop");
		}
		sortStack.remove(0);
		symStack.remove(0);
		sorts = sortStack.get(0);
		names = symStack.get(0);
	}
	
	/** Removes the previous background frame, then removes the top frame and 
	 * inserts it as the bottom (background) frame. */
	public void moveToBackground() {
		sortStack.remove(sortStack.size()-1);
		symStack.remove(symStack.size()-1);
		sortStack.add(sortStack.remove(0));
		symStack.add(symStack.remove(0));
		names = symStack.get(0);
		sorts = sortStack.get(0);
	}
	
	/** Adds the given symbol as a sort to the top scope of the sort table; 
	 * returns false if the given symbol is already in the top scope (and the sort table is unchanged);
	 * returns true if the symbol is not already in the top scope.
	 * @param symbol the symbol to add
	 * @return true if successfully added, false if already present
	 */
	public boolean addSortParameter(ISymbol symbol) {
		ISort.IDefinition previous = sorts.put(symbol, smtConfig.sortFactory.createSortParameter(symbol));
		if (previous == null) return true;
		sorts.put(symbol, previous);
		return false;
	}
	
	/** Adds a new sort declaration to the top frame
	 * 
	 * @param identifier the identifier of the new Sort definition
	 * @param arity the arity of the new Sort definition
	 * @return true if successfully added, false if there already is a sort 
	 * (in any scope) with this identifier
	 */
	public boolean addSortDefinition(IIdentifier identifier, INumeral arity) {
		// We don't allow shadowing of previous sort definitions, so check for them
		ISort.IDefinition s = lookupSort(identifier);
		if (s != null) return false;
		
		ISort.IDefinition def = smtConfig.sortFactory.createSortFamily(identifier,arity);
		sorts.put(identifier, def);
		return true;
	}
	
	/** Adds a new sort abbreviation definition to the top frame
	 * 
	 * @param identifier the name of the new Sort definition
	 * @param parameters the names of the parameters of the Sort abbreviation
	 * @param definition the expression of the Sort abbreviation
	 * @return true if successfully added, false if there already is a sort by 
	 * this name in the top scope
	 */ // FIXME - why is this only the top scope and the previous call is any scope?
	public boolean addSortDefinition(IIdentifier identifier, List<IParameter> parameters, ISort definition) {
		ISort.IDefinition s = sorts.get(identifier);
		if (s != null) return false;
		sorts.put(identifier, smtConfig.sortFactory.createSortAbbreviation(identifier,parameters,definition));
		return true;
	}
	
	/** Looks up the Sort definition with the given name
	 * 
	 * @param name the name of the Sort definition to find
	 * @return null if not found
	 */
	/*@Nullable*/
	public ISort.IDefinition lookupSort(IIdentifier name) {
		for (Map<IIdentifier,ISort.IDefinition> set: sortStack) {
			ISort.IDefinition s = set.get(name);
			if (s != null) return s;
		}
		
		// FIXME _ improve so this is not hard coded
		if (name instanceof IParameterizedIdentifier) {
			IParameterizedIdentifier pf = (IParameterizedIdentifier)name;
			if (bitVectorTheorySet && pf.headSymbol().toString().equals("BitVec")) { // FIXME -  toString() or value()?
				if (pf.numerals().size() != 1) {
					return new ISort.ErrorDefinition(name,"A bit-vector sort must have exactly one numeral",
							pf.numerals().size() > 1 ? pf.numerals().get(1).pos()
									: pf.headSymbol().pos());
				}
				if (pf.numerals().get(0).intValue() == 0) {
					return new ISort.ErrorDefinition(name,"A bit-vector sort must have a length of at least 1",pf.numerals().get(0).pos());
				}
				ISort.IDefinition def = smtConfig.sortFactory.createSortFamily(name,smtConfig.exprFactory.numeral(0));
				sorts.put(name, def);
				return def;
			}
		}

		return null;
	}
	
	/** Lookup the Symbol with the given identifier and arity, returning its Sort.
	 * @param arity the arity of the Symbol
	 * @param name the name of the Symbol
	 * @return null if not found, the Sort of the Symbol if found
	 */
	/*@Nullable*/
	public IFcnSort lookup(int arity, IIdentifier name) {
		for (Map<IIdentifier,Map<Integer,List<Entry>>> set: symStack) {
			Map<Integer,List<Entry>> arityMap = set.get(name);
			if (arityMap != null) {
				List<Entry> entrylist = arityMap.get(arity);
				if (entrylist != null && entrylist.size() > 0) return entrylist.get(0).sort;
			}
		}
		return null;
	}

	/** Lookup the Symbol with the given identifier, returning a Map of arity to List&lt;Entry&gt;.
	 * @param name the name of the Symbol
	 * @return null if not found, the corresponding List&lt;Entry&gt from the 
	 * top-most scope in which the identifier is found
	 */
	public /*@Nullable*/ Map<Integer,List<Entry>> lookup(IIdentifier name) {
		for (Map<IIdentifier,Map<Integer,List<Entry>>> set: symStack) {
			Map<Integer,List<Entry>> arityMap = set.get(name);
			if (arityMap != null) return arityMap;
		}
		return null;
	}
	
	// FIXME - review
	/** Lookup a Symbol with the given name and argument Sorts and result Sort.
	 * @param name the name to find
	 * @param argSorts the Sorts of the arguments
	 * @return the result Sort
	 */
	// The background scope may overload an identifier with definitions of the same or
	// different arity (but different sort). However, in non-background scopes, no 
	// overloading is allowed of any arity in any scope.
	/*@Nullable*/
	public Entry lookup(IIdentifier name, List<ISort> argSorts, ISort resultSort) {
		Entry found = null;
		boolean foundMatchButNotOnResult = false;
		int arity = argSorts.size();
		for (Map<IIdentifier,Map<Integer,List<Entry>>> set: symStack) {
			Map<Integer,List<Entry>> arityMap = set.get(name);
			if (arityMap != null) {
				// We have a name match
				// First check for an exact match on arity
				List<Entry> entrylist = arityMap.get(arity);
				if (entrylist != null) for (Entry entry: entrylist) {
					java.util.Iterator<ISort> actuals = argSorts.iterator();
					java.util.Iterator<ISort> defs = Arrays.asList(entry.sort.argSorts()).iterator();
					while (actuals.hasNext() && defs.hasNext()) {
						if (!defs.next().equals(actuals.next())) { entry = null; break; }
					}
					// Cases to consider
					//   resultSort != null & just one argument sort match -> error - not supposed to use a qualifier
					//   resultSort != null & multiple argument sort matches -> pick the one that matches on result sort
					//   resultSort == null & and just one argument sort match -> return it
					//   resultSort == null & multiple argument sort matches -> ambiguous
						
					if (entry != null) {
						// Have a match on the arguments, so check for a match on the result
						if (resultSort != null) {
							if (resultSort.equals(entry.sort.resultSort())) {
								if (found != null) {
									// FIXME - there appear to be two entries that match on all arguments and the result
									return null;
								} else {
									found = entry;
								}
							} else {
								foundMatchButNotOnResult = true;
							}
						} else {
							// No result sort specified - there should not be any overloading
							if (found != null) {
								// Found something previously and now have this match - so ambiguous
								// FIXME - no place to give an error message that the result sort is ambiguous
								return null;
							}
							found = entry;
							// Otherwise have just one match - keep checking the rest of the list
						}
					}
				}
				if (resultSort != null && found != null && !foundMatchButNotOnResult) {
					// FIXME - should report unneeded disambiguation
					return null;
				}
				if (found != null) return found;
				
					// Check for left-assoc etc.
				if (argSorts.size() <= 2) return null;
				entrylist = arityMap.get(2);
				if (entrylist != null) outer: for (Entry entry: entrylist) {
					ISort left = entry.sort.argSorts()[0];
					ISort right = entry.sort.argSorts()[1];
					java.util.Iterator<ISort> actuals = argSorts.iterator();
					if (hasAttribute(entry,":left-assoc")) {
						if (!actuals.next().equals(left)) continue;
						while (actuals.hasNext()) {
							if (!actuals.next().equals(right)) continue outer;
						}
					} else if (hasAttribute(entry,":right-assoc")) {
						ISort sort = actuals.next();
						while (actuals.hasNext()) {
							if (!sort.equals(left)) continue outer;
							sort = actuals.next();
						}
						if (!sort.equals(right)) continue;
					} else if (hasAttribute(entry,":chainable") || hasAttribute(entry,":pairwise")) {
						while (actuals.hasNext()) {
							ISort sort = actuals.next();
							if (!sort.equals(left)) continue outer;
						}
					} else {
						// None of the attributes apply
						continue;
					}
					return entry;
				}
				return null;
			}
		}
		return null;
	}
	
	/** Returns true if the entry contains a value for the given attribute name */ // FIXME - lookup by keyword?
	private boolean hasAttribute(Entry entry, String attr) {
		for (IExpr.IAttribute<?> a: entry.attributes) {
			if (a.keyword().value().equals(attr)) return true;
		}
		return false;
	}
	
	/** Adds the given entry to the symbol table.
	 * @param entry the Entry to add
	 */
	public void add(Entry entry) {
		Map<IIdentifier,Map<Integer,List<Entry>>> lnames = names;
		if (smtConfig.globalDeclarations) {
			lnames = symStack.get(symStack.size()-1);
		}
		Map<Integer,List<Entry>> arityMap = lnames.get(entry.name);
		if (arityMap == null) {
			arityMap = new HashMap<Integer,List<Entry>>();
			lnames.put(entry.name,arityMap);
		}
		List<Entry> entrylist = arityMap.get(entry.sort.argSorts().length);
		if (entrylist == null) {
				entrylist = new LinkedList<Entry>();
				arityMap.put(entry.sort.argSorts().length,entrylist);
		}
		entrylist.add(entry);
	}
	
	/** Adds the given entry to the symbol table; if overload is false and the 
	 * identifier in the entry is already in the table,
	 * the method returns false (without changing the symbol table); 
	 * otherwise the entry is added and the
	 * method returns true
	 * 
	 * @param entry the Entry to add
	 */
	public boolean add(Entry entry, boolean overload) {
		// Check if the entry is already present in any scope;
		// return false if it is.  Allow overloading if the second argument is true.
		if (!overload) {
			for (Map<IIdentifier,Map<Integer,List<Entry>>> set: symStack) {
				if (set.get(entry.name) != null) {
					return false;
				}
			}
		}
		// Symbol is not present or overloading is allowed, so add it
		add(entry);
		return true;
	}
}
