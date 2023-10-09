package org.smtlib;

import java.util.List;

import org.smtlib.IExpr.IIdentifier;

/** This interface represents the functionality of an SMT-LIB language - the combination of one or more theories and various restrictions 
 * on the permitted expressions. The various checks for permitted expressions and declarations may refer to the current state of the symbol table.
 * @author David Cok
 */

public interface ILanguage {
	// FIXME - should we be able to query the theories that are part of this language; the name of the language?
	// FIXME - should we add the symbol table to the argument lists?
	
	/** Checks whether the given expression is permitted in the language, throwing an exception if not */
	void validExpression(IExpr expression) throws IVisitor.VisitorException;
	
	/** Checks whether the given function declaration is permitted in the language, throwing an exception if not */
	void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException;
	
	/** Checks whether the given sort declaration is permitted in the language, throwing an exception if not */
	void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException;
}