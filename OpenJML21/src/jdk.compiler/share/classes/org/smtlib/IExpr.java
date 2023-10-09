/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

import org.smtlib.ICommand.IScript;
import org.smtlib.IPos.IPosable;

/** This interface represents the functionality for any class implementing an SMT-LIB term or formula */
public interface IExpr extends IAccept, IPosable, IAttributeValue {
	
	/** Helpful method that indicates the class of expression, used in human-readable messages. */
	//@ pure
	String kind();

	/** The interface defining the factory type for producing objects of various subtypes of IExpr;
	 * the IPos argument is an optional argument giving information about the textual position of an expression. */
	static public interface IFactory {
		/** Creates a INumeral object; the argument must be a string of digits. */
		INumeral numeral(String v);
		/** Creates a INumeral object; the argument must be non-negative */
		//@ requires v >= 0;
		INumeral numeral(long v);
		/** Creates a IDecimal object; the argument must be a string of digits with just one decimal point */
		IDecimal decimal(String v);
		/** The argument is a pure character string, with no Java or SMTLIB escapes or enclosing quotes */
		IStringLiteral unquotedString(String v);
		/** The argument is SMTLIB escaped, with enclosing quotes */
		IStringLiteral quotedString(String v);
		/** Creates a IKeyword object from a canonical string representation */
		IKeyword keyword(String v);
		/** Creates a IBinaryLiteral from a string of 0 and 1 digits */
		IBinaryLiteral binary(String v);
		/** Creates a IHexLiteral object from a string of hex digits (either case) */
		IHexLiteral hex(String v);
		/** Creates a ISymbol object from a canonical String representation of the symbol */
		ISymbol symbol(String v);
		/** Creates an attribute with just a keyword and no attribute value */
		IAttribute<?> attribute(IKeyword k);
		/** Creates an attribute with a keyword and a value */
		<T extends IAttributeValue> IAttribute<T> attribute(IKeyword k, T value);
		/** Creates an attributed expression (an expression with a positive number of attributes) */
		//@ requires attributes.size() > 0;
		IAttributedExpr attributedExpr(IExpr e, List<IAttribute<?>> attributes);
		/** Creates an attributed expression with just one attribute. */
		<T extends IAttributeValue> IAttributedExpr attributedExpr(IExpr e, IKeyword key, /*@Nullable*/T value);
		/** Creates a function expression (perhaps with an empty argument list) */
        IFcnExpr fcn(IQualifiedIdentifier id, List<IExpr> args);
		/** Creates a function expression (perhaps with an empty argument list) */
        IFcnExpr fcn(IQualifiedIdentifier id, IExpr... args);
        /** Creates a parameterized identifier from a symbol and a non-empty list of numerals */
        //@ requires num.size() > 0;
		IParameterizedIdentifier id(ISymbol symbol, List<INumeral> num);
		/** Creates a 'as' identifier from an identifier and a sort qualifier */
		IAsIdentifier id(IIdentifier identifier, ISort qualifier);
		/** Creates a Let expression */
		//@ requires bindings.size() > 0;
		ILet let(List<IBinding> bindings, IExpr e);
		/** Creates a binding for a Let expression */
		IBinding binding(ISymbol symbol, IExpr expr);
		/** Creates a parameter declaration */
		IDeclaration declaration(ISymbol symbol, ISort sort);
		/** Creates a Forall expression */
		//@ requires params.size() > 0;
        IForall forall(List<IDeclaration> params, IExpr e);
        IForall forall(List<IDeclaration> params, IExpr e, List<IExpr> patterns);
		/** Creates a Exists expression */
		//@ requires params.size() > 0;
        IExists exists(List<IDeclaration> params, IExpr e);
        IExists exists(List<IDeclaration> params, IExpr e, List<IExpr> patterns);

		/** Creates a command script from a file of commands or a list of commands */
		IScript script(/*@Nullable*/IStringLiteral filename, /*@Nullable*/List<ICommand> commands);

		/** Creates an error expression */
		IError error(String text);

	}
	
	/** This interface represents all literal (explicit constant) expressions. */
	static public interface ILiteral extends IExpr, IAttributeValue {
	}
	
	/** This interface represents non-negative integers of arbitrary size. */
	static public interface INumeral extends ILiteral {
		//@ ensures compareTo(BigInteger.ZERO) >= 0;
		/*@ pure */
		BigInteger value();
		
		//@ ensures value().compareTo(BigInteger.valueOf(Integer.INT_MAX)) <= 0 ==> value().intValue() == \result;
		//@ ensures \result >= 0;
		/*@ pure */
		int intValue();
		
	}
	
	/** This interface represents non-negative decimal numbers of arbitrary size
	 * (i.e. an arbitrary non-negative integer divided by an arbitrary non-negative power of ten).
	 */
	static public interface IDecimal extends ILiteral {
		//@ pure
		BigDecimal value();
	}
	
	/** This interface represents SMT-LIB ids; equal ids have equal (using .equals) values
	 * of value().
	 */
	static public interface ISymbol extends IAttributeValue, IIdentifier {
		/** A String giving the canonical value of symbol. */
		//@ pure
		String value();

		/** A printable String giving the original text of this symbol. */
		//@ pure
		@Override
		String toString();
	}
	
	/** This interface represents SMT-LIB attribute and infoflag names. */
	static public interface IKeyword extends IAccept, IPosable{
		/** A canonical representation of keyword key */
		//@ pure
		String value();
		
		/** The original textual representation of the keyword */
		//@ pure
		@Override
		String toString();
		
		/** Helpful method that indicates the class of expression, used in human-readable messages. */
		//@ pure
		String kind();
		
		@Override
		boolean equals(Object o);
	}
	
	/** This interface represents SMT-LIB binary literals */
	static public interface IBinaryLiteral extends ILiteral {
		/** Returns a canonical value of the binary literal: 0 and 1 digits from MSB to LSB */
		String value();
		
		/** The binary value as an unsigned integer */
		BigInteger intValue();
		
		/** Number of binary bits */
		int length();
	}
	
	/** This interface represents SMT-LIB hex literals */
	static public interface IHexLiteral extends ILiteral {
		/** Returns a canonical value of the hex literal; lower-case hex digits from most-significant to least-significant */
		String value(); 
		
		/** The hex value as an unsigned integer */
		BigInteger intValue();
		
		/** Number of hex digits */
		int length();
	}
	
	// FIXME - document toString for all interfaces
	// FIXME - review headSymbol, head
	// FIXME - review IParameter, ILetParameter
	
	/** This interface represents SMT-LIB string literals */
	static public interface IStringLiteral extends ILiteral {
		/** Returns the value without enclosing quotes and without any escape sequences; there may be explicit new line (and other white space characters) */
		//@ pure
		String value();

		/** Returns a value with enclosing quotes and appropriate SMT-LIB escape sequences so that the String value
		 * can be represented with SMT-LIB printable characters; the result may have explicit newline characters. */
		//@ pure
		@Override
		String toString();
	}
	
	/** This interface represents SMT-LIB expressions that are a function identifier applied to one or more arguments. */
	static public interface IFcnExpr extends IExpr {
		/** The function identifier */
		//@ pure
		IQualifiedIdentifier head();
		
		/** The arguments of the function */
		//@ ensures \result.size() > 0;
		//@ pure
		List<IExpr> args();
	}

	/** This interface represents SMT-LIB identifiers for function ids (either ids or parameterized ids
	 * or as-type identifiers) */
	static public interface IQualifiedIdentifier extends IExpr {
		/** The head symbol of the identifier */
		ISymbol headSymbol();
	}
	
	/** This interface represents SMT-LIB identifiers (either ids or parameterized ids) */
	static public interface IIdentifier extends IQualifiedIdentifier {
		/** The head symbol of the identifier */
		@Override
		ISymbol headSymbol();

	}
	
	/** This interface represents SMT-LIB identifiers that are sort qualifiers on function ids */
	static public interface IAsIdentifier extends IQualifiedIdentifier {
		/** The head of the identifier */
		IIdentifier head();
		
		/** The head symbol of the identifier */
		@Override
		ISymbol headSymbol();

		/** The Sort qualifier */
		ISort qualifier();
	}
	
	/** This interface represents SMT-LIB parameterized identifiers */
	static public interface IParameterizedIdentifier extends IIdentifier {
		
		// TODO - document
		IIdentifier head();
		
		/** The head symbol of the identifier */
		@Override
		ISymbol headSymbol();
		
		/** The non-negative integer parameters of the identifier */
		//@ ensures \result.size() > 0;
		List<INumeral> numerals();
	}
	
	/** This interface represents an SMT-LIB expression with attributes. */
	static public interface IAttributedExpr extends IExpr {
		//@ pure
		IExpr expr();
		
		//@ ensures \result.size() > 0;
		//@ pure
		List<IAttribute<?>> attributes();
	}
	
	/** This interface represents an SMT-LIB attribute-value pair */
	static public interface IAttribute<TT extends IAttributeValue> extends IAccept, IPosable, IResponse {
		//@ pure
		IKeyword keyword();
		
		//@ pure
		/*@Nullable*/ TT attrValue();
	}
	
	/** This interface represents a declaration of a parameter and its sort */
	static public interface IDeclaration extends IAccept, IPosable {
		ISymbol parameter();
		ISort sort();
	}
	
	/** This interface represents a binding of a parameter and an expression */
	static public interface IBinding extends IAccept, IPosable {
		ISymbol parameter();
		IExpr expr();
	}
	
	/** This interface represents an SMT-LIB let-expression */
	static public interface ILet extends IExpr {
		//@ ensures \result.size() > 0;
		List<IBinding> bindings();
		IExpr expr();
	}

	/** This interface represents an SMT-LIB quantified forall expression */
	static public interface IForall extends IExpr {
		//@ ensures \result.size() > 0;
		List<IDeclaration> parameters();
		IExpr expr();
	}
	
	/** This interface represents an SMT-LIB quantified exists expression */
	static public interface IExists extends IExpr {
		//@ ensures \result.size() > 0;
		List<IDeclaration> parameters();
		IExpr expr();
	}
	
	/** This interface represents an error, e.g. a parsing error that is part of a larger
	 * expression.  Using an error expression as a sub-expression allows further error
	 * checking to be performed.
	 */
	static public interface IError extends IExpr {
		/** Returns an informational message about the error */
		String value();
	}

}
