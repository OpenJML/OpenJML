/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.impl;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.*;

import org.smtlib.*;

// FIXME - Decide whether we use reference or structural equality - either complete or remove equals and hashCode

/** This class defines a number of subclasses that implement the SMT-LIB abstract AST;
 * they are used by commands and expressions. */
public abstract class SMTExpr implements IExpr {
	static public SMT.Configuration smtConfig;
	
	/** Just a convenient base class to provide some method implementations */
	static abstract public class Literal<T> extends Pos.Posable {
		protected T value;
		public T value() { return value; }
		public Literal(T value) { this.value = value; }
		public boolean isOK() { return false; }
		public boolean isError() { return false; }
		
		/** Just for debugging - use a Printer for proper output */
		@Override
		public String toString() { return value.toString(); }
	}

	/** This class represents an SMT Numeral expression or syntax token */
	static public class Numeral extends Literal<BigInteger> implements INumeral {
		/** A value equivalent to the BigInteger, when it is in range. */
		protected int number;
		
		/** Constructs a Numeral with the given value. */  // FIXME - test with too big a number
		public Numeral(BigInteger i) {
			super(i);
			number = value.intValue();
		}
		
		/** Constructs a Numeral with the given value. */ 
		public Numeral(int i) {
			super(BigInteger.valueOf(i));
			number = i;
		}
		
		@Override
		public int intValue() { return number; }
		
		@Override
		public String kind() { return "numeral"; }
		
		/** Equal to any INumeral with the same numeric value */
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof INumeral)) return false;
			return ((INumeral)o).value().equals(value);
		}
		
		@Override
		public int hashCode() { return value.hashCode(); }
		
		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

	}
	
	/** This class represents an SMT String literal expression or syntax token */
	static public class StringLiteral extends Literal<String>  implements IStringLiteral {
		
		// The 'value' field holds an unquoted string
		
		/** If quoted is true, then the value should be the string with all escape sequences intact and
		 * enclosing quotes in place; if quoted is false, the value should not have enclosing quotes and
		 * any escape sequences should be replaced by the actual characters.
		 */
		public StringLiteral(String value, boolean quoted) {
			super(quoted ? smtConfig.utils.unescape(value) : value);
		}
		
		/** For a StringLiteral, toString produces a properly escaped and quoted string */
		@Override
		public String toString() { return smtConfig.utils.quote(value); }

		@Override
		public String kind() { return "string-literal"; }

		/** Equal to any IStringLiteral with the same string value */
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IStringLiteral)) return false;
			return ((IStringLiteral)o).value().equals(value);
		}
		
		@Override
		public int hashCode() { return value.hashCode(); }
		
		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}
	
	/** This class represents an SMT Decimal literal expression or syntax token */
	static public class Decimal extends Literal<BigDecimal> implements IDecimal {
		
		public Decimal(BigDecimal v) {
			super(v);
		}
		
		@Override
		public String kind() { return "decimal"; }

		/** Equal to any IDecimal with the same BigDecimal value */
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IDecimal)) return false;
			return ((IDecimal)o).value().equals(value);
		}
		
		@Override
		public int hashCode() { return value.hashCode(); }
		
		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}
	
	/** This class represents an SMT Keyword syntax token */
	static public class Keyword extends Pos.Posable  implements IKeyword {
		protected String value; // Keyword string with leading colon (TODO - check this)
		
		public Keyword(String v) {
			super();
			value = v.intern();
		}
		
		@Override
		public String value() { return value; }
		
		@Override
		public String kind() { return "keyword"; }

		/** Equal to any IKeyword designating the same abstract keyword. */
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IKeyword)) return false;
			return ((IKeyword)o).value().equals(value);
		}
		
		@Override
		public int hashCode() { 
			return value.hashCode(); 
		}
		
		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

		/** Just for debugging - use a Printer for proper output */
		@Override
		public String toString() { return value.toString(); }
	}
	
	/** This class represents an SMT as-identifier AST */
	static public class AsIdentifier extends Pos.Posable implements IAsIdentifier {
		protected IIdentifier head;
		protected ISort qualifier;
		
		public AsIdentifier(IIdentifier symbol, ISort qualifier) {
			this.head = symbol;
			this.qualifier = qualifier;
		}
		
		@Override
		public IIdentifier head() { return head; }
		
		@Override
		public ISymbol headSymbol() { return head.headSymbol(); }
		
		@Override
		public ISort qualifier() { return qualifier; }
		
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof AsIdentifier)) return false;
			AsIdentifier p = (AsIdentifier)o;
			return this.head().equals(p.head()) &&
					this.qualifier().equals(p.qualifier);
		}
		
		@Override
		public int hashCode() {
			int hash = (head().hashCode() << 4) ^ qualifier().hashCode();
			return hash;
		}
		
		@Override
		public String kind() { return "qualifiedSymbol"; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
		
		/** Just for debugging - use a Printer for proper output */
		@Override
		public String toString() { return org.smtlib.sexpr.Printer.write(this); }

		@Override
		public boolean isOK() { throw new RuntimeException(); } // FIXME - should never be called

		@Override
		public boolean isError() { throw new RuntimeException(); } // FIXME - should never be called
	}
	
	/** This class represents an SMT parameterized-identifier AST */
	static public class ParameterizedIdentifier extends Pos.Posable implements IParameterizedIdentifier {
		protected IIdentifier head;
		protected List<INumeral>  nums;
		
		public ParameterizedIdentifier(IIdentifier symbol, List<INumeral> nums) {
			this.head = symbol;
			this.nums = nums;
		}
		
		@Override
		public IIdentifier head() { return this; }
		
		@Override
		public ISymbol headSymbol() { return head.headSymbol(); }
		
		@Override
		public List<INumeral> numerals() {return nums; }
		
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof ParameterizedIdentifier)) return false;
			ParameterizedIdentifier p = (ParameterizedIdentifier)o;
			if (! this.headSymbol().equals(p.headSymbol())) return false;
			if (this.nums.size() != p.nums.size()) return false;
			for (int i=0; i< this.nums.size(); i++) {
				if (!this.nums.get(i).equals(p.nums.get(i))) return false;
			}
			return true;
		}
		
		@Override
		public int hashCode() {
			int hash = headSymbol().hashCode();
			Iterator<INumeral> iter = this.numerals().iterator();
			while (iter.hasNext()) {
				hash = (hash<<1) + iter.next().hashCode();
			}
			return hash;
		}
		
		@Override
		public String kind() { return "parameterizedSymbol"; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
		
		/** Just for debugging - use a Printer for proper output */
		@Override
		public String toString() { return org.smtlib.sexpr.Printer.write(this); }

		@Override
		public boolean isOK() { throw new RuntimeException(); } // FIXME - should never be called

		@Override
		public boolean isError() { throw new RuntimeException(); } // FIXME - should never be called
	}
	
	/** This class represents an SMT Symbol */
	static public class Symbol extends Pos.Posable  implements ISymbol {
		
		 // FIXME - this incorporates some concrete syntax
		
		protected String value; // canonical string (without bars)
		protected String originalString;
		
		/** The argument is a Symbol string, with or without enclosing bars */
		public Symbol(String v) { 
			value = v.length() > 0 && v.charAt(0) == '|' ? v.substring(1,v.length()-1) : v;
			originalString = v;
		}
		
		/** Returns the unique string for this symbol (e.g. modulo enclosing bars) */
		@Override
		public String value() { return value; }
		
		/** Returns the original String - use for debugging and use a printer to print to concrete syntax. */
		@Override
		public String toString() { return originalString; }
		
		@Override
		public ISymbol headSymbol() { return this; }
		
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof Symbol)) return false;
			return ((Symbol)o).value().equals(value());
		}
		
		@Override
		public int hashCode() {
			return value().hashCode();
		}
		
		@Override
		public String kind() { return "symbol"; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { 
			return v.visit(this); 
		}
		
		@Override
		public boolean isOK() { return value.equals(Response.OK) || value.equals(Response.EMPTY); }

		@Override
		public boolean isError() { return false; }
		
//		// FIXME - do we want these?
//		public static class Parameter extends Symbol implements IParameter {
//			public Parameter(ISymbol s) { super(s.toString()); pos = s.pos(); }
//		}
//
//		public static class LetParameter extends Symbol implements ILetParameter {
//
//
//			public LetParameter(ISymbol s) { super(s.toString()); pos = s.pos();  }
//		}

	}
	
	static public class FcnExpr extends Pos.Posable implements IFcnExpr {
		protected IQualifiedIdentifier id;
		protected List<IExpr> args;
		
		public FcnExpr(IQualifiedIdentifier id, List<IExpr> args) {
			this.id = id;
			this.args = args;
		}

		@Override
		public IQualifiedIdentifier head() {
			return id;
		}

		@Override
		public List<IExpr> args() {
			return args;
		}
		
		@Override
		public String kind() { return "fcn"; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

		/** Just for debugging - use a Printer for proper output */
		@Override
		public String toString() { return org.smtlib.sexpr.Printer.write(this); }

		@Override
		public boolean isOK() { throw new RuntimeException(); } // FIXME - should never be called

		@Override
		public boolean isError() { throw new RuntimeException(); } // FIXME - should never be called
	}

	static public class BinaryLiteral extends Literal<String>  implements IBinaryLiteral {
		
		public BinaryLiteral(String unquotedValue) {
			super(unquotedValue);
			length = unquotedValue.length();
			intvalue = new BigInteger(unquotedValue,2);
		}
		
		int length;
		BigInteger intvalue;
		
		@Override
		public BigInteger intValue() { return intvalue; }
		
		@Override
		public int length() { return length; }
		
		@Override
		public String kind() { return "binary"; }

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IBinaryLiteral)) return false;
			return ((IBinaryLiteral)o).intValue().equals(intvalue);
		}
		
		@Override
		public int hashCode() { return intvalue.hashCode(); }
		
		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}
	
	static public class HexLiteral extends Literal<String>  implements IHexLiteral {
		
		public HexLiteral(String unquotedValue) {
			super(unquotedValue);
			length = unquotedValue.length();
			intvalue = new BigInteger(unquotedValue,16);
		}
		
		int length; // in hex digits
		BigInteger intvalue;
		
		@Override
		public BigInteger intValue() { return intvalue; }
		
		@Override
		public int length() { return length; }
		
		@Override
		public String kind() { return "hex-literal"; }

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (!(o instanceof IHexLiteral)) return false;
			return ((IHexLiteral)o).intValue().equals(intvalue);
		}
		
		@Override
		public int hashCode() { return value.hashCode(); }
		
		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}
	
	static public class Let extends Pos.Posable  implements ILet {
		
		protected List<IBinding> bindings;
		protected IExpr expression;
		
		public Let(List<IBinding> bindings, IExpr expr) {
			this.bindings = bindings;
			this.expression = expr;
		}
		
		@Override
		public List<IBinding> bindings() { return bindings; }
		
		@Override
		public IExpr expr() { return expression; }

		@Override
		public String kind() {
			return "let";
		}

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

		@Override
		public boolean isOK() { throw new RuntimeException(); } // FIXME - should never be called

		@Override
		public boolean isError() { throw new RuntimeException(); } // FIXME - should never be called
	}

	static public class Exists extends Pos.Posable implements IExists {

		protected List<IDeclaration> parameters;
		protected IExpr expression;
		
		public Exists(List<IDeclaration> parameters, IExpr expr) {
			this.parameters = parameters;
			this.expression = expr;
		}
		
		@Override
		public List<IDeclaration> parameters() { return parameters; }
		
		@Override
		public IExpr expr() { return expression; }

		@Override
		public String kind() {
			return "exists";
		}

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

		@Override
		public boolean isOK() { throw new RuntimeException(); } // FIXME - should never be called

		@Override
		public boolean isError() { throw new RuntimeException(); } // FIXME - should never be called
	}

	static public class Forall extends Pos.Posable implements IForall {

		protected List<IDeclaration> parameters;
		protected IExpr expression;
		
		public Forall(List<IDeclaration> parameters, IExpr expr) {
			this.parameters = parameters;
			this.expression = expr;
		}
		
		@Override
		public List<IDeclaration> parameters() { return parameters; }
		
		@Override
		public IExpr expr() { return expression; }
		
		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

		@Override
		public String kind() {
			return "forall";
		}

		@Override
		public boolean isOK() { throw new RuntimeException(); } // FIXME - should never be called

		@Override
		public boolean isError() { throw new RuntimeException(); } // FIXME - should never be called
	}

	static public class Declaration extends Pos.Posable implements IDeclaration {
		ISymbol parameter;
		ISort sort;
		
		public Declaration(ISymbol parameter, ISort sort) {
			this.parameter = parameter;
			this.sort = sort;
		}
		
		@Override
		public ISymbol parameter() { return parameter; }
		
		@Override
		public ISort sort() { return sort; }
		
		// FIXME @Override
		public String kind() {
			return "declaration";
		}

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}

	static public class Binding extends Pos.Posable implements IBinding {
		ISymbol parameter;
		IExpr expr;
		
		public Binding(ISymbol parameter, IExpr expr) {
			this.parameter = parameter;
			this.expr = expr;
		}
		
		@Override
		public ISymbol parameter() { return parameter; }
		
		@Override
		public IExpr expr() { return expr; }
		
		// FIXME @Override
		public String kind() {
			return "binding";
		}

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
		
		@Override
		public String toString() {
			return parameter + ":" + expr;
		}
	}
	
	static public class Attribute<TT extends IAttributeValue> extends Pos.Posable implements IAttribute<TT> {
		protected IKeyword keyword;
		protected TT value;
		protected /*@Nullable*//*@ReadOnly*/IPos pos;
		
		public Attribute(IKeyword keyword, TT value) {
			this.keyword = keyword;
			this.value = value;
		}
		
		@Override
		public boolean isOK() { return false; }
		
		@Override
		public boolean isError() { return false; }
		
		@Override
		public IKeyword keyword() { return keyword; }
		
		@Override
		public TT attrValue() { return value; }
		
		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

		// for debugging only
		@Override
		public String toString() {
			return keyword.toString() + " " + value.toString();
		}
	}
	
	static public class AttributedExpr extends Pos.Posable implements IAttributedExpr {
		
		protected IExpr expression;
		protected List<IAttribute<?>> attributes;
		
		public AttributedExpr(IExpr expression, List<IAttribute<?>> attributes) {
			this.expression = expression;
			this.attributes = attributes;
		}

		@Override
		public String kind() {
			return "attributedExpr";
		}

		@Override
		public IExpr expr() {
			return expression;
		}

		@Override
		public List<IAttribute<?>> attributes() {
			return attributes;
		}

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

		// For debugging only
		@Override
		public String toString() {
			String s = "(! " + expr().toString();
			for (IAttribute<?> a: attributes) s = s + " " + a.toString();
			return s + ")";
		}

		@Override
		public boolean isOK() { throw new RuntimeException(); } // FIXME - should never be called

		@Override
		public boolean isError() { throw new RuntimeException(); } // FIXME - should never be called
	}
	
	static public class Logic implements ILogic {
		/** Creates a logic */
		public Logic(ISymbol name, Collection<IAttribute<?>> attributes) {
			this.logicName = name;
			for (IAttribute<?> attr: attributes) {
				this.attributes.put(attr.keyword(),attr);
			}
		}
		/** The name of the logic */
		protected ISymbol logicName;
		
		/** The logic's attributes */
		protected Map<IKeyword,IAttribute<?>> attributes = new HashMap<IKeyword,IAttribute<?>>();
		
		/** The name of the logic */
		@Override
		public ISymbol logicName() { return logicName; }
		
		/** The attributes, as a Map, keyed by the keyword in the attribute */
		@Override
		public Map<IKeyword,IAttribute<?>> attributes() { return attributes; }
		
		/** The value of a given attribute */
		@Override
		public /*@Nullable*/IAttributeValue value(IKeyword keyword) {
			IAttribute<?> attr = attributes.get(keyword);
			if (attr == null) return null;
			return attr.attrValue();
		}
		
		// FIXME - do we really want this here
		@Override
		public void validExpression(IExpr expr)  throws IVisitor.VisitorException {}

		@Override
		public void checkFcnDeclaration(IExpr.IIdentifier id, List<ISort> argSorts, ISort resultSort, /*@Nullable*/IExpr definition) throws IVisitor.VisitorException {}

		@Override
		public void checkSortDeclaration(IIdentifier id, List<ISort.IParameter> params, ISort expr) throws IVisitor.VisitorException {}

		// FIXME @Override
		public String kind() { return "logic"; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}
	
	static public class Theory implements ITheory {
		/** Creates a theory */
		public Theory(ISymbol name, Collection<IAttribute<?>> attributes) {
			this.theoryName = name;
			for (IAttribute<?> attr: attributes) {
				this.attributes.put(attr.keyword(),attr);
			}
		}
		/** The name of the theory */
		protected ISymbol theoryName;
		
		/** The theory attributes */
		protected Map<IKeyword,IAttribute<?>> attributes = new HashMap<IKeyword,IAttribute<?>>();
		
		/** The name of the theory */
		@Override
		public ISymbol theoryName() { return theoryName; }
		
		/** The attributes, as a Map, keyed by the keyword in the attribute */
		@Override
		public Map<IKeyword,IAttribute<?>> attributes() { return attributes; }
		
		/** The value of a given attribute */
		@Override
		public /*@Nullable*/ IAttributeValue value(IKeyword keyword) {
			IAttribute<?> attr = attributes.get(keyword);
			if (attr == null) return null;
			return attr.attrValue();
		}
		
		//FIXME @Override
		public String kind() { return "theory"; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }
	}
	
	static public class Error extends Pos.Posable  implements IError {
		protected String message;
		
		public Error(String msg) {
			message = msg;
		}
		
		/** Returns the error message */
		@Override
		public String value() {
			return this.message;
		}
		
		/** Shows a string for debugging; use an IPrinter to get concrete syntax */
		@Override
		public String toString() {
			return "Error: " + this.message;
		}
		
		@Override
		public String kind() { return "error"; }

		@Override
		public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

		@Override
		public boolean isOK() { throw new RuntimeException(); } // FIXME - should never be called

		@Override
		public boolean isError() { throw new RuntimeException(); } // FIXME - should never be called
	}
	

}
