/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.impl;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import org.smtlib.*;
import org.smtlib.ICommand.IScript;
import org.smtlib.IExpr.IAsIdentifier;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IAttributedExpr;
import org.smtlib.IExpr.IBinaryLiteral;
import org.smtlib.IExpr.IBinding;
import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IError;
import org.smtlib.IExpr.IExists;
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IExpr.IForall;
import org.smtlib.IExpr.IHexLiteral;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.ILet;
import org.smtlib.IExpr.ILiteral;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IParameterizedIdentifier;
import org.smtlib.IExpr.IQualifiedIdentifier;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IPos.IPosable;
import org.smtlib.ISort.IApplication;
import org.smtlib.ISort.IParameter;
import org.smtlib.impl.SMTExpr.AsIdentifier;
import org.smtlib.impl.SMTExpr.Attribute;
import org.smtlib.impl.SMTExpr.AttributedExpr;
import org.smtlib.impl.SMTExpr.BinaryLiteral;
import org.smtlib.impl.SMTExpr.Binding;
import org.smtlib.impl.SMTExpr.Decimal;
import org.smtlib.impl.SMTExpr.Declaration;
import org.smtlib.impl.SMTExpr.Exists;
import org.smtlib.impl.SMTExpr.FcnExpr;
import org.smtlib.impl.SMTExpr.Forall;
import org.smtlib.impl.SMTExpr.HexLiteral;
import org.smtlib.impl.SMTExpr.Keyword;
import org.smtlib.impl.SMTExpr.Let;
import org.smtlib.impl.SMTExpr.Numeral;
import org.smtlib.impl.SMTExpr.ParameterizedIdentifier;
import org.smtlib.impl.SMTExpr.StringLiteral;
import org.smtlib.impl.SMTExpr.Symbol;
import org.smtlib.impl.Sort.Abbreviation;
import org.smtlib.impl.Sort.Application;
import org.smtlib.impl.Sort.Family;
import org.smtlib.impl.Sort.FcnSort;
import org.smtlib.impl.Sort.Parameter;
import org.smtlib.sexpr.Utils;

// FIXME - spearate out the concrete syntax?

/** Implements a factory for SMT-LIB expressions using the standard concrete syntax.
 * Instances of these IExpr objects have an IPos element. 
 * The various factories are all implemented together in this one class because they
 * use each other mutually; combining them lets them be overridden in a consistent fashion. */
public class Factory implements IExpr.IFactory, ISort.IFactory {
	
	/** Initializes the SMT configuration object for the implementation 
	 * in org.smtlib.impl - all the appropriate factories, etc.
	 * @param config the configuration object to initialize
	 */
	public static void initFactories(SMT.Configuration config) {
		config.responseFactory = new Response.Factory(config);
		Factory f = new Factory();
		config.sortFactory = f;
		config.exprFactory = f;
		config.utils = new Utils(config);
		config.reservedWords.addAll(Utils.reservedWords);
		config.reservedWordsNotCommands.addAll(Utils.reservedWordsNotCommands);
	}
	
	/** Sets the text position for a given instance. This is a template so it can return its
	 * receiver object without the type changing. */
	<T extends IPosable> T setPos(/*@Nullable*//*@ReadOnly*/IPos pos, T t) { t.setPos(pos); return t; }
	
	// The following methods are those of the Sort factory

	@Override
	public Family createSortFamily(IIdentifier identifier, INumeral arity) {
		return new Family(identifier,arity);
	}

	@Override
	public Parameter createSortParameter(ISymbol symbol) {
		return new Parameter(symbol);
	}

	// CAUTION: keeps a reference to the list of ISort parameters
	@Override
	public Application createSortExpression(IIdentifier sortFamily,
			List<ISort> exprs) {
		return new Application(sortFamily,exprs);
	}

	@Override
	public Application createSortExpression(IIdentifier sortFamily,
			ISort... exprs) {
		return new Application(sortFamily, Arrays.asList(exprs));
	}

	@Override
	public Abbreviation createSortAbbreviation(IIdentifier identifier,
			List<IParameter> params, ISort sortExpr) {
		return new Abbreviation(identifier,params,sortExpr);
	}

	@Override
	public FcnSort createFcnSort(ISort[] args, ISort result) {
		return new FcnSort(args,result);
	}

	@Override
	public IApplication Bool() {
		return Sort.Bool();
	}
	
	// The following methods are those of the IExpr factory

	@Override
	public IScript script(/*@Nullable*/IStringLiteral filename, /*@Nullable*/List<ICommand> commands) {
		return new Script(filename,commands);
	}


	@Override
	public INumeral numeral(String v) {
		return new Numeral(new BigInteger(v));
	}

	@Override
	public Numeral numeral(long v) {
		return setPos(null,new Numeral(BigInteger.valueOf(v)));
	}

	@Override
	public IDecimal decimal(String v) {
		return new Decimal(new BigDecimal(v));
	}

	@Override
	public IStringLiteral unquotedString(String v) {
		return new StringLiteral(v,false);
	}

	@Override
	public IStringLiteral quotedString(String v) {
		return new StringLiteral(v,true);
	}

	@Override
	public IKeyword keyword(String v) {
		return new Keyword(v);
	}

	@Override
	public IBinaryLiteral binary(String v) {
		return new BinaryLiteral(v);
	}

	@Override
	public IHexLiteral hex(String v) {
		return new HexLiteral(v);
	}

	@Override
	public ISymbol symbol(String v) {
		return new Symbol(v);
	}

	@Override
	public IAttribute<?> attribute(IKeyword k) {
		return new Attribute<ILiteral>(k,null); // Just using ILiteral because we have to use some type
	}

	@Override
	public <T extends IAttributeValue> IAttribute<T> attribute(IKeyword k, T value) {
		return new Attribute<T>(k,value);
	}

	@Override
	public IAttributedExpr attributedExpr(IExpr e,
			List<IAttribute<?>> attributes) {
		return new AttributedExpr(e,attributes);
	}
	
	static class AttributeList<T> implements IAttributeValue {
	    public List<T> list;
	    public AttributeList(List<T> list) {this.list = list; }
        public IPos pos() { return null; }
        public void setPos(IPos p) {  }
        @Override
        public <T> T accept(org.smtlib.IVisitor<T> v) throws IVisitor.VisitorException { return v.visit(this); }

        // For debugging only
        @Override
        public String toString() {
            String s = "(" ;
            for (T t: list) s = s + " " + t.toString();
            return s + " )";
        }

        @Override
        public boolean isOK() { throw new RuntimeException(); } // FIXME - should never be called

        @Override
        public boolean isError() { throw new RuntimeException(); } // FIXME - should never be called
	}

	@Override
	public <T extends IAttributeValue> IAttributedExpr attributedExpr(IExpr e,
			IKeyword key, T value) {
		IAttribute<T> a = attribute(key,value);
		List<IAttribute<?>> list = new LinkedList<IAttribute<?>>();
		list.add(a);
		return new AttributedExpr(e,list);
	}

	@Override
	public IFcnExpr fcn(IQualifiedIdentifier id, List<IExpr> args) {
		List<IExpr> arglist = new LinkedList<IExpr>();
		for (IExpr a: args) arglist.add(a);
		return new FcnExpr(id,arglist);
	}

	@Override
    public IFcnExpr fcn(IQualifiedIdentifier id, IExpr... args) {
		List<IExpr> arglist = new LinkedList<IExpr>();
		for (IExpr a: args) arglist.add(a);
		return new FcnExpr(id,arglist);
	}

	@Override
	public IParameterizedIdentifier id(ISymbol symbol, List<INumeral> num) {
		return new ParameterizedIdentifier(symbol,num);
	}

	@Override
	public IAsIdentifier id(IIdentifier identifier, ISort qualifier) {
		return new AsIdentifier(identifier,qualifier);
	}

	@Override
	public ILet let(List<IBinding> bindings, IExpr e) {
		return new Let(bindings,e);
	}

	@Override
	public IBinding binding(ISymbol symbol, IExpr expr) {
		return new Binding(symbol,expr);
	}

	@Override
	public IDeclaration declaration(org.smtlib.IExpr.ISymbol symbol,
			ISort sort) {
		return new Declaration(symbol,sort);
	}
	
    @Override
    public IForall forall(List<IDeclaration> params, IExpr e) {
        return new Forall(params,e);
    }

    @Override
    public IForall forall(List<IDeclaration> params, IExpr e, List<IExpr> patterns) {
        if (patterns != null) {
            List<IAttribute<?>> attributes = new LinkedList<>();
            for (IExpr p: patterns) {
                attributes.add(attribute(keyword(":pattern"),p));
            }
            e = attributedExpr(e, attributes);
        }
        return new Forall(params,e);
    }

    @Override
    public IExists exists(List<IDeclaration> params, IExpr e) {
        return new Exists(params,e);
    }

    @Override
    public IExists exists(List<IDeclaration> params, IExpr e, List<IExpr> patterns) {
        if (patterns != null) {
            List<IAttribute<?>> attributes = new LinkedList<>();
            for (IExpr p: patterns) {
                attributes.add(attribute(keyword(":pattern"),p));
            }
            e = attributedExpr(e, attributes);
        }
        return new Exists(params,e);
    }

	@Override
	public IError error(String text) {
		return new SMTExpr.Error(text);
	}

}
