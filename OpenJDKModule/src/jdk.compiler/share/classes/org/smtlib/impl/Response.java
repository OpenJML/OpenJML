/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.impl;

// FIXME - Document Response; fix how it's classes fit into the Sexpr class hierarchy

import java.util.LinkedList;
import java.util.List;

import org.smtlib.*;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IPos.IPosable;
import org.smtlib.IResponse.IAttributeList;
import org.smtlib.IResponse.IError;
import org.smtlib.IResponse.IPair;

/** This class holds subclasses that are implementations of the various IResponse interfaces. */
public class Response {
	static public SMT.Configuration smtConfig;
	
	final static String ERROR = "error";
	final static String OK = "success";
	final static public SMTExpr.Symbol EMPTY = new SMTExpr.Symbol("");
	final static public SMTExpr.Symbol SUCCESS = new SMTExpr.Symbol(OK);
	final static public SMTExpr.Symbol UNSUPPORTED = new SMTExpr.Symbol("unsupported");
	final static public SMTExpr.Symbol UNKNOWN = new SMTExpr.Symbol("unknown");
	final static public SMTExpr.Symbol SAT = new SMTExpr.Symbol("sat");
	final static public SMTExpr.Symbol UNSAT = new SMTExpr.Symbol("unsat");
	final static public SMTExpr.Symbol IMMEDIATE_EXIT = new SMTExpr.Symbol("immediate-exit");
	final static public SMTExpr.Symbol CONTINUED_EXECUTION = new SMTExpr.Symbol("continued-execution");
	final static public SMTExpr.Symbol MEMOUT = new SMTExpr.Symbol("memout");
	final static public SMTExpr.Symbol TIMEOUT = new SMTExpr.Symbol("timeout"); // TODO - timeout is not standard SMTLIB
	final static public SMTExpr.Symbol INCOMPLETE = new SMTExpr.Symbol("incomplete"); // TODO - incomplete is not standard SMTLIB
	
	/** Implements the IResponse.IPair interface */
	static public class Pair<T1,T2> implements IResponse.IPair<T1,T2>{
		public Pair(T1 first, T2 second) { this.first = first; this.second = second; }
		public T1 first;
		public T2 second;
		@Override
		public T1 first() { return first; }
		@Override
		public T2 second() { return second; }
	}
	
	/** Implements the IResponse.IFactory interface */
	static public class Factory implements IResponse.IFactory {
		public boolean printSuccess = true;
		
		SMT.Configuration smtConfig;
		public Factory(SMT.Configuration smtConfig) { this.smtConfig = smtConfig; }

		@Override
		public IError error(String msg) { return new Error(msg); }

		@Override
		public IError error(String msg, /*@Nullable*//*@ReadOnly*/ IPos pos) { return new Error(msg,pos); }

		@Override
		public IResponse empty() { return EMPTY; }

		@Override
		public IResponse success() { return printSuccess ? SUCCESS : EMPTY; }

		@Override
		public IResponse unsupported() { return UNSUPPORTED; }

		@Override
		public IResponse unknown() { return UNKNOWN; }

		@Override
		public IResponse sat() { return SAT; }

		@Override
		public IResponse unsat() { return UNSAT; }

		@Override
		public IResponse immediate_exit() { return IMMEDIATE_EXIT; }

		@Override
		public IResponse continued_execution() { return CONTINUED_EXECUTION; }

		@Override
		public IResponse memout() { return MEMOUT; }

		@Override
		public IResponse incomplete() { return INCOMPLETE; }

		@Override
		public ISymbol constant(String sym) { return new SMTExpr.Symbol(sym); }

		@Override
		public IStringLiteral stringLiteral(String value) { return new SMTExpr.StringLiteral(value,false); }

		@Override
		public INumeral numericLiteral(int value) { return new SMTExpr.Numeral(value); }

		@Override
		public IResponse.IAttributeList get_info_response(IAttribute<? extends IAttributeValue> attr) {
			return new Seq(attr);
		}
		
		@Override
		public IResponse.IAttributeList get_info_response(List<IAttribute<? extends IAttributeValue>> attributes) {
			return new Seq(attributes);
		}
		
		@Override
		public <T1,T2> Pair<T1,T2> pair(T1 first, T2 second) {
			return new Pair<T1,T2>(first,second);
		}

		// The response to get-option is a literal or symbol or s-expression 
		@Override
		public IResponse get_option_response(IAttributeValue v) {
			return v;
		}
		
		@Override
		public ProofResponse get_proof_response() { return new ProofResponse(); }
		
		@Override
		public ValueResponse get_value_response(List<IPair<IExpr,IExpr>> values) {
			return new ValueResponse(values);
		}

		@Override
		public AssignmentResponse get_assignment_response(List<IResponse.IPair<IExpr.ISymbol,Boolean>> assignments) {
			return new AssignmentResponse(assignments);
		}
		
		@Override
		public UnsatCoreResponse get_unsat_core_response(List<ISymbol> names) {
			return new UnsatCoreResponse(names);
		}
		
		@Override
		public AssertionsResponse get_assertions_response(List<IExpr> exprs) {
			return new AssertionsResponse(exprs);
		}

	}
	
	/** Implements the IResponse.IError interface */
	static public class Error extends Pos.Posable implements IResponse.IError, IPosable {
		
		private String msg;
		
		public Error(String errorMsg) {
			this(errorMsg,null);
		}

		public Error(String errorMsg, /*@Nullable*//*@ReadOnly*/ IPos pos) {
			this.pos = pos;
			this.msg = errorMsg;
		}

		@Override
		public boolean isOK() {
			return false;
		}

		@Override
		public boolean isError() {
			return true;
		}
		
		@Override
		public String toString() {
			return "(error " + smtConfig.utils.quote(msg) + ")";
		}
		
		@Override
		public String errorMsg() {
			return msg;
		}
		
		/** Setting the textual position of the command */
		public <T extends IPosable> T setPos(T t, /*@Nullable*/ IPos p) { t.setPos(p); return t; }

		@Override
		public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
	}

	/** Implements the IResponse.IAssignmentResponse interface */
	static public class AssignmentResponse implements IResponse.IAssignmentResponse {
		private List<IPair<IExpr.ISymbol,Boolean>> assignments = new LinkedList<IPair<IExpr.ISymbol,Boolean>>();
		@Override 
		public List<IPair<IExpr.ISymbol,Boolean>> assignments() { return assignments; }
		public AssignmentResponse(List<IPair<IExpr.ISymbol,Boolean>> assignments) {
			this.assignments = assignments;
		}
		
		@Override public boolean isOK() { return false; }
		@Override public boolean isError() { return false; }
		public IPos pos() { return null; }  // FIXME - should override?
		public void add(IExpr.ISymbol name, Boolean value) {
			assignments.add(new Pair<IExpr.ISymbol,Boolean>(name,value));
		}

		@Override
		public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
	}

	/** Implements the IResponse.IValueResponse interface */
	static public class ValueResponse implements IResponse.IValueResponse {
		private List<IPair<IExpr,IExpr>> values = new LinkedList<IPair<IExpr,IExpr>>();
		@Override public List<IPair<IExpr,IExpr>> values() { return values; }
		public ValueResponse(List<IPair<IExpr,IExpr>> values) {
			this.values = values;
		}
		
		@Override
		public boolean isOK() { return false; }
		@Override
		public boolean isError() { return false; }

		@Override
		public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
	}

	/** Implements the IResponse.IAssertionsResponse interface */
	static public class AssertionsResponse implements IResponse.IAssertionsResponse {
		private List<IExpr> assertions = new LinkedList<IExpr>();
		@Override public List<IExpr> assertions() { return assertions; }
		public AssertionsResponse(List<IExpr> assertions) {
			this.assertions = assertions;
		}

		@Override
		public boolean isOK() { return false; }
		@Override
		public boolean isError() { return false; }

		@Override
		public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
	}

	/** Implements the IResponse.IUnsatCoreResponse interface */
	static public class UnsatCoreResponse implements IResponse.IUnsatCoreResponse {
		private List<ISymbol> names = new LinkedList<ISymbol>();
		@Override 
		public List<ISymbol> names() { return names; }
		
		public UnsatCoreResponse(List<ISymbol> names) {
			this.names = names;
		}

		@Override
		public boolean isOK() { return false; }
		@Override
		public boolean isError() { return false; }

		@Override
		public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
	}

	/** Implements the IResponse.IProofResponse interface */
	static public class ProofResponse implements IResponse.IProofResponse {
		// TODO - no implementation for proofs as yet
		public ProofResponse() {}
		@Override public Object proof() { return null; }
		@Override public boolean isOK() { return false; }
		@Override public boolean isError() { return false; }
		public IPos pos() { return null; }

		@Override
		public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
	}

	static public class Seq extends Pos.Posable implements IAttributeList {
		List<IAttribute<? extends IAttributeValue>> list = new LinkedList<IAttribute<? extends IAttributeValue>>();

		public <T extends IAttributeValue> Seq(IAttribute<T> attr) {
			list.add(attr);
		}
		
		public Seq(List<IAttribute<? extends IAttributeValue>> list) {
			this.list = list;
		}
		
		@Override 
		public List<IAttribute<? extends IAttributeValue>> attributes() { return list; }


		@Override
		public boolean isOK() {
			return false;
		}

		@Override
		public boolean isError() {
			return false;
		}
		
		@Override 
		public String toString() {
			return super.toString();
		}

		@Override
		public <T> T accept(IVisitor<T> v) throws IVisitor.VisitorException {
			return v.visit(this);
		}
		
		// FIXME - equals, hashCode
	}
	

}
