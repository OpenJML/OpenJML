/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.util.List;

import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IPos.IPosable;
import org.smtlib.sexpr.ISexpr.ISeq;

/** This interface represents responses that can be received from SMT-LIB commands. */
public interface IResponse extends IAccept {
	
	/** Returns true if the response is a SUCCESS response */
	boolean isOK();
	
	/** Returns true if the response is an error response */
	//@ ensures \result <==> (this instanceof IResponse.IError);
	boolean isError();
	
	/** The interface for error responses */
	public static interface IError extends IResponse, IPosable {
		/** Returns the error message held by this response */
		String errorMsg();
		
		/** Returns the textual location for the response, if available and applicable, otherwise null. */
		/*@Nullable*/ IPos pos();
	}
	
	/** An interface for simple pairs of objects */
	public static interface IPair<T1,T2> {
		T1 first();
		T2 second();
	}

	
	/** The interface representing the factory for IResponse instances */ // TODO _ more restrictive return types?
	public static interface IFactory {
		IError error(String msg);
		IError error(String msg, /*@Nullable*//*@ReadOnly*/ IPos pos);
		IResponse empty();
		IResponse success();
		IResponse unsupported();
		IResponse unknown();
		IResponse sat();
		IResponse unsat();
		IResponse immediate_exit();
		IResponse continued_execution();
		IResponse memout();
		IResponse incomplete();
		/** Returns a constant response with the given canonical name */
		IResponse constant(String id); // FIXME - use abstract keyword?
		/** The argument has no SMT-LIB escapes and no enclosing quotes */
		IResponse stringLiteral(String value);
		IResponse numericLiteral(int value);
		IResponse get_option_response(IAttributeValue v);
		IResponse.IAttributeList get_info_response(IAttribute<?> attr);
		IResponse.IAttributeList get_info_response(List<IAttribute<?>> attrList);
		IResponse.IProofResponse get_proof_response();
		IResponse.IValueResponse get_value_response(List<IPair<IExpr,IExpr>> values);
		<T1,T2> IPair<T1,T2> pair(T1 first, T2 second);
		IResponse.IAssignmentResponse get_assignment_response(List<IPair<IExpr.ISymbol,Boolean>> assignments);
		IResponse.IUnsatCoreResponse get_unsat_core_response(List<ISymbol> names);
		IResponse.IAssertionsResponse get_assertions_response(List<IExpr> exprs);
	}
	
	static public interface IAttributeList extends IResponse {
		public List<IAttribute<? extends IAttributeValue>> attributes();
	}

	static public interface IAssignmentResponse extends IResponse {
		public List<IPair<IExpr.ISymbol,Boolean>> assignments();
	}

	static public interface IValueResponse extends IResponse {
		public List<IPair<IExpr,IExpr>> values();
	}

	static public interface IUnsatCoreResponse extends IResponse {
		public List<IExpr.ISymbol> names();
	}

	static public interface IAssertionsResponse extends IResponse {
		public List<IExpr> assertions();
	}

	static public interface IProofResponse extends IResponse {
		public Object proof();
	}
}
