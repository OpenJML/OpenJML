/*
 * This file is part of the OpenJML project. 
 * Author: Sachin Shah
 */
package org.jmlspecs.openjml.esc;

import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.*;

public class JmlBoundsExtractor {

	protected static class Bounds {
		public JCExpression lo;
		public JCExpression hi;

		public Bounds(JCExpression lo, JCExpression hi) {
			this.lo = lo;
			this.hi = hi;
		}

	}

	/**
	 * Take a comparison expression (<, <=, >, >=), and return the lowest and highest values.
	 */
	public static Bounds orientComparison(JCBinary expr, JCVariableDecl decl) {
		JCTree.Tag tag = expr.getTag();

		// X <= Y, X < Y
		if (tag == JCTree.Tag.LE || tag == JCTree.Tag.LT) {
			return new Bounds(expr.lhs, expr.rhs);
		}

		// X >= Y, X > Y
		if (tag == JCTree.Tag.GE || tag == JCTree.Tag.GT) {
			return new Bounds(expr.rhs, expr.lhs);
		}

		// nameexpr seems suspect
		return new Bounds(null, null);
	}


	// Checks if a given expression is an identifier in the declaration list
	public static boolean inDecls(List<JCVariableDecl> decls, JCExpression expr) {
		if (!(expr instanceof JCIdent)) {
			return false;
		}
		JCIdent ident = (JCIdent) expr;
		
		for (JCVariableDecl decl : decls) {
			if (decl.getName().equals(ident.name)) return true;
		}
		return false;
	}

	// returns true if the operator is: &&, &, ||, |
	private static boolean isConjunctiveOperator(JCTree.Tag tag) {
		return tag == JCTree.Tag.AND || tag == JCTree.Tag.BITAND || tag == JCTree.Tag.OR || tag == JCTree.Tag.BITOR;
	}

	// primary bounds extracting logic
	public static Bounds extract(List<JCVariableDecl> decls, JCExpression range, boolean isRoot, Context context, SMTTranslator smtTranslator) {
		if ((range instanceof JCParens)) {
			range = ((JCParens) range).getExpression();
		}

		if (!(range instanceof JCBinary)) {
			// TODO: implement true/false logic and return non-null value 
			smtTranslator.notImplWarn(range, "The range expression is not binary.");
			return null;
		}

		JCBinary expr = (JCBinary) range;
		if (isRoot && !isConjunctiveOperator(expr.getTag())) {
			smtTranslator.notImplWarn(range, "Range expressions without && or || are not supported because those expressions often result in infinite ranges.");
			return null;
		}

		if (isConjunctiveOperator(expr.getTag())){
			TreeMaker treeMaker =  TreeMaker.instance(context);
			Bounds left = extract(decls, expr.lhs, false, context, smtTranslator);
			Bounds right = extract(decls, expr.rhs, false, context, smtTranslator);

			JCExpression lo;
			if (!inDecls(decls, left.lo) && inDecls(decls, right.lo)) {
				lo = left.lo;
			} else if (inDecls(decls, left.lo) && !inDecls(decls, right.lo)) {
				lo = right.lo;
			} else if (!inDecls(decls, left.lo) && !inDecls(decls, right.lo)) {
				lo = treeMaker.Conditional(treeMaker.Binary(JCTree.Tag.LT, left.lo, right.lo), left.lo, right.lo);
			} else {
				lo = decls.get(0).nameexpr;
			}

			JCExpression hi;
			if (!inDecls(decls, left.hi) && inDecls(decls, right.hi)) {
				hi = left.hi;
			} else if (inDecls(decls, left.hi) && !inDecls(decls, right.hi)) {
				hi = right.hi;
			} else if (!inDecls(decls, left.hi) && !inDecls(decls, right.hi)) {
				hi = treeMaker.Conditional(treeMaker.Binary(JCTree.Tag.GT, left.hi, right.hi), left.hi, right.hi);
			} else {
				hi = decls.get(0).nameexpr;
			}

			return new Bounds(lo, hi);
		}

		if (expr.getTag() == JCTree.Tag.LT ||
		    expr.getTag() == JCTree.Tag.LE ||
			expr.getTag() == JCTree.Tag.GT ||
			expr.getTag() == JCTree.Tag.GE) {

			return orientComparison(expr, decls.get(0));
		}
		
		return new Bounds(decls.get(0).nameexpr, decls.get(0).nameexpr);
	}
}
