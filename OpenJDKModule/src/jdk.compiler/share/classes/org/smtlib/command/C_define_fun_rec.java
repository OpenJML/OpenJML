package org.smtlib.command;

import java.io.IOException;
import java.util.List;

import org.smtlib.IExpr;
import org.smtlib.ISort;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.sexpr.Printer;
import org.smtlib.IVisitor;

public class C_define_fun_rec extends C_define_fun {
	
	/** The command name */
	public static final String commandName = "define-fun-rec";
	/** The command name */
	@Override
	public String commandName() { return commandName; }

	public C_define_fun_rec(ISymbol id, List<IDeclaration> declarations, ISort resultSort, IExpr expr) {
		super(id, declarations, resultSort, expr);
	}

	/** Writes the command in the syntax of the given printer */
	public void write(Printer p) throws IOException, IVisitor.VisitorException {
		p.writer().append("(" + commandName + " ");
		symbol().accept(p);
		p.writer().append(" (");
		for (IDeclaration d: parameters()) {
			d.accept(p);
		}
		p.writer().append(") ");
		resultSort().accept(p);
		p.writer().append(" ");
		expression().accept(p);
		p.writer().append(")");
	}
}
