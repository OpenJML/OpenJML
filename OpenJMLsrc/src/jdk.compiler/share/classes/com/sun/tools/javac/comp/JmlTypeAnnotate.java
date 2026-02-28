package com.sun.tools.javac.comp;

import org.jmlspecs.openjml.visitors.IJmlVisitor;

import org.jmlspecs.openjml.JmlTree;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotatedType;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

public class JmlTypeAnnotate extends Annotate.TypeAnnotate implements IJmlVisitor {

	public JmlTypeAnnotate(Annotate annotate, Env<AttrContext> env, Symbol sym, DiagnosticPosition deferPos) {
		annotate.super(env, sym, deferPos);
	}
	
	public void scan(JCTree tree) {
		if (tree != null) tree.accept(this);
	}

	
    @Override
    public void visitAnnotatedType(JCAnnotatedType tree) {
    	// This is called more than once, giving duplicate error messages (e.g. for repeated annotations),
    	// FIXME - but I'm not sure how to avoid it
    	super.visitAnnotatedType(tree);
    }

    // FIXME - do we really need this?
    @Override
    public void visitClassDef(JCClassDecl tree) {
        for (var def: tree.defs) {
            if (def instanceof JmlTree.JmlTypeClause) scan(def);
        }
    }

}
