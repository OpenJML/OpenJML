package org.jmlspecs.openjml.jmldoc;

import com.sun.javadoc.ClassDoc;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Position;
import com.sun.tools.javadoc.ClassDocImpl;
import com.sun.tools.javadoc.DocEnv;

public class ClassDocJml extends ClassDocImpl {

    public ClassDocJml(DocEnv env, ClassSymbol sym, String documentation,
            JCClassDecl tree, Position.LineMap lineMap) {
        super(env,sym,documentation,tree,lineMap);
    }
    
    public ClassDocJml(DocEnv env, ClassSymbol sym) {
        this(env, sym, null, null, null);
    }

    
    public ClassDoc[] innerClasses(boolean filter) {
        ClassDoc[] inners = super.innerClasses(filter);
        return inners;
    }
    
    protected void addAllClasses(ListBuffer<ClassDocImpl> l, boolean filtered) {
        super.addAllClasses(l,filtered);
        // Add nested model classes
    }


}
