package org.jmlspecs.openjml.jmldoc;

import com.sun.javadoc.ClassDoc;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javadoc.ClassDocImpl;
import com.sun.tools.javadoc.DocEnv;

public class ClassDocJml extends ClassDocImpl {

    public ClassDocJml(DocEnv env, ClassSymbol sym, TreePath path) {
        super(env,sym,path);
    }
    
    public ClassDocJml(DocEnv env, ClassSymbol sym) {
        this(env, sym, null);
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
