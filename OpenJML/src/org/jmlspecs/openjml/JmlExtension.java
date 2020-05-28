/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import java.lang.reflect.Method;

import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;

/** Any class that contains JML extensions to be registered in the keyword recognizer
 *  must implement this marker interface*/
public abstract class JmlExtension {

    public Context context;
        
    public void register() {}
    
    public void register(Context context) {
        this.context = context;
        register();
    }
    
    public void synonym(String s, IJmlClauseKind t) {
        Extensions.allKinds.put(s,t);
    }
    
    /** This marker interface marks classes that contain extensions that are new
     *  type clauses (like invariant) */
    public static abstract class TypeClause extends JmlExtension {
    }
    
    public static abstract class ClassLike extends JmlExtension {
        public void register(Context context) {
            super.register(context);
            Extensions.classLike.put(this.name(), this);
        }
        
        abstract public String name();
        abstract public JCClassDecl parse(JmlParser parser, JCTree.JCModifiers mods);
    }
    
    
    /** This marker interface marks classes containing extensions that are
     *  new method specification clauses (like requires). */
    public static abstract class MethodClause extends JmlExtension {
    }

    /** This marker interface marks classes that contain extensions that are new
     *  JML statements clauses (like assert) */
    public static abstract class Statement extends JmlExtension {
    }

    /** This marker interface marks classes that contain extensions that are new
     *  JML statements clauses (like assert) */
    public static abstract class LineAnnotation extends JmlExtension.Statement {
    }

}
