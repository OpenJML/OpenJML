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
    
    /** Returns a list of clause type objects that sre the extensions provided by
     *  this derived class of JmlExtension
     */
    abstract public IJmlClauseKind[] clauseTypesA(); 
    
    public void register() {}
    
    public void register(Context context) {
        this.context = context;
    }
    
    /** This marker interface marks classes that contain extensions that are new
     *  type clauses (like invariant) */
    public static abstract class TypeClause extends JmlExtension {
        public void register(Context context) {
            super.register(context);
            IJmlClauseKind[] cTypes = clauseTypesA();
            for (IJmlClauseKind t: cTypes) {
                Extensions.typeMethodClauses.put(t.name(), t);
            }
            //register();
        }
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
        public void register(Context context) {
            super.register(context);
            IJmlClauseKind[] cTypes = clauseTypesA();
            for (IJmlClauseKind t: cTypes) {
                Extensions.typeMethodClauses.put(t.name(), t);
                Extensions.statementMethodClauses.put(t.name(), t);
            }
            register();
        }
    }

    /** This marker interface marks classes that contain extensions that are new
     *  JML statements clauses (like assert) */
    public static abstract class Statement extends JmlExtension {
        public void register(Context context) {
            super.register(context);
            IJmlClauseKind[] cTypes = clauseTypesA();
            for (IJmlClauseKind t: cTypes) {
                Extensions.statementMethodClauses.put(t.name(), t);
            }
            //register();
        }
    }

    /** This marker interface marks classes that contain extensions that are new
     *  JML statements clauses (like assert) */
    public static abstract class LineAnnotation extends JmlExtension.Statement {
        public void register(Context context) {
            super.register(context);
            IJmlClauseKind[] cTypes = clauseTypesA();
            for (IJmlClauseKind t: cTypes) {
                Extensions.lineAnnotations.put(t.name(), t);
            }
            //register();
        }
    }

}
