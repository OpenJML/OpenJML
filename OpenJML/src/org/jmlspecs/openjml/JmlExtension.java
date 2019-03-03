/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import java.lang.reflect.Method;

import com.sun.tools.javac.util.Context;

/** Any class that contains JML extensions to be registered in the keyword recognizer
 *  must implement this marker interface*/
public abstract class JmlExtension {

    public Context context;
    
    /** Returns a list of clause type objects that sre the extensions provided by
     *  this derived class of JmlExtension
     */
    abstract public IJmlClauseKind[] clauseTypes(); 
    
    public void register() {}
    
    public void register(Context context) {
        this.context = context;
    }
    
    /** This marker interface marks classes that contain extensions that are new
     *  type clauses (like invariant) */
    public static abstract class TypeClause extends JmlExtension {
        public void register(Context context) {
            super.register(context);
            IJmlClauseKind[] cTypes = clauseTypes();
            for (IJmlClauseKind t: cTypes) {
                Extensions.typeMethodClauses.put(t.name(), t);
            }
            //register();
        }
    }
    
    
    /** This marker interface marks classes containing extensions that are
     *  new method specification clauses (like requires). */
    public static abstract class MethodClause extends JmlExtension {
        public void register(Context context) {
            super.register(context);
            IJmlClauseKind[] cTypes = clauseTypes();
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
            IJmlClauseKind[] cTypes = clauseTypes();
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
            IJmlClauseKind[] cTypes = clauseTypes();
            for (IJmlClauseKind t: cTypes) {
                Extensions.lineAnnotations.put(t.name(), t);
            }
            //register();
        }
    }

}
