/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

/** Any class that contains JML extensions to be registered in the keyword recognizer
 *  must implement this marker interface */
public interface JmlDefinitions {

    default void register() {}
    
//    public void register(Context context) {
//        this.context = context;
//    }
    
//    /** This marker interface marks classes that contain extensions that are new
//     *  type clauses (like invariant) */
//    public static abstract class TypeClause extends JmlExtension {
//        public void register(Context context) {
//            super.register(context);
//            IJmlClauseKind[] cTypes = clauseTypesA();
//            for (IJmlClauseKind t: cTypes) {
//                Extensions.typeClauses.put(t.name(), t);
//            }
//            //register();
//        }
//    }
    
    
//    /** This marker interface marks classes containing extensions that are
//     *  new method specification clauses (like requires). */
//    public static abstract class MethodClause extends JmlExtension {
//        public void register(Context context) {
//            super.register(context);
//            IJmlClauseKind[] cTypes = clauseTypesA();
//            for (IJmlClauseKind t: cTypes) {
//                Extensions.methodSpecKeywords.put(t.name(), (IJmlClauseKind.MethodClause)t);
//            }
//            register();
//        }
//    }

//    /** This marker interface marks classes that contain extensions that are new
//     *  JML statements clauses (like assert) */
//    public static abstract class Statement extends JmlExtension {
//        public void register(Context context) {
//            super.register(context);
//            IJmlClauseKind[] cTypes = clauseTypesA();
//            for (IJmlClauseKind t: cTypes) {
//                Extensions.statementClauses.put(t.name(), t);
//            }
//            //register();
//        }
//    }
//
//    /** This marker interface marks classes that contain extensions that are new
//     *  JML statements clauses (like assert) */
//    public static abstract class LineAnnotation extends JmlExtension.Statement {
//        public void register(Context context) {
//            super.register(context);
//            IJmlClauseKind[] cTypes = clauseTypesA();
//            for (IJmlClauseKind t: cTypes) {
//                Extensions.lineAnnotations.put(t.name(), t);
//            }
//            //register();
//        }
//    }

}
