package org.jmlspecs.openjml;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticListener;

// FIXME - I don't believe this is used.

public class DiagnosticFilter<S> implements DiagnosticListener<S> {
//        private List<Diagnostic<? extends S>> diagnostics =
//            Collections.synchronizedList(new ArrayList<Diagnostic<? extends S>>());

        public void report(Diagnostic<? extends S> diagnostic) {
            diagnostic.getClass(); // null check
            if (!diagnostic.getCode().contains("jml")) return;
            //diagnostics.add(diagnostic);
            System.out.println(diagnostic.toString());
        }

//        /**
//         * Gets a list view of diagnostics collected by this object.
//         *
//         * @return a list view of diagnostics
//         */
//        public List<Diagnostic<? extends S>> getDiagnostics() {
//            return Collections.unmodifiableList(diagnostics);
//        }
    }
