package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;

public class MethodExprClauseExtensions extends JmlExtension {
    
    public static final String requiresID = "requires";
    public static final String ensuresID = "ensures";
    public static final String divergesID = "diverges";
    public static final String whenID = "when";
    public static final String continuesID = "continues";
    public static final String breaksID = "breaks";
    public static final String returnsID = "returns";
    
    public static final IJmlClauseKind requiresClauseKind = new MethodClauseExprType(requiresID) {
        public boolean isPreconditionClause() { return true; }
    };
    
    public static final IJmlClauseKind ensuresClauseKind = new MethodClauseExprType(ensuresID) {
        public boolean oldNoLabelAllowed() { return true; }
    };
    
    public static final IJmlClauseKind divergesClauseKind = new MethodClauseExprType(divergesID);
    
    public static final IJmlClauseKind whenClauseKind = new MethodClauseExprType(whenID);
    
    public static final IJmlClauseKind continuesClauseKind = new MethodClauseExprType(continuesID) {
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };
    
    public static final IJmlClauseKind breaksClauseKind = new MethodClauseExprType(breaksID) {
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };
    
    public static final IJmlClauseKind returnsClauseKind = new MethodClauseExprType(returnsID) {
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };
}
