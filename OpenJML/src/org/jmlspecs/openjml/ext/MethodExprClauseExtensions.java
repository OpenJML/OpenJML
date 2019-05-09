package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;

public class MethodExprClauseExtensions extends JmlExtension.MethodClause {
    
    public static final String ensuresID = "ensures";
    public static final String divergesID = "diverges";
    public static final String whenID = "when";
    public static final String continuesID = "continues";
    public static final String breaksID = "breaks";
    public static final String returnsID = "returns";
    
    public static final IJmlClauseKind ensuresClauseKind = new MethodClauseExprType(ensuresID) {
        public boolean oldNoLabelAllowed() { return true; }
    };
    
    public static final IJmlClauseKind divergesClause = new MethodClauseExprType(divergesID);
    
    public static final IJmlClauseKind whenClause = new MethodClauseExprType(whenID);
    
    public static final IJmlClauseKind continuesClause = new MethodClauseExprType(continuesID) {
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };
    
    public static final IJmlClauseKind breaksClause = new MethodClauseExprType(breaksID) {
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };
    
    public static final IJmlClauseKind returnsClause = new MethodClauseExprType(returnsID) {
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };
    
    @Override
    public IJmlClauseKind[]  clauseTypesA() { return clauseTypes(); }
    public static IJmlClauseKind[]  clauseTypes() { return new IJmlClauseKind[]{
            ensuresClauseKind, divergesClause, whenClause,
            continuesClause, breaksClause, returnsClause}; }
    
}
