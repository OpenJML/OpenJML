package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseType;
import org.jmlspecs.openjml.JmlExtension;

public class MethodExprClauseExtensions extends JmlExtension.MethodClause {
    
    public static final String ensuresID = "ensures";
    public static final String divergesID = "diverges";
    public static final String whenID = "when";
    public static final String continuesID = "continues";
    public static final String breaksID = "breaks";
    public static final String returnsID = "returns";
    
    public static final IJmlClauseType ensuresClause = new MethodClauseExprType(ensuresID) {
        public boolean oldNoLabelAllowed() { return true; }
    };
    
    public static final IJmlClauseType divergesClause = new MethodClauseExprType(divergesID);
    
    public static final IJmlClauseType whenClause = new MethodClauseExprType(whenID);
    
    public static final IJmlClauseType continuesClause = new MethodClauseExprType(continuesID) {
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };
    
    public static final IJmlClauseType breaksClause = new MethodClauseExprType(breaksID) {
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };
    
    public static final IJmlClauseType returnsClause = new MethodClauseExprType(returnsID) {
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };
    
    @Override
    public IJmlClauseType[]  clauseTypes() { return new IJmlClauseType[]{
            ensuresClause, divergesClause, whenClause,
            continuesClause, breaksClause, returnsClause}; }
    
}
