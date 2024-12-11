package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.IJmlClauseKind.ModifierKind;
import org.jmlspecs.openjml.JmlExtension;

public class Modifiers extends JmlExtension {

    static public final ModifierKind GHOST = new IJmlClauseKind.ModifierKind("ghost", true);
    static public final ModifierKind MODEL = new IJmlClauseKind.ModifierKind("model", true);
    static public final ModifierKind CAPTURED = new IJmlClauseKind.ModifierKind("captured", true);
    static public final ModifierKind CODE_BIGINT_MATH = new IJmlClauseKind.ModifierKind("code_bigint_math", true);
    static public final ModifierKind CODE_JAVA_MATH = new IJmlClauseKind.ModifierKind("code_java_math", true);
    static public final ModifierKind CODE_SAFE_MATH = new IJmlClauseKind.ModifierKind("code_safe_math", true);
    static public final ModifierKind EXTRACT = new IJmlClauseKind.ModifierKind("extract", true);
    static public final ModifierKind NO_STATE = new IJmlClauseKind.ModifierKind("no_state", true);
    static public final ModifierKind HELPER = new IJmlClauseKind.ModifierKind("helper", true);
    static public final ModifierKind IMMUTABLE = new IJmlClauseKind.ModifierKind("immutable", true); // Need to change specs if this is set properly to false
    static public final ModifierKind INLINE = new IJmlClauseKind.ModifierKind("inline", false);
    static public final ModifierKind INSTANCE = new IJmlClauseKind.ModifierKind("instance", true);
    static public final ModifierKind MONITORED = new IJmlClauseKind.ModifierKind("monitored", true);
    static public final ModifierKind NON_NULL = new IJmlClauseKind.TypeAnnotationKind("non_null", true);
    static public final ModifierKind NON_NULL_BY_DEFAULT = new IJmlClauseKind.ModifierKind("non_null_by_default", true);
    //static public final ModifierKind NON_NULL_ELEMENTS = new IJmlClauseKind.ModifierKind("non_null_elements", true); // FIXME - what's this?
    static public final ModifierKind NULLABLE = new IJmlClauseKind.TypeAnnotationKind("nullable", true);
    static public final ModifierKind NULLABLE_BY_DEFAULT = new IJmlClauseKind.ModifierKind("nullable_by_default", true);
    //static public final ModifierKind NULLABLE_ELEMENTS = new IJmlClauseKind.ModifierKind("nullable_elements", true);
    static public final ModifierKind OPTIONS = new IJmlClauseKind.ModifierKind("options", false) {
        @Override public boolean isNormalModifier() {
            return false;
        }
    };
    static public final ModifierKind PEER = new IJmlClauseKind.ModifierKind("peer", true);
    static public final ModifierKind PURE = new IJmlClauseKind.ModifierKind("pure", true);
    static public final ModifierKind QUERY = new IJmlClauseKind.ModifierKind("query", false);
    static public final ModifierKind READONLY = new IJmlClauseKind.ModifierKind("readonly", true);
    static public final ModifierKind REP = new IJmlClauseKind.ModifierKind("rep", true);
    static public final ModifierKind SECRET = new IJmlClauseKind.ModifierKind("secret", false);
    static public final ModifierKind SKIPESC = new IJmlClauseKind.ModifierKind("skipesc", true, "SkipEsc");
    static public final ModifierKind SKIPRAC = new IJmlClauseKind.ModifierKind("skiprac", true, "SkipRac");
    static public final ModifierKind SPEC_PROTECTED = new IJmlClauseKind.ModifierKind("spec_protected", true);
    static public final ModifierKind SPEC_PUBLIC = new IJmlClauseKind.ModifierKind("spec_public", true);
    static public final ModifierKind SPEC_PURE = new IJmlClauseKind.ModifierKind("spec_pure", true);
    static public final ModifierKind SPEC_BIGINT_MATH = new IJmlClauseKind.ModifierKind("spec_bigint_math", true);
    static public final ModifierKind SPEC_JAVA_MATH = new IJmlClauseKind.ModifierKind("spec_java_math", true);
    static public final ModifierKind SPEC_SAFE_MATH = new IJmlClauseKind.ModifierKind("spec_safe_math", true);
    static public final ModifierKind STRICTLY_PURE = new IJmlClauseKind.ModifierKind("strictly_pure", true);
    static public final ModifierKind UNINITIALIZED = new IJmlClauseKind.ModifierKind("uninitialized", true);
    static public final ModifierKind BSREADONLY = new IJmlClauseKind.ModifierKind("\\readonly", true, "org.jmlspecs.annotation.Readonly");

}
