package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;

public class Modifiers extends JmlExtension {

    IJmlClauseKind captured = new IJmlClauseKind.ModifierKind("captured", true);
    IJmlClauseKind codeBigintMathModifier = new IJmlClauseKind.ModifierKind("code_bigint_math", true);
    IJmlClauseKind codeJavaMathModifier = new IJmlClauseKind.ModifierKind("code_java_math", true);
    IJmlClauseKind codeSafeMathModifier = new IJmlClauseKind.ModifierKind("code_safe_math", true);
    IJmlClauseKind extractModifier = new IJmlClauseKind.ModifierKind("extract", true);
    IJmlClauseKind functionModifier = new IJmlClauseKind.ModifierKind("function", false);
    IJmlClauseKind helperModifier = new IJmlClauseKind.ModifierKind("helper", true);
    IJmlClauseKind immutableModifier = new IJmlClauseKind.ModifierKind("immutable", false);
    IJmlClauseKind inlineModifier = new IJmlClauseKind.ModifierKind("inline", false);
    IJmlClauseKind instanceModifier = new IJmlClauseKind.ModifierKind("instance", true);
    IJmlClauseKind monitoredModifier = new IJmlClauseKind.ModifierKind("monitored", true);
    IJmlClauseKind nonNullModifier = new IJmlClauseKind.ModifierKind("non_null", true);
    IJmlClauseKind nonNullByDefaultModifier = new IJmlClauseKind.ModifierKind("non_null_by_default", true);
    IJmlClauseKind nullableModifier = new IJmlClauseKind.ModifierKind("nullable", true);
    IJmlClauseKind nullableByDefaultModifier = new IJmlClauseKind.ModifierKind("nullable_by_default", true);
    IJmlClauseKind queryModifier = new IJmlClauseKind.ModifierKind("query", false);
    IJmlClauseKind peerModifier = new IJmlClauseKind.ModifierKind("peer", true);
    IJmlClauseKind pureModifier = new IJmlClauseKind.ModifierKind("pure", true);
    IJmlClauseKind readonlyModifier = new IJmlClauseKind.ModifierKind("readonly", true);
    IJmlClauseKind repModifier = new IJmlClauseKind.ModifierKind("rep", true);
    IJmlClauseKind secretModifier = new IJmlClauseKind.ModifierKind("secret", false);
    IJmlClauseKind skipescModifier = new IJmlClauseKind.ModifierKind("skipesc", true, "SkipEsc");
    IJmlClauseKind skipracModifier = new IJmlClauseKind.ModifierKind("skiprac", true, "SkipRac");
    IJmlClauseKind specProtectedModifier = new IJmlClauseKind.ModifierKind("spec_protected", true);
    IJmlClauseKind specPublicModifier = new IJmlClauseKind.ModifierKind("spec_public", true);
    IJmlClauseKind specBigintMathModifier = new IJmlClauseKind.ModifierKind("spec_bigint_math", true);
    IJmlClauseKind specJavaMathModifier = new IJmlClauseKind.ModifierKind("spec_java_math", true);
    IJmlClauseKind specSafeMathModifier = new IJmlClauseKind.ModifierKind("spec_safe_math", true);
    IJmlClauseKind uninitializedModifier = new IJmlClauseKind.ModifierKind("uninitialized", true);

}
