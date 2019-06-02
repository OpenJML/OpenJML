/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static org.jmlspecs.openjml.ext.ProgramLocation.*;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.ext.ModifierExtension;
import org.jmlspecs.openjml.ext.MiscExtensions.NoTypeMisc;

public class Modifiers {
    public static final String PURE_ID = "pure";
    public static final ModifierExtension PURE_KIND = new ModifierExtension(
            PURE_ID, 
            org.jmlspecs.annotation.Pure.class,
            new ProgramLocation[]{ 
                    TOP_LEVEL_TYPE,
                    NESTED_TYPE,
                    LOCAL_TYPE,
                    METHOD,
                    CONSTRUCTOR,
                    MODEL_METHOD,
                    MODEL_CONSTRUCTOR,
            });

    public static final String FUNCTION_ID = "function";
    public static final ModifierExtension FUNCTION_KIND = new ModifierExtension(
            FUNCTION_ID, 
            org.jmlspecs.annotation.Function.class,
            new ProgramLocation[]{ 
                    METHOD,
                    CONSTRUCTOR,
                    MODEL_METHOD,
                    MODEL_CONSTRUCTOR,
            });

    public static final String HELPER_ID = "helper";
    public static final ModifierExtension HELPER_KIND = new ModifierExtension(
            HELPER_ID, 
            org.jmlspecs.annotation.Helper.class,
            new ProgramLocation[]{ 
                    METHOD,
                    CONSTRUCTOR,
                    MODEL_METHOD,
                    MODEL_CONSTRUCTOR,
            });

    public static final String UNINITIALIZED_ID = "uninitialized";
    public static final ModifierExtension UNINITIALIZED_KIND = new ModifierExtension(
            UNINITIALIZED_ID, 
            org.jmlspecs.annotation.Uninitialized.class,
            new ProgramLocation[]{ 
                    JAVA_FIELD,
                    GHOST_FIELD,
                    LOCAL_VARIABLE,
            });

    public static final String MONITORED_ID = "monitored";
    public static final ModifierExtension MONITORED_KIND = new ModifierExtension(
            MONITORED_ID, 
            org.jmlspecs.annotation.Monitored.class,
            new ProgramLocation[]{ 
                    JAVA_FIELD,
                    GHOST_FIELD,
            });

    public static final String QUERY_ID = "query";
    public static final ModifierExtension QUERY_KIND = new ModifierExtension(
            QUERY_ID, 
            org.jmlspecs.annotation.Query.class,
            new ProgramLocation[]{ 
                    METHOD,
            });

    public static final String SECRET_ID = "secret";
    public static final ModifierExtension SECRET_KIND = new ModifierExtension(
            SECRET_ID, 
            org.jmlspecs.annotation.Secret.class,
            new ProgramLocation[]{ 
                    JAVA_FIELD,  // FIXME - not sure about these
                    MODEL_FIELD,
                    GHOST_FIELD,
                    FORMAL_PARAMETER,
                    LOCAL_VARIABLE,
            });

    public static final String IMMUTABLE_ID = "immutable";
    public static final ModifierExtension IMMUTABLE_KIND = new ModifierExtension(
            IMMUTABLE_ID, 
            org.jmlspecs.annotation.Immutable.class,
            new ProgramLocation[] { 
                    TOP_LEVEL_TYPE,
                    NESTED_TYPE,
                    LOCAL_TYPE,
            });

    public static final String CAPTURES_ID = "captures";
    public static       ModifierExtension CAPTURES_KIND = new ModifierExtension(
            CAPTURES_ID, 
            org.jmlspecs.annotation.Captures.class,
            new ProgramLocation[]{ 
                    GHOST_FIELD,
            });

    public static final String INSTANCE_ID = "instance";
    public static final ModifierExtension INSTANCE_KIND = new ModifierExtension(
            INSTANCE_ID, 
            org.jmlspecs.annotation.Instance.class,
            new ProgramLocation[]{ 
                    JAVA_FIELD,
                    MODEL_FIELD,
                    GHOST_FIELD,
            });

    public static final String GHOST_ID = "ghost";
    public static final ModifierExtension GHOST_KIND = new ModifierExtension(
            GHOST_ID, 
            org.jmlspecs.annotation.Ghost.class,
            new ProgramLocation[]{ 
                    GHOST_FIELD,
                    LOCAL_VARIABLE,
            });

    public static final String MODEL_ID = "model";
    public static final ModifierExtension MODEL_KIND = new ModifierExtension(
            MODEL_ID, 
            org.jmlspecs.annotation.Model.class,
            new ProgramLocation[]{ 
                    TOP_LEVEL_TYPE,
                    NESTED_TYPE,
                    LOCAL_TYPE,
                    JAVA_FIELD,
                    MODEL_FIELD,
                    METHOD,
                    CONSTRUCTOR,
                    MODEL_METHOD,
                    MODEL_CONSTRUCTOR,
            });

    public static final String NONNULL_ID = "non_null";
    public static final ModifierExtension NONNULL_KIND = new ModifierExtension(
            NONNULL_ID, 
            org.jmlspecs.annotation.NonNull.class, 
            new ProgramLocation[]{ 
                    METHOD,
                    JAVA_FIELD,
                    MODEL_FIELD,
                    GHOST_FIELD,
                    FORMAL_PARAMETER,
                    LOCAL_VARIABLE,
            });

    public static final String NULLABLE_ID = "nullable";
    public static final ModifierExtension NULLABLE_KIND = new ModifierExtension(
            NULLABLE_ID, 
            org.jmlspecs.annotation.Nullable.class, 
            new ProgramLocation[]{ 
                    METHOD,
                    JAVA_FIELD,
                    MODEL_FIELD,
                    GHOST_FIELD,
                    FORMAL_PARAMETER,
                    LOCAL_VARIABLE,
            });

    public static final String NONNULLBYDEFAULT_ID = "non_null_by_default";
    public static final ModifierExtension NONNULLBYDEFAULT_KIND = new ModifierExtension(
            NONNULLBYDEFAULT_ID, 
            org.jmlspecs.annotation.NonNullByDefault.class,
            new ProgramLocation[]{ 
                    TOP_LEVEL_TYPE,
                    NESTED_TYPE,
                    LOCAL_TYPE,
                    METHOD,
                    CONSTRUCTOR,
                    MODEL_METHOD,
                    MODEL_CONSTRUCTOR,
            });

    public static final String NULLABLEBYDEFAULT_ID = "nullable_by_default";
    public static final ModifierExtension NULLABLEBYDEFAULT_KIND = new ModifierExtension(
            NULLABLEBYDEFAULT_ID, 
            org.jmlspecs.annotation.NullableByDefault.class,
            new ProgramLocation[]{ 
                    TOP_LEVEL_TYPE,
                    NESTED_TYPE,
                    LOCAL_TYPE,
                    METHOD,
                    CONSTRUCTOR,
                    MODEL_METHOD,
                    MODEL_CONSTRUCTOR,
            });

    public static final String INLINE_ID = "inline";
    public static final ModifierExtension INLINE_KIND = new ModifierExtension(
            INLINE_ID, 
            org.jmlspecs.annotation.Inline.class,
            new ProgramLocation[]{ 
                    METHOD,
                    CONSTRUCTOR,
                    MODEL_METHOD,
                    MODEL_CONSTRUCTOR,
            });

    public static final String EXTRACT_ID = "extract";
    public static final ModifierExtension EXTRACT_KIND = new ModifierExtension(
            EXTRACT_ID, 
            org.jmlspecs.annotation.Extract.class,
            new ProgramLocation[] 
            { 
                    METHOD,
                    CONSTRUCTOR,
            });

    public static final String PEER_ID = "peer";
    public static final ModifierExtension PEER_KIND = new ModifierExtension(
            PEER_ID, 
            org.jmlspecs.annotation.Peer.class,
            new ProgramLocation[]{ 
                    METHOD,
                    CONSTRUCTOR,
                    MODEL_METHOD,
                    MODEL_CONSTRUCTOR,
                    JAVA_FIELD,
                    MODEL_FIELD,
                    GHOST_FIELD,
                    FORMAL_PARAMETER,
                    LOCAL_VARIABLE,
            });

    public static final String REP_ID = "rep";
    public static final ModifierExtension REP_KIND = new ModifierExtension(
            REP_ID, 
            org.jmlspecs.annotation.Rep.class,
            new ProgramLocation[] { 
                    METHOD,
                    CONSTRUCTOR,
                    MODEL_METHOD,
                    MODEL_CONSTRUCTOR,
                    JAVA_FIELD,
                    MODEL_FIELD,
                    GHOST_FIELD,
                    FORMAL_PARAMETER,
                    LOCAL_VARIABLE,
            });

    public static final String READONLY_ID = "readonly";
    public static final ModifierExtension READONLY_KIND = new ModifierExtension(
            READONLY_ID, 
            org.jmlspecs.annotation.Readonly.class,
            new ProgramLocation[]{ 
                    METHOD,
                    CONSTRUCTOR,
                    MODEL_METHOD,
                    MODEL_CONSTRUCTOR,
                    JAVA_FIELD,
                    MODEL_FIELD,
                    GHOST_FIELD,
                    FORMAL_PARAMETER,
                    LOCAL_VARIABLE,
            });

    public static final String SKIPESC_ID = "skipesc";
    public static final ModifierExtension SKIPESC_KIND = new ModifierExtension(
            SKIPESC_ID, 
            org.jmlspecs.annotation.SkipEsc.class,
            new ProgramLocation[]{ 
                    TOP_LEVEL_TYPE,
                    NESTED_TYPE,
                    LOCAL_TYPE,
                    METHOD,
                    CONSTRUCTOR,
                    MODEL_METHOD,
                    MODEL_CONSTRUCTOR,
            });

    public static final String SKIPRAC_ID = "skiprac";
    public static final ModifierExtension SKIPRAC_KIND = new ModifierExtension(
            SKIPRAC_ID, 
            org.jmlspecs.annotation.SkipRac.class,
            new ProgramLocation[]{ 
                    TOP_LEVEL_TYPE,
                    NESTED_TYPE,
                    LOCAL_TYPE,
                    METHOD,
                    CONSTRUCTOR,
                    MODEL_METHOD,
                    MODEL_CONSTRUCTOR,
            });

    public static final String OPTIONS_ID = "options";
    public static final ModifierExtension OPTIONS_KIND = new ModifierExtension(
        OPTIONS_ID, 
        org.jmlspecs.annotation.Options.class,
        new ProgramLocation[]{ 
                TOP_LEVEL_TYPE,
                NESTED_TYPE,
                LOCAL_TYPE,
                    METHOD,
                    CONSTRUCTOR,
                    MODEL_METHOD,
                    MODEL_CONSTRUCTOR,
            });

    public static final String SPECPUBLIC_ID = "spec_public";
    public static final ModifierExtension SPECPUBLIC_KIND = new ModifierExtension(
            SPECPUBLIC_ID, 
            org.jmlspecs.annotation.SpecPublic.class,
            new ProgramLocation[]{ 
                    NESTED_TYPE,
                    JAVA_FIELD,
                    METHOD,  // FIXME - not for model methods
                    CONSTRUCTOR,   // FIXME - not for model constructors
            });

    public static final String SPECPROTECTED_ID = "spec_protected";
    public static final ModifierExtension SPECPROTECTED_KIND = new ModifierExtension(
            SPECPROTECTED_ID, 
            org.jmlspecs.annotation.SpecProtected.class,
            new ProgramLocation[]{ 
                    NESTED_TYPE,
                    JAVA_FIELD,
                    METHOD,  // FIXME - not for model methods
                    CONSTRUCTOR,   // FIXME - not for model constructors
            });

    private static final ProgramLocation[] mathLocations = new ProgramLocation[]{ 
            TOP_LEVEL_TYPE,
            NESTED_TYPE,
            LOCAL_TYPE,
            METHOD,
            CONSTRUCTOR,
            MODEL_METHOD,
            MODEL_CONSTRUCTOR,
        };
    
    public static final String CODEJAVAMATH_ID = "code_java_math";
    public static final ModifierExtension CODEJAVAMATH_KIND = new ModifierExtension(
            CODEJAVAMATH_ID, 
            org.jmlspecs.annotation.CodeJavaMath.class,
            mathLocations);

    public static final String CODESAFEMATH_ID = "code_safe_math";
    public static final ModifierExtension CODESAFEMATH_KIND = new ModifierExtension(
            CODESAFEMATH_ID, 
            org.jmlspecs.annotation.CodeSafeMath.class,
            mathLocations);

    public static final String CODEBIGINTMATH_ID = "code_bigint_math";
    public static final ModifierExtension CODEBIGINTMATH_KIND = new ModifierExtension(
            CODEBIGINTMATH_ID, 
            org.jmlspecs.annotation.CodeBigintMath.class,
            mathLocations);

    public static final String SPECJAVAMATH_ID = "spec_java_math";
    public static final ModifierExtension SPECJAVAMATH_KIND = new ModifierExtension(
            SPECJAVAMATH_ID, 
            org.jmlspecs.annotation.SpecJavaMath.class,
            mathLocations);

    public static final String SPECSAFEMATH_ID = "spec_safe_math";
    public static final ModifierExtension SPECSAFEMATH_KIND = new ModifierExtension(
            SPECSAFEMATH_ID, 
            org.jmlspecs.annotation.SpecSafeMath.class,
            mathLocations);

    public static final String SPECBIGINTMATH_ID = "spec_bigint_math";
    public static final ModifierExtension SPECBIGINTMATH_KIND = new ModifierExtension(
            SPECBIGINTMATH_ID, 
            org.jmlspecs.annotation.SpecBigintMath.class,
            mathLocations);

    private static final ProgramLocation[] peerLocations = new ProgramLocation[]{ 
            METHOD,
            MODEL_METHOD,
            FORMAL_PARAMETER,
            LOCAL_VARIABLE,
            JAVA_FIELD,
        };
    public static final String bspeerID = "\\peer";
    public static final IJmlClauseKind bspeerKind = new ModifierExtension(
            bspeerID,
            org.jmlspecs.annotation.Peer.class,
            peerLocations);
    
    public static final String bsreadonlyID = "\\readonly";
    public static final IJmlClauseKind bsreadonlyKind = new ModifierExtension(
            bsreadonlyID,
            org.jmlspecs.annotation.Readonly.class,
            peerLocations);

    public static final String bsrepID = "\\rep";
    public static final IJmlClauseKind bsrepKind = new ModifierExtension(
            bsrepID,
            org.jmlspecs.annotation.Rep.class,
            peerLocations);

}
