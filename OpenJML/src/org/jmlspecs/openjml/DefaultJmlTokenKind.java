package org.jmlspecs.openjml;

import java.util.EnumSet;
import java.util.HashMap;
import java.util.Map;

// These are represented as enums. I'm not sure that is the best design since,
// although Enums are nice, they are not extensible. That is how Token is
// implemented, and we could not extend that.
// TODO - we should think about how to re-design JmlToken so that it is extensible.
public enum DefaultJmlTokenKind implements JmlTokenKind {
    //    STARTJMLCOMMENT("<JMLSTART>"),
    ENDJMLCOMMENT("<JMLEND>"),

    // These are statement types
    ASSUME("assume"),  // Keep this one first of the method statement tokens
    ASSERT("assert"),
    COMMENT("comment"), // For comments in BasicBlock programs
    HAVOC("havoc"), // Just used in ESC
    //    DEBUG("debug"),
    END("end"),
    //    SET("set"),
    SHOW("show"),
    USE("use"),
    DECREASES("decreases"),
    LOOP_DECREASES("loop_decreases"),
    INLINED_LOOP("inlined_loop"),
    LOOP_INVARIANT("loop_invariant"),
    LOOP_MODIFIES("loop_modifies"),
    HENCE_BY("hence_by"),
    REFINING("refining"),
    REACHABLE("reachable"),
    UNREACHABLE("unreachable"), // Keep this one last of the method statement tokens

    // These are modifiers
    PURE("pure", org.jmlspecs.annotation.Pure.class), // Keep this one the first of the modifiers (see the modifiers Map below)
    CODE_JAVA_MATH("code_java_math", org.jmlspecs.annotation.CodeJavaMath.class),
    CODE_SAFE_MATH("code_safe_math", org.jmlspecs.annotation.CodeSafeMath.class),
    EXTRACT("extract", org.jmlspecs.annotation.Extract.class),
    GHOST("ghost", org.jmlspecs.annotation.Ghost.class),
    IMMUTABLE("immutable", org.jmlspecs.annotation.Immutable.class), // FIXME - this is an extension - comment
    INSTANCE("instance", org.jmlspecs.annotation.Instance.class),
    MODEL("model", org.jmlspecs.annotation.Model.class),
    NONNULL("non_null", org.jmlspecs.annotation.NonNull.class),
    NULLABLE("nullable", org.jmlspecs.annotation.Nullable.class),
    NULLABLE_BY_DEFAULT("nullable_by_default", org.jmlspecs.annotation.NullableByDefault.class),
    NON_NULL_BY_DEFAULT("non_null_by_default", org.jmlspecs.annotation.NonNullByDefault.class), // TODO: In some code, but not in JML
    FUNCTION("function", org.jmlspecs.annotation.Function.class),
    HELPER("helper", org.jmlspecs.annotation.Helper.class),
    UNINITIALIZED("uninitialized", org.jmlspecs.annotation.Uninitialized.class),
    MONITORED("monitored", org.jmlspecs.annotation.Monitored.class),
    OPTIONS(null, org.jmlspecs.annotation.Options.class),
    PEER("peer", org.jmlspecs.annotation.Peer.class),
    READONLY("readonly", org.jmlspecs.annotation.Readonly.class),
    REP("rep", org.jmlspecs.annotation.Rep.class),
    SKIP_ESC("skipesc", org.jmlspecs.annotation.SkipEsc.class),
    SKIP_RAC("skiprac", org.jmlspecs.annotation.SkipRac.class),
    SPEC_BIGINT_MATH("spec_bigint_math", org.jmlspecs.annotation.SpecBigintMath.class),
    SPEC_JAVA_MATH("spec_java_math", org.jmlspecs.annotation.SpecJavaMath.class),
    SPEC_SAFE_MATH("spec_safe_math", org.jmlspecs.annotation.SpecSafeMath.class),
    SPEC_PUBLIC("spec_public", org.jmlspecs.annotation.SpecPublic.class),
    SPEC_PROTECTED("spec_protected", org.jmlspecs.annotation.SpecProtected.class),
    CODE_BIGINT_MATH("code_bigint_math", org.jmlspecs.annotation.CodeBigintMath.class), // Keep this one the last of the standard modifiers (see the modifiers Map below)
    // Anything between CODE_BIGINT_MATH and LAST is automatically considered an OpenJML extension
    QUERY("query", org.jmlspecs.annotation.Query.class),  // FIXME - this is an extension - comment
    SECRET("secret", org.jmlspecs.annotation.Secret.class),  // FIXME - this is an extension - comment
    INLINE("inline", org.jmlspecs.annotation.Inline.class), // FIXME - This is an extension
    LAST("_", null), // This is a fake entry that is the end of the standard+extension modifiers list

    // These are class/interface clause types
    INVARIANT("invariant"),
    INITIALLY("initially"),
    CONSTRAINT("constraint"),
    AXIOM("axiom"),
    REPRESENTS("represents"),
    JMLDECL("jml declaration"), // not a scannable token
    IN("in"),
    MAPS("maps"),
    INITIALIZER("initializer"),
    STATIC_INITIALIZER("static_initializer"),
    MONITORS_FOR("monitors_for"),
    READABLE("readable"),
    WRITABLE("writable"),

    // These are related to specification cases
    ALSO("also"),  // Keep this one first
    NORMAL_BEHAVIOR("normal_behavior"),
    BEHAVIOR("behavior"),
    EXCEPTIONAL_BEHAVIOR("exceptional_behavior"),
    ABRUPT_BEHAVIOR("abrupt_behavior"),
    NORMAL_EXAMPLE("normal_example"),
    EXAMPLE("example"),
    EXCEPTIONAL_EXAMPLE("exceptional_example"),
    MODEL_PROGRAM("model_program"),
    IMPLIES_THAT("implies_that"),
    FOR_EXAMPLE("for_example"),
    CODE("code"),  // Keep this one last

    // These are the method clause types
    REQUIRES("requires"),   // Keep this one first
    ENSURES("ensures"),
    SIGNALS("signals"),
    SIGNALS_ONLY("signals_only"),
    DIVERGES("diverges"),
    WHEN("when"),
    DURATION("duration"),
    WORKING_SPACE("working_space"),
    FORALL("forall"),
    OLD("old"),
    ASSIGNABLE("assignable"),
    ACCESSIBLE("accessible"),
    MEASURED_BY("measured_by"),
    CALLABLE("callable"),
    CAPTURES("captures"),  // Keep this one last

    // These are only in model programs
    CHOOSE("choose"),
    CHOOSE_IF("choose_if"),
    BREAKS("breaks"),
    CONTINUES("continues"),
    OR("or"),
    RETURNS("returns"),

    // Other misc
    CONSTRUCTOR("constructor"),
    FIELD("field"),
    METHOD("method"),
    NOWARN("nowarn"),

    // These are various tokens related to JML expressions
    BSEXCEPTION("\\exception"), // This is for internal use only, so it is before \result
    BSRESULT("\\result"), // Keep this one the first of the backslash tokens
    BSEVERYTHING("\\everything"),
    BSLOCKSET("\\lockset"),
    BSCOUNT("\\count"), // New version of \index
    BSINDEX("\\index"), // Obsolete in favor of \count
    BSVALUES("\\values"),
    BSNOTHING("\\nothing"),
    BSSAME("\\same"),
    BSNOTSPECIFIED("\\not_specified"),

    BSCONCAT("\\concat"),
    BSDISTINCT("\\distinct"),
    BSDURATION("\\duration"),
    BSELEMTYPE("\\elemtype"),
    BSERASURE("\\erasure"),
    BSFRESH("\\fresh"),
    BSINVARIANTFOR("\\invariant_for"),
    BSISINITIALIZED("\\is_initialized"),
    BSKEY("\\key"),
    BSLBLANY("\\lbl"),
    BSLBLNEG("\\lblneg"),
    BSLBLPOS("\\lblpos"),
    BSLET("\\let"),
    BSMAX("\\max"),
    BSNONNULLELEMENTS("\\nonnullelements"),
    BSNOTASSIGNED("\\not_assigned"),
    BSNOTMODIFIED("\\not_modified"),
    BSOLD("\\old"),
    BSONLYACCESSED("\\only_accessed"),
    BSONLYASSIGNED("\\only_assigned"),
    BSONLYCALLED("\\only_called"),
    BSONLYCAPTURED("\\only_captured"),
    BSPAST("\\past"),
    BSPRE("\\pre"), // overloaded both \post-like and \old-like
    BSPOST("\\post"),
    BSASSIGNS("\\assigns"),
    BSREACH("\\reach"),
    BSSPACE("\\space"),
    BSTYPEOF("\\typeof"),
    BSTYPELC("\\type"),
    BSWORKINGSPACE("\\working_space"),

    BSBIGINT_MATH("\\bigint_math"),
    BSJAVAMATH("\\java_math"),
    BSSAFEMATH("\\safe_math"),
    BSNOWARN("\\nowarn"),
    BSNOWARNOP("\\nowarn_op"),
    BSWARN("\\warn"),
    BSWARNOP("\\warn_op"),

    BSINTO("\\into"),
    BSSUCHTHAT("\\such_that"),

    BSPEER("\\peer"),
    BSREADONLY("\\readonly"),
    BSREP("\\rep"),

    // These are quantifier types (also \max )
    BSEXISTS("\\exists"),
    BSFORALL("\\forall"),
    BSMIN("\\min"),
    BSNUMOF("\\num_of"),
    BSPRODUCT("\\product"),
    BSSUM("\\sum"),

    // These are JML type literals
    BSTYPEUC("\\TYPE"),
    BSREAL("\\real"),
    BSBIGINT("\\bigint"), // Keep this one the last of the backslash tokens
    PRIMITIVE_TYPE("\\primitive"),

    // These are JML operators (in expressions)
    // Note that the jmloperators set relies on this ordering
    EQUIVALENCE("<==>"),
    INEQUIVALENCE("<=!=>"),
    IMPLIES("==>"),
    REVERSE_IMPLIES("<=="),
    SUBTYPE_OF("<:"), // Operands are \TYPE values
    JSUBTYPE_OF("<::"), // Operands are Class<?> values, used only internally
    LOCK_LT("<#"),
    LOCK_LE("<#="),

    // Other special character combinations
    DOT_DOT(".."),
    LEFT_ARROW("<-"),
    //    RIGHT_ARROW("->"),
    INFORMAL_COMMENT("(*...*)"),
    SPEC_GROUP_START("{|"),
    SPEC_GROUP_END("|}"),

    ;

    /**
     * This is a map from string to token for backslash tokens; the input string
     * includes the initial backslash.
     */
    public final static Map<String, JmlTokenKind> backslashTokens = new HashMap<>();
    /**
     * This is a map from string to token for all of the tokens, and includes defined synonyms.
     */
    public final static Map<String, JmlTokenKind> allTokens = new HashMap<>();
    /**
     * This is a set of all the modifier tokens, defined so that it is quick
     * and easy to test if a token is a modifier.
     */
    public final static EnumSet<DefaultJmlTokenKind> modifiers = EnumSet.range(PURE, LAST);  // BSREADONLY added below
    public final static EnumSet<DefaultJmlTokenKind> extensions = EnumSet.range(CODE_BIGINT_MATH, LAST);
    public final static EnumSet<DefaultJmlTokenKind> jmloperators = EnumSet.range(EQUIVALENCE, LOCK_LE);
    /**
     * This is a set of the modifiers that may be used to characterize a type.
     */
    public final static JmlTokenKind[] typeModifiers = new JmlTokenKind[]{NULLABLE, NONNULL, BSREADONLY};
    /**
     * This is a set of all of the tokens that begin method specification clauses,
     * defined so that it is quick and easy to test for a given token.
     */
    public final static EnumSet<DefaultJmlTokenKind> methodClauseTokens = EnumSet.range(REQUIRES, CAPTURES);
    /**
     * This is a set of all of the tokens that begin JML statements in the body of a method,
     * defined so that it is quick and easy to test for a given token.
     */
    public final static EnumSet<DefaultJmlTokenKind> methodStatementTokens = EnumSet.range(ASSUME, UNREACHABLE);
    /**
     * This is the set of tokens that can occur at the beginning of a specification case
     */
    public final static EnumSet<DefaultJmlTokenKind> specCaseTokens = EnumSet.range(ALSO, CODE);

    static {
        extensions.remove(CODE_BIGINT_MATH); // This is not an extension - it marks the last of non-extensions
        extensions.remove(LAST); // Not real - just marks the end of any extensions
    }

    static {
        for (DefaultJmlTokenKind t : EnumSet.range(BSEXCEPTION, BSBIGINT)) {
            backslashTokens.put(t.internedName(), t);
        }
        for (DefaultJmlTokenKind t : DefaultJmlTokenKind.values()) {
            allTokens.put(t.internedName(), t);
        }
        //allTokens.remove(BSEXCEPTION.internedName());
        modifiers.add(BSREADONLY);
        // the LAST token is fake and doesn't really need to be in the modifiers set
        modifiers.remove(LAST);

        // Synonyms

        allTokens.put("modifies", ASSIGNABLE);
        allTokens.put("modifiable", ASSIGNABLE);
        allTokens.put("pre", REQUIRES);
        allTokens.put("post", ENSURES);
        allTokens.put("exsures", SIGNALS);
        allTokens.put("behaviour", BEHAVIOR);
        allTokens.put("exceptional_behaviour", EXCEPTIONAL_BEHAVIOR);
        allTokens.put("normal_behaviour", NORMAL_BEHAVIOR);
        allTokens.put("abrupt_behaviour", ABRUPT_BEHAVIOR);
        allTokens.put("decreasing", LOOP_DECREASES);
        allTokens.put("decreases", LOOP_DECREASES);
        allTokens.put("maintaining", LOOP_INVARIANT);
    }

    /**
     * The annotation class associated with this token (for modifiers only), if any
     */
    //@ nullable
    public Class<?> annotationType = null;
    public boolean isRedundant;
    /**
     * The canonical form of the token in text
     */
    private String name;

    /**
     * Constructs an Enum token from a string - not available to users
     *
     * @param s The string that will be the canonical form of the token
     */
    private DefaultJmlTokenKind(String s) {
        this(s, null);
    }

    /**
     * Constructs an Enum token from a string and annotation type - not available to users.
     * Any modifier token should use this constructor
     *
     * @param s The string that will be the canonical form of the token
     */
    private DefaultJmlTokenKind(String s, Class<?> annotationType) {
        this.name = s;
        this.annotationType = annotationType;
    }

    /**
     * A human readable form of the token, and how it appears in text
     *
     * @return the canonical, printable form of the token (not the internal toString() form)
     */
    public String internedName() {
        return name;
    }

    @Override
    public Class<?> getAnnotationType() {
        return annotationType;
    }

    @Override
    public boolean isRedundant() {
        return isRedundant;
    }
}
