/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import com.sun.tools.javac.parser.Tokens.ITokenKind;
import com.sun.tools.javac.tree.JCTree;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.*;
import static org.jmlspecs.openjml.ext.AssignableClauseExtension.*;
import static org.jmlspecs.openjml.ext.SignalsClauseExtension.*;
import static org.jmlspecs.openjml.ext.StatementLocationsExtension.*;
import static org.jmlspecs.openjml.ext.StatementExprExtensions.*;

/**
 * This class defines the scanner tokens that represent JML syntax.
 * 
 * @author David Cok
 */

// These are represented as enums. I'm not sure that is the best design since,
// although Enums are nice, they are not extensible. That is how Token is
// implemented, and we could not extend that.
// TODO - we should think about how to re-design JmlToken so that it is extensible.
public enum JmlTokenKind implements ITokenKind {
//    STARTJMLCOMMENT("<JMLSTART>"),
    ENDJMLCOMMENT("<JMLEND>"),
    
    // These are statement types
    //REFINING("refining"),
    //LAST("_",null), // This is a fake entry that is the end of the standard+extension modifiers list
    
    
    
//    // Other misc
//    CONSTRUCTOR("constructor"),
//    FIELD("field"),
//    METHOD("method"),
    
    // These are various tokens related to JML expressions
//    MATCH("match"),
//    BSREQUIRES("\\requires"),
//    BSREADS("\\reads"),
//    BSWRITES("\\writes"),
//    BSENSURES("\\ensures"),
//    BSLET("\\let"),
    BSPRE("\\pre"), // overloaded both \post-like and \old-like
//    BSASSIGNS("\\assigns"),

    
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
    SUBTYPE_OF_EQ("<:="), // Operands are \TYPE values
    JSUBTYPE_OF("<::"), // Operands are Class<?> values, used only internally
    JSUBTYPE_OF_EQ("<::="), // Operands are Class<?> values, used only internally
    LOCK_LT("<#"),
    LOCK_LE("<#="),
    WF_LT("<<<"),
    WF_LE("<<<="),
    
    // Other special character combinations
    DOT_DOT(".."),
    LEFT_ARROW("<-"),
    INFORMAL_COMMENT("(*...*)"),
    SPEC_GROUP_START("{|"),
    SPEC_GROUP_END("|}"),
    
    ;
    
    /** The canonical form of the token in text */
    private String name;
    
    /** The annotation class associated with this token (for modifiers only), if any */
    //@ nullable
    public Class<?> annotationType = null;
    
    public boolean isRedundant;
    
    /** A human readable form of the token, and how it appears in text
     * @return the canonical, printable form of the token (not the internal toString() form)
     */
    public String internedName() { return name; }
    
    
    /** Constructs an Enum instance using an empty string */
    private JmlTokenKind() { this("",null); }
    
    /** Constructs an Enum token from a string - not available to users
     * @param s The string that will be the canonical form of the token
     */
    private JmlTokenKind(String s) { this(s,null); }
    
    /** Constructs an Enum token from a string and annotation type - not available to users.
     * Any modifier token should use this constructor
     * @param s The string that will be the canonical form of the token
     */
    private JmlTokenKind(String s, Class<?> annotationType) { 
        this.name = s == null ? null : s.intern(); 
        this.annotationType = annotationType;
    }
    
    /** This is a map from string to token for backslash tokens; the input string
     * includes the initial backslash.
     */
    public final static Map<String,JmlTokenKind> backslashTokens = new HashMap<String,JmlTokenKind>();
    
    /** This is a map from string to token for all of the tokens, and includes defined synonyms. */
    public final static Map<String,JmlTokenKind> allTokens = new HashMap<>();
    
    
    public final static EnumSet<JmlTokenKind> jmloperators = EnumSet.range(EQUIVALENCE, LOCK_LE);
    
    
    
    static {
        
        for (JmlTokenKind t: EnumSet.range(BSPRE,BSBIGINT)) {
            backslashTokens.put(t.internedName(),t);
        }
        for (JmlTokenKind t: JmlTokenKind.values()) {
            allTokens.put(t.internedName(),t);
        }
    }
}
