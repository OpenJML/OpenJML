/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 * Reviewed: 2018-03-18
 */
package com.sun.tools.javac.parser;

import org.jmlspecs.openjml.IJmlClauseKind;

import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.parser.Tokens.Comment;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.JCDiagnostic;
import javax.tools.JavaFileObject;

/**
 * This class is an extension of the JDK Token class so that we can represent JML tokens
 * as a JDK Token.
 * 
 * A Token can be one of a number of subclasses (or a Token):
 * <ul>Token                tag=DEFAULT   kind=(some TokenKind)                               toString()              -- Java keyword, operator, punctuation
 * <li>Token.NamedToken     tag=NAMED     kind=IDENTIFIER                                     toString(), name()      -- Java identifier
 * <li>Token.NamedToken     tag=NAMED     kind=(some TokenKind)                               toString(), name()      -- Java primitive type, enum, true, false, null, assert
 * <li>Token.StringToken    tag=STRING    kind=(some TokenKind)                               toString(), stringVal() -- Java string, string fragment
 * <li>Token.NumericToken   tag=NUMERIC   kind=(some TokenKind)                               toString(), stringVal() -- Java numeric literal
 * <li>JmlToken             tag=DEFAULT   kind=CUSTOM            jmlclauseKind=...            toString()              -- JML tokens, distinguished by jmlClauseKind  
 * </ul>
 * Note that some identifiers may either be simple identifiers or may be (unreserved) JML keywords,
 * when in specific grammatical locations.
 *
 * @author David Cok
 */
public class JmlToken extends Token implements JCDiagnostic.DiagnosticPosition {

    /** The kind of token. An IJmlClauseKind is like an enum -- a single object representing each kind of token. */
    public IJmlClauseKind jmlclausekind;
    /** The source file containing the token */
    public JavaFileObject source;
    
    /** a necessary override, but just returns null */
    @Override
    public JCTree getTree() { return null; }
    
    /** Returns the source position of the token */
    public JCDiagnostic.DiagnosticPosition pos() { return this; }
    
    @Override
    public int getStartPosition() { return pos; }
    
    @Override
    public int getPreferredPosition() { return pos; }
    
    @Override
    public int getEndPosition(com.sun.tools.javac.tree.EndPosTable t) { return endPos; }

    /** Creates a JmlToken object
      */
    public JmlToken(IJmlClauseKind jmlclausekind, int pos, int endPos) {
        this(jmlclausekind, null, pos, endPos, null);
    }

    public JmlToken(IJmlClauseKind jmlclausekind, int pos, int endPos, List<Comment> comments) {
        this(jmlclausekind, null, pos, endPos, comments);
    }

    public JmlToken(IJmlClauseKind jmlclausekind, JavaFileObject source, int pos, int endPos) {
        this(jmlclausekind, source, pos, endPos, null);
    }

    public JmlToken(IJmlClauseKind jmlclausekind, JavaFileObject source, int pos, int endPos, List<Comment> comments) {
        super(TokenKind.CUSTOM, pos, endPos, comments);
        this.jmlclausekind = jmlclausekind;
        this.source = source;
    }

    /** Creates a JmlToken object using positions from Java token (with no source file information)
     */
    public JmlToken(IJmlClauseKind jmlclausekind, Token javaToken) {
        super(TokenKind.CUSTOM, javaToken.pos, javaToken.endPos, javaToken.comments);
        this.jmlclausekind = jmlclausekind;
        this.source = null;
    }

    /** Makes a copy of the token, as used in the tree copier, but only implemented for JmlTokens */
    public JmlToken copy() {
        return new JmlToken( this.jmlclausekind, this.source, this.pos, this.endPos, this.comments);
    }

    /** Called by the super constructor */
    @Override
    protected void checkKind() {
        if (kind != TokenKind.CUSTOM) {
            throw new AssertionError("Bad token kind - expected " + TokenKind.CUSTOM);
        }
    }

    @Override
    public IJmlClauseKind jmlclausekind() {
        return jmlclausekind;
    }
    
    @Override
    public String toString() {
        return (jmlclausekind != null ? jmlclausekind.keyword : "?");
    }

    @Override
    public String toStringDetail() {
        return toStringPrefix() + ":" + jmlclausekind + "]";
    }
}
