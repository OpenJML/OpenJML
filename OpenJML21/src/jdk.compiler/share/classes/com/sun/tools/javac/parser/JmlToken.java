/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 * Reviewed: 2018-03-18
 */
package com.sun.tools.javac.parser;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlTokenKind;

import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.parser.Tokens.Comment;
import com.sun.tools.javac.util.List;
import javax.tools.JavaFileObject;

/**
 * This class is an extension of the JDK Token class so that we can represent JML tokens
 * as a JDK Token.
 *
 * @author David Cok
 */
public class JmlToken extends Token {

    public JmlTokenKind jmlkind;
    public IJmlClauseKind jmlclausekind;
    public JavaFileObject source;

    /** Creates a JmlToken object, as either, if jmlkind is null, a Java token in a JMLToken wrapper or,
      * if jmlkind is not null, a JMlToken object for a JML construct.
      */
    public JmlToken(/*@ nullable */JmlTokenKind jmlkind, IJmlClauseKind jmlclausekind, TokenKind tk, int pos, int endPos) {
        this(jmlkind, jmlclausekind, tk, pos, endPos, null);
    }

    public JmlToken(/*@ nullable */JmlTokenKind jmlkind, IJmlClauseKind jmlclausekind, TokenKind tk, int pos, int endPos, List<Comment> comments) {
        super(jmlkind != null ? jmlkind : tk, pos, endPos, comments); // FIXME - do we ever need to add in a List<Comment>
        this.jmlkind = jmlkind;
        this.jmlclausekind = jmlclausekind;
    }

    public JmlToken(IJmlClauseKind jmlclausekind, JavaFileObject source, int pos, int endPos) {
        this(null, jmlclausekind, TokenKind.CUSTOM, pos, endPos, null);
        this.source = source;
    }

    /** Creates a JmlTOken that just wraps a Java Token */
    public JmlToken(Token javaToken) {
        this(null, null, javaToken);
    }

    /** Creates a JmlToken object, as either, if jmlkind is null, a Java token in a JMLToken wrapper or,
     * if jmlkind is not null, a JMlToken object for a JML construct.
     */
    public JmlToken(IJmlClauseKind jmlclausekind, Token javaToken) {
        super(TokenKind.CUSTOM, javaToken.pos, javaToken.endPos, javaToken.comments);
        this.jmlkind = null;
        this.jmlclausekind = jmlclausekind;
    }
    
    public JmlToken(JmlTokenKind jmlkind, IJmlClauseKind jmlclausekind, Token javaToken) {
        super(jmlkind != null ? jmlkind : javaToken.kind, javaToken.pos, javaToken.endPos, javaToken.comments);
        this.jmlkind = jmlkind;
        this.jmlclausekind = jmlclausekind;
    }
    
    public JmlToken copy() {
    	JmlToken t = new JmlToken(this.jmlkind, this.jmlclausekind, this.kind, this.pos, this.endPos);
    	t.source = this.source;
    	// FIXME - copy comments?
    	return t;
    }

    protected void checkKind() {
    }

    public String toString() {
        return (jmlclausekind != null ? jmlclausekind.keyword : "?");
    }
}
