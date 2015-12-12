/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package com.sun.tools.javac.parser;

import java.nio.CharBuffer;
import java.util.Map;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.parser.Tokens.Token.Tag;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.DiagnosticSource;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;
import com.sun.tools.javac.util.LayoutCharacters;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Options;

/* NOTE: - oddities in the Scanner class
 It seems that if the first character of a token is unicode, then pos is
 set to be the last character of that initial unicode sequence.
 I don't think the endPos value is set correctly when a unicode is read;
 endPos appears to be the end of the character after the token characters,
 which is not correct if the succeeding token is a unicode character

 unicodeConversionBp does not seem to be useful for anything; does it stop
 two unicode conversions in a row?  Actually, when an initial backslash is
 in unicode, then that backslash is not the beginning of another unicode
 sequence - the check on unicodeConversionBp stops this.

 Recovery after an ERROR token that is a \ seems to consume extra characters

 I'm not sure the behavior of unicode with multiple backslashes is correct
 */

// FIXME - turn off jml when an exception happens?
/**
 * This class is an extension of the JDK scanner that scans JML constructs as
 * well. Note that it relies on some fields and methods of Scanner being
 * protected that are not declared protected in the current version of OpenJDK.
 * No other changes to Scanner are made, which does require a number of complicating
 * workarounds in this code. In retrospect, a much simpler JML scanner could have
 * been produced by being more surgical with JavaScanner; but given the goal to 
 * be minimally invasive, this is what we have.
 * 
 * @author David Cok
 */
public class JmlToken extends Token {

    public JmlTokenKind jmlkind;
    
    public JmlToken(JmlTokenKind jmlkind, TokenKind tk, int pos, int endPos) {
        super(jmlkind != null ? jmlkind : tk, pos, endPos, null); // FIXME List<COmment> ?
        this.jmlkind = jmlkind;
    }
    
    public JmlToken(Token javaToken) {
        this(null, javaToken);
    }
    
    public JmlToken(JmlTokenKind jmlkind, Token javaToken) {
        super(jmlkind != null ? jmlkind : javaToken.kind, javaToken.pos, javaToken.endPos, javaToken.comments);
        this.jmlkind = jmlkind;
    }

    protected void checkKind() {
//        if (kind.tag != Tag.DEFAULT) {
//            throw new AssertionError("Bad token kind - expected " + Tag.STRING);
//        }
    }

    public String toString() {
        return ikind.toString();
    }
    
}
