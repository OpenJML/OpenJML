/*
 * Copyright (c) 2004, 2010, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

package com.sun.tools.javac.parser;

import java.nio.*;

import com.sun.tools.javac.util.*;
import static com.sun.tools.javac.util.LayoutCharacters.*;

/** An extension to the base lexical analyzer that captures
 *  and processes the contents of doc comments.  It does so by
 *  translating Unicode escape sequences and by stripping the
 *  leading whitespace and starts from each line of the comment.
 *
 *  <p><b>This is NOT part of any supported API.
 *  If you write code that depends on this, you do so at your own risk.
 *  This code and its internal interfaces are subject to change or
 *  deletion without notice.</b>
 */
public class DocCommentScanner extends Scanner {

    /** Create a scanner from the input buffer.  buffer must implement
     *  array() and compact(), and remaining() must be less than limit().
     */
    protected DocCommentScanner(ScannerFactory fac, CharBuffer buffer) {
        super(fac, buffer);
    }

    /** Create a scanner from the input array.  The array must have at
     *  least a single character of extra space.
     */
    protected DocCommentScanner(ScannerFactory fac, char[] input, int inputLength) {
        super(fac, input, inputLength);
    }

    /** Starting position of the comment in original source
     */
    private int pos; // DRC - commented out because inherited from Scanner

    /** The comment input buffer, index of next chacter to be read,
     *  index of one past last character in buffer.
     */
    private char[] _buf; // DRC - renamed so as not to interfere with similar names in super and derived classes
    private int __bp; // DRC - renamed so as not to interfere with similar names in super and derived classes
    private int _buflen; // DRC - renamed so as not to interfere with similar names in super and derived classes

    /** The current character.
     */
    private char _ch; // DRC - renamed so as not to interfere with similar names in super and derived classes

    /** The column number position of the current character.
     */
    private int _col; // DRC - renamed so as not to interfere with similar names in super and derived classes

    /** The buffer index of the last converted Unicode character
     */
    private int unicodeConversionBp = 0;

    /**
     * Buffer for doc comment.
     */
    private char[] docCommentBuffer = new char[1024];

    /**
     * Number of characters in doc comment buffer.
     */
    private int docCommentCount;

    /**
     * Translated and stripped contents of doc comment
     */
    protected String docComment = null; // DRC _ changed from private to protected


    /** Unconditionally expand the comment buffer.
     */
    private void expandCommentBuffer() {
        char[] newBuffer = new char[docCommentBuffer.length * 2];
        System.arraycopy(docCommentBuffer, 0, newBuffer,
                         0, docCommentBuffer.length);
        docCommentBuffer = newBuffer;
    }

    /** Convert an ASCII digit from its base (8, 10, or 16)
     *  to its value.
     */
    private int digit(int base) {
        char c = _ch;
        int result = Character.digit(c, base);
        if (result >= 0 && c > 0x7f) {
            _ch = "0123456789abcdef".charAt(result);
        }
        return result;
    }

    /** Convert Unicode escape; bp points to initial '\' character
     *  (Spec 3.3).
     */
    private void convertUnicode() {
        if (_ch == '\\' && unicodeConversionBp != __bp) {
            __bp++; _ch = _buf[__bp]; _col++;
            if (_ch == 'u') {
                do {
                    __bp++; _ch = _buf[__bp]; _col++;
                } while (_ch == 'u');
                int limit = __bp + 3;
                if (limit < _buflen) {
                    int d = digit(16);
                    int code = d;
                    while (__bp < limit && d >= 0) {
                        __bp++; _ch = _buf[__bp]; _col++;
                        d = digit(16);
                        code = (code << 4) + d;
                    }
                    if (d >= 0) {
                        _ch = (char)code;
                        unicodeConversionBp = __bp;
                        return;
                    }
                }
                // "illegal.Unicode.esc", reported by base scanner
            } else {
                __bp--;
                _ch = '\\';
                _col--;
            }
        }
    }


    /** Read next character.
     */
    private void _scanChar() { // DRC - changed to protected; back to private; changed name
        __bp++;
        _ch = _buf[__bp];
        switch (_ch) {
        case '\r': // return
            _col = 0;
            break;
        case '\n': // newline
            if (__bp == 0 || _buf[__bp-1] != '\r') {
                _col = 0;
            }
            break;
        case '\t': // tab
            _col = (_col / TabInc * TabInc) + TabInc;
            break;
        case '\\': // possible Unicode
            _col++;
            convertUnicode();
            break;
        default:
            _col++;
            break;
        }
    }

    /**
     * Read next character in doc comment, skipping over double '\' characters.
     * If a double '\' is skipped, put in the buffer and update buffer count.
     */
    private void scanDocCommentChar() {
        _scanChar();
        if (_ch == '\\') {
            if (_buf[__bp+1] == '\\' && unicodeConversionBp != __bp) {
                if (docCommentCount == docCommentBuffer.length)
                    expandCommentBuffer();
                docCommentBuffer[docCommentCount++] = _ch;
                __bp++; _col++;
            } else {
                convertUnicode();
            }
        }
    }

    /* Reset doc comment before reading each new token
     */
    public void nextToken() {
        docComment = null;
        super.nextToken();
    }

    /**
     * Returns the documentation string of the current token.
     */
    public String docComment() {
        return docComment;
    }

    /**
     * Process a doc comment and make the string content available.
     * Strips leading whitespace and stars.
     */
    @SuppressWarnings("fallthrough")
    protected void processComment(CommentStyle style) {
        if (style != CommentStyle.JAVADOC) {
            return;
        }

        _pos = pos();
        _buf = getRawCharacters(_pos, endPos());
        _buflen = _buf.length;
        __bp = 0;
        _col = 0;

        docCommentCount = 0;

        boolean firstLine = true;

        // Skip over first slash
        scanDocCommentChar();
        // Skip over first star
        scanDocCommentChar();

        // consume any number of stars
        while (__bp < _buflen && _ch == '*') {
            scanDocCommentChar();
        }
        // is the comment in the form /**/, /***/, /****/, etc. ?
        if (__bp < _buflen && _ch == '/') {
            docComment = "";
            return;
        }

        // skip a newline on the first line of the comment.
        if (__bp < _buflen) {
            if (_ch == LF) {
                scanDocCommentChar();
                firstLine = false;
            } else if (_ch == CR) {
                scanDocCommentChar();
                if (_ch == LF) {
                    scanDocCommentChar();
                    firstLine = false;
                }
            }
        }

    outerLoop:

        // The outerLoop processes the doc comment, looping once
        // for each line.  For each line, it first strips off
        // whitespace, then it consumes any stars, then it
        // puts the rest of the line into our buffer.
        while (__bp < _buflen) {

            // The wsLoop consumes whitespace from the beginning
            // of each line.
        wsLoop:

            while (__bp < _buflen) {
                switch(_ch) {
                case ' ':
                    scanDocCommentChar();
                    break;
                case '\t':
                    _col = ((_col - 1) / TabInc * TabInc) + TabInc;
                    scanDocCommentChar();
                    break;
                case FF:
                    _col = 0;
                    scanDocCommentChar();
                    break;
// Treat newline at beginning of line (blank line, no star)
// as comment text.  Old Javadoc compatibility requires this.
/*---------------------------------*
                case CR: // (Spec 3.4)
                    scanDocCommentChar();
                    if (ch == LF) {
                        col = 0;
                        scanDocCommentChar();
                    }
                    break;
                case LF: // (Spec 3.4)
                    scanDocCommentChar();
                    break;
*---------------------------------*/
                default:
                    // we've seen something that isn't whitespace;
                    // jump out.
                    break wsLoop;
                }
            }

            // Are there stars here?  If so, consume them all
            // and check for the end of comment.
            if (_ch == '*') {
                // skip all of the stars
                do {
                    scanDocCommentChar();
                } while (_ch == '*');

                // check for the closing slash.
                if (_ch == '/') {
                    // We're done with the doc comment
                    // _scanChar() and breakout.
                    break outerLoop;
                }
            } else if (! firstLine) {
                //The current line does not begin with a '*' so we will indent it.
                for (int i = 1; i < _col; i++) {
                    if (docCommentCount == docCommentBuffer.length)
                        expandCommentBuffer();
                    docCommentBuffer[docCommentCount++] = ' ';
                }
            }

            // The textLoop processes the rest of the characters
            // on the line, adding them to our buffer.
        textLoop:
            while (__bp < _buflen) {
                switch (_ch) {
                case '*':
                    // Is this just a star?  Or is this the
                    // end of a comment?
                    scanDocCommentChar();
                    if (_ch == '/') {
                        // This is the end of the comment,
                        // set ch and return our buffer.
                        break outerLoop;
                    }
                    // This is just an ordinary star.  Add it to
                    // the buffer.
                    if (docCommentCount == docCommentBuffer.length)
                        expandCommentBuffer();
                    docCommentBuffer[docCommentCount++] = '*';
                    break;
                case ' ':
                case '\t':
                    if (docCommentCount == docCommentBuffer.length)
                        expandCommentBuffer();
                    docCommentBuffer[docCommentCount++] = _ch;
                    scanDocCommentChar();
                    break;
                case FF:
                    scanDocCommentChar();
                    break textLoop; // treat as end of line
                case CR: // (Spec 3.4)
                    scanDocCommentChar();
                    if (_ch != LF) {
                        // Canonicalize CR-only line terminator to LF
                        if (docCommentCount == docCommentBuffer.length)
                            expandCommentBuffer();
                        docCommentBuffer[docCommentCount++] = (char)LF;
                        break textLoop;
                    }
                    /* fall through to LF case */
                case LF: // (Spec 3.4)
                    // We've seen a newline.  Add it to our
                    // buffer and break out of this loop,
                    // starting fresh on a new line.
                    if (docCommentCount == docCommentBuffer.length)
                        expandCommentBuffer();
                    docCommentBuffer[docCommentCount++] = _ch;
                    scanDocCommentChar();
                    break textLoop;
                default:
                    // Add the character to our buffer.
                    if (docCommentCount == docCommentBuffer.length)
                        expandCommentBuffer();
                    docCommentBuffer[docCommentCount++] = _ch;
                    scanDocCommentChar();
                }
            } // end textLoop
            firstLine = false;
        } // end outerLoop

        if (docCommentCount > 0) {
            int i = docCommentCount - 1;
        trailLoop:
            while (i > -1) {
                switch (docCommentBuffer[i]) {
                case '*':
                    i--;
                    break;
                default:
                    break trailLoop;
                }
            }
            docCommentCount = i + 1;

            // Store the text of the doc comment
            docComment = new String(docCommentBuffer, 0 , docCommentCount);
        } else {
            docComment = "";
        }
    }

    /** Build a map for translating between line numbers and
     * positions in the input.
     *
     * @return a LineMap */
    public Position.LineMap getLineMap() {
        char[] buf = getRawCharacters();
        return Position.makeLineMap(buf, buf.length, true);
    }
}
