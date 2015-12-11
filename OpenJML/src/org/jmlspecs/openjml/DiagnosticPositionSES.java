/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import java.util.Map;

import com.sun.tools.javac.tree.EndPosTable;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.DiagnosticSource;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

/** A derived class of DiagnosticPosition that allows for straightforward setting of the
 * various positions associated with an error message.
 */
public class DiagnosticPositionSES implements DiagnosticPosition {
    // Character positions are 1-based from the beginning of the source file.
    
    /** The 1-based starting character of the error */
    protected int begin;
    /** The preferred single location to designate the error (1-based character count from beginning of file) */
    protected int preferred;
    /** The 1-based end character of the error (NOT one character beyond the end) */
    protected int end; // The end character, NOT ONE CHARACTER BEYOND
    /** The source object in which the error occrred. */
    protected DiagnosticSource source;
    
    /** Constructs a diagnostic location object. The preferred position is
     * set to the beginning of the error.
     * 
     * @param begin 1-based character position of the beginning of the error
     * @param end 1-based character position of the end of the error
     * @param source source object containing the error
     */
    public DiagnosticPositionSES(int begin, int end, DiagnosticSource source) {
        this.begin = begin;
        this.preferred = begin;
        this.end = end;
        this.source = source;
    }
    
    /** Constructs a diagnostic location object. The preferred position is
     * set to the beginning of the error.
     * 
     * @param begin 1-based character position of the beginning of the error
     * @param preferred -1-based character position of the preferred location to indicate the error
     * @param end 1-based character position of the end of the error
     * @param source source object containing the error
     */
    public DiagnosticPositionSES(int begin, int preferred, int end, DiagnosticSource source) {
        this.begin = begin;
        this.preferred = preferred;
        this.end = end;
        this.source = source;
    }
    
    @Override
    public JCTree getTree() {
        return null;
    }

    @Override
    public int getStartPosition() {
        return begin;
    }

    @Override
    public int getPreferredPosition() {
        return preferred;
    }

    public int getEndPosition() {
        return end;
    }
    
    public DiagnosticSource getSource() {
        return source;
    }

    @Override
    public int getEndPosition(EndPosTable endPosTable) {
        return end;// FIXME
    }
    
}

