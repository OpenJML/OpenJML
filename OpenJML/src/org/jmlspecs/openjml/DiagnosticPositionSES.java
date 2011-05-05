package org.jmlspecs.openjml;

import java.util.Map;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.DiagnosticSource;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

/** A derived class of DiagnosticPosition that allows for straightforward setting of the
 * various positions associated with an error message.
 */
public class DiagnosticPositionSES implements DiagnosticPosition {
    protected int begin;
    protected int preferred;
    protected int end; // The end character, NOT ONE CHARACTER BEYOND
    protected DiagnosticSource source;
    
    public DiagnosticPositionSES(int begin, int end, DiagnosticSource source) {
        this.begin = begin;
        this.preferred = begin;
        this.end = end;
        this.source = source;
    }
    
//    public DiagnosticPositionSES(int begin, int preferred, int end) {
//        this.begin = begin;
//        this.preferred = preferred;
//        this.end = end;
//    }
    
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

    @Override
    public int getEndPosition(Map<JCTree, Integer> endPosTable) {
        return end;
    }
    
    public int getEndPosition() {
        return end;
    }
    
    public DiagnosticSource getSource() {
        return source;
    }
    
}

