package org.jmlspecs.openjml.jmldoc.builders;

import java.util.ArrayList;
import java.util.Collections;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.FieldDoc;
import com.sun.javadoc.ProgramElementDoc;
import com.sun.tools.doclets.internal.toolkit.Configuration;
import com.sun.tools.doclets.internal.toolkit.FieldWriter;
import com.sun.tools.doclets.internal.toolkit.builders.FieldBuilder;
import com.sun.tools.doclets.internal.toolkit.builders.XMLNode;
import com.sun.tools.doclets.internal.toolkit.util.VisibleMemberMap;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.jmldoc.writers.FieldWriterJml;

/**
 * Builds the summary for a given Field.
 *
 * @author Arjun Mitra Reddy Donthala
 */
public class FieldBuilderJml extends FieldBuilder {
    /**
     * The FieldWriterJml instance
     */
    private FieldWriterJml w;

    /**
     * Construct a new FieldBuilder.
     *
     * @param configuration the current configuration of the doclet.
     * @param classDoc the class being documented.
     * @param writer the doclet specific writer.
     */
    protected FieldBuilderJml(Configuration configuration, ClassDoc classDoc,
            FieldWriter writer) {

        super(configuration);
        super.classDoc = classDoc;
        super.writer = writer;
        super.visibleMemberMap = new VisibleMemberMap(classDoc,
                VisibleMemberMap.FIELDS, configuration.nodeprecated);
        super.fields = new ArrayList<ProgramElementDoc>(
                super.visibleMemberMap.getLeafClassMembers(configuration));
        if (configuration.getMemberComparator() != null) {
            Collections.sort(super.fields, configuration.getMemberComparator());
        }
        w = (FieldWriterJml) writer;
    }

    /**
     * Handles the &lt;FieldCommentsJml> tag.
     *
     * @param elements the XML elements that specify how to document a class.
     */
    public void buildFieldCommentsJml(XMLNode node) {
        w.writeJmlSpecs((FieldDoc) fields.get(currentFieldIndex));
    }

    /**
     * Handles the &lt;GhostFieldJml> tag.
     *
     * @param elements the XML elements that specify how to document a class.
     */
    public void buildGhostFieldJml(XMLNode node) {
        w.writeJmlGhostModelFieldDetail(classDoc, JmlToken.GHOST, "Ghost");
    }
    
    /**
     * Handles the &lt;ModelFieldJml> tag.
     *
     * @param elements the XML elements that specify how to document a class.
     */
    public void buildModelFieldJml(XMLNode node) {
        w.writeJmlGhostModelFieldDetail(classDoc, JmlToken.MODEL, "Model");
    }

    /**
     * Handles the &lt;RepresentsDetailJml> tag.
     *
     * @param elements the XML elements that specify how to document a class.
     */
    public void buildRepresentsDetailJml(XMLNode node) {
        w.writeJmlRepresentsDetail(classDoc);
    }
}
