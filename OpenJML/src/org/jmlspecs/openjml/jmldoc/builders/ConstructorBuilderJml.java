package org.jmlspecs.openjml.jmldoc.builders;

import java.util.ArrayList;
import java.util.Collections;

import org.jmlspecs.openjml.jmldoc.writers.ConstructorWriterJml;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.ConstructorDoc;
import com.sun.javadoc.ProgramElementDoc;
import com.sun.tools.doclets.internal.toolkit.Configuration;
import com.sun.tools.doclets.internal.toolkit.ConstructorWriter;
import com.sun.tools.doclets.internal.toolkit.builders.ConstructorBuilder;
import com.sun.tools.doclets.internal.toolkit.builders.XMLNode;
import com.sun.tools.doclets.internal.toolkit.util.VisibleMemberMap;

/**
 * Builds the summary for a given constructor.
 *
 * @author Arjun Mitra Reddy Donthala
 */
public class ConstructorBuilderJml extends ConstructorBuilder {

    /**
     * The ConstructorWriterJml instance
     */
    private ConstructorWriterJml w;

    
    /**
     * Construct a new ConstructorBuilder.
     *
     * @param configuration the current configuration of the doclet.
     * @param classDoc the class being documented.
     * @param writer the doclet specific writer.
     */
    protected ConstructorBuilderJml(Configuration configuration,
            ClassDoc classDoc, ConstructorWriter writer) {

        super(configuration);
        super.classDoc = classDoc;
        super.writer = writer;
        super.visibleMemberMap = new VisibleMemberMap(classDoc,
                VisibleMemberMap.CONSTRUCTORS, configuration.nodeprecated);
        super.constructors = new ArrayList<ProgramElementDoc>(
                super.visibleMemberMap.getMembersFor(classDoc));
        for (int i = 0; i < super.constructors.size(); i++) {
            if (super.constructors.get(i).isProtected()
                    || super.constructors.get(i).isPrivate()) {
                writer.setFoundNonPubConstructor(true);
            }
        }
        if (configuration.getMemberComparator() != null) {
            Collections.sort(super.constructors,
                    configuration.getMemberComparator());
        }
        w = (ConstructorWriterJml) writer;
    }

    /**
     * Handles the &lt;ConstructorDocJml> tag.
     *
     * @param elements the XML elements that specify how to document a class.
     */
    public void buildConstructorDocJml(XMLNode node) {
        w.writeJmlSpecs((ConstructorDoc) constructors.get(currentConstructorIndex));
    }

    /**
     * Handles the &lt;ModelConstructorJml> tag.
     *
     * @param elements the XML elements that specify how to document a class.
     */
    public void buildModelConstructorJml(XMLNode node) {
        w.writeJmlModelConstructors(classDoc);
    }

}
