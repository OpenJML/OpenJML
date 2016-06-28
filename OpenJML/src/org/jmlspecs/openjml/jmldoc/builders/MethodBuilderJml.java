package org.jmlspecs.openjml.jmldoc.builders;

import java.util.ArrayList;
import java.util.Collections;

import org.jmlspecs.openjml.jmldoc.writers.MethodWriterJml;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.MethodDoc;
import com.sun.javadoc.ProgramElementDoc;
import com.sun.tools.doclets.internal.toolkit.Configuration;
import com.sun.tools.doclets.internal.toolkit.MethodWriter;
import com.sun.tools.doclets.internal.toolkit.builders.MethodBuilder;
import com.sun.tools.doclets.internal.toolkit.builders.XMLNode;
import com.sun.tools.doclets.internal.toolkit.util.VisibleMemberMap;

/**
 * Builds documentation for a Method.
 *
 * @author Arjun Mitra Reddy Donthala
 */
public class MethodBuilderJml extends MethodBuilder {

    private MethodWriterJml w;

    /**
     * Construct a new MethodBuilderJml and instantiates fields in parent class.
     *
     * @param configuration
     *            the current configuration of the doclet.
     * @param classDoc
     *            the class whoses members are being documented.
     * @param writer
     *            the doclet specific writer.
     */
    protected MethodBuilderJml(Configuration configuration, ClassDoc classDoc,
            MethodWriter writer) {

        super(configuration);
        super.classDoc = classDoc;
        super.writer = writer;
        super.visibleMemberMap = new VisibleMemberMap(classDoc,
                VisibleMemberMap.METHODS, configuration.nodeprecated);
        super.methods = new ArrayList<ProgramElementDoc>(
                super.visibleMemberMap.getLeafClassMembers(configuration));
        if (configuration.getMemberComparator() != null) {
            Collections.sort(super.methods,
                    configuration.getMemberComparator());
        }
        w = (MethodWriterJml) writer;

    }

    /**
     * Handles the &lt;MethodDocJml> tag.
     *
     * @param elements
     *            the XML elements that specify how to document a class.
     */
    public void buildMethodDocJml(XMLNode node) {
        w.writeJmlSpecs((MethodDoc) methods.get(currentMethodIndex));
    }

    /**
     * Handles the &lt;ModelMethodsJml> tag.
     *
     * @param elements
     *            the XML elements that specify how to document a class.
     */
    public void buildModelMethodsJml(XMLNode node) {
        w.writeJmlModelMethods(classDoc);
    }

}
