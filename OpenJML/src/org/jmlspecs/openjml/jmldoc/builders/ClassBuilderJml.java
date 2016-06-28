package org.jmlspecs.openjml.jmldoc.builders;

import java.util.HashSet;

import org.jmlspecs.openjml.jmldoc.writers.ClassWriterJml;

import com.sun.javadoc.ClassDoc;
import com.sun.tools.doclets.internal.toolkit.ClassWriter;
import com.sun.tools.doclets.internal.toolkit.Configuration;
import com.sun.tools.doclets.internal.toolkit.builders.ClassBuilder;
import com.sun.tools.doclets.internal.toolkit.builders.XMLNode;
import com.sun.tools.doclets.internal.toolkit.util.Util;

/**
 * Builds the summary for a given class.
 *
 * @author Arjun Mitra Reddy Donthala
 */
public class ClassBuilderJml extends ClassBuilder {

    /**
     * The ClassWriterJml instance
     */
    ClassWriterJml w;

    /**
     * Construct a new ClassBuilder.
     *
     * @param configuration the current configuration of the doclet.
     * @param classDoc the class being documented.
     * @param writer the doclet specific writer.
     */
    public ClassBuilderJml(Configuration configuration, ClassDoc classDoc,
            ClassWriter writer) {
        super(configuration);
        super.classDoc = classDoc;
        super.writer = writer;
        if (classDoc.isInterface()) {
            super.isInterface = true;
        } else if (classDoc.isEnum()) {
            super.isEnum = true;
            Util.setEnumDocumentation(configuration, classDoc);
        }
        if (containingPackagesSeen == null) {
            containingPackagesSeen = new HashSet<String>();
        }
        w = (ClassWriterJml) writer;
    }

    /**
     * Handles the &lt;ClassDocJml> tag.
     *
     * @param elements the XML elements that specify how to document a class.
     */
    public void buildClassDocJml(XMLNode node) throws Exception {
        w.writeClassSpecs();
    }

    /**
     * Handles the &lt;ClassHeaderJml> tag.
     *
     * @param elements the XML elements that specify how to document a class.
     */
    public void buildClassHeaderJml(XMLNode node) {
        w.printHtmlJmlHeader();
    }

}
