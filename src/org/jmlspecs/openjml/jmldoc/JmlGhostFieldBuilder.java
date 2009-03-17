package org.jmlspecs.openjml.jmldoc;

import java.util.ArrayList;
import java.util.Collections;

import com.sun.javadoc.ClassDoc;
import com.sun.tools.doclets.internal.toolkit.Configuration;
import com.sun.tools.doclets.internal.toolkit.FieldWriter;
import com.sun.tools.doclets.internal.toolkit.builders.FieldBuilder;
import com.sun.tools.doclets.internal.toolkit.util.VisibleMemberMap;

public class JmlGhostFieldBuilder extends FieldBuilder {

    /**
     * Construct a new FieldBuilder.
     *
     * @param configuration the current configuration of the doclet.
     * @param classDoc the class whoses members are being documented.
     * @param writer the doclet specific writer.
     */
    public static JmlGhostFieldBuilder getInstance(
            Configuration configuration,
            ClassDoc classDoc,
            FieldWriter writer) {
        JmlGhostFieldBuilder builder = new JmlGhostFieldBuilder(configuration);
        if (configuration.getMemberComparator() != null) {
            Collections.sort(
                    builder.fields,
                    configuration.getMemberComparator());
        }
        return builder;
    }

    /**
     * Construct a new FieldBuilder.
     *
     * @param configuration the current configuration of the
     *                      doclet.
     */
    protected JmlGhostFieldBuilder(Configuration configuration) { // DRC - changed from private to protected
            super(configuration);
    }

    /**
     * Build the overall header.
     */
    public void buildHeader() {
            writer.writeHeader(
                    classDoc,
                    "JML Ghost Fields");  // FIXME - do we want to use properties?
                    //configuration.getText("doclet.Field_Detail"));
    }
    
}
