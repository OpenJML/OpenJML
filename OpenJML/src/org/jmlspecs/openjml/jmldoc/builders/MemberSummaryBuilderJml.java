package org.jmlspecs.openjml.jmldoc.builders;

import java.util.Iterator;
import java.util.List;

import org.jmlspecs.openjml.jmldoc.writers.ConstructorWriterJml;
import org.jmlspecs.openjml.jmldoc.writers.FieldWriterJml;
import org.jmlspecs.openjml.jmldoc.writers.MethodWriterJml;
import org.jmlspecs.openjml.jmldoc.writers.NestedClassWriterJml;

import com.sun.javadoc.ClassDoc;
import com.sun.tools.doclets.internal.toolkit.AnnotationTypeWriter;
import com.sun.tools.doclets.internal.toolkit.ClassWriter;
import com.sun.tools.doclets.internal.toolkit.Configuration;
import com.sun.tools.doclets.internal.toolkit.MemberSummaryWriter;
import com.sun.tools.doclets.internal.toolkit.builders.MemberSummaryBuilder;
import com.sun.tools.doclets.internal.toolkit.builders.XMLNode;
import com.sun.tools.doclets.internal.toolkit.util.Util;
import com.sun.tools.doclets.internal.toolkit.util.VisibleMemberMap;

/**
 * Builds the summary for a given class.
 *
 * @author Arjun Mitra Reddy Donthala
 */
public class MemberSummaryBuilderJml extends MemberSummaryBuilder {

    /**
     * The current configuration of the doclet.
     */
    Configuration configuration;

    /**
     * The ClassWriterJml instance
     */
    ClassWriter   classWriter;

    /**
     * Construct a new MemberSummaryBuilder.
     *
     * @param classWriter   the writer for the class whose members are being
     *                      summarized.
     * @param configuration the current configuration of the doclet.
     */
    public MemberSummaryBuilderJml(ClassWriter classWriter,
            Configuration configuration) throws Exception {
        super(configuration);
        super.classDoc = classWriter.getClassDoc();
        super.init(classWriter);
        this.configuration = configuration;
        this.classWriter = classWriter;
    }

    /**
     * Construct a new MemberSummaryBuilder.
     *
     * @param annotationTypeWriter the writer for the class whose members are
     *                             being summarized.
     * @param configuration the current configuration of the doclet.
     */
    public MemberSummaryBuilderJml(AnnotationTypeWriter annotationTypeWriter,
            Configuration configuration) throws Exception {
        super(configuration);
        super.classDoc = annotationTypeWriter.getAnnotationTypeDoc();
        super.init(annotationTypeWriter);
    }

    /**
     * Handles the &lt;FieldsSummaryJml> tag.
     *
     * @param elements the XML elements that specify how to document a class.
     */
    public void buildFieldsSummaryJml(XMLNode node) throws Exception {
        MemberSummaryWriter w = memberSummaryWriters[VisibleMemberMap.FIELDS];
        if (w == null) w = (MemberSummaryWriter) configuration
                .getWriterFactory().getFieldWriter(classWriter);
        ((FieldWriterJml) w).checkJmlSummary(classDoc);
    }

    /**
     * Handles the &lt;FieldsInheritedSummaryJml> tag.
     *
     * @param elements the XML elements that specify how to document a class.
     */
    public void buildFieldsInheritedSummaryJml(XMLNode node) throws Exception {
        MemberSummaryWriter w = memberSummaryWriters[VisibleMemberMap.FIELDS];
        if (w == null) w = (MemberSummaryWriter) configuration
                .getWriterFactory().getFieldWriter(classWriter);
        VisibleMemberMap visibleMemberMap = visibleMemberMaps[VisibleMemberMap.FIELDS];
        for (Iterator<?> iter = visibleMemberMap.getVisibleClassesList()
                .iterator(); iter.hasNext();) {
            ClassDoc inhclass = (ClassDoc) (iter.next());
            if (!(inhclass.isPublic()
                    || Util.isLinkable(inhclass, configuration))) {
                continue;
            }
            if (inhclass == classDoc) {
                continue;
            }
            List<?> inhmembers = visibleMemberMap.getMembersFor(inhclass);
            ((FieldWriterJml) w).checkJmlInheritedSummary(classDoc, inhmembers);
        }
    }

    /**
     * Handles the &lt;NestedClassesSummaryJml> tag.
     *
     * @param elements the XML elements that specify how to document a class.
     */
    public void buildNestedClassesSummaryJml(XMLNode node) throws Exception {
        MemberSummaryWriter w = memberSummaryWriters[VisibleMemberMap.INNERCLASSES];
        if (w == null)
            w = configuration.getWriterFactory().getMemberSummaryWriter(
                    classWriter, VisibleMemberMap.INNERCLASSES);
        ((NestedClassWriterJml) w).writeJmlNestedClassSummary(classDoc);
    }
    
    /**
     * Handles the &lt;NestedClassesInheritedSummaryJml> tag.
     *
     * @param elements the XML elements that specify how to document a class.
     */
    public void buildNestedClassesInheritedSummaryJml(XMLNode node)
            throws Exception {
        MemberSummaryWriter w = memberSummaryWriters[VisibleMemberMap.INNERCLASSES];
        if (w == null)
            w = configuration.getWriterFactory().getMemberSummaryWriter(
                    classWriter, VisibleMemberMap.INNERCLASSES);
        ((NestedClassWriterJml) w)
                .writeJmlInheritedNestedClassSummaryFooter(classDoc);
    }

    /**
     * Handles the &lt;MethodsSummaryJml> tag.
     *
     * @param elements the XML elements that specify how to document a class.
     */
    public void buildMethodsSummaryJml(XMLNode node) throws Exception {
        MemberSummaryWriter w = memberSummaryWriters[VisibleMemberMap.METHODS];
        if (w == null) w = (MemberSummaryWriter) configuration
                .getWriterFactory().getMethodWriter(classWriter);
        ((MethodWriterJml) w).writeJmlMethodSummary(classDoc);
    }

    /**
     * Handles the &lt;MethodsInheritedSummaryJml> tag.
     *
     * @param elements the XML elements that specify how to document a class.
     */
    public void buildMethodsInheritedSummaryJml(XMLNode node) throws Exception {
        MemberSummaryWriter w = memberSummaryWriters[VisibleMemberMap.METHODS];
        if (w == null) w = (MemberSummaryWriter) configuration
                .getWriterFactory().getMethodWriter(classWriter);
        ((MethodWriterJml) w).writeJmlInheritedMemberSummaryFooter(classDoc);
    }

    /**
     * Handles the &lt;ConstructorSummaryJml> tag.
     *
     * @param elements the XML elements that specify how to document a class.
     */
    public void buildConstructorSummaryJml(XMLNode node) throws Exception {
        MemberSummaryWriter w = memberSummaryWriters[VisibleMemberMap.CONSTRUCTORS];
        if (w == null) w = (MemberSummaryWriter) configuration
                .getWriterFactory().getConstructorWriter(classWriter);
        ((ConstructorWriterJml) w).writeJmlConstructorSummary(classDoc);
    }

}
