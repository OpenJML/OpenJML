package org.jmlspecs.openjml.jmldoc;


import com.sun.javadoc.AnnotationTypeDoc;
import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.PackageDoc;
import com.sun.javadoc.Type;
import com.sun.tools.doclets.formats.html.*;
import com.sun.tools.doclets.internal.toolkit.*;
import com.sun.tools.doclets.internal.toolkit.util.ClassTree;
import com.sun.tools.doclets.internal.toolkit.util.VisibleMemberMap;

// MAINTENANCE: This replicates the code in
// com.sun.tools.doclets.formats.html.WriterFactoryImpl
// even though much of it is unchanged. We would like to extend that class, but
// it is not written in an extensible way.

/**
 * This class extends WriterFactoryImpl in order to override factory methods so that
 * they create JML-enabled writer, that then write HTML content that includes
 * JML information.
 */
public class WriterFactoryJml extends WriterFactoryImpl
//public class WriterFactoryJml implements WriterFactory
{
//    /** A lazily-initialized singleton instance of the factory */
//    private static WriterFactoryJml instance;

    /** A cached value of the Configuration object */
    private ConfigurationJml configuration;

    /** Constructs a new factory object 
     * 
     * @param configuration the configuration object to use
     */
    public WriterFactoryJml(ConfigurationJml configuration) {
        super(configuration);
        this.configuration = configuration;
    }

//    /**
//     * Return an instance of this factory.
//     *
//     * @return an instance of this factory.
//     */
//    public static WriterFactoryJml getInstance() {
//        if (instance == null) {
//            instance = new WriterFactoryJml(ConfigurationJml.getInstance());
//        }
//        return instance;
//    }

//    // FIXME - any JML information about constants to write?
//    /**
//     * {@inheritDoc}
//     */ // Unchanged
//    public ConstantsSummaryWriter getConstantsSummaryWriter() throws Exception {
//        return new ConstantsSummaryWriterImpl(configuration);
//    }

//    // FIXME - any JML information about packages to write?
//    /**
//     * {@inheritDoc}
//     */ // Unchanged
//    public PackageSummaryWriter getPackageSummaryWriter(PackageDoc packageDoc,
//        PackageDoc prevPkg, PackageDoc nextPkg) throws Exception {
//        return new PackageWriterImpl(ConfigurationImpl.getInstance(), packageDoc,
//            prevPkg, nextPkg);
//    }

    /**
     * {@inheritDoc}
     */
    // Overridden to return a JML ClassWriter
    public ClassWriter getClassWriter(ClassDoc classDoc, ClassDoc prevClass,
            ClassDoc nextClass, ClassTree classTree)
            throws Exception {
        return new ClassWriterJml(classDoc, prevClass, nextClass, classTree);
    }

//    // FIXME - any JML information about annotation types ?
//    /**
//     * {@inheritDoc}
//     */ // Unchanged
//    public AnnotationTypeWriter getAnnotationTypeWriter(
//        AnnotationTypeDoc annotationType, Type prevType, Type nextType)
//    throws Exception {
//        return new AnnotationTypeWriterImpl(annotationType, prevType, nextType);
//    }
//
//    // FIXME - any JML information about annotation types to write?
//    /**
//     * {@inheritDoc}
//     */ // Unchanged
//    public AnnotationTypeOptionalMemberWriter
//            getAnnotationTypeOptionalMemberWriter(
//        AnnotationTypeWriter annotationTypeWriter) throws Exception {
//        return new AnnotationTypeOptionalMemberWriterImpl(
//            (SubWriterHolderWriter) annotationTypeWriter,
//            annotationTypeWriter.getAnnotationTypeDoc());
//    }
//
//    // FIXME - any JML information about annotation types to write?
//    /**
//     * {@inheritDoc}
//     */ // Unchanged
//    public AnnotationTypeRequiredMemberWriter
//            getAnnotationTypeRequiredMemberWriter(AnnotationTypeWriter annotationTypeWriter) throws Exception {
//        return new AnnotationTypeRequiredMemberWriterImpl(
//            (SubWriterHolderWriter) annotationTypeWriter,
//            annotationTypeWriter.getAnnotationTypeDoc());
//    }

//    // FIXME - any JML information about enums to write?
//    /**
//     * {@inheritDoc}
//     */ // Unchanged
//    public EnumConstantWriter getEnumConstantWriter(ClassWriter classWriter)
//            throws Exception {
//        return new EnumConstantWriterImpl((SubWriterHolderWriter) classWriter,
//            classWriter.getClassDoc());
//    }

    /**
     * {@inheritDoc}
     */
    // Overridden to return a JML FieldWriter
    public FieldWriter getFieldWriter(ClassWriter classWriter)
            throws Exception {
        return new FieldWriterJml((SubWriterHolderWriter) classWriter,
            classWriter.getClassDoc());
    }

    /**
     * {@inheritDoc}
     */
    // Overridden to return a JML MethodWriter
    public  MethodWriter getMethodWriter(ClassWriter classWriter)
            throws Exception {
        return new MethodWriterJml((SubWriterHolderWriter) classWriter,
            classWriter.getClassDoc());
    }

    /**
     * {@inheritDoc}
     */
    // Overridden to return a JML ConstructorWriter
    public ConstructorWriter getConstructorWriter(ClassWriter classWriter)
            throws Exception {
        return new ConstructorWriterJml((SubWriterHolderWriter) classWriter,
            classWriter.getClassDoc());
    }

    /**
     * {@inheritDoc}
     */
    // Overridden to generate jmldoc for nested classes
    public MemberSummaryWriter getMemberSummaryWriter(
        ClassWriter classWriter, int memberType)
    throws Exception {
        switch (memberType) {
            case VisibleMemberMap.CONSTRUCTORS:
                return (ConstructorWriterImpl) getConstructorWriter(classWriter);
            case VisibleMemberMap.ENUM_CONSTANTS:
                return (EnumConstantWriterImpl) getEnumConstantWriter(classWriter);
            case VisibleMemberMap.FIELDS:
                return (FieldWriterImpl) getFieldWriter(classWriter);
            case VisibleMemberMap.INNERCLASSES:
                return new NestedClassWriterJml((SubWriterHolderWriter)
                    classWriter, classWriter.getClassDoc());
            case VisibleMemberMap.METHODS:
                return (MethodWriterImpl) getMethodWriter(classWriter);
            default:
                return null;
        }
    }

//    /**
//     * {@inheritDoc}
//     */ // Unchanged
//    public MemberSummaryWriter getMemberSummaryWriter(
//        AnnotationTypeWriter annotationTypeWriter, int memberType)
//    throws Exception {
//        switch (memberType) {
//            case VisibleMemberMap.ANNOTATION_TYPE_MEMBER_OPTIONAL:
//                return (AnnotationTypeOptionalMemberWriterImpl)
//                    getAnnotationTypeOptionalMemberWriter(annotationTypeWriter);
//            case VisibleMemberMap.ANNOTATION_TYPE_MEMBER_REQUIRED:
//                return (AnnotationTypeRequiredMemberWriterImpl)
//                    getAnnotationTypeRequiredMemberWriter(annotationTypeWriter);
//            default:
//                return null;
//        }
//    }
//
//    /**
//     * {@inheritDoc}
//     */ // Unchanged
//    public SerializedFormWriter getSerializedFormWriter() throws Exception {
//        return new SerializedFormWriterImpl();
//    }

}
