package org.jmlspecs.openjml.jmldoc.builders;

import com.sun.javadoc.ClassDoc;
import com.sun.tools.doclets.internal.toolkit.AnnotationTypeWriter;
import com.sun.tools.doclets.internal.toolkit.ClassWriter;
import com.sun.tools.doclets.internal.toolkit.Configuration;
import com.sun.tools.doclets.internal.toolkit.WriterFactory;
import com.sun.tools.doclets.internal.toolkit.builders.AbstractBuilder;
import com.sun.tools.doclets.internal.toolkit.builders.BuilderFactory;
import com.sun.tools.doclets.internal.toolkit.builders.ClassBuilder;
import com.sun.tools.doclets.internal.toolkit.builders.EnumConstantBuilder;
import com.sun.tools.doclets.internal.toolkit.builders.FieldBuilder;
import com.sun.tools.doclets.internal.toolkit.util.ClassTree;

/**
 * The factory for constructing builders.
 * @David R. Cok
 * @author Arjun Mitra Reddy Donthala
 */
public class BuilderFactoryJml extends BuilderFactory {
    
    /**
     * The current configuration of the doclet.
     */
    private Configuration configuration;

    /**
     * The factory to retrieve the required writers from.
     */
    private WriterFactory writerFactory;
    
    /**
     * The ClassDoc Object
     */
    private ClassDoc classDoc;
    
    /**
     * Construct a builder factory using the given configuration.
     * @param configuration the configuration for the current doclet
     * being executed.
     */
    public BuilderFactoryJml(Configuration configuration) {
        super(configuration);
        this.configuration = configuration;
        this.writerFactory = configuration.getWriterFactory();
    }
    
    /**
     * Return the builder for the class.
     *
     * @param classDoc the class being documented.
     * @param prevClass the previous class that was documented.
     * @param nextClass the next class being documented.
     * @param classTree the class tree.
     * @return the writer for the class.  Return null if this
     * writer is not supported by the doclet.
     */
    @Override
    public AbstractBuilder getClassBuilder(ClassDoc classDoc,
            ClassDoc prevClass, ClassDoc nextClass, ClassTree classTree) throws Exception {
        
        return new ClassBuilderJml(configuration, classDoc,
                writerFactory.getClassWriter(classDoc, prevClass, nextClass,
                    classTree));
    }
    
    /**
     * Return an instance of the method builder for the given class.
     *
     * @return an instance of the method builder for the given class.
     */
   @Override
    public AbstractBuilder getMethodBuilder(ClassWriter classWriter) throws Exception {
        return new MethodBuilderJml(configuration,
            classWriter.getClassDoc(),
            writerFactory.getMethodWriter(classWriter));
    }
   
   /**
    * Return an instance of the field builder for the given class.
    *
    * @return an instance of the field builder for the given class.
    */
    @Override
    public AbstractBuilder getFieldBuilder(ClassWriter classWriter) throws Exception {
        return new FieldBuilderJml(configuration, classWriter.getClassDoc(),
                writerFactory.getFieldWriter(classWriter));
    }
    
    /**
     * Return an instance of the constructor builder for the given class.
     *
     * @return an instance of the constructor builder for the given class.
     */
    @Override
    public AbstractBuilder getConstructorBuilder(ClassWriter classWriter) throws Exception {
        return new ConstructorBuilderJml(configuration,
            classWriter.getClassDoc(), writerFactory.getConstructorWriter(
            classWriter));
    }
    
    /**
     * Return an instance of the member summary builder for the given class.
     *
     * @return an instance of the member summary builder for the given class.
     */
    @Override
    public AbstractBuilder getMemberSummaryBuilder(ClassWriter classWriter) throws Exception {
        return new MemberSummaryBuilderJml(classWriter, configuration);
    }
    
    /**
     * Return an instance of the member summary builder for the given annotation
     * type.
     *
     * @return an instance of the member summary builder for the given
     *         annotation type.
     */
    @Override
    public AbstractBuilder getMemberSummaryBuilder(AnnotationTypeWriter annotationTypeWriter) throws Exception {
        return new MemberSummaryBuilderJml(annotationTypeWriter, configuration);
    }

}
