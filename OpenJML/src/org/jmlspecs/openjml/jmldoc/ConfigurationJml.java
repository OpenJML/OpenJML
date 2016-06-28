package org.jmlspecs.openjml.jmldoc;


import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.text.SimpleDateFormat;
import java.util.Date;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.jmldoc.builders.BuilderFactoryJml;
import org.jmlspecs.openjml.jmldoc.writers.WriterFactoryJml;

import com.sun.tools.doclets.formats.html.ConfigurationImpl;
import com.sun.tools.doclets.internal.toolkit.WriterFactory;
import org.jmlspecs.annotation.NonNull;
import com.sun.tools.doclets.internal.toolkit.builders.BuilderFactory;

/**
 * This class extends the ConfigurationImpl class that is part of the javadoc
 * tool; the extension is needed so that the configuration used by the doclet
 * contains the factory that writes JML information.
 * 
 * @author David R. Cok
 * @author Arjun Mitra Reddy Donthala
 */
public class ConfigurationJml extends ConfigurationImpl {
    
    static {
        // overwrites the instance created by ConfigurationImpl
        // instance should always be a ConfigurationJml object in jmldoc
        instance = new ConfigurationJml(); 
    }
    
    /** Returns the current singleton instance of the configuration object */
    static public ConfigurationJml getInstance() {
        return (ConfigurationJml)instance;
    }


   public ConfigurationJml() {
        builderXMLPath = "src/org/jmlspecs/openjml/jmldoc/resources/doclet.xml";
    }

    /*public InputStream getBuilderXML() throws FileNotFoundException {
        return builderXMLPath == null ?
            ConfigurationJml.class.getResourceAsStream("src/org/jmlspecs/openjml/jmldoc/resources/doclet.xml") :
            new FileInputStream(new File(builderXMLPath));
    }*/


    /** This method overrides the parent class to return a JML-specific writer
     * factory
     * @return a JML-specific factory that produces JML-aware writers
     */
    @NonNull @Override
    public WriterFactory getWriterFactory() {
        return new WriterFactoryJml(this);
    }
    
    
    @NonNull @Override
    public BuilderFactory getBuilderFactory() {
        return new BuilderFactoryJml(this);
    }

    /**
     * Return the build date for the doclet.
     * @return an identification string with the build date
     */
    @NonNull
    public String getDocletSpecificBuildDate() {
        String s = new SimpleDateFormat("yyyymmdd").format(new Date());
        if (notimestamp) s = "DATE-VERSION";
        return "OpenJMLDoc: " + s;
    }

}
