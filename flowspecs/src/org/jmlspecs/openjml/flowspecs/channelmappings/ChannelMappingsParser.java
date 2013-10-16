package org.jmlspecs.openjml.flowspecs.channelmappings;

import java.io.File;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;
import javax.xml.validation.SchemaFactory;

import org.dom4j.Document;
import org.dom4j.DocumentException;
import org.dom4j.io.SAXReader;
import org.jmlspecs.openjml.flowspecs.Lattice;
import org.jmlspecs.openjml.flowspecs.SecurityType;
import org.xml.sax.SAXException;

public class ChannelMappingsParser {
    
    /**The XML file specifying the mappings from a Channel to a Level*/
    private File channelMappingsFile;
    /**The schema describing the channel mappings XML file*/
    private File channelMappingsXSDFile;
    
    private Lattice<SecurityType> securityLattice;
    private boolean useSchemaValidation;

    /**Constructs a new ChannelMappingsParser and sets it to use XSD validation.
     * @param channelMappingsFile The XML file specifying the mappings of Channels
     *  to Levels that will be parsed*/
    public ChannelMappingsParser(File channelMappingsFile, File channelMappingsXSDFile, Lattice<SecurityType> securityLattice) {
        this.channelMappingsFile = channelMappingsFile;
        this.channelMappingsFile = channelMappingsFile;
        this.securityLattice = securityLattice;
        this.useSchemaValidation = true;
    }
    
    /**Constructs a new ChannelMappingsParser and sets it to not use XSD validation. To use
     * schema validation, construct a ChannelMappingParser using the overloaded constructor
     * that allows for specification of an XSD file.
     * @param channelMappingsFile The XML file specifying the mappings of Channels
     *  to Levels that will be parsed*/
    public ChannelMappingsParser(File channelMappingsFile, Lattice<SecurityType> securityLattice) {
        this.channelMappingsFile = channelMappingsFile;
        this.securityLattice = securityLattice;
        this.useSchemaValidation = false;
    }
    

    /**
     * Parses the Channel Mappings XML file specified at construction and
     * returns a ChannelMappings object that can be used to see what channels
     * map to what security levels. For parsing validation, uses the XSD file
     * specified internally in the Channel Mappings XML source file.
     * @return ChannelMappings object that can be used for accessing ChannelMappings
     * @throws LevelDoesNotExistException 
     */
    public ChannelMappings parse() throws LevelDoesNotExistException {
        //Create our factory
        SAXParserFactory factory = SAXParserFactory.newInstance();
        
        if (useSchemaValidation) {
            //Setup our parsing to use the specified XSD file
            SchemaFactory schemaFactory = SchemaFactory
                    .newInstance("http://www.w3.org/2001/XMLSchema");
            try {
                factory.setSchema(schemaFactory
                        .newSchema(channelMappingsXSDFile));
            } catch (SAXException e1) {
                // TODO Auto-generated catch block
                e1.printStackTrace();
            }
        }
        
        //Create and configure our parser
        SAXParser parser = null;
        try {
            parser = factory.newSAXParser();
        } catch (ParserConfigurationException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (SAXException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } finally {
            assert parser != null; //Our exception handling must make sure that we don't silently pass a null pointer anywhere
        }
        
        //Create and configure our reader
        SAXReader reader = null;
        try {
            reader = new SAXReader(parser.getXMLReader());
            reader.setValidation(false);
            reader.setErrorHandler(new ChannelMappingsErrorHandler());
        } catch (SAXException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } finally {
            assert reader != null;
        }
        
        //Read our Channel Mappings file
        Document channelMappingsDocument = null;
        try {
            channelMappingsDocument = reader.read(channelMappingsFile);
        } catch (DocumentException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } finally {
            assert channelMappingsDocument != null;
        }
        
        //create a ChannelMappings data structure that can be manipulated by someone else
        ChannelMappings channelMappings = null;
        try {
            channelMappings = new ChannelMappings(channelMappingsDocument, securityLattice);
        } catch (ChannelAlreadyExistsException e) {
         // TODO Auto-generated catch block
            e.printStackTrace();
        } finally {
            assert channelMappings != null;
        }
        
        return channelMappings;
    }
}
