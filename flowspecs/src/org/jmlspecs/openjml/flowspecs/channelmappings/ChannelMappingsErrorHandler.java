/**
 * 
 */
package org.jmlspecs.openjml.flowspecs.channelmappings;

import org.xml.sax.ErrorHandler;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

/**
 * Class for reporting any errors during the parsing of the XML Channel
 * Mappings file.
 * 
 * @author Toby Tobkin
 *
 */
public class ChannelMappingsErrorHandler implements ErrorHandler {

    /* (non-Javadoc)
     * @see org.xml.sax.ErrorHandler#error(org.xml.sax.SAXParseException)
     */
    @Override
    public void error(SAXParseException arg0) throws SAXException {
        // TODO Auto-generated method stub

    }

    /* (non-Javadoc)
     * @see org.xml.sax.ErrorHandler#fatalError(org.xml.sax.SAXParseException)
     */
    @Override
    public void fatalError(SAXParseException arg0) throws SAXException {
        // TODO Auto-generated method stub

    }

    /* (non-Javadoc)
     * @see org.xml.sax.ErrorHandler#warning(org.xml.sax.SAXParseException)
     */
    @Override
    public void warning(SAXParseException arg0) throws SAXException {
        // TODO Auto-generated method stub

    }

}
