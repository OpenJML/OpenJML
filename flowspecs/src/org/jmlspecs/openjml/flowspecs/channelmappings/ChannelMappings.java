package org.jmlspecs.openjml.flowspecs.channelmappings;

import java.util.HashMap;
import java.util.Iterator;

import org.dom4j.Document;
import org.dom4j.Element;
import org.jmlspecs.openjml.flowspecs.Lattice;
import org.jmlspecs.openjml.flowspecs.SecurityType;

/**
 * A {@link java.util.HashMap} extended to do checks for semantic correctness in the ChannelMappings
 * XML file. Typically constructed using the ChannelMappingsParser class.
 * 
 * @author Toby Tobkin
 *
 */
public class ChannelMappings extends HashMap<ChannelName, ChannelSpec>  {
    
    private final Document channelMappingsDocument;
    private final Lattice<SecurityType> securityLattice;

    /**
     * Constructs a new ChannelMappings object that can be used to easily access
     * ChannelName-SecurityLevel key-value pairs. Uses a specified ChannelMappings
     * XML document parameter to construct itself.
     * 
     * @param channelMappingsDocument The Document that contains the ChannelMappings specifications
     * @param securityLattice The security lattice containing the levels of the policy
     * @throws ChannelAlreadyExistsException
     * @throws LevelDoesNotExistException 
     */
    public ChannelMappings(Document channelMappingsDocument, Lattice<SecurityType> securityLattice) throws ChannelAlreadyExistsException, LevelDoesNotExistException {
        super();
        this.channelMappingsDocument = channelMappingsDocument;
        this.securityLattice = securityLattice;
        createMappingsFromDocument();
    }
       
/**Using the document given to the constructor, populates this ChannelMappings
    * object with the appropriate key-value pairs.
    * 
    * @throws ChannelAlreadyExistsException
    * @throws LevelDoesNotExistException
    */
   private void createMappingsFromDocument() throws ChannelAlreadyExistsException, LevelDoesNotExistException {
       Element channelsRoot = channelMappingsDocument.getRootElement();
       Element curChannel = null;
       String keyString, inputLevel, outputLevel;
       ChannelSpec value = null;
       ChannelName key = null;
           for(Iterator i1 = channelsRoot.elementIterator("Channel"); i1.hasNext();){
               curChannel = (Element) i1.next();
               
               //get our key
               keyString = curChannel.elementText("ChannelName");
               
               //get our value
               inputLevel = curChannel.element("ChannelSpec").elementText("InputLevel").toUpperCase();
               outputLevel = curChannel.element("ChannelSpec").elementText("OutputLevel").toUpperCase();
               
               //create the key-value pair
               key = new ChannelName(keyString);
               value = new ChannelSpec(inputLevel, outputLevel, securityLattice);
               
               //Ensure that this ChannelName isn't already a key
               if(this.containsKey(key))
                   throw new ChannelAlreadyExistsException(key);
               
               //insert the pair
               this.put(key, value);
           }
    }
}
