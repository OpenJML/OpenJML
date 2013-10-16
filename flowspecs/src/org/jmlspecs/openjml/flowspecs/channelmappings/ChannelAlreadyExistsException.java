package org.jmlspecs.openjml.flowspecs.channelmappings;

/**
 * Exception that is thrown when a parsed Channel Mappings XML file contains
 * more than one instance of a particular ChannelName. This could happen if,
 * say, a ChannelName DISPLAY was specified twice.
 * 
 * @author Toby Tobkin
 *
 */
public class ChannelAlreadyExistsException extends Exception {
    
    private final ChannelName duplicateChannelName;

    public ChannelAlreadyExistsException(ChannelName key) {
        this.duplicateChannelName = key;
    }

    /**Gets the ChannelName that is a duplicate of one already added to the key-value mapping
     * 
     * @return the duplicateChannelName
     */
    public ChannelName getDuplicateChannelName() {
        return duplicateChannelName;
    }
    
}
