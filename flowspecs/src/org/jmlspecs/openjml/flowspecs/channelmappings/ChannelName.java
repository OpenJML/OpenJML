/**
 * 
 */
package org.jmlspecs.openjml.flowspecs.channelmappings;


/**Class for holding and operating on Channel Names. Used primarily
 * for readability and sanity in code.
 * 
 * @author Toby Tobkin
 *
 */
public class ChannelName {
    private final String channelName;
    
    public ChannelName(String channelName){
        this.channelName = channelName;
    }
    
    public String getChannelName() { 
        return this.channelName; 
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result
                + ((channelName == null) ? 0 : channelName.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        ChannelName other = (ChannelName) obj;
        if (channelName == null) {
            if (other.channelName != null) return false;
        } else if (!channelName.equals(other.channelName)) return false;
        return true;
    }
}
