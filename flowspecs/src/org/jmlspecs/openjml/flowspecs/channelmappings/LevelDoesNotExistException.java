/**
 * 
 */
package org.jmlspecs.openjml.flowspecs.channelmappings;

import java.io.ObjectInputStream.GetField;

/**Thrown when a level is referenced that does not exist in the
 * security lattice XML file.
 * 
 * @author Toby Tobkin
 *
 */
public class LevelDoesNotExistException extends Exception {
    
    private final String invalidLevel;
    
    public LevelDoesNotExistException(String invalidLevel){
        assert invalidLevel != null;
        this.invalidLevel = invalidLevel;
    }
    
    @Override
    public String getMessage() {
        return ("Invalid level specified in Channel Mappings XML file: " + invalidLevel);
    }
}
