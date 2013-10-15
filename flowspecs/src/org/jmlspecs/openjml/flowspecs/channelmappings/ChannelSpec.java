/**
 * 
 */
package org.jmlspecs.openjml.flowspecs.channelmappings;

import java.util.Set;

import org.jmlspecs.openjml.flowspecs.Lattice;
import org.jmlspecs.openjml.flowspecs.SecurityType;

/**What an individual ChannelName maps to. Contains two security levels: an input and an output. A ChannelMappings consists of 0 or 
 * more ChannelNames, each mapped to 1 of 0 or more ChannelSpecs.
 * 
 * @see ChannelName
 * @author Toby Tobkin
 *
 */
public class ChannelSpec {
    private final String inputLevel, outputLevel;
    
    /**Constructs a new ChannelSpec with the levels specified as paramaters and 
     * ensures that the levels are valid against the provided security lattice.
     * 
     * @param inputLevel The name of the security level corresponding to this ChannelSpec's input
     * @param outputLevel The name of the security level corresponding to this ChannelSpec's output
     * @param securityLattice The security lattice used in this channel mapping session
     */
    public ChannelSpec(String inputLevel, String outputLevel, Lattice securityLattice) throws LevelDoesNotExistException{
        assert inputLevel != null && outputLevel != null && securityLattice != null;
        
        boolean inputLevelExists = false, outputLevelExists = false;
        
        Set<SecurityType> securityTypes = securityLattice.getVertexes();
        for(SecurityType st : securityTypes){
            if(st.toString().compareToIgnoreCase(inputLevel) == 0)
                inputLevelExists = true; 
            if(st.toString().compareToIgnoreCase(outputLevel) == 0)
                outputLevelExists = true;
        }
        
        /*TODO: make it so that error reporting is useful. That is, make it
         * so that all invalid levels and their corresponding line numbers
         * in the XML document are reported. Right now, it only gives the 
         * first occurrence of a bad level which is dumb.
         */
        if(!inputLevelExists)
            throw new LevelDoesNotExistException(inputLevel);
        if(!outputLevelExists)
            throw new LevelDoesNotExistException(outputLevel);
        
        this.inputLevel = inputLevel;
        this.outputLevel = outputLevel;
    }

    public String getInputLevel() {
        return inputLevel;
    }

    public String getOutputLevel() {
        return outputLevel;
    }

}
