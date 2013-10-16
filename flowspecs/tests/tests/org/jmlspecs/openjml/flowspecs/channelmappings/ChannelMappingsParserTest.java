/**
 * 
 */
package tests.org.jmlspecs.openjml.flowspecs.channelmappings;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.net.URL;
import java.util.LinkedList;

import org.jmlspecs.openjml.flowspecs.AdjacencyMatrix;
import org.jmlspecs.openjml.flowspecs.Lattice;
import org.jmlspecs.openjml.flowspecs.SecurityType;
import org.jmlspecs.openjml.flowspecs.channelmappings.ChannelMappings;
import org.jmlspecs.openjml.flowspecs.channelmappings.ChannelMappingsParser;
import org.jmlspecs.openjml.flowspecs.channelmappings.ChannelName;
import org.jmlspecs.openjml.flowspecs.channelmappings.ChannelSpec;
import org.jmlspecs.openjml.flowspecs.channelmappings.LevelDoesNotExistException;
import org.junit.Before;
import org.junit.Test;

/**
 * @author <a href="mailto:toby.tobkin@gmail.com">Toby Tobkin</a>
 *
 */
public class ChannelMappingsParserTest {
    
    private static Lattice<SecurityType> securityLattice;
    
    @Before
    public void setupSecurityLattice(){        
        //Create a lattice
        LinkedList<SecurityType> levels = new LinkedList<SecurityType>();
        levels.add(new SecurityType("private"));
        levels.add(new SecurityType("public"));
        
        AdjacencyMatrix<SecurityType> backingMatrix = new AdjacencyMatrix<SecurityType>(levels);
        
        securityLattice = new Lattice<SecurityType>(backingMatrix);
    }

    /**
     * Test method for {@link org.jmlspecs.openjml.flowspecs.channelmappings.ChannelMappingsParser#parse()}.
     */
    @Test
    public void Parse_ValidChannelMappingsFileGivenWithoutSchema_ProperChannelMappingsObjectReturned(){
        ChannelMappings resultantMappings = null; //the parser will give this to us
        URL inputFileUrl = getClass().getResource("ChannelMappingsFileTest-ShortWell-Formed.xml");
        File channelMappingsFile = new File(inputFileUrl.getFile());
        
        if(!channelMappingsFile.exists())
            fail();
        
        ChannelMappingsParser p = new ChannelMappingsParser(channelMappingsFile, securityLattice);
        try {
            resultantMappings = p.parse();
        } catch (LevelDoesNotExistException e) {
            fail("LevelDoesNotExistException should not have been thrown.");
        }
        
        ChannelName display = new ChannelName("DISPLAY"),
                microphone = new ChannelName("MICROPHONE"),
                network = new ChannelName("NETWORK");
        
        ChannelSpec value;
        
        value = resultantMappings.get(display);
        assertTrue(value.getInputLevel().equals("PUBLIC"));
        assertTrue(value.getOutputLevel().equals("PRIVATE"));
        
        value = resultantMappings.get(microphone);
        assertTrue(value.getInputLevel().equals("PRIVATE"));
        assertTrue(value.getOutputLevel().equals("PUBLIC"));
        
        value = resultantMappings.get(network);
        assertTrue(value.getInputLevel().equals("PRIVATE"));
        assertTrue(value.getOutputLevel().equals("PRIVATE"));
    }
    
//    /**
//     * Test method for {@link org.jmlspecs.openjml.flowspecs.channelmappings.ChannelMappingsParser#parse()}.
//     */
//    @Test
//    public void Parse_MalformedChannelMappingsFileGivenWithoutSchema_BehaviorTBD(){
//        fail("Not yet implemented");
//    }
//    
//    /**
//     * Test method for {@link org.jmlspecs.openjml.flowspecs.channelmappings.ChannelMappingsParser#parse()}.
//     */
//    @Test
//    public void Parse_InvalidLevelSpecifiedInXMLFileWithoutSchema_BehaviorTBD(){
//        fail("Not yet implemented");
//    }
//    
//    /**
//     * Test method for {@link org.jmlspecs.openjml.flowspecs.channelmappings.ChannelMappingsParser#parse()}.
//     */
//    @Test
//    public void Parse_DuplicateChannelSpecifiedInXMLFileWithoutSchema_BehaviorTBD(){
//        fail("Not yet implemented");
//    }
//    
//    /**
//     * Test method for {@link org.jmlspecs.openjml.flowspecs.channelmappings.ChannelMappingsParser#parse()}.
//     */
//    @Test
//    public void Parse_ValidChannelMappingsFileGivenWithSchema_ProperChannelMappingsObjectReturned(){
//        fail("Not yet implemented");
//    }
//    
//    /**
//     * Test method for {@link org.jmlspecs.openjml.flowspecs.channelmappings.ChannelMappingsParser#parse()}.
//     */
//    @Test
//    public void Parse_MalformedChannelMappingsFileGivenWithSchema_BehaviorTBD(){
//        fail("Not yet implemented");
//    }
//    
//    /**
//     * Test method for {@link org.jmlspecs.openjml.flowspecs.channelmappings.ChannelMappingsParser#parse()}.
//     */
//    @Test
//    public void Parse_InvalidLevelSpecifiedInXMLFileWithSchema_BehaviorTBD(){
//        fail("Not yet implemented");
//    }
//    
//    /**
//     * Test method for {@link org.jmlspecs.openjml.flowspecs.channelmappings.ChannelMappingsParser#parse()}.
//     */
//    @Test
//    public void Parse_DuplicateChannelSpecifiedInXMLFileWithSchema_BehaviorTBD(){
//        fail("Not yet implemented");
//    }

}
