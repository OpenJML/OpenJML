package org.jmlspecs.openjml.safe;

import java.io.File;
import java.net.MalformedURLException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.dom4j.Document;
import org.dom4j.DocumentException;
import org.dom4j.Element;
import org.dom4j.io.SAXReader;
import org.jmlspecs.openjml.Strings;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JavacMessages;
import com.sun.tools.javac.util.Log;

//
// TODO 
// This parser should use a proper XSD to validate the XML. Before we ship this needs to be done.
// This will greatly improve the accuracy of the errors we can report and make integration with IDEs
// a little easier since we will be able to provide specific errors about the lines on which an error
// happened. Please remove me when this is done. -- JLS
//

public class LatticeParser {

    private File config;

    public LatticeParser(File config) {
        this.config = config;
    }

    public Lattice parse() throws MalformedURLException, DocumentException, LatticeParserException {


        SAXReader reader = new SAXReader();
        Document document = reader.read(config.toURI().toURL());

        AdjacencyMatrix<String> matrix = parseDocument(document);

        // make sure there are no cycles
        checkGraphContainsCycles(matrix);

        return new Lattice(matrix);
    }

    private List<String> getLevels(Document document) throws DuplicateLevelException {

        List<String> levels = new ArrayList<String>();

        List<Element> list = document.selectNodes("//levels/level");

        for (Element e : list) {

            // don't allow duplicates
            if (levels.contains(e.getTextTrim())) {
                uninitializedLog().error("jml.lattice.dupulicate.level",e.getTextTrim());
                throw new DuplicateLevelException();
            }

            levels.add(e.getTextTrim());
        }


        return levels;
    }

    private boolean checkGraphContainsCycles(AdjacencyMatrix<String> matrix) throws CyclicSubclassGraphException {

        List<String> vertexes = matrix.getVertexList();

        // run a modified dfs forall vertexes

        for (String vertex : vertexes) {

            Set<String> seen = new HashSet<String>();
            seen.add(vertex);
            verifyGraph(vertex, matrix, seen);
        }


        return false;
    }

    private void verifyGraph(String root, AdjacencyMatrix<String> matrix, Set<String> seen) throws CyclicSubclassGraphException {

        for (String v : matrix.getAdjacentVertexes(root)) {

            if (seen.contains(v) == false) {
                Set<String> nseen = new HashSet<String>(seen);
                nseen.add(v);
                verifyGraph(v, matrix, nseen);
            } else {
                uninitializedLog().error("jml.lattice.hascycles", root, v);
                throw new CyclicSubclassGraphException();
            }

        }


    }


    private AdjacencyMatrix<String> parseDocument(Document document) throws  LatticeParserException {

        List<String> levels = getLevels(document);

        AdjacencyMatrix<String> matrix = new AdjacencyMatrix<String>(levels);

        // work through the level specs, adding edges where needed.
        List<Element> list = document.selectNodes("//level-specs/level-spec");

        for (Element e : list) {

            List<Element> nameNodes = e.selectNodes("./name");

            if (nameNodes.size() != 1) {
                uninitializedLog().error("jml.lattice.invalid.number.of.nodes");
                throw new MissingNameNodesException();
            }

            String levelName = nameNodes.get(0).getTextTrim();

            List<Element> subClasses = e.selectNodes("./trusts/level");

            for (Element subclass : subClasses) {

                if (levels.contains(subclass.getTextTrim()) == false) {
                    uninitializedLog().error("jml.lattice.undeclared.level", subclass.getTextTrim() );
                    throw new MissingNameNodesException();
                }

                matrix.addEdge(levelName, subclass.getTextTrim());
            }
        }

        
        
        return matrix;

    }


    public static void main(String args[]) throws MalformedURLException, DocumentException {

        LatticeParser p = new LatticeParser(new File("security.xml"));

//        p.parse();


    }
    
    static protected Log uninitializedLog() {
        Context context = new Context(); // This is a temporary context just for this error message.
        // It is not the one used for the options and compilation
        JavacMessages.instance(context).add(Strings.messagesJML);
        return Log.instance(context);
    }


    
    class LatticeParserException extends Exception {
        public LatticeParserException(){
            super();
        }
    }
    
    class MissingNameNodesException extends LatticeParserException {
        public MissingNameNodesException(){
            super();
        }
    }
    
    
    class CyclicSubclassGraphException extends LatticeParserException {
        public CyclicSubclassGraphException() {
            super();
        }
    }

    class DuplicateLevelException extends LatticeParserException {
        public DuplicateLevelException() {
            super();
        }
    }

}
