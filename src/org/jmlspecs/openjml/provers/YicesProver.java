package org.jmlspecs.openjml.provers;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.Writer;
import java.nio.CharBuffer;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.ProverException;
import org.jmlspecs.openjml.proverinterface.ProverResult;
import org.jmlspecs.openjml.proverinterface.Sort;
import org.jmlspecs.openjml.proverinterface.Term;


public class YicesProver implements IProver {

    Process process = null;
    StringBuilder sb = new StringBuilder();
    Writer toProver;
    Reader fromProver;
    //BufferedReader fromProver;
    Reader errors;
    CharBuffer buf = CharBuffer.allocate(10000);

    StringBuilder builder = new StringBuilder();
    List<Term> assertedTerms = new ArrayList<Term>();
    List<String> sent = new LinkedList<String>();
    
    String app = "C:/home/apps/yices-cygwin/yices-1.0.12/bin/yices.exe";
    
    public YicesProver() throws ProverException {
        try {
            // The interactive mode is used so that we get a prompt back, thereby
            // knowing when we have erceived the prover's response
            process = Runtime.getRuntime().exec(new String[]{app,"-i","-e","-v","0"});
        } catch (IOException e) {
            process = null;
            throw new ProverException("Failed to launch prover process: " + app + " " + e);
        }
        toProver = new OutputStreamWriter(process.getOutputStream());
        //fromProver = new BufferedReader(new InputStreamReader(process.getInputStream()));
        fromProver = new InputStreamReader(process.getInputStream()); // FIXME should we use buffered readers/writers
        errors = new InputStreamReader(process.getErrorStream());
        eatPrompt();
        // Send the background predicate
        send("(define-type REF) (define null::REF)\n");
        eatPrompt();
        //System.out.println("New Prover");
    }
    
    public String eatPrompt() throws ProverException {
        // We read characters until we get to the sequence "> ", which is the
        // end of the Yices prover's prompt (which is "yices> ").  Be careful 
        // that sequence is not elsewhere in the input as well.
        // FIXME - check of additional input at least???
        try {
            buf.position(0);
            outer: while (true) {
                int n = fromProver.read();
                if (n < 0) {
                    throw new ProverException("Prover died");
                }
                char c = (char)n;
                buf.append(c);
                if (c != '>') continue;
                while (true) {
                    n = fromProver.read();
                    if (n < 0) {
                        throw new ProverException("Prover died");
                    }
                    c = (char)n;
                    buf.append(c);
                    if (c == ' ') break outer;
                    if (c != '>') break;
                }
            }
            buf.limit(buf.position());
            buf.rewind();
            String s = buf.toString();
            buf.clear();
            if (errors.ready()) {
                while (errors.ready()) {
                    int n = errors.read(buf);
                    if (n <= 0) break;
                }
                if (buf.position() > 0) {
                    buf.limit(buf.position());
                    buf.rewind();
                    if (!buf.toString().startsWith("\nWARNING"))
                        throw new ProverException("Prover error message: " + buf);
                }
                buf.clear();
            }
            return s;
        } catch (IOException e) {
            throw new ProverException("IO Error on reading from prover: " + e);
        }
    }
    
    public void assume(Term t) throws ProverException {
        try {
            assertedTerms.add(t);
            builder.setLength(0);
            builder.append("(assert+ ");
            builder.append(t.toString());
            builder.append(")\n");
            send(builder.toString());
            eatPrompt();
        } catch (ProverException e) {
            e.mostRecentInput = builder.toString();
            throw e;
        }
    }
    
    public void send(String s) throws ProverException {
        sent.add(s);
        System.out.print("SENDING " + s);
        try {
            toProver.append(s);
            toProver.flush();
        } catch (IOException e) {
            throw new ProverException("Failed to write to prover: " + e);
        }
    }
    
    public void define(String id, Sort sort) throws ProverException {
        builder.setLength(0);
        builder.append("(define ");
        builder.append(id);
        builder.append("::");
        String s;
        switch (sort) {
            case VARBOOL: s = "bool"; break;
            case VARINT: s = "int"; break;
            default: s = "REF"; break;
        }
        builder.append(s);
        builder.append(")\n");
        try {
            send(builder.toString());
            eatPrompt();
        } catch (ProverException e) {
            e.mostRecentInput = builder.toString();
            throw e;
        }
    }


//    public TermBuilder getBuilder() {
//        // TODO Auto-generated method stub
//        return null;
//    }
//    
    public IProverResult getDetailedAnswer() {
        // TODO Auto-generated method stub
        return null;
    }
    
    public boolean isSat(Term t) throws ProverException {
        return false; // FIXME
    }

    public boolean isSat() throws ProverException {
        send("(check)\n");
        String output = eatPrompt();
        //System.out.println("HEARD " + output);
        boolean sat = output.startsWith("sat");
        boolean unsat = output.startsWith("unsat");
        if (sat == unsat) throw new ProverException("Improper response to (check) query: \"" + output + "\"");
        satResult = output.substring(0,output.length()-8);
        return sat;
    }
    
    public IProverResult check() throws ProverException {
        send("(check)\n");
        String output = eatPrompt();
        //System.out.println("HEARD " + output);
        boolean sat = output.startsWith("sat");
        boolean unsat = output.startsWith("unsat");
        if (sat == unsat) throw new ProverException("Improper response to (check) query: \"" + output + "\"");
        ProverResult r = new ProverResult();
        if (sat) {
            r.result(ProverResult.SAT);
            satResult = output.substring(0,output.length()-8);
            r.add(new ProverResult.Counterexample(satResult));
        } else if (unsat) {
            r.result(ProverResult.UNSAT);
            satResult = output.substring(0,output.length()-8);
            // Need to show the unsat core FIXME
        } else {
            r.result(ProverResult.UNKNOWN);

        }
        
        return r;
    }
    
    // FIXME - just temporary
    public String satResult = null;

    public void pop() throws ProverException {
        send("(pop)\n");
        eatPrompt();
    }

    public void push() throws ProverException {
        send("(push)\n");
        eatPrompt();
    }

    public void restartProver() throws ProverException {
        // TODO Auto-generated method stub

    }

    public void retract() throws ProverException {
        // TODO Auto-generated method stub

    }

}
