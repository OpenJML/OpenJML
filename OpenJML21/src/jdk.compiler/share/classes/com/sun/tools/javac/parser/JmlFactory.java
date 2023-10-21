/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 * Reviewed 2018-03-19
 */
package com.sun.tools.javac.parser;

import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Names;

/**
 * This class extends the Java Parser factory class to be able to produce
 * JML ast nodes as well. There is just one factory per context, but there
 * may be multiple instances of parsers.
 * 
 * @author David Cok
 */
public class JmlFactory extends ParserFactory {

    /**
     * The constructor for the factory.
     * 
     * @param context
     *            the Context for which this is the factory
     */
    protected JmlFactory(Context context) {
        super(context);
        this.context = context;
    }

    /** The context in which this factory works */
    protected Context context;

    /**
     * A static call that registers an instance of JmlFactory as the factory
     * to use for this context.
     * 
     * @param context
     *            the context in which to register the factory
     */
    public static void preRegister(final Context context) {
        context.put(parserFactoryKey, new Context.Factory<ParserFactory>() {
            @Override
            public ParserFactory make(Context context) {
                return new JmlFactory(context);
            }
        });
    }

    /**
     * Creates a new parser from the factory, given a lexer and flags as to
     * whether to keep javadoc comments and whether to generate end position
     * information.
     */
    // @ requires S != null;
    // @ ensures this.S != null && this.context != null;
    // @ ensures this.names != null && this.jmlF != null;
    @Override
    public JavacParser newParser(CharSequence input, boolean keepDocComments, boolean genEndPos, boolean keepLineMap) {
        return newParser(input, keepDocComments, genEndPos, keepLineMap,
                false); // The last argument says that the parser begins outside a JML comment
    }

    /** Generates a new parser set to parse the given input, with parameters
     * set to control various aspects of the parser.
     * @param input    the input to parse
     * @param keepDocComments  if true, javadoc comments are kept
     * @param genEndPos   if true, AST node end position information is kept
     * @param keepLineMap  if true, the mapping from position to line is kept
     * @param enableJml   if true, parser begins within a JML comment
     * @return the new parser, ready to go
     */
    public JmlParser newParser(CharSequence input, boolean keepDocComments,
            boolean genEndPos, boolean keepLineMap, boolean enableJml) {
        JmlScanner lexer = (JmlScanner) scannerFactory.newScanner(input, keepDocComments);
        lexer.setJml(enableJml);
        JmlParser p = new JmlParser(this, lexer, keepDocComments);
        p.names = Names.instance(context);
        p.context = context;
        p.utils = Utils.instance(context);
        return p;
    }
    
}