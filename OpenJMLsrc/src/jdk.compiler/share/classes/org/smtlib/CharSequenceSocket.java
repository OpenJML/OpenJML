/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.io.Reader;
import java.net.ServerSocket;
import java.net.Socket;


/** This class implements a CharSequence that obtains its characters from a ServerSocket.  The characters 
 * read are held in an internal char array, whose size grows as needed; it starts as initialSize and
 * is expanded to currentSize*sizeMultiple + sizeIncrease whenever needed.
 * <P>
 * The CharSequenceReader is an unconventional CharSequence in that its length() is not known; 
 * whether this will cause problems
 * in some uses of the CharSequenceReader is unknown.  The user should not use the value of length()
 * directly; it seems to work in the ways it is called from Pattern.matcher.
 * @author David R. Cok
 *
 */
public class CharSequenceSocket extends CharSequenceInfinite {

	/** The socket from which characters are read */
	protected ServerSocket serverSocket;

	/** The configuration for this instance of SMT */
	protected SMT.Configuration smtConfig;
	
	/** Constructor for a new instance
	 * 
	 * @param serverSocket the ServerSocket that supplies characters on demand
	 * @param initialSize the beginning size of the internal char array
	 * @param sizeIncrease the amount to add to the current size of the internal char array when the array needs expanding
	 * @param sizeMultiple the factor by which to multiply the current size of the internal char array when it needs expanding
	 */
	//@ requires initialSize > 0 && sizeIncrease >= 0 && sizeMultiple >= 1;
	//@ requires !(sizeIncrease == 0 && sizeMultiple == 1)
	public CharSequenceSocket(SMT.Configuration smtConfig, ServerSocket serverSocket, int initialSize, int sizeIncrease, double sizeMultiple) {
		super(initialSize, sizeIncrease, sizeMultiple);
		this.serverSocket = serverSocket;
		this.smtConfig = smtConfig;
	}

	/** Internal state - if true then we need to create a new connection before reading characters */
	private boolean needsNewConnection = true;
	
	/** Internal state - the client socket on which we are reading */
	private /*@Nullable*/ Socket clientSocket = null;
	
	/** Internal state - the current Reader for fetching characters */
	private /*@Nullable*/ Reader rdr = null;
	
	//@ requires !needsNewConnection => rdr != null;
	@Override
	protected boolean readChars() throws java.io.IOException {
		while (true) {
			if (needsNewConnection) {
				if (rdr != null) rdr.close();
				if (clientSocket != null) clientSocket.close();

				// Wait for a client to initiate a call
				clientSocket = serverSocket.accept();

				// Create the input and output streams
				// FIXME - use a listener?
				// FIXME - are there any other exceptions?  what if the connection is unexpectedly broken
				smtConfig.log.out = new PrintStream(clientSocket.getOutputStream(),true);
				rdr = new BufferedReader(
						new InputStreamReader(
								clientSocket.getInputStream()));
				needsNewConnection = false;
			}
			/*@SuppressWarnings("nullness")*/
			/*@NonNull*/ Reader nnrdr = rdr;
			int nread = 0;
			do {
				nread = nnrdr.read(buf,amountRead,buf.length-amountRead);
				if (nread == -1) {
					break;
				}
				if (smtConfig.verbose != 0) smtConfig.log.logDiag("SOCKET READ " + nread + ":" + new String(buf,amountRead,nread));
				amountRead += nread;
			} while (amountRead < buf.length && nnrdr.ready());

			if (nread == -1) {
				needsNewConnection = true;
				// end of file so no characters read - go read some more
			} else if (buf[amountRead-1] == 0) {
				amountRead--;
				needsNewConnection = true;
				if (nread > 1) return true;
				// read only the 0 so no characters read - go read some more
			} else {
				return true;
			}
		}
	}

}
