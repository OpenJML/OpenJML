/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.io.*;
import java.net.*;
import java.util.LinkedList;
import java.util.List;

// TODO - must be sure that the server prints success and is interactive
// TODO _ add other options? smtConfig echo; allow getting port from a env. variable - same one as used by server


/** The Driver class is a client that can send commands to the SMT application acting as a server. */
public class Driver {
	
	// These constants are exit codes emitted from the application
	
	/** The exit code corresponding to a 'success' response to an SMT-LIB command */
	static final int EX_SUCCESS = 0;

	/** The exit code corresponding to a 'sat' response to an SMT-LIB command */
	static final int EX_SMT_SAT = 2;

	/** The exit code corresponding to a 'unsat' response to an SMT-LIB command */
	static final int EX_SMT_UNSAT = 3;

	/** The exit code corresponding to a 'unknown' response to an SMT-LIB command */
	static final int EX_SMT_UNKNOWN = 4;

	/** The exit code corresponding to any other response to an SMT-LIB command */
	static final int EX_SMT_OTHER = 5;

	/** The exit code corresponding to and 'error' response to an SMT-LIB command */
	static final int EX_SMT_ERROR = 10;

	/** The exit code used when there is an error in the command-line arguments */
	static final int EX_CMD_LINE_ERROR = 11;

	/** The exit code used when there is an internal exception in the application */
	static final int EX_EXCEPTION = 12;
	
	/** The port to which to send commands (set as a command-line option)*/
	protected int port = 0;

	/** If true, verbose, debugging information is emitted by the application (set as a command-line option)*/
	protected boolean verbose = false;

	/** If true, do not echo 'success' responses (unless verbose is enabled) */
	protected boolean quiet = false;

	/** Whether to start a service process from this process */
	protected boolean start = false;
	
	/** The commands as specified on the command-line */
	protected List<String> commands = new LinkedList<String>();
	
	/** The main entry point to the application 
	 * @param args the command-line arguments
	 */
	public static void main(String[] args) {
		int exitCode = (new Driver()).exec(args);
		System.exit(exitCode);
	}
	
	/** The non-static entry point to the application 
	 * @param args the command-line arguments
	 * @return the exit code
	 */
	public int exec(String[] args) {
		int exitCode = processOptions(args);
		if (exitCode != 0) return exitCode>0 ? exitCode : 0;
		if (port <= 0) {
			System.out.println("Error: no port is specified");
			return EX_CMD_LINE_ERROR;
		}
		try {
			return send();
		} catch (java.io.IOException e) {
			System.out.println(e);
			e.printStackTrace(System.out);
		}
		return EX_EXCEPTION;
	}
	
	/** Sets the fields of the class according to the command-line */
	protected int processOptions(String[] args) {
		int i = 0;
		while (i < args.length) {
			if ("--port".equals(args[i]) || "-p".equals(args[i])) {
				++i;
				if (i >= args.length) {
					System.out.println("--port option must have an integer value");
					return EX_CMD_LINE_ERROR;
				} else {
					try {
						port = Integer.valueOf(args[i]).intValue();
					} catch (NumberFormatException e) {
						System.out.println(e);
						return EX_CMD_LINE_ERROR;
					}
				}
			} else if ("--verbose".equals(args[i]) || "-v".equals(args[i])) {
				verbose = true;
				quiet = false;
			} else if ("--nosuccess".equals(args[i]) || "-q".equals(args[i])) {
				quiet = true;
			} else if ("--help".equals(args[i]) || "-h".equals(args[i])) {
				usage();
				return -1;
			} else if (args[i].startsWith("-")) {
				System.out.println("Unknown option: " + args[i]);
				return EX_CMD_LINE_ERROR;
			} else {
				commands.add(args[i]);
			}
			++i;
		}
		return EX_SUCCESS;
	}
	
	/** Prints out the usage information */
	public void usage() {
		System.out.println("java org.smtlib.Driver [options] commands");
		System.out.println("  -h or --help : prints out the usage information");
		System.out.println("  -v or --verbose : enables printing of detailed progress information");
		System.out.println("  -q or --nosuccess : disables printing the 'success' reponses");
		System.out.println("  -p <number> or --port <number> : (required) specifies the port to which to send commands");
		System.out.println("    The port must match the port on which the server process is listening");
		System.out.println("  This process sends SMT-LIB commands (as specified on the command-line) to a");
		System.out.println("  server process, which must be on the local host, and is started by ");
		System.out.println("  'java org.smtlib.SMT --port <number>' ");
		System.out.println("  Each SMT command is a (quoted) single command-line argument.");
	}

	/** Sends the options and commands to the port; returns the exit code corresponding to the response
	 * from the last command. */
	public int send() throws IOException {

		/*@Mutable*/ Socket serverSocket = null;
		/*@Mutable*/ PrintWriter out = null;
		/*@Mutable*/ BufferedReader in = null;

		try {
			// FIXME - Inet6?  Allow non-local host?
			serverSocket = new Socket(Inet4Address.getLocalHost(), port);
			out = new PrintWriter(serverSocket.getOutputStream(), true);
			in = new BufferedReader(new InputStreamReader(
					serverSocket.getInputStream()));

			int exitcode = -1;
			for (String command: commands) {
				if (verbose) System.out.println("send: " + command);
				out.println(command);
				do {
					String answer = in.readLine();
					if ("success".equals(answer)) exitcode = EX_SUCCESS;
					else if ("sat".equals(answer)) exitcode = EX_SMT_SAT;
					else if ("unsat".equals(answer)) exitcode = EX_SMT_UNSAT;
					else if ("unknown".equals(answer)) exitcode = EX_SMT_UNKNOWN;
					else if (answer.indexOf("error") != -1) exitcode = EX_SMT_ERROR;
					else exitcode = EX_SMT_OTHER;
					if (!quiet || verbose || exitcode != EX_SUCCESS) System.out.println("SMT: " + answer );
				} while (in.ready());
			}

			if (verbose) System.out.println("exitcode = " + exitcode);
			return exitcode;
		} catch (UnknownHostException e) {
			System.err.println("Failure to connect to local host: " + e);
			return EX_EXCEPTION;
		} catch (IOException e) {
			System.err.println("Couldn't get I/O from the socket connection: " + e);
			return EX_EXCEPTION;
		} finally {
			if (out != null) out.close();
			if (in != null) in.close();
			if (serverSocket != null) serverSocket.close();
		}
	}
}
