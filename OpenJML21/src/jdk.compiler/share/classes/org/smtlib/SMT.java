/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;
//FIXME-NOW - SMT needs more review and documentation
// FIXME - check that this uses interfaces as much as possible

import java.io.*;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.net.ServerSocket;
import java.net.URL;
import java.util.*;

import org.smtlib.IExpr.IKeyword;
import org.smtlib.IParser.AbortParseException;
import org.smtlib.IParser.ParserException;
import org.smtlib.IPos.IPosable;
import org.smtlib.solvers.Printer;

//import checkers.javari.quals.Mutable; NonNull

/** This is the main class for the SMT-LIB tool. 
 * The tool is invoked as a command-line tool by running main within org.smtlib.SMT.
 * The tool can also be invoked programmatically by calling exec() in a new instance of
 * the SMT class, created with the default constructor.  Separate instances of SMT objects
 * can be run independently and in parallel.  They are thread-safe (though they all may write
 * to the same standard and error output streams).
 * <P>
 * To extend this tool, e.g. to use it with other factory objects for a different implementation,
 * or to add configuration options:
 * <UL>
 * <LI> Create subclasses of SMT, SMT.Configuration
 * <LI> The SMT' should set a new object of type SMT.Configuration' in its constructor
 * <LI> SMT' can override parseCommandLine, help, usage
 * <LI> Create a new main method; the new main should also instantiate the derived SMT and call exec on it 
 * <LI> SMT.Configuration' can have new options added; it can also instantiate different object factories
 * <LI> SMT.COnfiguration' can also instantiate a derived Utils or Log object
 * <LI> FIXME - more; parseCommandLine, help, usage are not easy to extend; what about replacing the SymbolTable or SolverProcess; should have interfaces for Log, Utils?
 * </UL> 
 */
public class SMT {
	
//	public SMT() {
//		this(Utils.SMTLIB_VERSION_CURRENT);
//	}
//	
//	public SMT(String version) {
//		Configuration.smtlib = version;
//	}
	
	public Properties props;
	
	static public interface IConfiguration {} // FIXME - do we need this?
	
	/** The configuration object holds the values of all of the current options (e.g. command-line
	 * settings); it also holds factory objects that are used to create objects for the particular
	 * concrete syntax being used; it also holds a few internal state values
	 */
	static public class Configuration implements Cloneable, IConfiguration { // FIXME - make cloneable?
		/* If you want to add an option to the configuration:
		 * - add a field here
		 * - edit the copy constructor
		 * - edit processCommand to be able to set the value from the commandline
		 * - edit the help/usage messages
		 * - in the plugin, edit Preferences:
		 * 		add a key
		 * 		add a preference object
		 * 		add a preference widget to the right PrferenceWidget array
		 * 		edit extractOptions
		 */
		
		/** Creates a default configuration, initialized from org.smtlib.impl */
		public Configuration() {
			// Initialize all the factories to use the concrete implementations in
			// the app package
			// TODO - this hard-codes the concrete syntax to be the syntax defined in
			// package org.smtlib.impl ; we should generalize this, allowing the package
			// to be specified on the command-line and the appropriate initFactories
			// method called by reflection
			org.smtlib.impl.Factory.initFactories(this);
			org.smtlib.sexpr.Factory.initFactories(this);
			Printer.smtConfig = this;
			org.smtlib.impl.Response.smtConfig = this;
			org.smtlib.impl.SMTExpr.smtConfig = this;
		}
		
		/** Makes a copy (using reference copy on objects) of the configuration */ 
		public Configuration clone() throws CloneNotSupportedException {
			Configuration c = (Configuration)super.clone();
			//c.commandExtensionPrefixes = Array.copy(commandExtensionPrefixes);
			c.commands = new HashMap<String,Class<? extends ICommand>>();
			c.commands.putAll(commands);
			// FIXME - ok to have a reference copy of Log ?
			c.reservedWords = new HashSet<String>();
			c.reservedWords.addAll(reservedWords);
			c.reservedWordsNotCommands = new HashSet<String>();
			c.reservedWordsNotCommands.addAll(reservedWordsNotCommands);
			utils.smtConfig = this;
			return c;
		}
		
		/** A list of reserved words that are not commands */
		public Set<String> reservedWordsNotCommands = new HashSet<String>();

		/** A list of all reserved words */
		public Set<String> reservedWords = new HashSet<String>();

		/** The version of SMT-LIB to be supported; default (null) is the most recent version */
		public static String smtlib = null;
		public static enum SMTLIB {
			V20("V2.0"),
			V25("V2.5"),
			V26("V2.6");
			public String id;
			private SMTLIB(String id) { this.id = id; }
			public String toString() { return id; }
			public static SMTLIB find(String id) { for (SMTLIB e: SMTLIB.values()) { if (e.id.equals(id)) return e; } return null; } 
		}
		
		public boolean isVersion(SMTLIB version) {
			if (smtlib == null && version == SMTLIB.V25) return true;
			return version.toString().equals(smtlib);
		}
		
		public boolean atLeastVersion(SMTLIB version) {
			if (smtlib == null && version == SMTLIB.V25) return true;
			return version.toString().compareTo(smtlib) <= 0;
		}
		
		/** True to emit diagnostic output through the SMT-LIB diagnostic channel */
		public int verbose = 0;
		
		/** The verbosity level of the SMT solver */
		public int solverVerbosity = 0;

		/** The timeout for a given query, if supported by the solver */
		public double timeout = -1; // seconds, <=0 means infinity
		
		/** This field is set from the command-line and sets the initial state of the :print-success option
		 * within a solver. */
		public boolean nosuccess = false;
		
		/** If true, command processing in a solver (not in check mode) aborts
		 * on the first error
		 */
		public boolean abort = false;
		
		/** True if the application is to echo commands as it executes them; only applies in interactiveMode mode */
		public boolean echo = false;
		
		/** This field is set from the command-line; if set, then sets the logic used by the solver,
		 * as if the first command were the corresponding set-logic command.
		 */
		/*@Nullable*/ public String logic;
		
		/** Whether declarations are global */
		public boolean globalDeclarations;
		
		/** The solver to use */
		/*@Nullable*/ public String solvername = null;
		
		/** The path to the executable for the solver to use */
		/*@Nullable*/ public String executable = null;
		
		/** The file to which to write the communication, for debugging or reference; null means default */
		/*@Nullable*/ public String logfile = null;
		
		/** The files of SMT-LIB commands to process; if null or empty then the standard input is used */
		/*@Nullable*/ public List<String> files = new LinkedList<String>();
		
		/** A string containing the SMT-LIB commands to use; if null the given file is used; if non-null
		 * this text is used instead of the content of the file or the input from a port.
		 */
		/*@Nullable*/ public String text = null;
		
        /** If true, then information about the position of an error is not shown */
        public boolean noshow = false;
        
        /** If non-zero, a seed to pass to the solver to initialize its random number generator */
        public int seed = 0;
        
		/** FIXME */
		/*@Nullable*/ public String out = null;
		/*@Nullable*/ public String diag = null;
		
		/** The port to use for socket communications; a port > 0 supersedes any file value, but is
		 * ignored if the text option is set. */
		public int port = -1;
		
		/** The log to use for regular, error, and diagnostic output */ 
		public /*@NonNull*/ Log log = new Log(this);
		
		/** The utils object to use for utility methods */
		public /*@NonNull*/ Utils utils = new Utils(this);
		
		/** When true, allows some convenience relaxations of the SMTLIB standard; when
		 *  false, the standard is strictly enforced.
		 */
		public boolean relax = false;
		
		/** An array of fully-qualified class name prefixes; a command name (with hyphen
		 * replaced by underscore) is appended to the prefix to obtain a fully-qualified class name that
		 * implements the command.
		 */
		public String[] commandExtensionPrefixes = { "org.smtlib.command.C_","org.smtlib.ext.C_"};
		
		/** The path on which to find logic and theory definitions - currently a single directory */
		public /*@Nullable*/ String logicPath = null;
		
		/** The prompt to use when needing new input from the user in an interactive mode. */
		public /*@NonNull*/ String prompt = "> ";
		/** The prompt to use when in the middle of a command */
		public /*@NonNull*/ String prompt2 = "...> ";

		/** The factory to use to create ISort objects */
		public ISort.IFactory sortFactory;
		/** The factory to use to create IResponse objects */
		public IResponse.IFactory responseFactory;
		/** The factory to use to create IExpr objects */
		public IExpr.IFactory exprFactory;
		/** The factory to use to create ICommand objects */
		public ICommand.IFactory commandFactory;
		/** The factory to use to create IParser, IPos, ISource objects */
		public IParser.IFactory smtFactory;
		
		public /*@LazyNonNull*/IPrinter defaultPrinter = null;
		
		// FIXME - document
		public int initialInputBufferSize = 1000000;
		
		/** Holds a mapping from command name to the class implementing the command */
		public Map<String,Class<? extends ICommand>> commands = new HashMap<String,Class<? extends ICommand>>();
		/** A class that implements ICommandFinder, whose one method returns the class 
		 * object of the class that implements a command with a given name; the algorithm to
		 * identify the command class first looks for an entry in the command map above and
		 * otherwise uses this default: replace each - in the command name by _, and append 
		 * the resulting string to the elements of 'commandExtensionPrefixes', looking for
		 * the first such class that exists;  if relax is false (strict SMT-LIB) then
		 * the commands map and all but the initial entry of commandExtensionPrefixes are 
		 * ignored. 
		 */
		public /*@Nullable*/ ICommand.IFinder commandFinder = new ICommand.IFinder() {
			@Override
			public Class<? extends ICommand> findCommand(String name) {
				Class<? extends ICommand> clazz = commands.get(name);
				if (relax && clazz != null) return clazz;
				for (String prefix: relax ? commandExtensionPrefixes : new String[]{commandExtensionPrefixes[0]}) {
					String className = prefix + name.replace('-','_');
					try {
						Class<?> clazzz = Class.forName(className);
						if (clazzz == null) continue; // This won't happen - exception is thrown instead
						if (!ICommand.class.isAssignableFrom(clazzz)) continue; // FIXME - message?
                                                @SuppressWarnings("unchecked") // FIXME - do better on checking typing
						var cl = (Class<? extends ICommand>)clazzz; // Check for this - implementation may be wrong
                                                return cl;
					} catch (ClassNotFoundException e) {
						continue;
					}
				}
				return null;
			}
		};
		
		
		// These should not be set by the user - they hold internal state - they are public because
		// they need to be seen in other packages of this tool
		// FIXME - can this internal state be removed from the configuration


		/** This variable records whether we are reading from standard input,
		 * in which case the input text is usually already present.  
		 * If this field is true, then we prompt when we need additional
		 * input and we do not need to echo back an invalid command.
		 */
		public boolean interactive = false;
		
		/** Encodes an aspect of current parser state so that we know what kind of prompt to use. */
		public boolean topLevel = true;
		
			
	}
	
	/** The set of configuration settings for this instance of the SMT object */
	public Configuration smtConfig = new Configuration();
	
	/** The main method of the SMT application */
	public static void main(String[] args) {
		//System.err.println("#Start main");
		int exitValue = (new SMT()).exec(args);
		System.exit(exitValue);
	}
	
	/** Reads and returns the properties file for the application:
	 * from file Utils.PROPS_FILE in the working directory 
	 * or user's home directory
	 * or on the class path
	 * or in the directory in which jSMTLIB.jar resides (if it is being run with -jar).
	 */
	public Properties readProperties() {
		Properties p = new Properties();
		/*@Nullable @Mutable*/ Reader rdr = null;
		File f;
		// Find and read file on class path
		URL url =  ClassLoader.getSystemResource(Utils.PROPS_FILE);
		if (url != null) {
			f = new File(url.getFile());
			try {
				if (smtConfig.verbose > 0) smtConfig.log.logDiag("#reading properties (class path) from " + f);
				rdr = new FileReader(f);
				p.load(rdr);
			} catch (IOException e) {
				smtConfig.log.logDiag("IOException " + e); // FIXME - is this how to report this error
			} finally {
				try {
					if (rdr != null) rdr.close();
				} catch (Exception ee) {
					smtConfig.log.logDiag("Failed to close reader " + f); // FIXME - is this how to report this error
				} // Ignore
			}
		}
		// Find and read file in the directory that contains
		// the jSMTLIB.jar file
		url =  ClassLoader.getSystemResource(".");
		if (url != null) {
			String s = url.toString();
			String prefix = "jar:file:/";
			String suffix = "jSMTLIB.jar!/";
			if (s.startsWith(prefix) && s.endsWith(suffix)) {
				s = s.substring(prefix.length(),s.length()-suffix.length());
				s = s + Utils.PROPS_FILE;
				f = new File(s);
				if (f.isFile()) {
					try {
						if (smtConfig.verbose > 0) smtConfig.log.logDiag("#reading properties (class path dir) from " + f);
						rdr = new FileReader(f);
						p.load(rdr);
					} catch (IOException e) {
					} finally {
						try {
							if (rdr != null) rdr.close();
						} catch (Exception ee) {} // Ignore
					}
				}
			}
		}
		// Find and read file from user's home directory
		String home = System.getProperty("user.home");
		f = new File(home,Utils.PROPS_FILE);
		if (f.isFile()) {
			try {
				if (smtConfig.verbose > 0) smtConfig.log.logDiag("#reading properties (user home) from " + f);
				rdr = new FileReader(f);
				p.load(rdr);
			} catch (IOException e) {
			} finally {
				try {
					if (rdr != null) rdr.close();
				} catch (Exception ee) {} // Ignore
			}
		}
		// Find and read file in current working directory
		f = new File(Utils.PROPS_FILE);
		if (f.isFile()) {
			try {
				if (smtConfig.verbose > 0) smtConfig.log.logDiag("#reading properties (current dir) from " + f);
				rdr = new FileReader(f);
				p.load(rdr);
			} catch (IOException e) {
			} finally {
				try {
					if (rdr != null) rdr.close();
				} catch (Exception ee) {} // Ignore
			}
		}
		return p;
	}
	
	/** The method that does all the execution for the main method, here made a non-static method, so that
	 * multiple SMT operations can be proceeding independently.
	 * @param args the command-line arguments
	 * @return the exit code to return to the command-line: FIXME - document exit codes
	 */
	public int exec(String[] args) {
		//System.err.println("#Start exec");
		int ret = processCommandLine(args,smtConfig);
		if (ret == -1) return 0; // help or version
		if (ret != 0) return ret;
		ret = exec();
		return ret;
	}
	
	public /*@Nullable*/ IResponse checkSatStatus = null;
	
	/** Executes, presuming all options (e.g. from the command-line) are set in the configuration object */
	public int exec() {
		int retcode = 0;
		IParser p;
		ISource src;
		if (smtConfig.text != null) {
			// If 'text' is set, use it as the input
			smtConfig.interactive = false;
			Reader rdr = new StringReader(smtConfig.text);
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Start parsing text input");
			// In the case of text input, the file name, if specified, is used just as an
			// indicator of where the text came from. The name is not used to open or read
			// from the file. This is used particularly when called from the plug-in; in that
			// case the text is the edited but unsaved text of a file and the file name is
			// the name of the edited file, so that any error messages can be directed back
			// to the correct editor.
			src = smtConfig.smtFactory.createSource(new CharSequenceReader(rdr,100000,0,2), 
					(smtConfig.files == null || smtConfig.files.isEmpty())? null : smtConfig.files.get(0)); // FIXME - use factory
			p = smtConfig.smtFactory.createParser(smtConfig,src);
			return doParser(p);

		} else if (smtConfig.port >= 0) {
			// If port is set, use the input from the socket.  We still set interactive to true,
			// so that the prompt is sent back on the socket and the client knows that the communication
			// has been received and responded to.
			smtConfig.interactive = false;
			ServerSocket serverSocket;
			try {
				serverSocket = new ServerSocket(smtConfig.port);
			} catch (IOException e) {
				System.out.println("Could not listen on port: " + smtConfig.port);
				return 1;
			}

			CharSequenceSocket csq = new CharSequenceSocket(smtConfig,serverSocket,100000,0,2);
			csq.prompter = new Prompter(smtConfig);
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Start parsing");
			src = smtConfig.smtFactory.createSource(csq, null);
			p = smtConfig.smtFactory.createParser(smtConfig,src);
			return doParser(p);

		} else if (smtConfig.files == null || smtConfig.files.isEmpty()) {
			// No files listed - use standard input
			smtConfig.interactive = true;
			Reader rdr = new BufferedReader(new InputStreamReader(System.in));
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Start parsing standard input");
			CharSequenceReader csr = new CharSequenceReader(rdr,100000,0,2);
			csr.prompter = new Prompter(smtConfig);
			src = smtConfig.smtFactory.createSource(csr, null);
			p = smtConfig.smtFactory.createParser(smtConfig,src);
			return doParser(p);
			
		} else {
			// Otherwise, iterate over all the files
			smtConfig.interactive = false;
			for (String file: smtConfig.files) {
				try {
					Reader rdr = new BufferedReader(new FileReader(file));
					CharSequenceReader csr = new CharSequenceReader(rdr,100000,0,2);
					src = smtConfig.smtFactory.createSource(csr, file);
					p = smtConfig.smtFactory.createParser(smtConfig,src);
					if (smtConfig.verbose != 0) smtConfig.log.logDiag("Starting file " + file);
					int e = doParser(p);
					if (e != 0) retcode = e;
				} catch (FileNotFoundException e) {
					smtConfig.log.logError("Could not find file: " + file + " Exception: " + e);
				}
			}
			return retcode;
		}
	}
	
	public int execCommand(String cmd) {
		ISource src = smtConfig.smtFactory.createSource(cmd,null);
		IParser p = smtConfig.smtFactory.createParser(smtConfig,src);
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("Command " + cmd);
		int e = doParser(p,false);
		return e;
	}
	
	protected int doParser(IParser p) { 
		return doParser(p,true);
	}
	
	protected /*@Nullable*/ ISolver solver = null;
	
	public IResponse lastResponse = null; // FIXME - quick hack to export the result of an interactive command
	
	protected int doParser(IParser p, boolean restart) { 
		boolean checkMode = Utils.TEST_SOLVER.equals(smtConfig.solvername);
		boolean abortMode = smtConfig.abort && !checkMode;

		if (restart && solver != null) {
		    solver.exit();
		    solver = null;
		}
		if (restart || solver == null) solver = startSolver(smtConfig, smtConfig.solvername, smtConfig.executable);
		if (solver == null) return 1;
		IKeyword printSuccessKW = smtConfig.exprFactory.keyword(Utils.PRINT_SUCCESS);
		if (smtConfig.nosuccess) {
			solver.set_option(printSuccessKW,Utils.FALSE);
		}
		if (smtConfig.logic != null) solver.set_logic(smtConfig.logic,null);
		// FIXME: if (smtConfig.verboseSolver) 
		int retcode = 0;
		try {
			IResponse result = null;
			ICommand command = null;
			while (!(command instanceof ICommand.Iexit) && !p.isEOD()) {
				try {
					command = p.parseCommand();
					if (command == null) {
						retcode = 1;
						if (abortMode) {
							if (!smtConfig.interactive) {
								smtConfig.log.logDiag("Aborting because of a parsing error");
								break;
							}
							p.abortLine();
						}
						result = p.lastError();
						continue;
					}

					if (smtConfig.echo) {
						smtConfig.log.logDiag(smtConfig.defaultPrinter.toString(command));
					}
					else if (smtConfig.verbose != 0) smtConfig.log.logDiag("Command to execute: " +  command);
					result = command.execute(solver);
					if (result.isError()) {
						IResponse.IError eresult = (IResponse.IError)result;
						if (eresult.pos() == null && command instanceof IPosable) {
							// This is in case we omitted setting the position when the error
							// was generated - we set it to the whole command.  However, we ought
							// to root out all such omissions and correct them where possible.
							eresult.setPos(((IPosable)command).pos());
						}
						smtConfig.log.logError(eresult);
						retcode = 1;
						if (abortMode) {
							if (!smtConfig.interactive) {
								smtConfig.log.logDiag("Aborting because of a type-checking error");
								break;
							}
							p.abortLine();
						}
					} else if (result.toString().equals("success")) {  // FIXME need a better way to do this
						if (!smtConfig.nosuccess) smtConfig.log.logOut(result);
					} else if (!result.toString().isEmpty()) { // FIXME - is there a more abstract way to do this?
						smtConfig.log.logOut(result);
					}
					lastResponse = result;
				} catch (AbortParseException e) {
					smtConfig.topLevel = true;
					if (abortMode) {
						if (!smtConfig.interactive) {
							smtConfig.log.logDiag("Aborting because of a lexical error");
							break;
						}
						p.abortLine();
					}
				}
			}
			checkSatStatus = solver.checkSatStatus();
		} catch (IOException e) {
			error("IOException reading input: " + e);
			retcode = 2;
		} catch (ParserException e) {
			error("ParserException reading input: " + e);
			retcode = 2;
		} catch (StackOverflowError e) {
			error("Stack overflow while processing input");
			retcode = 2;
		} catch (OutOfMemoryError e) {
			error("Out of memory while processing input");
			retcode = 2;
		}
		solver.forceExit();  // Just in case the solver was not explicitly exited
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("Exiting program");
		return retcode;
	}
	
	/** Parses the command-line, setting any option in the given configuration argument. */
	public int processCommandLine(String[] args, SMT.Configuration options) {
		//smtConfig.log.logDiag("#Start processing command-line");
		// Handle smtConfig
		int i = 0;
		while (i < args.length) {
			String s = args[i++];
			if ("--solver".equals(s) || "-s".equals(s)) {
				if (i >= args.length) {
					error("The --solver option expects an argument");
					usage();
					return 1;
				}
				options.solvername = args[i++];

			} else if ("--exec".equals(s) || "-e".equals(s)) {
				if (i >= args.length) {
					error("The --exec option expects an argument");
					usage();
					return 1;
				}
				options.executable = args[i++]; 

			} else if ("--logics".equals(s) || "-L".equals(s)) {
				if (i >= args.length) {
					error("The --logics option expects an argument");
					usage();
					return 1;
				}
				options.logicPath = args[i++];
				if (options.logicPath != null && options.logicPath.trim().length()==0) options.logicPath = null;

			} else if ("--diag".equals(s)) {
				if (i >= args.length) {
					error("The --diag option expects an argument");
					usage();
					return 1;
				}
				options.diag = args[i++];

			} else if ("--out".equals(s)) {
				if (i >= args.length) {
					error("The --out option expects an argument");
					usage();
					return 1;
				}
				options.out = args[i++];

			} else if ("--port".equals(s)) {
				if (i >= args.length) {
					error("The --port option expects an argument");
					usage();
					return 1;
				}
				options.port = Integer.valueOf(args[i++]).intValue();

			} else if ("--text".equals(s)) {
				if (i >= args.length) {
					error("The --text option expects an argument");
					usage();
					return 1;
				}
				options.text = args[i++];

			} else if ("--verbose".equals(s) || "-v".equals(s)) {
				if (i >= args.length) {
					error("The --verbose option expects an integer argument");
					usage();
					return 1;
				}
				try {
					options.verbose = Integer.valueOf(args[i++]);
				} catch (NumberFormatException e) {
					error("The --verbose option expects an integer argument");
					usage();
					return 1;
				}
				if (options.verbose < 0) {
					error("The argument to --verbose must be non-negative");
					usage();
					return 1;
				}

			} else if ("--help".equals(s) || "-h".equals(s)) {
				help();
				return -1;
			} else if ("--version".equals(s)) {
				System.out.println(Version.version());
				return -1;
			} else if ("--echo".equals(s)) {
				options.echo = true;
			} else if ("--nosuccess".equals(s) || "-q".equals(s)) {
				options.nosuccess = true;
			} else if ("--abort".equals(s)) {
				options.abort = true;
			} else if ("--relax".equals(s)) {
				options.relax = true;
            } else if ("--noshow".equals(s)) {
                options.noshow = true;
            } else if ("--seed".equals(s)) {
                options.seed = 0;
                if (i >= args.length) {
                    error("The --seed option expects an argument");
                    usage();
                    return 1;
                }
                String a = args[i];
                try {
                    options.seed = Integer.parseInt(a);
                    i++;
                } catch (NumberFormatException e) {
                    error("The --seed option expects an integer value: " + a);
                    usage();
                    return 1;
                }
			} else if (s.startsWith("-")) {
				error("Unknown option: " + s);
				usage();
				return 1;
			} else {
				if (options.files == null) options.files = new LinkedList<String>();
				options.files.add(s);
			}
		}
		
		props = readProperties();

		if (options.logicPath == null) options.logicPath = props.getProperty(Utils.PROPS_LOGIC_PATH);
		if (options.logicPath != null) {
			options.logicPath = options.logicPath.trim();
			if (options.logicPath.length() == 0) options.logicPath = null;
		}

		if (options.out != null) {
			try {
				options.log.out = new PrintStream(options.out);
			} catch (java.io.IOException e) {
				options.log.logOut("Failed to open output stream on " + options.out);
			}
		}
		if (options.diag != null) {
			try {
				options.log.diag = new PrintStream(options.diag);
			} catch (java.io.IOException e) {
				options.log.logOut("Failed to open output stream on " + options.diag);
			}
		}
		if (options.files != null && !options.files.isEmpty() && options.port >= 0) {
			error("You may not specify both a port and file input");
			usage();
			return 1;
		}

		if (options.solvername == null) {
			String p = props.getProperty(Utils.PROPS_DEFAULT_SOLVER);
			if (p == null || p.isEmpty()) p = Utils.TEST_SOLVER;
			options.solvername = p;
			if (options.executable != null) {
				error("If you specify an executable, you must also specify a solver");
				usage();
				return 1;
			}
		}
		return 0;
	}
	
	/** Starts the solver with the given name and executable, preset according to the given configuration.
	 * If executable is null, then an executable path is looked for in the org.smtlib.SMT_EXE_solvername 
	 * property or the SMT_EXE_solvername environment variable.
	 * @param smtConfig the configuration object to use for solver settings
	 * @param solvername the name of the solver to use
	 * @param executable the executable path
	 * @return the ISolver object, or null if errors happened
	 */
	/*@Nullable*/
	public ISolver startSolver(SMT.Configuration smtConfig, /*@NonNull*/String solvername, /*@Nullable*/String executable) {
		/*@NonNull*/ ISolver solver;
		Class<? extends Object> adapterClass = null;
		String[] command = null;
		String adapterClassName = null;
		
		// Find the adapter, executable, command
		if (!solvername.equals(Utils.TEST_SOLVER)) {
			String solvernameNormalized = solvername.replace('-','_').replace('.', '_');
			// But use this if it is specified
			if (props != null) {
				adapterClassName = props.getProperty(Utils.PROPS_SOLVER_PREFIX + solvername + Utils.PROPS_ADAPTER_SUFFIX);
				if (adapterClassName != null) try {
					adapterClass = Class.forName(adapterClassName);
				} catch (ClassNotFoundException e) {
					adapterClass = null;
				}
			}

			if (adapterClass == null) {
				adapterClassName = "org.smtlib.solvers.Solver_" + solvernameNormalized;
				try {
					adapterClass = Class.forName(adapterClassName);
				} catch (ClassNotFoundException e) {
					adapterClass = null;
				}
			}

			// But otherwise presume the solver is a standard smt solver
            if (adapterClass == null) {
            	adapterClass = org.smtlib.solvers.Solver_smt.class;
            	adapterClassName = "org.smtlib.solvers.Solver_smt";
            }
		
			String propName = Utils.PROPS_SOLVER_PREFIX + solvername + Utils.PROPS_COMMAND_SUFFIX;
			String commandString = null;
			if (props != null) {
				commandString = props.getProperty(propName);
				if (commandString != null && !commandString.isEmpty()) {
					command = commandString.split(",");
					if (command.length == 0) {
						error("The command specified for " + propName + " appears to have no content");
						usage();
						return null;
					}
				}
			}

			if (executable == null && props != null) {
				executable = props.getProperty(Utils.PROPS_SOLVER_PREFIX + solvername + Utils.PROPS_EXEC_SUFFIX);
				if (executable != null && executable.trim().isEmpty()) executable = null;
			}
			
			if (command != null && executable != null) command[0] = executable;
			
			if (executable == null && command == null) {
				error("Neither an executable nor a command specified for a solver named " + solvername );
				usage();
				return null;
			}
		} else {
			adapterClass = org.smtlib.solvers.Solver_test.class;
		}
		
		try {
			Constructor<?> constructor;
			if (command == null) {
	            constructor = adapterClass.getConstructor(SMT.Configuration.class,String.class);
				solver = (ISolver)(constructor.newInstance(smtConfig,executable));
			} else {
	            constructor = adapterClass.getConstructor(SMT.Configuration.class,command.getClass());
				solver = (ISolver)(constructor.newInstance(smtConfig,command));
			}
			//System.out.println("SMT START " + solver + " " + command);
			IResponse res = solver.start();
            //System.out.println("SMT RES " + res);
			if (res.isError()) {
				smtConfig.log.logError((IResponse.IError)res);
				error(solvername + " failed to start: " + ((IResponse.IError)res).errorMsg());
				return null;
			}
		} catch (NoSuchMethodException e) {
			error("Could not find an appropriate constructor in " + adapterClassName + ": " + e);
			usage();
			return null;
		} catch (IllegalAccessException e) {
			error("Could not find an adapter class named " + adapterClassName + ": " + e);
			usage();
			return null;
		} catch (InstantiationException e) {
			error("Could not create an instance of a " + adapterClassName + ": " + e);
			usage();
			return null;
		} catch (InvocationTargetException e) {
			e.printStackTrace();
			error("Could not invoke the constructor of " + adapterClassName + ": " + e);
			usage();
			return null;
		} catch (SolverProcess.ProverException e) {
			error("Problem in starting or running " + solvername + ": " + e.getMessage());
			return null;
		}
		return solver;
	}
	
	/** Helper function to log a command-line error */
	protected void error(String msg) {
		smtConfig.log.logError(smtConfig.responseFactory.error(msg));
	}
	
	// FIXME - combine, update, document usage() and help()
	/** Prints a summary of the command-line arguments */
	public void usage() {
		System.out.println("Usage: java org.smtlib.SMT [args] [file]");
		System.out.println("       --help [-h]");
		System.out.println("       --version");
		System.out.println("       --verbose [-v] <int>");
		System.out.println("       --solver [-s] <solvername>");
		System.out.println("       --exec   [-e] <path>");
		System.out.println("       --logics [-L] <path>");
		System.out.println("       --out         <filename or 'stdout' or 'stderr'>");
		System.out.println("       --diag        <filename or 'stdout' or 'stderr'>");
		System.out.println("       --port        <int>");
		System.out.println("       --text        <string>");
		System.out.println("       --echo   [-e]");
		System.out.println("       --abort");
		System.out.println("       --noshow");
		System.out.println("       --nosuccess   [-q]");
		System.out.println("       --relax  [-r]");

	}
	
	/** Prints a verbose message about command line arguments */
	public void help() {
		System.out.println("The main routine of this Java executable is org.smtlib.SMT,");
		System.out.println("    but the jar file is an executable jar file, and can be run");
		System.out.println("    using the command: java -jar jSMTLIB.jar ");
		System.out.println("THIS IS AN ALPHA VERSION AND STILL BEING CORRECTED AND POLISHED");
		System.out.println("The command-line arguments are typical options and files.");
		System.out.println("If no files are present, commands are read from standard input");
		System.out.println("    until a control-D is read, indicating end of input.");
		System.out.println("If files are listed on the command-line they are processed");
		System.out.println("    after all options are read and in the order the fies are listed.");
		System.out.println("Option names have a long version, beginning with --");
		System.out.println("    and an abbreviated version, beginning with a single -.");
		System.out.println("The recognized options are these:");
		System.out.println("    -h, --help : prints this help message and exits");
		System.out.println("        --version : prints the version of this application and exits");
		System.out.println("    -v, --verbose <int>: enables verbose mode, so more stuff is printed");
// FIXME-NOW - distinguish verbose for app and verbose for solver?
		System.out.println("    -s, --solver <name> : indicates the SMT solver to use (or 'test')");
		System.out.println("        The name of the adaptor class is \"org.smtlib.solvers.Solver_\" + <name>");
		System.out.println("    -e, --exec <path> : indicates the SMT solver executable to use");
		System.out.println("        The argument is the pathname of the executable for the named solver");
// FIXME - if not specified, uses the value of...		
		System.out.println("    -L, --logics <path>: the directory containing SMT-LIB logic and theory ");
		System.out.println("              definitions (default is to use the internal, built-in definitions)");
		System.out.println("        --out <filename or 'stdout' or 'stderr'>: where to send normal and error output");
		System.out.println("        --diag <filename or 'stdout' or 'stderr'>: where to send verbose (diagnostic) output");
		System.out.println("        --port <number>: which port to use for client-server communication");
		System.out.println("        --text: text to process (ignoring file and port input)");
		System.out.println("        --echo: if enabled, commands are echoed to diagnostic output when successfully parsed");
		System.out.println("        --abort: if enabled, an error causes immediate exit");
		System.out.println("        --noshow: if enabled, error location information is not shown");
		System.out.println("    -q, --nosuccess: if enabled, 'success' responses are suppressed");
		System.out.println("        --relax: if enabled, extensions to strict SMT-LIB are permitted");
		System.out.println("This software is Copyright 2010 by David R. Cok. The accompanying LICENSE ");
		System.out.println("    file describes the conditions under which it may be used.");
	}
	
	/** This class is used to turn internal bugs that we do not want to try
	 * to recover into exceptions that can be reported */
	public static class InternalException extends RuntimeException {
		private static final long serialVersionUID = 1L;

		public InternalException(String msg) {
			super(msg);
		}
	}
	
	/** This class is a prompter used when more data is needed from a data source */
	public static class Prompter implements CharSequenceInfinite.IPrompter {
		public SMT.Configuration smtConfig;
		
		/** Creates a prompter object - the object knows how to prompt for input based on current settings and state */
		public Prompter(SMT.Configuration smtConfig) { this.smtConfig = smtConfig; }
		
		/** Prints out the prompt (with no new-line), if a prompt is wanted */
		@Override
		public void prompt() {
			if (smtConfig.interactive) {
				String p = smtConfig.topLevel ? smtConfig.prompt : smtConfig.prompt2;
				smtConfig.log.logOutNoln(p);
				smtConfig.log.indent(p);
			}
		}
	}
	
	public static interface ILogicFinder {
		/** Looks for a logic with the given name, returning an InputStream by which to read it
		 * @param smtConfig the current smt configuration, indicating where to look for logics
		 * @param logicName the name of the logic to find
		 * @param pos if not null, the textual position of the logicName, used for error messages
		 * @return an InputStream from which to read the logic
		 * @throws IOException if the file cannot be opened or other I/O exception happens
		 * @throws Utils.SMTLIBException if the logic file cannot be found
		 */
		/*@Mutable*/ InputStream find(Configuration smtConfig, String logicName, /*@Nullable*/IPos pos) throws IOException, Utils.SMTLIBException;
	}
	
	/** An instance of a logic finder that looks in the configuration's logicPath, or (if there is no such path) as a file on the system CLASSPATH */
	public static ILogicFinder logicFinder = new ILogicFinder() {
		@Override
		public /*@Mutable*/ InputStream find(Configuration smtConfig, String name, /*@Nullable*/IPos pos) throws IOException, Utils.SMTLIBException {
			String path = smtConfig.logicPath;
			if (path == null) {
				URL url = ClassLoader.getSystemResource(name + org.smtlib.Utils.SUFFIX);
				if (url == null) {
					throw new Utils.SMTLIBException(smtConfig.responseFactory.error("No logic file found for " + name, pos));
				}
				return url.openStream();
			} else {
				for (String d: path.split(File.pathSeparator)) {
					File f = new File(d + File.separator + name + org.smtlib.Utils.SUFFIX);
					if (f.exists()) return new FileInputStream(f);
				}
				if (this.getClass().getClassLoader().getResource(name + org.smtlib.Utils.SUFFIX) != null) {
					return this.getClass().getClassLoader().getResourceAsStream(name + org.smtlib.Utils.SUFFIX);
				}
				throw new Utils.SMTLIBException(smtConfig.responseFactory.error("No logic file found for " + name + " on path \"" + path + "\"", pos));
			}
		}
	};
}
