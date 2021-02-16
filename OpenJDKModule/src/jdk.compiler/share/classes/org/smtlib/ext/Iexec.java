package org.smtlib.ext;

import org.smtlib.ICommand;

/** Interface to be implemented by all objects representing SMT-LIB exec commands. */
public interface Iexec extends ICommand {
	/** The script to execute */
	IScript script();
}