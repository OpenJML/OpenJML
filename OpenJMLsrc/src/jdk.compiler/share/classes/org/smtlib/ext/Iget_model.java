package org.smtlib.ext;

import org.smtlib.ICommand;

/** Interface to be implemented by all objects representing SMT-LIB get-model commands;
 * get-model is not part of SMT-LIB but may become so in the future. */
public interface Iget_model extends ICommand {
	// Not expected to have any arguments
}