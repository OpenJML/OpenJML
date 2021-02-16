package org.smtlib.ext;

import java.util.List;

import org.smtlib.ICommand;
import org.smtlib.IExpr.IIdentifier;

/** Interface to be implemented by all objects representing SMT-LIB what commands. */
public interface Iwhat extends ICommand {
	/** The ids to look for and describe */
	List<IIdentifier> ids();
}