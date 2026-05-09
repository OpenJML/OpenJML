/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

/**
 * Preferences sub-page: "Plugin and LSP Settings".
 *
 * <p>Registered as a child of the main OpenJML page in {@code plugin.xml}
 * (giving the tree node a twistie).  Opens the same tabbed
 * {@link OpenJMLPreferences} page with Tab 1 pre-selected.
 */
public class OpenJMLPluginPage extends OpenJMLPreferences {

    @Override
    protected int getInitialTab() { return 0; }
}
