/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

/**
 * Preferences sub-page: "Project Options".
 *
 * <p>Registered as a child of the main OpenJML page in {@code plugin.xml}
 * (giving the tree node a twistie).  Opens the same tabbed
 * {@link OpenJMLPreferences} page with Tab 4 pre-selected.
 */
public class OpenJMLProjectPage extends OpenJMLPreferences {

    @Override
    protected int getInitialTab() { return 3; }
}
