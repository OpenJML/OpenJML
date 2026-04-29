/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;

/**
 * Registers default preference values for the OpenJML plugin.
 *
 * <p>Declared via the {@code org.eclipse.core.runtime.preferences} extension
 * point in {@code plugin.xml}.  Eclipse calls {@link #initializeDefaultPreferences()}
 * before any preference page is opened and when "Restore Defaults" is clicked,
 * ensuring the defaults are always in effect.
 */
public class OpenJMLPreferenceInitializer extends AbstractPreferenceInitializer {

    @Override
    public void initializeDefaultPreferences() {
        IPreferenceStore store = org.openjml.ui.Activator.getDefault().getPreferenceStore();
        OpenJMLOptions.initializeDefaults(store);
    }
}
