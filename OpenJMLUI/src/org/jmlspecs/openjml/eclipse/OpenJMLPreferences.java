/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2024 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;

/**
 * Main OpenJML preferences page — shows two tabs:
 * <ol>
 *   <li>"Plugin and LSP Settings"</li>
 *   <li>"OpenJML Tool Options"</li>
 * </ol>
 *
 * The same content is also accessible as individual sub-pages in the
 * preferences tree (see {@link OpenJMLPluginPage} and
 * {@link OpenJMLToolPage}), which causes the tree node to show a twistie.
 *
 * <p>Field creation and lifecycle management live in
 * {@link OpenJMLPreferencesBase}.
 */
public class OpenJMLPreferences extends OpenJMLPreferencesBase {

    /**
     * Returns the zero-based index of the tab to show initially.
     * Subclasses ({@link OpenJMLPluginPage}, {@link OpenJMLToolPage}) override
     * this to pre-select their respective tab when opened from the tree.
     */
    protected int getInitialTab() { return 0; }

    @Override
    protected Control createContents(Composite parent) {
        TabFolder tabFolder = new TabFolder(parent, SWT.NONE);
        tabFolder.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));

        createPluginAndLspFields(addTab(tabFolder, "Plugin and LSP Settings"));
        createToolOptionFields(addTab(tabFolder, "OpenJML Tool Options"));

        tabFolder.setSelection(getInitialTab());
        return tabFolder;
    }

    /**
     * Creates a tab with an inner composite that has 8 px padding on all sides
     * (so field editor content doesn't crowd the tab border) and returns the
     * inner composite for field editors to populate.
     */
    private Composite addTab(TabFolder folder, String title) {
        TabItem item = new TabItem(folder, SWT.NONE);
        item.setText(title);

        // Outer composite: provides padding inside the tab.
        Composite outer = new Composite(folder, SWT.NONE);
        GridLayout outerLayout = new GridLayout(1, false);
        outerLayout.marginWidth = 8;
        outerLayout.marginHeight = 8;
        outer.setLayout(outerLayout);
        item.setControl(outer);

        // Inner composite: managed by field editors and finalizeTab().
        Composite inner = new Composite(outer, SWT.NONE);
        inner.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
        return inner;
    }
}
