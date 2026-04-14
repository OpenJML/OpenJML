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
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;

/**
 * Main OpenJML preferences page — shows three tabs:
 * <ol>
 *   <li>"Plugin and LSP Settings"</li>
 *   <li>"Syntax Colors"</li>
 *   <li>"OpenJML Tool Options"</li>
 * </ol>
 *
 * The same content is also accessible as individual sub-pages in the
 * preferences tree (see {@link OpenJMLPluginPage}, {@link OpenJMLSyntaxColorPage},
 * and {@link OpenJMLToolPage}), which causes the tree node to show a twistie.
 *
 * <p>Field creation and lifecycle management live in
 * {@link OpenJMLPreferencesBase}.
 */
public class OpenJMLPreferences extends OpenJMLPreferencesBase {

    /**
     * Returns the zero-based index of the tab to show initially.
     * Subclasses ({@link OpenJMLPluginPage}, {@link OpenJMLSyntaxColorPage},
     * {@link OpenJMLToolPage}) override this to pre-select their tab.
     */
    protected int getInitialTab() { return 0; }

    @Override
    protected Control createContents(Composite parent) {
        Composite page = new Composite(parent, SWT.NONE);
        GridLayout pageLayout = new GridLayout(1, false);
        pageLayout.marginWidth = 0;
        pageLayout.marginHeight = 0;
        pageLayout.verticalSpacing = 4;
        page.setLayout(pageLayout);

        TabFolder tabFolder = new TabFolder(page, SWT.NONE);
        tabFolder.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));

        createPluginAndLspFields(addTab(tabFolder, "Plugin and LSP Settings"));
        createSyntaxColorFields(addTab(tabFolder, "Syntax Colors"));
        createToolOptionFields(addTab(tabFolder, "OpenJML Tool Options"));

        tabFolder.setSelection(getInitialTab());

        Label hint = new Label(page, SWT.NONE);
        hint.setText("\"Restore Defaults\" and \"Apply\" act on all three tabs.");
        hint.setLayoutData(new GridData(SWT.RIGHT, SWT.CENTER, true, false));

        return page;
    }

    /**
     * Creates a tab with an inner composite that has 8 px padding on all sides
     * and returns the inner composite for content population.
     */
    private Composite addTab(TabFolder folder, String title) {
        TabItem item = new TabItem(folder, SWT.NONE);
        item.setText(title);

        Composite outer = new Composite(folder, SWT.NONE);
        GridLayout outerLayout = new GridLayout(1, false);
        outerLayout.marginWidth  = 8;
        outerLayout.marginHeight = 8;
        outer.setLayout(outerLayout);
        item.setControl(outer);

        Composite inner = new Composite(outer, SWT.NONE);
        inner.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
        return inner;
    }
}
