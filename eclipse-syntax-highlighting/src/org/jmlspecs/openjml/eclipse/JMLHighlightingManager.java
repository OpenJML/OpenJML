/**
 * 
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.jdt.internal.ui.JavaPlugin;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;



// This class needs to refer to a lot of static constants several times over.
import static org.eclipse.jdt.ui.PreferenceConstants.EDITOR_FOLDING_PROVIDER;
import static org.jmlspecs.openjml.eclipse.HighlightingFoldingStructureProvider.PROVIDER_ID;
import static org.jmlspecs.openjml.eclipse.Options.innerFoldingProvider;
import static org.jmlspecs.openjml.eclipse.Options.highlightEnableKey;;

/**
 * This class is used to keep the JML plugin's highlighting preference
 * {@link Options.highlightEnableKey} and the JDT's FoldingStructureProvider
 * {@link org.eclipse.jdt.ui.PreferenceConstants.EDITOR_FOLDING_PROVIDER}
 * synchronized; that is, the JML plugin's preference should always be the same
 * as whether or not the JDT's FoldingStructureProvider is actually set to the
 * JML highlighting one while the plugin is running.
 * 
 *  <p>
 *  The reason these two separate preferences are needed, instead of the JML
 *  plugin setting the JDT's preferences directly when the highlighting checkbox
 *  is checked, is twofold:
 *  <ol><li>JML has highlighting enabled by default, and the JDT does not
 *  use our FoldingStructureProvider by default</li>
 *  <li>If anybody uninstalls the JML plugin, it would be a good idea to not
 *  mess with their Java folding settings, only whether or not JML is
 *  highlighted. This means that when the JML plugin is deactivated, it cannot
 *  still be set as the FoldingStructureProvider in case it is being uninstalled.
 *  If JML folding is ever introduced, then this reason may go away depending on
 *  the details of how that's implemented, but the first reason will probably
 *  remain.</ol>
 *  </p>
 * 
 * @author dhouck
 */
public class JMLHighlightingManager {
	/**
	 * A reference to the JDT preference store, so that we can go against the
	 * API documentation and change or read its preferences to set the
	 * FoldingProvider to our own if appropriate.
	 */
	private static final IPreferenceStore JDT_PREFS =
			JavaPlugin.getDefault().getPreferenceStore();
	
	/**
	 * A reference to the JML preference store. We use the Options class when
	 * possible, but that does not allow setting a preference by Boolean
	 * value or adding PropertyChangeListeners.
	 */
	private static final IPreferenceStore JML_PREFS =
			Activator.getDefault().getPreferenceStore();
	
	/**
	 * A PropertyChangeListener to install on the JML preference store, allowing
	 * us to notice when the option to enable highlighting is enabled or disabled
	 * and react accordingly with the JDT FoldingProvider option. To avoid
	 * undue recursion with the JDT listener, this only does anything when the
	 * property value actually changes.
	 */
	private static final IPropertyChangeListener JML_PROPERTY_CHANGE_LISTENER =
			new IPropertyChangeListener() {
				
				@Override
				public void propertyChange(PropertyChangeEvent event) {
					if (event.getProperty().equals(highlightEnableKey) &&
						! event.getOldValue().equals(event.getNewValue()))
					{
						// We only set this property as a boolean, and its
						// default value is a boolean. We can assume this cast
						// is valid.
						if ((Boolean) event.getNewValue())
						{
							ensureHighlighting();
						}
						else
						{
							ensureNotHighlighting();
						}
					}
				}
			};
	
	/**
	 * A PropertyChangeListener to install on the JDT preference store, allowing
	 * us to notice when the FoldingProvider changes and react accordingly with
	 * the JDT option for highlighting JML. Although it would not lead to undue
	 * recursion with the JDT listener, we avoid doing anything if the preference
	 * hasn't actually changed.
	 */
	private static final IPropertyChangeListener JDT_PROPERTY_CHANGE_LISTENER =
			new IPropertyChangeListener() {
				
				@Override
				public void propertyChange(PropertyChangeEvent event) {
					if (event.getProperty().equals(EDITOR_FOLDING_PROVIDER) &&
						! event.getOldValue().equals(event.getNewValue()))
					{
						JML_PREFS.setValue(highlightEnableKey,
								event.getNewValue().equals(PROVIDER_ID));
					}
				}
			};
	
	/**
	 * Makes sure that the JDT's current FoldingStructureProvider actually is
	 * the JML highlighting one, without changing the actual provided folding
	 * structure. Does not change the JML highlighting preference, just the JDT
	 * FoldingStructureProvider preference and the JML innerFoldingProvider
	 * preference if necessary.
	 */
	private static void ensureHighlighting()
	{
		String currentProviderID = JDT_PREFS.getString(EDITOR_FOLDING_PROVIDER);
		
		if (!currentProviderID.equals(PROVIDER_ID))
		{
			Options.setValue(innerFoldingProvider, currentProviderID);
			JDT_PREFS.setValue(EDITOR_FOLDING_PROVIDER, PROVIDER_ID);
		}
	}
	
	/**
	 * Makes sure that the JDT's current FoldingStructureProvider actually is
	 * not the JML highlighting one, without changing the actual provided folding
	 * structure. Does not change the JML highlighting preference, just the JDT
	 * FoldingStructureProvider preference if necessary.
	 */
	private static void ensureNotHighlighting()
	{
		String currentProviderID = JDT_PREFS.getString(EDITOR_FOLDING_PROVIDER);
		
		if (currentProviderID.equals(PROVIDER_ID))
		{
			JDT_PREFS.setValue(EDITOR_FOLDING_PROVIDER, innerFoldingProvider);
		}
	}
	
	/**
	 * Ensures that the JDT's current FoldingStructureProvider is the JML
	 * highlighting one iff the JML highlighting preference is set, and install
	 * the listeners to keep the two preferences in sync. The first part is
	 * necessary to enable JML highlighting by default on the first installation
	 * of this plugin and because of the shutDown method.
	 */
	public static void startUp()
	{
		if (Options.isOption(highlightEnableKey))
		{
			ensureHighlighting();
		}
		else
		{
			ensureNotHighlighting();
		}
		
		JDT_PREFS.addPropertyChangeListener(JDT_PROPERTY_CHANGE_LISTENER);
		JML_PREFS.addPropertyChangeListener(JML_PROPERTY_CHANGE_LISTENER);
	}
	
	/**
	 * Uninstalls the listeners that keep the JML highlighting preference and
	 * the JDT current FoldingStructureProvider in sync, and then ensures that
	 * the JDT's provider is not the JML highlighting one. This last step is to
	 * ensure that anybody uninstalling the JML plugin doesn't have trouble with
	 * the code folding in Java editors.
	 */
	public static void shutDown()
	{
		JDT_PREFS.removePropertyChangeListener(JDT_PROPERTY_CHANGE_LISTENER);
		JML_PREFS.removePropertyChangeListener(JML_PROPERTY_CHANGE_LISTENER);
		ensureNotHighlighting();
	}
}
