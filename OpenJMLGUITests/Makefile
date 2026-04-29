## ============================================================================
## OpenJMLGUITests/Makefile — SWTBot GUI tests for the OpenJMLUI Eclipse plugin
## ============================================================================
##
## QUICK START
## -----------
##   make fetch-eclipse        # one-time: download Eclipse + install SWTBot
##   make run-install-test     # install OpenJML via UI, verify in Installed Software
##
## VARIABLES (all overridable on the command line)
##   ECLIPSE_RELEASE  — Eclipse simultaneous-release name, e.g. 2026-03 (default)
##   UPDATE_SITE      — p2 update site URL for OpenJML (default: local file:// path)
##   ECLIPSE_SRC      — path to an existing Eclipse .app (macOS) or eclipse dir (Linux)
##                      to seed the pristine cache instead of downloading.
##                      Example: make fetch-eclipse ECLIPSE_SRC=/path/to/Eclipse.app
##
## PLATFORM NOTES
##   macOS  — tested; SWT requires -XstartOnFirstThread, handled by eclipse binary.
##   Linux  — the do-run-tests recipe prepends xvfb-run automatically.
##   Windows — not supported.
## ============================================================================

mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
UITEST      := $(patsubst %/,%,$(dir $(mkfile_path)))
REPO_ROOT   := $(UITEST)/..

## --------------------------------------------------------------------------
## Eclipse release to download
## --------------------------------------------------------------------------
ECLIPSE_RELEASE ?= 2026-03

## --------------------------------------------------------------------------
## Platform detection
## --------------------------------------------------------------------------
UNAME_S := $(shell uname -s)
UNAME_M := $(shell uname -m)

ifeq ($(UNAME_S),Darwin)
  ifeq ($(UNAME_M),arm64)
    ECLIPSE_PLATFORM := macosx-cocoa-aarch64
  else
    ECLIPSE_PLATFORM := macosx-cocoa-x86_64
  endif
  ECLIPSE_EXT      := dmg
  ECLIPSE_PROFILE  := epp.package.committers
  ## Inside the macOS .app bundle
  PRISTINE_HOME    = $(PRISTINE_DIR)/Eclipse.app/Contents/Eclipse
  PRISTINE_BIN     = $(PRISTINE_DIR)/Eclipse.app/Contents/MacOS/eclipse
  TEST_HOME        = $(TEST_ECLIPSE)/Eclipse.app/Contents/Eclipse
  TEST_BIN         = $(TEST_ECLIPSE)/Eclipse.app/Contents/MacOS/eclipse
  TEST_PLUGINS     = $(TEST_HOME)/plugins
  DMG_MOUNT        := /tmp/openjml-eclipse-dmg-mount
  ## rsync the whole .app bundle
  COPY_CMD          = rsync -a --delete "$(PRISTINE_DIR)/Eclipse.app/" "$(TEST_ECLIPSE)/Eclipse.app/"
else
  ECLIPSE_PLATFORM := linux-gtk-$(UNAME_M)
  ECLIPSE_EXT      := tar.gz
  ECLIPSE_PROFILE  := epp.package.committers
  PRISTINE_HOME    = $(PRISTINE_DIR)/eclipse
  PRISTINE_BIN     = $(PRISTINE_DIR)/eclipse/eclipse
  TEST_HOME        = $(TEST_ECLIPSE)/eclipse
  TEST_BIN         = $(TEST_ECLIPSE)/eclipse/eclipse
  TEST_PLUGINS     = $(TEST_HOME)/plugins
  COPY_CMD          = rsync -a --delete "$(PRISTINE_DIR)/eclipse/" "$(TEST_ECLIPSE)/eclipse/"
  ## Prepend xvfb-run on headless Linux
  XVFB             := xvfb-run --auto-servernum --server-args="-screen 0 1280x1024x24"
endif

## --------------------------------------------------------------------------
## Download URL
## --------------------------------------------------------------------------
ECLIPSE_FILE := eclipse-committers-$(ECLIPSE_RELEASE)-R-$(ECLIPSE_PLATFORM).$(ECLIPSE_EXT)
ECLIPSE_CDN  := https://download.eclipse.org/technology/epp/downloads/release/$(ECLIPSE_RELEASE)/R
ECLIPSE_URL  := $(ECLIPSE_CDN)/$(ECLIPSE_FILE)

## --------------------------------------------------------------------------
## Cache layout  (none of this is committed to source control)
## --------------------------------------------------------------------------
CACHE_DIR    := $(UITEST)/eclipse-cache
PRISTINE_DIR := $(CACHE_DIR)/pristine
DOWNLOAD_DIR := $(CACHE_DIR)/downloads
TEST_ECLIPSE := $(CACHE_DIR)/test-eclipse

## --------------------------------------------------------------------------
## SWTBot
## --------------------------------------------------------------------------
SWTBOT_SITE := https://download.eclipse.org/technology/swtbot/releases/latest/
SWTBOT_IUS  := org.eclipse.swtbot.eclipse.feature.group,org.eclipse.swtbot.eclipse.test.junit.feature.group

## --------------------------------------------------------------------------
## OpenJML update site
## Default: local sibling repo.  Override with a published URL when available.
## --------------------------------------------------------------------------
LOCAL_UPDATE_SITE := file://$(abspath $(REPO_ROOT)/../openjml.github.io/eclipse-update-site)
UPDATE_SITE       ?= $(LOCAL_UPDATE_SITE)
OPENJML_FEATURE   := org.openjml.OpenJMLFeature.feature.group

## Path to the openjml-lsp launcher used by the running tests.
OPENJML_LSP_PATH  := $(abspath $(REPO_ROOT)/OpenJMLlsp/openjml-lsp)

## --------------------------------------------------------------------------
## Build
## --------------------------------------------------------------------------
SRC_DIR     := $(UITEST)/src
CLASSES_DIR := $(UITEST)/build/classes
TEST_JAR    := $(UITEST)/build/org.openjml.OpenJMLGUITest_0.21.0.jar
RESULTS_DIR := $(UITEST)/build/results
TEST_WS     := $(UITEST)/test-ws

## Sentinel files inside the test-eclipse directory.
TEST_PREPARED_STAMP     := $(TEST_ECLIPSE)/.prepared
OPENJML_INSTALLED_STAMP := $(TEST_ECLIPSE)/.openjml-installed

## Test bundle symbolic name (must match MANIFEST.MF)
TEST_BUNDLE := org.openjml.OpenJMLGUITest

## Java sources
SRCS := $(shell find "$(SRC_DIR)" -name '*.java' 2>/dev/null)

## --------------------------------------------------------------------------
## Shared test-launch constants
## --------------------------------------------------------------------------
## SWTBot headless application (no socket connection needed, unlike uitestapplication)
SWTBOT_APP := org.eclipse.swtbot.eclipse.junit.headless.swtbottestapplication

## JUnit XML formatter class (Ant taskdef)
JUNIT_FORMATTER := org.apache.tools.ant.taskdefs.optional.junit.XMLJUnitResultFormatter

## Flags passed to the Eclipse launcher for every test invocation.
## Shared here so all launch recipes stay in sync.
ECLIPSE_LAUNCH_FLAGS := -nosplash --launcher.suppressErrors -application $(SWTBOT_APP) \
    -data "$(TEST_WS)" -testPluginName $(TEST_BUNDLE)

## VM arguments shared by all plugin test launches.
## Keep in one place so run-one-plugin-test, run-plugin-tests, and
## run-plugin-suite all behave identically.
PLUGIN_TEST_VMARGS = -Xmx1g -ea \
    "-Dopenjml.update.site=$(UPDATE_SITE)" \
    "-Dopenjml.lsp.server.path=$(OPENJML_LSP_PATH)" \
    -Dorg.eclipse.epp.mpc.ui.showMPCPopup=false \
    -Declipse.p2.unsignedPolicy=allow

## --------------------------------------------------------------------------
## Classpath construction (needs pristine Eclipse with SWTBot to be present)
## --------------------------------------------------------------------------
## These are evaluated lazily (= not :=) so they're correct after fetch-eclipse.
PLUGINS_DIR  = $(PRISTINE_HOME)/plugins

find_jar  = $(shell find "$(PLUGINS_DIR)" -maxdepth 1 -name "$(1)_*.jar" 2>/dev/null | sort -V | tail -1)

SWTBOT_ECLIPSE_JAR  = $(call find_jar,org.eclipse.swtbot.eclipse.finder)
SWTBOT_CORE_JAR     = $(call find_jar,org.eclipse.swtbot.swt.finder)
SWTBOT_ECLIPSE_CORE = $(call find_jar,org.eclipse.swtbot.eclipse.core)
SWTBOT_JUNIT_JAR    = $(call find_jar,org.eclipse.swtbot.junit4_x)
ECLIPSE_UI_JAR      = $(call find_jar,org.eclipse.ui)
ECLIPSE_RUNTIME_JAR = $(call find_jar,org.eclipse.core.runtime)
ECLIPSE_RESOURCES_JAR = $(call find_jar,org.eclipse.core.resources)
ECLIPSE_JDT_CORE_JAR  = $(call find_jar,org.eclipse.jdt.core)
ECLIPSE_JFACE_JAR   = $(call find_jar,org.eclipse.jface)
ECLIPSE_EQUINOX_JAR = $(call find_jar,org.eclipse.equinox.common)
ECLIPSE_CORE_JOBS_JAR = $(call find_jar,org.eclipse.core.jobs)
ECLIPSE_OSGI_JAR    = $(call find_jar,org.eclipse.osgi)
ECLIPSE_UI_WORKBENCH_JAR = $(call find_jar,org.eclipse.ui.workbench)
ECLIPSE_UI_IDE_JAR       = $(call find_jar,org.eclipse.ui.ide)
ECLIPSE_CORE_COMMANDS_JAR = $(call find_jar,org.eclipse.core.commands)
JUNIT4_JAR          = $(shell find "$(PLUGINS_DIR)" -maxdepth 1 -name "org.junit_*.jar" 2>/dev/null | sort -V | tail -1)
HAMCREST_JAR        = $(shell find "$(PLUGINS_DIR)" -maxdepth 1 -name "org.hamcrest_*.jar" 2>/dev/null | sort -V | tail -1)
LAUNCHER_JAR        = $(shell find "$(PRISTINE_HOME)/plugins" -maxdepth 1 -name "org.eclipse.equinox.launcher_*.jar" 2>/dev/null | head -1)
TEST_LAUNCHER_JAR   = $(shell find "$(TEST_HOME)/plugins" -maxdepth 1 -name "org.eclipse.equinox.launcher_*.jar" 2>/dev/null | head -1)

## org.eclipse.swt_*.jar is an empty fragment host; real SWT classes are platform-specific.
ifeq ($(UNAME_S),Darwin)
  ECLIPSE_SWT_JAR = $(shell find "$(PLUGINS_DIR)" -maxdepth 1 -name "org.eclipse.swt.cocoa.macosx.*.jar" 2>/dev/null | grep -v source | sort -V | tail -1)
else
  ECLIPSE_SWT_JAR = $(shell find "$(PLUGINS_DIR)" -maxdepth 1 -name "org.eclipse.swt.gtk.linux.*.jar" 2>/dev/null | grep -v source | sort -V | tail -1)
endif

COMPILE_CP = $(SWTBOT_ECLIPSE_JAR):$(SWTBOT_CORE_JAR):$(SWTBOT_ECLIPSE_CORE):$(SWTBOT_JUNIT_JAR):$(ECLIPSE_UI_JAR):$(ECLIPSE_UI_WORKBENCH_JAR):$(ECLIPSE_UI_IDE_JAR):$(ECLIPSE_CORE_COMMANDS_JAR):$(ECLIPSE_RUNTIME_JAR):$(ECLIPSE_RESOURCES_JAR):$(ECLIPSE_JDT_CORE_JAR):$(ECLIPSE_SWT_JAR):$(ECLIPSE_JFACE_JAR):$(ECLIPSE_EQUINOX_JAR):$(ECLIPSE_CORE_JOBS_JAR):$(ECLIPSE_OSGI_JAR):$(JUNIT4_JAR):$(HAMCREST_JAR)

## --------------------------------------------------------------------------
## Phony targets
## --------------------------------------------------------------------------
.PHONY: all fetch-eclipse build-tests prepare-test-eclipse \
        run-install-test install-openjml \
        run-menu-test run-nature-test run-markers-test run-action-test \
        run-fileicon-test run-preferences-test run-lsp-test \
        run-plugin-tests run-plugin-suite \
        clean clean-test-eclipse clean-downloads clean-cache clean-all help .FORCE

all: run-install-test

## --------------------------------------------------------------------------
## help
## --------------------------------------------------------------------------
help:
	@echo "Targets:"
	@echo "  fetch-eclipse        Download Eclipse Committers + install SWTBot (one-time)"
	@echo "  build-tests          Compile test sources and build test jar"
	@echo "  prepare-test-eclipse Copy pristine → test instance (fresh per run)"
	@echo "  run-install-test     Install OpenJML via UI wizard and verify (integration test)"
	@echo "  install-openjml      Install OpenJML via p2 director (headless, fast)"
	@echo "  run-preferences-test Run PreferencesPageTest: Preferences page loads and shows fields"
	@echo "  run-menu-test        Run MenuPresenceTest: menu items and toolbar buttons"
	@echo "  run-nature-test      Run NatureTest: Add/Remove JML Nature"
	@echo "  run-fileicon-test    Run FileIconTest: file-type icons for .java/.jml/.xyz"
	@echo "  run-lsp-test         Run LspFeatureTest: Find References, Check JML markers (needs LSP)"
	@echo "  run-action-test      Run ActionTest (legacy — use run-lsp-test)"
	@echo "  run-markers-test     Run MarkersTest (legacy — use run-lsp-test)"
	@echo "  run-plugin-tests     Run each test class separately: [PASS]/[FAIL] per class"
	@echo "  run-plugin-suite     Run AllPluginTests in one JVM: one [PASS]/[FAIL] at end (faster)"
	@echo "  clean                Remove build/ and test-ws/ (keeps eclipse-cache and sentinels)"
	@echo "  clean-test-eclipse   Remove test Eclipse copy + sentinels (forces re-prepare+re-install)"
	@echo "  clean-downloads      Remove downloaded archives (keeps pristine)"
	@echo "  clean-cache          Remove all of eclipse-cache/ including sentinels (re-download required)"
	@echo "  clean-all            clean + clean-cache"
	@echo ""
	@echo "Key variables (override on command line):"
	@echo "  ECLIPSE_RELEASE=$(ECLIPSE_RELEASE)"
	@echo "  UPDATE_SITE=$(UPDATE_SITE)"

## --------------------------------------------------------------------------
## fetch-eclipse
## --------------------------------------------------------------------------
$(PRISTINE_DIR)/.swtbot-installed: | $(DOWNLOAD_DIR)
	@echo "=== fetch-eclipse: preparing pristine Eclipse ==="
	@mkdir -p "$(PRISTINE_DIR)"
ifeq ($(ECLIPSE_EXT),dmg)
	## ---- macOS ----
	@if [ ! -d "$(PRISTINE_DIR)/Eclipse.app" ]; then \
	  if [ -n "$(ECLIPSE_SRC)" ] && [ -d "$(ECLIPSE_SRC)" ]; then \
	    echo "Seeding pristine from $(ECLIPSE_SRC) ..."; \
	    rsync -a "$(ECLIPSE_SRC)/" "$(PRISTINE_DIR)/Eclipse.app/"; \
	    xattr -dr com.apple.quarantine "$(PRISTINE_DIR)/Eclipse.app" 2>/dev/null || true; \
	    echo "Pristine seeded from local Eclipse."; \
	  else \
	    if [ ! -f "$(DOWNLOAD_DIR)/$(ECLIPSE_FILE)" ]; then \
	      echo "Downloading $(ECLIPSE_FILE) (may take several minutes) ..."; \
	      curl -L --progress-bar -o "$(DOWNLOAD_DIR)/$(ECLIPSE_FILE).tmp" "$(ECLIPSE_URL)" \
	        || { rm -f "$(DOWNLOAD_DIR)/$(ECLIPSE_FILE).tmp"; \
	             echo "ERROR: download failed.  URL: $(ECLIPSE_URL)"; exit 1; }; \
	      _type=$$(file -b "$(DOWNLOAD_DIR)/$(ECLIPSE_FILE).tmp"); \
	      case "$$_type" in \
	        *HTML*|*html*) \
	          echo "ERROR: download returned an HTML page, not a DMG."; \
	          echo "       URL: $(ECLIPSE_URL)"; \
	          echo "       Download manually and place at:"; \
	          echo "       $(DOWNLOAD_DIR)/$(ECLIPSE_FILE)"; \
	          rm -f "$(DOWNLOAD_DIR)/$(ECLIPSE_FILE).tmp"; exit 1 ;; \
	      esac; \
	      mv "$(DOWNLOAD_DIR)/$(ECLIPSE_FILE).tmp" "$(DOWNLOAD_DIR)/$(ECLIPSE_FILE)"; \
	      echo "Download complete."; \
	    else \
	      echo "Using cached download: $(DOWNLOAD_DIR)/$(ECLIPSE_FILE)"; \
	    fi; \
	    echo "Mounting DMG (this may take a moment) ..."; \
	    hdiutil attach "$(DOWNLOAD_DIR)/$(ECLIPSE_FILE)" \
	        -mountpoint "$(DMG_MOUNT)" -nobrowse \
	        || { echo "ERROR: hdiutil attach failed."; exit 1; }; \
	    _app=$$(ls -d "$(DMG_MOUNT)"/*.app 2>/dev/null | head -1); \
	    if [ -z "$$_app" ]; then \
	      echo "ERROR: no .app found in mounted DMG at $(DMG_MOUNT):"; ls "$(DMG_MOUNT)"; \
	      hdiutil detach "$(DMG_MOUNT)" 2>/dev/null; exit 1; \
	    fi; \
	    echo "Copying $$(basename $$_app) to pristine dir ..."; \
	    cp -R "$$_app" "$(PRISTINE_DIR)/Eclipse.app"; \
	    hdiutil detach "$(DMG_MOUNT)"; \
	    xattr -dr com.apple.quarantine "$(PRISTINE_DIR)/Eclipse.app" 2>/dev/null || true; \
	    echo "Eclipse extracted to pristine dir."; \
	  fi; \
	fi
else
	## ---- Linux ----
	@if [ ! -d "$(PRISTINE_DIR)/eclipse" ]; then \
	  if [ -n "$(ECLIPSE_SRC)" ] && [ -d "$(ECLIPSE_SRC)" ]; then \
	    echo "Seeding pristine from $(ECLIPSE_SRC) ..."; \
	    rsync -a "$(ECLIPSE_SRC)/" "$(PRISTINE_DIR)/eclipse/"; \
	  else \
	    if [ ! -f "$(DOWNLOAD_DIR)/$(ECLIPSE_FILE)" ]; then \
	      echo "Downloading $(ECLIPSE_FILE) ..."; \
	      curl -L --progress-bar -o "$(DOWNLOAD_DIR)/$(ECLIPSE_FILE)" "$(ECLIPSE_URL)" \
	        || { echo "ERROR: download failed."; exit 1; }; \
	    else \
	      echo "Using cached download: $(DOWNLOAD_DIR)/$(ECLIPSE_FILE)"; \
	    fi; \
	    echo "Extracting Eclipse ..."; \
	    tar xzf "$(DOWNLOAD_DIR)/$(ECLIPSE_FILE)" -C "$(PRISTINE_DIR)"; \
	  fi; \
	fi
endif

	## ---- Install SWTBot via p2 director (headless, no SWT needed) ----
	@_launcher=$$(find "$(PRISTINE_HOME)/plugins" -name "org.eclipse.equinox.launcher_*.jar" | head -1); \
	 _profile=$$(ls "$(PRISTINE_HOME)/p2/org.eclipse.equinox.p2.engine/profileRegistry/" 2>/dev/null \
	             | head -1 | sed 's/\.profile//'); \
	 if [ -z "$$_profile" ]; then _profile=$(ECLIPSE_PROFILE); fi; \
	 echo "Installing SWTBot into pristine Eclipse (profile: $$_profile) ..."; \
	 java -jar "$$_launcher" \
	     -application org.eclipse.equinox.p2.director \
	     -repository "$(SWTBOT_SITE)" \
	     -installIU "$(SWTBOT_IUS)" \
	     -destination "$(PRISTINE_HOME)" \
	     -profile "$$_profile" \
	     -vmargs -Xmx512m \
	   && echo "SWTBot installed." \
	   || { echo "ERROR: SWTBot installation failed."; exit 1; }
	@touch "$@"
	@echo "=== fetch-eclipse complete: pristine Eclipse ready at $(PRISTINE_DIR) ==="

fetch-eclipse: $(PRISTINE_DIR)/.swtbot-installed

$(DOWNLOAD_DIR):
	@mkdir -p "$(DOWNLOAD_DIR)"

## --------------------------------------------------------------------------
## build-tests
## --------------------------------------------------------------------------
$(TEST_JAR): $(SRCS) $(PRISTINE_DIR)/.swtbot-installed
	@mkdir -p "$(CLASSES_DIR)"
	@echo "Compiling test sources ..."
	@javac -source 21 -target 21 \
	    -cp "$(COMPILE_CP)" \
	    -d "$(CLASSES_DIR)" \
	    $(SRCS)
	@echo "Packaging test jar ..."
	@jar --create \
	     --file="$(TEST_JAR)" \
	     --manifest="$(UITEST)/META-INF/MANIFEST.MF" \
	     -C "$(CLASSES_DIR)" . \
	     -C "$(UITEST)" testdata
	@echo "Test jar: $(TEST_JAR)"

build-tests: $(TEST_JAR)

## --------------------------------------------------------------------------
## prepare-test-eclipse
## --------------------------------------------------------------------------
$(TEST_PREPARED_STAMP): $(PRISTINE_DIR)/.swtbot-installed
	@echo "=== Preparing test Eclipse instance ==="
	@mkdir -p "$(TEST_ECLIPSE)"
	$(COPY_CMD)
	@touch $@
	@echo "Test instance ready at: $(TEST_ECLIPSE)"

prepare-test-eclipse: fetch-eclipse .FORCE
	@rm -f "$(TEST_PREPARED_STAMP)" "$(OPENJML_INSTALLED_STAMP)"
	@$(MAKE) --no-print-directory $(TEST_PREPARED_STAMP)

## --------------------------------------------------------------------------
## run-install-test
## --------------------------------------------------------------------------
## Full end-to-end: always starts with a FRESH test Eclipse (no pre-installed
## OpenJML), runs InstallPluginTest which drives the Install New Software wizard.
## Uses its own vmargs (only needs update site, not LSP path or MPC suppression).
## --------------------------------------------------------------------------
INSTALL_TEST_XML := $(RESULTS_DIR)/install-test-results.xml

run-install-test: build-tests prepare-test-eclipse
	@mkdir -p "$(RESULTS_DIR)"
	@rm -rf "$(TEST_WS)"
	@echo "Installing test bundle into test Eclipse ..."
	@cp "$(TEST_JAR)" "$(TEST_PLUGINS)/"
	@echo "=== Running InstallPluginTest ==="
	@echo "    Update site: $(UPDATE_SITE)"
	@rm -f "$(INSTALL_TEST_XML)"; \
	 $(XVFB) "$(TEST_BIN)" \
	     $(ECLIPSE_LAUNCH_FLAGS) \
	     -classname org.jmlspecs.openjml.eclipse.uitest.InstallPluginTest \
	     "formatter=$(JUNIT_FORMATTER),$(INSTALL_TEST_XML)" \
	     -vmargs -Xmx1g -ea \
	         "-Dopenjml.update.site=$(UPDATE_SITE)" \
	         -Declipse.p2.unsignedPolicy=allow
	$(call check-xml-results,InstallPluginTest,$(INSTALL_TEST_XML))

## --------------------------------------------------------------------------
## install-openjml
## --------------------------------------------------------------------------
$(OPENJML_INSTALLED_STAMP): $(TEST_PREPARED_STAMP) $(TEST_JAR)
	@echo "Installing test bundle ..."
	@cp "$(TEST_JAR)" "$(TEST_PLUGINS)/"
	@echo "Installing OpenJML plugin into test Eclipse via p2 director ..."
	@_launcher="$(TEST_LAUNCHER_JAR)"; \
	 _profile=$$(ls "$(TEST_HOME)/p2/org.eclipse.equinox.p2.engine/profileRegistry/" 2>/dev/null \
	             | head -1 | sed 's/\.profile//'); \
	 if [ -z "$$_profile" ]; then _profile=$(ECLIPSE_PROFILE); fi; \
	 java -jar "$$_launcher" \
	     -application org.eclipse.equinox.p2.director \
	     -repository "$(UPDATE_SITE)" \
	     -installIU "$(OPENJML_FEATURE)" \
	     -destination "$(TEST_HOME)" \
	     -profile "$$_profile" \
	     -vmargs -Xmx512m \
	   && echo "OpenJML installed." \
	   || { echo "ERROR: OpenJML installation failed.  UPDATE_SITE=$(UPDATE_SITE)"; exit 1; }
	## Copy openjml-lsp to the test Eclipse install dir so OpenJMLStreamConnectionProvider
	## finds it via its fallback (installLocation/openjml-lsp) without needing a preference.
	@_lsp="$(REPO_ROOT)/OpenJMLlsp/openjml-lsp"; \
	 if [ -f "$$_lsp" ]; then \
	    cp "$$_lsp" "$(TEST_HOME)/openjml-lsp"; \
	    chmod +x "$(TEST_HOME)/openjml-lsp"; \
	    echo "openjml-lsp installed at $(TEST_HOME)/openjml-lsp"; \
	else \
	    echo "WARNING: $$_lsp not found; LSP features will not work in tests"; \
	fi
	@touch $@

install-openjml: build-tests
	@rm -f "$(OPENJML_INSTALLED_STAMP)"
	@$(MAKE) --no-print-directory $(OPENJML_INSTALLED_STAMP)

## --------------------------------------------------------------------------
## check-xml-results  (internal macro)
## --------------------------------------------------------------------------
## Inspects an Ant XML JUnit result file and exits non-zero on failure.
## Usage: $(call check-xml-results,ClassName,XmlFile)
## --------------------------------------------------------------------------
define check-xml-results
	@_xml="$(2)"; \
	 if [ ! -f "$$_xml" ]; then \
	     echo "[FAIL] $(1) — no results file written (test class not found or runner crashed)"; \
	     exit 1; \
	 fi; \
	 _tests=$$(grep -oE 'tests="[0-9]+"' "$$_xml" | grep -oE '[0-9]+' | head -1); \
	 if [ "$${_tests:-0}" -eq 0 ]; then \
	     echo "[FAIL] $(1) — 0 tests ran; test class was not loaded"; \
	     cat "$$_xml"; \
	     exit 1; \
	 fi; \
	 if grep -qE '(failures|errors)="[1-9]' "$$_xml"; then \
	     echo "[FAIL] $(1) ($${_tests} tests — see $$_xml)"; \
	     exit 1; \
	 fi; \
	 echo "[PASS] $(1) ($${_tests} tests)"
endef

## --------------------------------------------------------------------------
## run-one-plugin-test  (internal macro)
## --------------------------------------------------------------------------
## Shared recipe for running a single SWTBot test class in isolation.
## Usage: $(call run-one-plugin-test,ClassName)
## --------------------------------------------------------------------------
define run-one-plugin-test
	@mkdir -p "$(RESULTS_DIR)"
	@rm -rf "$(TEST_WS)"
	@echo "=== Running $(1) ==="
	@_xml="$(RESULTS_DIR)/$(1)-results.xml"; \
	 rm -f "$$_xml"; \
	 $(XVFB) "$(TEST_BIN)" \
	     $(ECLIPSE_LAUNCH_FLAGS) \
	     -classname org.jmlspecs.openjml.eclipse.uitest.$(1) \
	     "formatter=$(JUNIT_FORMATTER),$$_xml" \
	     -vmargs $(PLUGIN_TEST_VMARGS)
	$(call check-xml-results,$(1),$(RESULTS_DIR)/$(1)-results.xml)
endef

## --------------------------------------------------------------------------
## Individual test targets
## --------------------------------------------------------------------------
run-menu-test: $(OPENJML_INSTALLED_STAMP)
	$(call run-one-plugin-test,MenuPresenceTest)

run-preferences-test: $(OPENJML_INSTALLED_STAMP)
	$(call run-one-plugin-test,PreferencesPageTest)

run-fileicon-test: $(OPENJML_INSTALLED_STAMP)
	$(call run-one-plugin-test,FileIconTest)

run-nature-test: $(OPENJML_INSTALLED_STAMP)
	$(call run-one-plugin-test,NatureTest)

run-lsp-test: $(OPENJML_INSTALLED_STAMP)
	$(call run-one-plugin-test,LspFeatureTest)

## Legacy aliases (these test classes still exist but LspFeatureTest is preferred)
run-action-test: $(OPENJML_INSTALLED_STAMP)
	$(call run-one-plugin-test,ActionTest)

run-markers-test: $(OPENJML_INSTALLED_STAMP)
	$(call run-one-plugin-test,MarkersTest)

## --------------------------------------------------------------------------
## run-plugin-tests
## --------------------------------------------------------------------------
## Runs each plugin test class in its own Eclipse JVM, sequentially.
## Prints [PASS]/[FAIL] + elapsed time for each class as it finishes.
## --------------------------------------------------------------------------
## Derived from AllPluginTests.java @Suite.SuiteClasses — add/remove test classes
## there and this list updates automatically.  Names are extracted by matching
## the pattern "XxxTest.class" inside the @Suite.SuiteClasses annotation.
PLUGIN_TEST_CLASSES := $(shell \
    grep -oE '[A-Z][A-Za-z0-9]+Test\.class' \
        "$(SRC_DIR)/org/jmlspecs/openjml/eclipse/uitest/AllPluginTests.java" \
    | sed 's/\.class//')

run-plugin-tests: $(OPENJML_INSTALLED_STAMP)
	@mkdir -p "$(RESULTS_DIR)"
	@_pass=0; _fail=0; \
	 for cls in $(PLUGIN_TEST_CLASSES); do \
	   rm -rf "$(TEST_WS)"; \
	   _xml="$(RESULTS_DIR)/$$cls-results.xml"; \
	   rm -f "$$_xml"; \
	   echo "[TEST] $$cls"; \
	   _start=$$(date +%s); \
	   ( $(XVFB) "$(TEST_BIN)" \
	            $(ECLIPSE_LAUNCH_FLAGS) \
	            -classname "org.jmlspecs.openjml.eclipse.uitest.$$cls" \
	            "formatter=$(JUNIT_FORMATTER),$$_xml" \
	            -vmargs $(PLUGIN_TEST_VMARGS) \
	       ) > "$(RESULTS_DIR)/$$cls.log" 2>&1; \
	   _elapsed=$$(( $$(date +%s) - _start )); \
	   _ok=1; \
	   if [ ! -f "$$_xml" ]; then \
	     echo "[FAIL] $$cls ($${_elapsed}s) — no results file (runner crashed; log: $(RESULTS_DIR)/$$cls.log)"; \
	     cat "$(RESULTS_DIR)/$$cls.log"; \
	     _ok=0; \
	   else \
	     _tests=$$(grep -oE 'tests="[0-9]+"' "$$_xml" | grep -oE '[0-9]+' | head -1); \
	     if [ "$${_tests:-0}" -eq 0 ]; then \
	       echo "[FAIL] $$cls ($${_elapsed}s) — 0 tests ran (class not loaded; log: $(RESULTS_DIR)/$$cls.log)"; \
	       cat "$(RESULTS_DIR)/$$cls.log"; \
	       _ok=0; \
	     elif grep -qE '(failures|errors)="[1-9]' "$$_xml"; then \
	       echo "[FAIL] $$cls ($${_elapsed}s) — $${_tests} tests, see $$_xml"; \
	       _ok=0; \
	     else \
	       echo "[PASS] $$cls ($${_elapsed}s, $${_tests} tests)"; \
	     fi; \
	   fi; \
	   [ "$$_ok" -eq 1 ] && _pass=$$(( _pass + 1 )) || _fail=$$(( _fail + 1 )); \
	 done; \
	 echo "Plugin tests: $${_pass} passed, $${_fail} failed."; \
	 [ "$$_fail" -eq 0 ]

## --------------------------------------------------------------------------
## run-plugin-suite
## --------------------------------------------------------------------------
## Runs AllPluginTests in a SINGLE Eclipse JVM — one [PASS]/[FAIL] at the end.
## Faster (one Eclipse startup) but produces no per-class progress output.
## --------------------------------------------------------------------------
PLUGIN_SUITE_XML := $(RESULTS_DIR)/plugin-suite-results.xml

run-plugin-suite: $(OPENJML_INSTALLED_STAMP)
	@mkdir -p "$(RESULTS_DIR)"
	@rm -rf "$(TEST_WS)"
	@rm -f "$(PLUGIN_SUITE_XML)"
	@echo "[TEST] AllPluginTests"
	@_start=$$(date +%s); \
	 ( $(XVFB) "$(TEST_BIN)" \
	          $(ECLIPSE_LAUNCH_FLAGS) \
	          -classname "org.jmlspecs.openjml.eclipse.uitest.AllPluginTests" \
	          "formatter=$(JUNIT_FORMATTER),$(PLUGIN_SUITE_XML)" \
	          -vmargs $(PLUGIN_TEST_VMARGS) \
	   ) > "$(RESULTS_DIR)/AllPluginTests.log" 2>&1; \
	 _elapsed=$$(( $$(date +%s) - _start )); \
	 if [ ! -f "$(PLUGIN_SUITE_XML)" ]; then \
	   echo "[FAIL] AllPluginTests ($${_elapsed}s) — no results file (runner crashed)"; \
	   cat "$(RESULTS_DIR)/AllPluginTests.log"; \
	   exit 1; \
	 fi; \
	 _tests=$$(grep -oE 'tests="[0-9]+"' "$(PLUGIN_SUITE_XML)" | grep -oE '[0-9]+' | head -1); \
	 if [ "$${_tests:-0}" -eq 0 ]; then \
	   echo "[FAIL] AllPluginTests ($${_elapsed}s) — 0 tests ran (class not loaded)"; \
	   cat "$(RESULTS_DIR)/AllPluginTests.log"; \
	   exit 1; \
	 fi; \
	 if grep -qE '(failures|errors)="[1-9]' "$(PLUGIN_SUITE_XML)"; then \
	   echo "[FAIL] AllPluginTests ($${_elapsed}s) — $${_tests} tests, see $(PLUGIN_SUITE_XML)"; \
	   exit 1; \
	 fi; \
	 echo "[PASS] AllPluginTests ($${_elapsed}s, $${_tests} tests)"

## --------------------------------------------------------------------------
## clean targets
## --------------------------------------------------------------------------

clean: .FORCE
	rm -rf "$(UITEST)/build"
	rm -rf "$(TEST_WS)"
	@echo "Build artifacts removed."

clean-test-eclipse: .FORCE
	rm -rf "$(TEST_ECLIPSE)"
	@echo "Test Eclipse copy removed (sentinels cleared)."

clean-downloads: .FORCE
	rm -rf "$(DOWNLOAD_DIR)"
	@echo "Download cache removed."

clean-cache: .FORCE
	rm -rf "$(CACHE_DIR)"
	@echo "Eclipse cache removed."

clean-all: clean clean-cache

.FORCE:
