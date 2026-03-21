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
## We use the Eclipse Committers package (not Eclipse for Java Developers) because
## running SWTBot tests via uitestapplication requires PDE (Plugin Development
## Environment) — specifically org.eclipse.pde.internal.junit.runtime — which
## is not present in the Java Developers package but IS in Committers.
##
## Eclipse EPP filenames include the full release tag, e.g. "2026-03-R".
## DMG (macOS) and tar.gz (Linux) are hosted directly on download.eclipse.org CDN.
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

## --------------------------------------------------------------------------
## Build
## --------------------------------------------------------------------------
SRC_DIR     := $(UITEST)/src
CLASSES_DIR := $(UITEST)/build/classes
TEST_JAR    := $(UITEST)/build/org.openjml.OpenJMLGUITest_0.21.0.jar
RESULTS_DIR := $(UITEST)/build/results
RESULTS_XML := $(RESULTS_DIR)/install-test-results.xml
TEST_WS     := $(UITEST)/test-ws

## Test bundle symbolic name (must match MANIFEST.MF)
TEST_BUNDLE := org.openjml.OpenJMLGUITest

## Java sources
SRCS := $(shell find "$(SRC_DIR)" -name '*.java' 2>/dev/null)

## --------------------------------------------------------------------------
## Classpath construction (needs pristine Eclipse with SWTBot to be present)
## --------------------------------------------------------------------------
## These are evaluated lazily (= not :=) so they're correct after fetch-eclipse.
PLUGINS_DIR  = $(PRISTINE_HOME)/plugins

find_jar  = $(shell find "$(PLUGINS_DIR)" -maxdepth 1 -name "$(1)_*.jar" 2>/dev/null | sort -V | tail -1)

SWTBOT_ECLIPSE_JAR  = $(call find_jar,org.eclipse.swtbot.eclipse.finder)
SWTBOT_CORE_JAR     = $(call find_jar,org.eclipse.swtbot.swt.finder)
SWTBOT_ECLIPSE_CORE = $(call find_jar,org.eclipse.swtbot.eclipse.core)
## SWTBotJunit4ClassRunner lives in org.eclipse.swtbot.junit4_x, not swt.finder.junit
SWTBOT_JUNIT_JAR    = $(call find_jar,org.eclipse.swtbot.junit4_x)
ECLIPSE_UI_JAR      = $(call find_jar,org.eclipse.ui)
ECLIPSE_RUNTIME_JAR = $(call find_jar,org.eclipse.core.runtime)
ECLIPSE_RESOURCES_JAR = $(call find_jar,org.eclipse.core.resources)
ECLIPSE_JFACE_JAR   = $(call find_jar,org.eclipse.jface)
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

COMPILE_CP = $(SWTBOT_ECLIPSE_JAR):$(SWTBOT_CORE_JAR):$(SWTBOT_ECLIPSE_CORE):$(SWTBOT_JUNIT_JAR):$(ECLIPSE_UI_JAR):$(ECLIPSE_RUNTIME_JAR):$(ECLIPSE_RESOURCES_JAR):$(ECLIPSE_SWT_JAR):$(ECLIPSE_JFACE_JAR):$(JUNIT4_JAR):$(HAMCREST_JAR)

## --------------------------------------------------------------------------
## Phony targets
## --------------------------------------------------------------------------
.PHONY: all fetch-eclipse build-tests prepare-test-eclipse \
        run-install-test clean clean-cache clean-all help .FORCE

all: run-install-test

## --------------------------------------------------------------------------
## help
## --------------------------------------------------------------------------
help:
	@echo "Targets:"
	@echo "  fetch-eclipse        Download Eclipse for Java Devs + install SWTBot (one-time)"
	@echo "  build-tests          Compile test sources and build test jar"
	@echo "  prepare-test-eclipse Copy pristine → test instance (fresh per run)"
	@echo "  run-install-test     Full install+verify test (fetch+build+prepare+run)"
	@echo "  clean                Remove build/ and test-ws/ (keeps eclipse-cache)"
	@echo "  clean-test-eclipse   Remove just the test Eclipse copy"
	@echo "  clean-downloads      Remove downloaded archives (keeps pristine)"
	@echo "  clean-cache          Remove all of eclipse-cache/ (re-download required)"
	@echo "  clean-all            clean + clean-cache"
	@echo ""
	@echo "Key variables (override on command line):"
	@echo "  ECLIPSE_RELEASE=$(ECLIPSE_RELEASE)"
	@echo "  UPDATE_SITE=$(UPDATE_SITE)"

## --------------------------------------------------------------------------
## fetch-eclipse
## --------------------------------------------------------------------------
## Downloads Eclipse for Java Developers, extracts it to eclipse-cache/pristine/,
## then installs the SWTBot feature into it via p2 director (headless).
## The pristine directory is never modified after this step.
##
## Re-run with:  make fetch-eclipse .FORCE
##
## If the download fails due to mirror-picker issues, manually download:
##   $(ECLIPSE_URL)
## and place the file at:
##   $(DOWNLOAD_DIR)/$(ECLIPSE_FILE)
## then re-run: make fetch-eclipse
## --------------------------------------------------------------------------
$(PRISTINE_DIR)/.swtbot-installed: | $(DOWNLOAD_DIR)
	@echo "=== fetch-eclipse: preparing pristine Eclipse ==="
	@mkdir -p "$(PRISTINE_DIR)"
ifeq ($(ECLIPSE_EXT),dmg)
	## ---- macOS ----
	## If ECLIPSE_SRC points at an existing .app, rsync from there (fast, no download).
	## Otherwise download the committers DMG from download.eclipse.org.
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
## Compile test sources and package them as an OSGi bundle jar.
## Depends on fetch-eclipse so SWTBot jars are on the classpath.
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
## Rsync a fresh copy of the pristine Eclipse to eclipse-cache/test-eclipse/.
## Always runs (no sentinel file) so each run starts clean.
## --------------------------------------------------------------------------
prepare-test-eclipse: fetch-eclipse .FORCE
	@echo "=== prepare-test-eclipse: creating fresh test instance ==="
	@mkdir -p "$(TEST_ECLIPSE)"
	$(COPY_CMD)
	@echo "Test instance ready at: $(TEST_ECLIPSE)"

## --------------------------------------------------------------------------
## run-install-test
## --------------------------------------------------------------------------
## Full end-to-end: prepare a fresh test Eclipse, drop in our test bundle,
## and run InstallPluginTest which drives the Install New Software wizard.
## --------------------------------------------------------------------------
run-install-test: build-tests prepare-test-eclipse
	@mkdir -p "$(RESULTS_DIR)"
	@rm -rf "$(TEST_WS)"
	@echo "Installing test bundle into test Eclipse ..."
	@cp "$(TEST_JAR)" "$(TEST_PLUGINS)/"
	@echo "=== Running InstallPluginTest ==="
	@echo "    Update site: $(UPDATE_SITE)"
	@_launcher="$(TEST_LAUNCHER_JAR)"; \
	 _cmd="$(XVFB) \"$(TEST_BIN)\" \
	     -nosplash \
	     --launcher.suppressErrors \
	     -application org.eclipse.pde.junit.runtime.uitestapplication \
	     -data \"$(TEST_WS)\" \
	     -testpluginname $(TEST_BUNDLE) \
	     -classnames org.jmlspecs.openjml.eclipse.uitest.InstallPluginTest \
	     -testLoaderClass org.eclipse.jdt.internal.junit4.runner.JUnit4TestLoader \
	     -loaderpluginname org.eclipse.jdt.junit4.runtime \
	     -testResultsXml \"$(RESULTS_XML)\" \
	     -vmargs -Xmx1g -ea \
	         -Dopenjml.update.site=\"$(UPDATE_SITE)\""; \
	 eval "$$_cmd"; \
	 _rc=$$?; \
	 if [ $$_rc -eq 0 ]; then \
	     echo "[PASS] InstallPluginTest"; \
	 else \
	     echo "[FAIL] InstallPluginTest (exit $$_rc)"; \
	     echo "Results: $(RESULTS_XML)"; \
	     exit 1; \
	 fi

## --------------------------------------------------------------------------
## clean targets
## --------------------------------------------------------------------------

## Remove build artifacts and the test workspace (leaves eclipse-cache intact).
clean: .FORCE
	rm -rf "$(UITEST)/build"
	rm -rf "$(TEST_WS)"
	@echo "Build artifacts removed."

## Remove the test Eclipse copy only (re-created by prepare-test-eclipse).
## Useful to force a fresh test instance without re-downloading.
clean-test-eclipse: .FORCE
	rm -rf "$(TEST_ECLIPSE)"
	@echo "Test Eclipse copy removed."

## Remove downloaded archives (re-downloaded on next fetch-eclipse).
## Keeps the already-extracted pristine Eclipse in place.
clean-downloads: .FORCE
	rm -rf "$(DOWNLOAD_DIR)"
	@echo "Download cache removed."

## Remove the entire eclipse-cache directory (downloaded archive + pristine + test copy).
## Next fetch-eclipse will re-download and re-install SWTBot from scratch.
clean-cache: .FORCE
	rm -rf "$(CACHE_DIR)"
	@echo "Eclipse cache removed."

## Remove everything: build artifacts, test workspace, and the full eclipse cache.
clean-all: clean clean-cache

.FORCE:
