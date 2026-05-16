mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
mkfile_dir  := $(dir $(mkfile_path))
LSPROOT     := $(patsubst %/,%,$(mkfile_dir))

## Sibling OpenJMLsrc directory
SRC      := $(LSPROOT)/../OpenJMLsrc
BUILDJDK := $(firstword $(wildcard $(SRC)/build/*/jdk))
## On Windows the built tools have .exe suffix; use wildcard to detect.
## NJAVAC/NJAVA must be the built OpenJML JDK (contains org.jmlspecs.openjml etc.);
## JAR can be the installed one from PATH since jar creation needs no OpenJML packages.
NJAVAC   := $(or $(wildcard $(BUILDJDK)/bin/javac.exe),$(BUILDJDK)/bin/javac)
NJAVA    := $(or $(wildcard $(BUILDJDK)/bin/java.exe),$(BUILDJDK)/bin/java)
JAR      := jar
## On Windows, javac.exe is a Windows PE process and does not understand WSL Unix paths.
## The OpenJDK build produces a configured fixpath wrapper that translates Unix paths to
## Windows format before exec-ing any Windows binary.  Use it when present (Windows only).
FIXPATH  := $(wildcard $(dir $(BUILDJDK))fixpath)
FIXPATH_EXEC := $(if $(FIXPATH),$(FIXPATH) exec)

## LSP4J jars (downloaded into libs/ on first build)
LSP4J_VERSION := 1.0.0
LIBS          := $(LSPROOT)/libs
LSP4J_JAR     := $(LIBS)/org.eclipse.lsp4j-$(LSP4J_VERSION).jar
LSP4J_RPC_JAR := $(LIBS)/org.eclipse.lsp4j.jsonrpc-$(LSP4J_VERSION).jar
LSP4J_CP      := $(LSP4J_JAR):$(LSP4J_RPC_JAR)

## Gson version required by the LSP server (via LSP4J's JSON-RPC layer).
## LSP does NOT bundle Gson — it uses Gson indirectly through OpenJML, which
## vendors Gson source inside jdk.compiler and exports the public packages from
## module-info.java.  The version embedded in OpenJML MUST match GSON_REQUIRED_VERSION;
## the check-gson target enforces this at build time.
GSON_REQUIRED_VERSION := 2.11.0
GSON_BUILD_CONFIG     := $(SRC)/src/jdk.compiler/share/classes/com/google/gson/internal/GsonBuildConfig.java

MAVEN := https://repo1.maven.org/maven2

## Build output
CLASSES := $(LSPROOT)/build/classes
JARFILE := $(LSPROOT)/build/openjml-lsp.jar

VERSION_TXT   := $(LSPROOT)/../version.txt
VERSION       := $(shell cat $(VERSION_TXT) | tr -d '[:space:]')
## VS Code/npm requires strict semver (major.minor.patch); strip any OSGi qualifier.
VSIX_VERSION  := $(shell echo $(VERSION) | sed 's/^\([0-9]*\.[0-9]*\.[0-9]*\).*/\1/')
VERSION_PROPS := $(CLASSES)/org/openjml/lsp/version.properties

## All Java source files in the server (exclude module-info.java — Eclipse artifact,
## incompatible with the classpath-based build)
JAVASRC := $(shell find $(LSPROOT)/src -name '*.java' ! -name 'module-info.java')

## Staging directory used by the release target
RELEASE_STAGE  := $(LSPROOT)/release-stage
VSIX_DIR       := $(LSPROOT)/vscode-extension
VSIX_NAME      := openjml-$(VSIX_VERSION).vsix

.PHONY: all jar compile libs check-gson run-tests release vsix clean .FORCE

all: release run-tests

run-tests: jar
	$(MAKE) -C $(LSPROOT)/../OpenJMLTest/lsp run-tests

## Download LSP4J from Maven Central if not already present
libs: $(LSP4J_JAR) $(LSP4J_RPC_JAR)

$(LSP4J_JAR):
	@mkdir -p $(LIBS)
	curl --fail --show-error -s -o $@.tmp $(MAVEN)/org/eclipse/lsp4j/org.eclipse.lsp4j/$(LSP4J_VERSION)/org.eclipse.lsp4j-$(LSP4J_VERSION).jar && mv $@.tmp $@

$(LSP4J_RPC_JAR):
	@mkdir -p $(LIBS)
	curl --fail --show-error -s -o $@.tmp $(MAVEN)/org/eclipse/lsp4j/org.eclipse.lsp4j.jsonrpc/$(LSP4J_VERSION)/org.eclipse.lsp4j.jsonrpc-$(LSP4J_VERSION).jar && mv $@.tmp $@

## Verify that the Gson version vendored in OpenJML matches GSON_REQUIRED_VERSION.
check-gson:
	@if [ ! -f "$(GSON_BUILD_CONFIG)" ]; then \
	    echo "ERROR: GsonBuildConfig.java not found at $(GSON_BUILD_CONFIG)"; \
	    echo "       Is OpenJMLsrc present and up to date?"; \
	    exit 1; \
	fi
	@actual=$$(grep 'VERSION' "$(GSON_BUILD_CONFIG)" | grep -o '"[0-9][^"]*"' | tr -d '"'); \
	echo "Gson version in OpenJML: $$actual (required: $(GSON_REQUIRED_VERSION))"; \
	if [ "$$actual" != "$(GSON_REQUIRED_VERSION)" ]; then \
	    echo "ERROR: Gson version mismatch."; \
	    echo "       OpenJML has $$actual but LSP requires $(GSON_REQUIRED_VERSION)."; \
	    echo "       Update GSON_REQUIRED_VERSION in OpenJMLlsp/Makefile or"; \
	    echo "       update the Gson source in OpenJMLsrc to match."; \
	    exit 1; \
	fi

## Compile the LSP server against the built OpenJML JDK.
## NOJML=1 disables JML processing in the extended javac so that JML processing
## is skipped during compilation.  A non-empty value is required on Windows
## (Win32 API treats an empty env var as absent).  WSLENV forwards NOJML to
## Windows PE processes (java.exe/javac.exe via binfmt_misc).
compile: libs check-gson
	@mkdir -p $(CLASSES)
	@( . $(SRC)/setup-exports; \
	   NOJML=1 WSLENV="$${WSLENV:+$$WSLENV:}NOJML" \
	   $(FIXPATH_EXEC) $(NJAVAC) $$OPENJML_EXPORTS \
	     -cp $(LSP4J_CP) \
	     -d $(CLASSES) \
	     $(JAVASRC) )

## Inject version into the classes tree as a properties resource.
## Only updates the file (and its mtime) when version.txt actually changes,
## so that the jar target is not forced to rebuild on every make invocation.
$(VERSION_PROPS): $(VERSION_TXT)
	@mkdir -p $(dir $@)
	@ver=$$(cat $(VERSION_TXT) | tr -d '[:space:]'); \
	echo "version=$$ver" > $@

## Package into an executable jar
jar: compile $(VERSION_PROPS)
	$(JAR) --create --file=$(JARFILE) \
	       --main-class=org.openjml.lsp.ServerLauncher \
	       -C $(CLASSES) .

## Build the VS Code extension .vsix package.
vsix:
	cd $(VSIX_DIR) && npm install
	cd $(VSIX_DIR) && npm version $(VSIX_VERSION) --no-git-tag-version --allow-same-version
	cd $(VSIX_DIR) && ./node_modules/.bin/vsce package --no-yarn --out $(VSIX_NAME)

## Stage LSP files for inclusion in an OpenJML release zip.
## Produces $(RELEASE_STAGE)/openjml-lsp   (launcher, goes to release root)
##          $(RELEASE_STAGE)/lsp/          (jars, goes to release root as lsp/)
##          $(RELEASE_STAGE)/openjml.vsix  (VS Code extension)
release: jar vsix
	rm -rf $(RELEASE_STAGE)
	mkdir -p $(RELEASE_STAGE)/lsp
	cp $(LSPROOT)/openjml-lsp $(RELEASE_STAGE)/
	chmod ugo+x $(RELEASE_STAGE)/openjml-lsp
	cp $(JARFILE) $(RELEASE_STAGE)/lsp/
	cp $(LSP4J_JAR) $(LSP4J_RPC_JAR) $(RELEASE_STAGE)/lsp/
	cp $(VSIX_DIR)/$(VSIX_NAME) $(RELEASE_STAGE)/openjml.vsix

clean: .FORCE
	rm -rf $(LSPROOT)/build $(RELEASE_STAGE)

.FORCE:
