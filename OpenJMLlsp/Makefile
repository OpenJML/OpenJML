mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
mkfile_dir  := $(dir $(mkfile_path))
LSPROOT     := $(patsubst %/,%,$(mkfile_dir))

## Sibling OpenJMLsrc directory
SRC      := $(LSPROOT)/../OpenJMLsrc
BUILDJDK := $(firstword $(wildcard $(SRC)/build/*/jdk))
NJAVAC   := $(BUILDJDK)/bin/javac
NJAVA    := $(BUILDJDK)/bin/java
JAR      := $(BUILDJDK)/bin/jar

## LSP4J and Gson jars (downloaded into libs/ on first build)
LSP4J_VERSION := 1.0.0
GSON_VERSION  := 2.11.0
LIBS          := $(LSPROOT)/libs
LSP4J_JAR     := $(LIBS)/org.eclipse.lsp4j-$(LSP4J_VERSION).jar
LSP4J_RPC_JAR := $(LIBS)/org.eclipse.lsp4j.jsonrpc-$(LSP4J_VERSION).jar
GSON_JAR      := $(LIBS)/gson-$(GSON_VERSION).jar
LSP4J_CP      := $(LSP4J_JAR):$(LSP4J_RPC_JAR):$(GSON_JAR)

MAVEN := https://repo1.maven.org/maven2

## Build output
CLASSES := $(LSPROOT)/build/classes
JARFILE := $(LSPROOT)/build/openjml-lsp.jar

## All Java source files in the server (exclude module-info.java — Eclipse artifact,
## incompatible with the classpath-based build)
JAVASRC := $(shell find $(LSPROOT)/src -name '*.java' ! -name 'module-info.java')

## Staging directory used by the release target
RELEASE_STAGE  := $(LSPROOT)/release-stage
VSIX_DIR       := $(LSPROOT)/vscode-extension
VSIX_NAME      := openjml-0.0.1.vsix

.PHONY: all jar compile libs release vsix clean .FORCE

all: jar

## Download LSP4J and Gson from Maven Central if not already present
libs: $(LSP4J_JAR) $(LSP4J_RPC_JAR) $(GSON_JAR)

$(LSP4J_JAR):
	@mkdir -p $(LIBS)
	curl -s -S -o $@ $(MAVEN)/org/eclipse/lsp4j/org.eclipse.lsp4j/$(LSP4J_VERSION)/org.eclipse.lsp4j-$(LSP4J_VERSION).jar

$(LSP4J_RPC_JAR):
	@mkdir -p $(LIBS)
	curl -s -S -o $@ $(MAVEN)/org/eclipse/lsp4j/org.eclipse.lsp4j.jsonrpc/$(LSP4J_VERSION)/org.eclipse.lsp4j.jsonrpc-$(LSP4J_VERSION).jar

$(GSON_JAR):
	@mkdir -p $(LIBS)
	curl -s -S -o $@ $(MAVEN)/com/google/code/gson/gson/$(GSON_VERSION)/gson-$(GSON_VERSION).jar

## Compile the LSP server against the built OpenJML JDK.
## NOJML= disables JML processing in the extended javac (same idiom as in
## OpenJMLsrc/Makefile) so that spec-path lookup is skipped during compilation.
compile: libs
	@mkdir -p $(CLASSES)
	@( . $(SRC)/setup-exports; \
	   NOJML= \
	   $(NJAVAC) $$OPENJML_EXPORTS \
	     -cp $(LSP4J_CP) \
	     -d $(CLASSES) \
	     $(JAVASRC) )

## Package into an executable jar
jar: compile
	$(JAR) --create --file=$(JARFILE) \
	       --main-class=org.openjml.lsp.ServerLauncher \
	       -C $(CLASSES) .

## Build the VS Code extension .vsix package.
vsix:
	cd $(VSIX_DIR) && npm install
	cd $(VSIX_DIR) && ./node_modules/.bin/vsce package --no-yarn --out $(VSIX_NAME)

## Stage LSP files for inclusion in an OpenJML release zip.
## Produces $(RELEASE_STAGE)/openjml-lsp  (launcher, goes to release root)
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
