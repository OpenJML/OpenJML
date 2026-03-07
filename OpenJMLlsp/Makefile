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
LSP4J_VERSION := 0.21.1
GSON_VERSION  := 2.10.1
LIBS          := $(LSPROOT)/libs
LSP4J_JAR     := $(LIBS)/org.eclipse.lsp4j-$(LSP4J_VERSION).jar
LSP4J_RPC_JAR := $(LIBS)/org.eclipse.lsp4j.jsonrpc-$(LSP4J_VERSION).jar
GSON_JAR      := $(LIBS)/gson-$(GSON_VERSION).jar
LSP4J_CP      := $(LSP4J_JAR):$(LSP4J_RPC_JAR):$(GSON_JAR)

MAVEN := https://repo1.maven.org/maven2

## Build output
CLASSES := $(LSPROOT)/build/classes
JARFILE := $(LSPROOT)/build/openjml-lsp.jar

## All Java source files in the server
JAVASRC := $(shell find $(LSPROOT)/src -name '*.java')

.PHONY: all jar compile libs clean .FORCE

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

clean: .FORCE
	rm -rf $(LSPROOT)/build

.FORCE:
