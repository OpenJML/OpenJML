mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
mkfile_dir  := $(dir $(mkfile_path))

# vscode-extension-tester v8 requires Node >= 18.
# If the current `node` is too old, fall back to any Node 20 found under ~/.nvm.
NODE_VER := $(shell node -e "process.exit(parseInt(process.versions.node) >= 18 ? 0 : 1)" 2>/dev/null && echo ok)
ifeq ($(NODE_VER),ok)
NODE := node
NPM  := npm
else
NODE := $(firstword $(wildcard $(HOME)/.nvm/versions/node/v20*/bin/node $(HOME)/.nvm/versions/node/v22*/bin/node))
NPM  := $(dir $(NODE))npm
endif

LSPROOT   := $(mkfile_dir)../../OpenJMLlsp
EXTENSION := $(LSPROOT)/vscode-extension

.PHONY: all build install test test-suite clean

## Build the LSP server jar, then run all VS Code UI test suites.
all: build test

## Compile + package the OpenJML LSP server (delegates to OpenJMLlsp/Makefile).
## Does NOT rebuild OpenJMLsrc/the JDK — run `make openjml` there first.
build:
	$(MAKE) -C $(LSPROOT) jar

## Install npm dependencies for the test harness and for the extension itself.
install: node_modules $(EXTENSION)/node_modules

node_modules: package.json
	$(NPM) install
	@touch node_modules

$(EXTENSION)/node_modules: $(EXTENSION)/package.json
	cd $(EXTENSION) && $(NPM) install
	@touch $(EXTENSION)/node_modules

## Run all VS Code UI test suites.
test: install
	$(NODE) runner.js

## Run one named suite:  make test-suite SUITE=02_commands
test-suite: install
	$(NODE) runner.js $(SUITE)

clean:
	rm -rf node_modules .test-resources
