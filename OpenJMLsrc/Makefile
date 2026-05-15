#
# Copyright (c) 2012, 2015, Oracle and/or its affiliates. All rights reserved.
# DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
#
# This code is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License version 2 only, as
# published by the Free Software Foundation.  Oracle designates this
# particular file as subject to the "Classpath" exception as provided
# by Oracle in the LICENSE file that accompanied this code.
#
# This code is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
# version 2 for more details (a copy is included in the LICENSE file that
# accompanied this code).
#
# You should have received a copy of the GNU General Public License version
# 2 along with this work; if not, write to the Free Software Foundation,
# Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
#
# Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
# or visit www.oracle.com if you need additional information or have any
# questions.
#

###
### This file is just a very small wrapper needed to run the real make/Init.gmk.
### It also performs some sanity checks on make.
###

### OPENJML: This file is slightly modified to create make targets for openjml
### See the material following the comment line below

# The shell code below will be executed on /usr/bin/make on Solaris, but not in GNU Make.
# /usr/bin/make lacks basically every other flow control mechanism.
.TEST_FOR_NON_GNUMAKE:sh=echo You are not using GNU Make/gmake, this is a requirement. Check your path. 1>&2 && exit 1

# The .FEATURES variable is likely to be unique for GNU Make.
ifeq ($(.FEATURES), )
  $(info Error: '$(MAKE)' does not seem to be GNU Make, which is a requirement.)
  $(info Check your path, or upgrade to GNU Make 3.81 or newer.)
  $(error Cannot continue)
endif

# Assume we have GNU Make, but check version.
ifeq ($(strip $(foreach v, 3.81% 3.82% 4.%, $(filter $v, $(MAKE_VERSION)))), )
  $(info Error: This version of GNU Make is too low ($(MAKE_VERSION)).)
  $(info Check your path, or upgrade to GNU Make 3.81 or newer.)
  $(error Cannot continue)
endif

# In Cygwin, the MAKE variable gets prepended with the current directory if the
# make executable is called using a Windows mixed path (c:/cygwin/bin/make.exe).
ifneq ($(findstring :, $(MAKE)), )
  MAKE := $(patsubst $(CURDIR)%, %, $(patsubst $(CURDIR)/%, %, $(MAKE)))
endif

# Locate this Makefile
ifeq ($(filter /%, $(lastword $(MAKEFILE_LIST))),)
  makefile_path := $(CURDIR)/$(strip $(lastword $(MAKEFILE_LIST)))
else
  makefile_path := $(lastword $(MAKEFILE_LIST))
endif
topdir := $(strip $(patsubst %/, %, $(dir $(makefile_path))))

# ... and then we can include the real makefile
include $(topdir)/make/Init.gmk

#### OpenJML-specific build targets

## This Makefile assumes that the OpenJML, JMLAnnotations, Specs, openjml.github.io, OpenJML_Demo, Solvers
## repos are cloned into sibling folders under one common folder
## I expect this Makefile and auxiliary scripts to fail if there are spaces in folder and file paths

## A temporary folder (relative to the location of the Makefile) used to stage materials in assembling a release
## May not contain whitespace
TEMP=release-temp

## A temporary folder (relative to the location of the Makefile) used to stage materials in assembling jmlruntime.jar
## Must be a simple name, not a multi-segment path, and not contain whitespace
TEMPLIB=templib

## Relative path to the tutorial source files
TUT=../../openjml.github.io/tutorial

## A permanent folder that holds auxiliary material to be included in a release
RELFILES=release-files

## The built JDK bin tools (jar, java, javac) from the most recent build target
BUILDJDK := $(firstword $(wildcard $(topdir)/build/*/jdk))
JAR      := $(BUILDJDK)/bin/jar

## The zip tool used to assemble the release archive; override on the command line if needed
ZIPCMD := zip

## OS name used to select the correct Solvers subfolder
UNAME := $(shell uname)
ANAME := $(shell uname -m)
## Under WSL, uname returns Linux but /proc/version contains "microsoft"
IS_WSL := $(shell grep -si microsoft /proc/version 2>/dev/null)
ifeq ($(UNAME),Darwin)
  OS_NAME := macos
else ifeq ($(UNAME),Windows)
  OS_NAME := windows
else ifneq ($(IS_WSL),)
  OS_NAME := windows
else ifeq ($(ANAME),aarch64)
  OS_NAME := linux-arm64
else
  OS_NAME := linux
endif

## Used in both the github build.yml action and the development environment

## Builds a full release. Modify (and commit) ../version.txt to set the version number that will be builtin to the release
## Note that the openjml.zip file produced by a release is specific to a particular machine architecture
## The created release zip is in $TEMP (./release-temp)
release: .FORCE
	$(MAKE) version-info
	$(MAKE) annotation
	$(MAKE) openjml
	$(MAKE) jmlruntime.jar
	$(MAKE) tutorial
	$(MAKE) post

clean-jml:
	rm -rf release-temp temp-release $(TEMPLIB) jmlruntime.jar $(USERGUIDE)
	$(MAKE) -C ../OpenJMLTest clean
	$(MAKE) -C ../OpenJMLlsp clean
	$(MAKE) -C ../OpenJMLUI clean
	$(MAKE) -C ../OpenJMLGUITests clean

## Cleans and makes release
clean-release:
	-$(MAKE) clean dist-clean clean-jml
	rm -rf $(makefile_path)/html
	rm -rf $(TEMP)
	rm -rf src/java.base/share/classes/org/jmlspecs/annotation
	rm -rf $(RELFILES)/tutorial
	./configure
	$(MAKE) release

## Creates/updates the version.properties source file from ../version.txt
version: .FORCE
	@ ./version.sh


## Creates the version-info.txt file, containing the public version number (from ../version.txt) and the commit shas
## of the commit points compiled into the release.
version-info: .FORCE
	@ if [ ! -e ../version.txt ]; then echo "No version.txt file"; exit 1; else echo "Building version" `cat ../version.txt`; fi
	@ $(MAKE) version > /dev/null
	@ cat ../version.txt > version-info.txt
	@ echo "OpenJML" `git rev-parse HEAD` >> version-info.txt
	@ (cd ../../Specs; echo "Specs" `git rev-parse HEAD`) >> version-info.txt
	@ (cd ../../JMLAnnotations; echo JMLAnnotations `git rev-parse HEAD` ) >> version-info.txt
	@ (cd ../../Solvers; echo Solvers `git rev-parse HEAD` ) >> version-info.txt
	@ (cd ../../openjml.github.io; echo openjml.github.io `git rev-parse HEAD` ) >> version-info.txt
	@ cat version-info.txt
	@ mv version-info.txt $(RELFILES)

## Updates the tutorial files into the repo
tutorial: .FORCE
	rm -rf $(RELFILES)/tutorial
	mkdir $(RELFILES)/tutorial
	cp -pR $(TUT)/*.java $(TUT)/*.out $(RELFILES)/tutorial

## Copies current annotation files into the development code
annotation: .FORCE
	cp -pR ../../JMLAnnotations/src/org  src/java.base/share/classes

## Assembles all the components of a release into an openjml.zip file for the host OS. Presumes a build has been successful.
## (Could delete $(TEMP) when finished, but we don't to make it easier to check the contents of the result
post: .FORCE
	rm -rf $(TEMP)
	mkdir $(TEMP)
	cp -pRL jmlruntime.jar $(TEMP)
	cp -pRL jmlruntime.jar $(TUT)
	cp -pRL build/*release/jdk $(TEMP)
	(cd $(TEMP); rm -rf `find . -name .DS_Store`)
	cp -pR ../../Solvers/Solvers-$(OS_NAME) $(TEMP)
	uname
	uname -m
	cp -pR ../../Specs/specs $(TEMP)
	cp -pR $(RELFILES)/* $(TEMP)
	cp setup-exports setup-vars openjml openjml-* $(TEMP)
	$(MAKE) openjml-lsp
	chmod ugo+x $(TEMP)/openjml $(TEMP)/openjml-* $(TEMP)/install-vscode-extension
	(cd $(TEMP); $(ZIPCMD) -qr ./openjml.zip * )

openjml-lsp:
	$(MAKE) -C ../OpenJMLlsp release
	cp -pR ../OpenJMLlsp/release-stage/. $(TEMP)

openjml-ui:
	../OpenJMLUI/release.sh --version `cat ../version.txt` --overwrite


USERGUIDE=tempUserGuide
REFMANID=5ceee26404c2854a1590029f
USERGUIDEID=620c2512d552cc226f5f4c94
ZIPNAME=userguide-examples.zip
## Creates a zip file of the user guide examples
userguide-examples:
	@ ( rm -rf $(USERGUIDE); mkdir -p ${USERGUIDE}; cd ${USERGUIDE}; git clone https://git@git.overleaf.com/${USERGUIDEID} ; )
	@ if [ -e ${USERGUIDE}/${USERGUIDEID}/examples ] ; then \
	        (cd ${USERGUIDE}/${USERGUIDEID}; $(ZIPCMD) -rq $(ZIPNAME) installLocation test-userguide-examples examples; mv ${ZIPNAME} ../../../../openjml.github.io/examples ); \
	        rm -rf ${USERGUIDE}; ls -la ../../openjml.github.io/examples/${ZIPNAME}; \
	else echo Userguide examples are not available; fi

TEMPDOCS=tempDocs
# Mac-specific path; adjust for other platforms
DOWNLOADS=$(HOME)/Desktop
## Pulls the JML reference manual and the OpenJML User Guide LaTeX sources from Overleaf and then builds the pdfs locally (not using Overleaf to build)
## Requires a local installation of pdflatex
update-docs:
	rm -rf ${DOWNLOADS}/OpenJMLUserGuide.pdf ${DOWNLOADS}/JML_Reference_Manual.pdf
	$(MAKE) userguide-examples
	@ ( rm -rf $(TEMPDOCS); mkdir -p ${TEMPDOCS}; cd ${TEMPDOCS}; git clone https://git@git.overleaf.com/${REFMANID} ; cd ${REFMANID}; pdflatex JMLReferenceManual.tex --interaction batchmode ; bibtex JMLReferenceManual ; pdflatex JMLReferenceManual.tex --interaction batchmode; pdflatex JMLReferenceManual.tex --interaction batchmode ; mv *.pdf ${DOWNLOADS}/JML_Reference_Manual.pdf; )
	@ ( rm -rf $(TEMPDOCS); mkdir -p ${TEMPDOCS}; cd ${TEMPDOCS}; git clone https://git@git.overleaf.com/${USERGUIDEID} ; cd ${USERGUIDEID} ; pdflatex OpenJMLUserGuide.tex --interaction batchmode; bibtex OpenJMLUserGuide; pdflatex OpenJMLUserGuide.tex --interaction batchmode ; pdflatex OpenJMLUserGuide.tex --interaction batchmode ; mv *.pdf ${DOWNLOADS}; )
	cp "${DOWNLOADS}/OpenJMLUserGuide.pdf" ../../openjml.github.io/documentation
	cp "${DOWNLOADS}/OpenJMLUserGuide.pdf" "$(RELFILES)"
	cp "${DOWNLOADS}/JML_Reference_Manual.pdf" ../../openjml.github.io/documentation
	cp "${DOWNLOADS}/JML_Reference_Manual.pdf" "$(RELFILES)"
	cp ../OpenJMLUI/html/JMLHelp.html ../../openjml.github.io/documentation

## Commits and pushes the builds produced by `update-docs` to openjml.github.io
## (Does not commit them to the current branch of OpenJMLsrc)
push-docs:
	( cd ../../openjml.github.io; git pull; git add documentation/JMLHelp.html documentation/OpenJMLUserGuide.pdf documentation/JML_Reference_Manual.pdf examples/${ZIPNAME} ; git commit -m "Updating docs"; git push )

## Smoke test of a newly constructed release
trial: .FORCE
	$(TEMP)/openjml --version
	$(TEMP)/openjml --esc --progress $(TEMP)/demos/Max.java

## Tests the most recently created release (release-temp/openjml.zip)
release-test: .FORCE
	@ echo Running release tests on newly created trial release
	@ ZIPARCHIVE="$(topdir)/$(TEMP)/openjml.zip" "$(topdir)/../OpenJMLTest/releaseTests/runtests"

## Development build targets

## Builds the openjml executable (without updating version, annotation and tutorial files)
## NOJML= disables JML during the build of OpenJML itself (since the openjml executable is the javac executable)
## On WSL, Windows PE binaries (java.exe) only inherit env vars listed in WSLENV; we add NOJML there so
## the Windows JVM running the interim bootstrap compiler also sees NOJML and returns false from Utils.isJML().
openjml: .FORCE
	NOJML= WSLENV="$${WSLENV:+$$WSLENV:}NOJML" $(MAKE)

## Updates the smt code from the jSMTLIB repo 
## The repo must be cloned locally and resident at ../../../jSMTLIB relative to the folder holding this Makefile
## This action is rarely needed
smt:
	if [ -e $(topdir)/../../../jSMTLIB/SMT ]; then \
	    cp -Rp $(topdir)/../../../jSMTLIB/SMT/src/org/ src/jdk.compiler/share/classes/org ; \
	elif [ -e $(topdir)/../../jSMTLIB/SMT ]; then \
	    cp -Rp $(topdir)/../../jSMTLIB/SMT/src/org/ src/jdk.compiler/share/classes/org ; \
	fi

## Builds the jmlruntime.jar, which holds classes needed for running rac
jmlruntime.jar: .FORCE
	@rm -rf $(TEMPLIB)
	@mkdir $(TEMPLIB)
	@mkdir -p $(TEMPLIB)/org/jmlspecs/runtime
	@mkdir -p $(TEMPLIB)/org/jmlspecs/annotation
	@cp build/*/jdk/modules/java.base/org/jmlspecs/runtime/*.class $(TEMPLIB)/org/jmlspecs/runtime
	@ ## Annotations are generally not needed at runtime, but they are included just in case one is executed in the future
	@cp build/*/jdk/modules/java.base/org/jmlspecs/annotation/*.class $(TEMPLIB)/org/jmlspecs/annotation
	@touch $(TEMPLIB)/JMLRUNTIME_MARKER
	@## jmlruntime.jar has bin-runtime, the annotations, and the marker file JMLRUNTIME_MARKER
	@## If Java is incorrectly setup, the jar command fails - so we check it this first time
	@(cd $(TEMPLIB); $(JAR) -cf ../jmlruntime.jar . ) || exit 1
	@rm -rf $(TEMPLIB)
	@echo "   " jmlruntime.jar created

