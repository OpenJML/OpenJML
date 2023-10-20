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

#### Additions for building OpenJML in the GitHub actions

REL=release-temp

## Used in the github build.yml action

release: clean version-info openjml jmlruntime.jar tutorial post

version:
	@ if [ ! -e ../version.txt ]; then echo "No version.txt file"; else echo "Building version" `cat ../version.txt`; fi
	@ ./version.sh

version-info: version
	@ rm -f version-info.txt
	@ cat ../version.txt > version-info.txt
	@ echo "OpenJML" `git rev-parse HEAD` >> version-info.txt
	@ (cd ../../Specs; echo "Specs" `git rev-parse HEAD`) >> version-info.txt
	@ (cd ../../JMLAnnotations; echo JMLAnnotations `git rev-parse HEAD` ) >> version-info.txt
	@ (cd ../../Solvers; echo Solvers `git rev-parse HEAD` ) >> version-info.txt
	@ (cd ../../openjml.github.io; echo openjml.github.io `git rev-parse HEAD` ) >> version-info.txt
	@ cat version-info.txt
	@ mv version-info.txt release-files

tutorial:
	rm -rf release-files/tutorial
	mkdir release-files/tutorial
	cp -pR ../../openjml.github.io/tutorial/*.java ../../openjml.github.io/tutorial/*.out release-files/tutorial

annotation:
	cp -pR ../../JMLAnnotations/src/org  src/java.base/share/classes

post:
	rm -rf $(REL)
	mkdir $(REL)
	cp -pRL jmlruntime.jar $(REL)
	cp -pRL build/*release/jdk $(REL)
	if [ `uname` = 'Darwin' ]; then echo Mac ; export S=macos ; elif [ `uname` = 'Linux' ]; then echo Linux; export S=linux ; else echo Win; export S=windows ; fi ;\
	cp -pR ../../Solvers/Solvers-$$S $(REL)
	cp -pR ../../Specs/specs $(REL)
	cp -pR release-files/* $(REL)
	chmod ugo+x $(REL)/openjml
	chmod ugo+x $(REL)/openjml-java
	(cd $(REL); zip -qr ./openjml.zip * )

trial:
	$(REL)/openjml -version
	$(REL)/openjml -esc -progress $(REL)/demos/Max.java

# Tests the most recently created release (release-temp/openjml.zip)
release-test:
	@ $(topdir)/../OpenJMLTest/releaseTests/runtests

## Development build targets

openjml: .FORCE
	NOJML= make

smt:
	if [ -e $(mkfile_dir)/../../../jSMTLIB/SMT ]; then \
	    cp -Rp $(mkfile_dir)/../../../jSMTLIB/SMT/src/org/ src/jdk.compiler/share/classes/org ; \
	elif [ -e $(mkfile_dir)/../../jSMTLIB/SMT ]; then \
	    cp -Rp $(mkfile_dir)/../../jSMTLIB/SMT/src/org/ src/jdk.compiler/share/classes/org ; \
	fi

jmlruntime.jar: .FORCE
	@rm -rf templib
	@mkdir templib
	@mkdir -p templib/org/jmlspecs/runtime
	@mkdir -p templib/org/jmlspecs/annotation
	@cp build/*/jdk/modules/java.base/org/jmlspecs/runtime/*.class templib/org/jmlspecs/runtime
	@ ## Annotations are generally not needed at runtime, but they are included just in case one is executed in the future
	@cp build/*/jdk/modules/java.base/org/jmlspecs/annotation/*.class templib/org/jmlspecs/annotation
	@touch templib/JMLRUNTIME_MARKER
	@## jmlruntime.jar has bin-runtime, the annotations, and the marker file JMLRUNTIME_MARKER
	@## If Java is incorrectly setup, the jar command fails - so we check it this first time
	@(cd templib; jar -cf ../jmlruntime.jar . ) || exit 1
	@rm -rf templib
	@echo "   " jmlruntime.jar created

## Misc helpful targets

clean-release:
	make clean dist-clean
	rm -rf $(REL)

release-image: version
	bash ./configure > log-release
	NOJML= make images > log-release-make 2>&1
	make post

release-quiet: version
	bash ./configure > log-release
	NOJML= make > log-release-make 2>&1
	make post


