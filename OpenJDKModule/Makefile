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

mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
mkfile_dir := $(dir $(mkfile_path))

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

release: clean version openjml post

version:
	./version.sh

post:
	rm -rf $(REL)
	mkdir $(REL)
	cp -pRL build/*release/jdk $(REL)
	if [ `uname` = 'Darwin' ]; then echo Mac ; export S=macos ; elif [ `uname` = 'Linux' ]; then echo Linux; export S=linux ; else echo Win; export S=windows ; fi ;\
	    cp -pR ../../Solvers/Solvers-$$S $(REL)
	cp -pR ../../Specs/specs $(REL)
	cp -pR release-files/* $(REL)
	chmod ugo+x $(REL)/openjml
	(cd $(REL); zip -qr ./openjml.zip * )

trial:
	$(REL)/openjml -version
	$(REL)/openjml -esc -progress $(REL)/demos/Max.java

# Tests a recently created release (releae-temp/openjml.zip)
release-test:
	$(topdir)/../OpenJMLTest/releaseTests/runtests

## Development build targets

openjml: .FORCE
	NOJML= make
	##make jmlruntime.jar

smt:
	if [ -e $(mkfile_dir)/../../../jSMTLIB/SMT ]; then \
	    cp -Rp $(mkfile_dir)/../../../jSMTLIB/SMT/src/org/ src/jdk.compiler/share/classes/org ; \
	elif [ -e $(mkfile_dir)/../../jSMTLIB/SMT ]; then \
	    cp -Rp $(mkfile_dir)/../../jSMTLIB/SMT/src/org/ src/jdk.compiler/share/classes/org ; \
	fi

jmlruntime.jar:
	cp -r bin-runtime/* temp2
	cp -r ${ANNOTATIONS}/bin/* temp2
	touch temp2/JMLRUNTIME_MARKER
	## jmlruntime.jar has bin-runtime, the annotations, and the marker file JMLRUNTIME_MARKER
	## If Java is incorrectly setup, the jar command fails - so we check it this first time
	(cd temp2; jar -cf ../${TEMPJAR}/jmlruntime.jar . ) || exit 1
	rm -rf temp2
	echo "   " jmlruntime.jar created

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

