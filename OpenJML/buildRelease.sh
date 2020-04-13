#!/bin/bash

## FIXME: This script works when run standalone in Cygwin or from Eclipse
## launched from Cygwin, but NOT from Eclipse launched from Windows.

## This script builds releases
## It is meant to be built from the root of the collection of OpenJML projects,
## that is, the current working directory should have OpenJML, Specs, JMLAnnotations,
## OpenJDK, and OpenJMLUI as direct subdirectories.


umask 022

## If these variables are not set, we set them to what they will be in 
## a standard Eclipse project setup for OpenJML.

if [[ "${ROOT}" == "" ]]; then
    ROOT=..
fi
if [[ "${ANNOTATIONS}" == "" ]]; then
    ANNOTATIONS=../../JMLAnnotations
fi
if [[ "${SPECS}" == "" ]]; then
    SPECS=../../Specs
fi

## Within Eclipse (in Cygwin at least), the paths that are defined do not work
## here, so we just set them.
    ROOT=..
    ANNOTATIONS=../../JMLAnnotations
    SPECS=../../Specs
    SOLVERS=../../Solvers
    UI=../OpenJMLUI

TEMPJAR=tempjars
RB=releaseBuilds

DATE=`date +%Y%m%d`
BRANCH=`git rev-parse --abbrev-ref HEAD`
##BRANCH=`git branch | grep '*' | sed 's/* //'`
NUM=`cat ../OpenJMLFeature/feature.xml | grep version | grep -v xml | head -1 | sed -e 's/      version=//' -e 's/\"//g'`
echo Branch = ${BRANCH}, VersionNumber = ${NUM}, Date = ${DATE}
if [ "${BRANCH}" = "master" ]; then VERSION=${NUM}-$DATE ; else VERSION=${BRANCH}-${DATE}; fi

NAME=openjml-${VERSION}.zip

	echo Building ${NAME}, version ${VERSION} in `pwd`

##### Make temp files, cleanup
	mkdir -p temp2; chmod -R u+rwx,a+rx temp2
	mkdir -p ${TEMPJAR}; chmod -R u+rwx,a+rx ${TEMPJAR}
	rm -f ${TEMPJAR}/jmlruntime.jar

##### Record versions
	rm -f ${TEMPJAR}/VERSION_INFO
	touch ${TEMPJAR}/VERSION_INFO
	echo "OpenJML " `git rev-parse --abbrev-ref HEAD` `git rev-parse HEAD` >> ${TEMPJAR}/VERSION_INFO
	(cd ${ANNOTATIONS}; echo "JMLAnnotations " `git rev-parse --abbrev-ref HEAD` `git rev-parse HEAD` )  >> ${TEMPJAR}/VERSION_INFO
	(cd ${SPECS};       echo "Specs " `git rev-parse --abbrev-ref HEAD` `git rev-parse HEAD` )  >> ${TEMPJAR}/VERSION_INFO
	(cd ${SOLVERS};     echo "Solvers " `git rev-parse --abbrev-ref HEAD` `git rev-parse HEAD` ) >> ${TEMPJAR}/VERSION_INFO
	cat ${TEMPJAR}/VERSION_INFO
	
##### Build jmlruntime.jar
	cp -r bin-runtime/* temp2
	cp -r ${ANNOTATIONS}/bin/* temp2
	touch temp2/JMLRUNTIME_MARKER
	## jmlruntime.jar has bin-runtime, the annotations, and the marker file JMLRUNTIME_MARKER
	## If Java is incorrectly setup, the jar command fails - so we check it this first time
	(cd temp2; jar -cf ../${TEMPJAR}/jmlruntime.jar . ) || exit 1
    cp ${TEMPJAR}/jmlruntime.jar ${UI}
	rm -rf temp2
	echo "   " jmlruntime.jar created

###### Build jmlspecs.jar openjml.jar:
	test -d temp && chmod -R u+rwx,a+rx temp || rm -rf temp
	test -d temp2 && chmod -R u+rwx,a+rx temp2 || rm -rf temp2
	(cd src/com/sun/tools/javac/resources; cat version.template | sed s/VERSION/OpenJML-${VERSION}/ > version.properties )
	cp src/com/sun/tools/javac/resources/version.properties bin/com/sun/tools/javac/resources/version.properties
	echo "openjml OpenJML-${VERSION}" > ../OpenJMLTest/releaseTests/testJmlVersion/expected
	mkdir -p temp; chmod -R u+rwx,go+rx temp
	mkdir -p ${TEMPJAR}; chmod -R u+rwx,go+rx ${TEMPJAR}
	rm -f ${TEMPJAR}/jmlspecs.jar ${TEMPJAR}/openjml.jar
	echo "   " Copying files
	(cd temp; for j in ../otherlibs/* ; do jar xf $j; done; rm -rf META-INF )
	chmod -R a+rwx,go+rx ${ROOT}/OpenJDK/bin ${ROOT}/OpenJML/bin*
    cp -r ${ROOT}/OpenJDK/bin/* temp
	cp -r ${ROOT}/OpenJML/bin/* temp
	cp -r ${ROOT}/OpenJML/bin-runtime/* temp
	cp -r ${ANNOTATIONS}/bin/* temp
	cp ${TEMPJAR}/VERSION_INFO temp
	cp jSMTLIB.jar temp
	cp otherlibs/*.jar temp
	mkdir -p temp/specs; chmod -R u+rwx,a+rx temp
	cp -r ${SPECS}/specs/* temp/specs
	echo "   " Creating jmlspecs.jar
	## The jmlspecs.jar contains the composite Java 1.8 specs files
	## The openjml.jar file contains the OpenJDK and OpenJML class files, and the specs directories, combined for each Java version
	(cd temp/specs; jar -cf ../../${TEMPJAR}/jmlspecs.jar . ) || exit 1
	
	(cd temp; jar xf ../jSMTLIB.jar ) || exit 1
	cp -r bin-runtime/* temp
    cp -r ${ANNOTATIONS}/bin/* temp
    touch temp/JMLRUNTIME_MARKER
	
	mkdir -p temp2; chmod -R u+rwx,a+rx temp2
	echo "   " Creating openjml.jar
	echo "Manifest-Version: 1.0" > temp2/manifest
	echo "Main-Class: org.jmlspecs.openjml.Main" >> temp2/manifest
	(cd temp; jar -cfm ../${TEMPJAR}/openjml.jar ../temp2/manifest . ) || exit 1
	##cp ${TEMPJAR}/openjml.jar ../OpenJMLUI
	echo "   " jmlspecs.jar openjml.jar created
	
    rm -rf temp temp2

##### Copy solvers to the zip file location
    cp -r ../../Solvers/Solvers-* ${TEMPJAR}
        
##### Collect other files for the zip file
    cp legal/* ${TEMPJAR}
#        ##(echo Building user manual; cd documentation/OpenJMLUserGuide; rm -f *.pdf; make all > build.log )
    DOC=/Users/davidcok/cok/texstuff/papers/JMLBook
    if [ -e $DOC/OpenJMLUserGuide.pdf ]; then
        cp $DOC/OpenJMLUserGuide.pdf ${TEMPJAR} && echo "   " UserGuide copied
        if ! cmp -s ${TEMPJAR}/OpenJMLUserGuide.pdf ../OpenJMLUI/html/OpenJMLUserGuide.pdf; then
		    cp ${TEMPJAR}/OpenJMLUserGuide.pdf ../OpenJMLUI/html
		    echo "        " Changed
		fi
		cp $DOC/jml-reference-manual.pdf ${TEMPJAR} && echo "   " RefMan copied
        if ! cmp -s ${TEMPJAR}/jml-reference-manual.pdf ../OpenJMLUI/html/JMLReferenceManual.pdf; then
		    cp ${TEMPJAR}/jml-reference-manual.pdf ../OpenJMLUI/html/JMLReferenceManual.pdf
		    echo "        " Changed
		fi
    else
        echo No User Guide file is found
    fi
    
##### Build the zip file
	(cd ${TEMPJAR}; \
    cp ../openjml-template.properties . ;\
	zip -qr ../${RB}/${NAME} *)
	##rm -rf ${TEMPJAR}  ## We don't delete them because some tests use them
	echo "   " zip created ${RB}/${NAME}
	    
##### End	
	echo Release complete ${NAME}
