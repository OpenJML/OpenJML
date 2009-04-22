## This makefile builds releases

ROOT=..
SPECS=../../../JMLspecs/trunk
VERSION:=$(shell date +%Y%m%d)
NAME=jml-${VERSION}.tar.gz

## Builds the release components and then tests it
jar: jars jmlruntime.jar tar
	@echo Release complete
	@echo Testing
	./releaseTest  ${NAME}
	@echo Testing Complete

## Builds a tar file of the release components
tar: openjml.jar jmlruntime.jar jmlspecs.jar
	tar -zcf ${NAME} README openjml.jar jmlruntime.jar jmlspecs.jar 

## Builds the individual jar files that constitute the release
## namely jmlspecs.jar and openjml.jar
jars jmlspecs.jar openjml.jar:
	echo `pwd`
	rm -rf temp temp2
	(cd src/com/sun/tools/javac/resources; cat version.template | sed s/VERSION/JML-${VERSION}/ > version.properties )
	mkdir temp
	(cd temp; for j in ${ROOT}/../OpenJML/otherlibs/* ; do jar xf $$j; echo $$j; done; rm -rf META-INF )
	cp -r ${ROOT}/OpenJML/bin/* temp
	cp -r ${ROOT}/OpenJDK/bin/* temp
	mkdir temp/specs14 temp/specs15 temp/specs16
	cp -r ${SPECS}/java4/* temp/specs14
	find temp/specs14 -name .svn -exec rm -rf \{\} +
	cp -r temp/specs14/* temp/specs15
	cp -r ${SPECS}/java5/* temp/specs15
	find temp/specs15 -name .svn -exec rm -rf \{\} +
	cp -r temp/specs15/* temp/specs16
	cp -r ${SPECS}/java6/* temp/specs16
	find temp/specs16 -name .svn -exec rm -rf \{\} +
	(cd temp/specs16; jar -cf ../../jmlspecs.jar . )
	mkdir temp2
	echo "Manifest-Version: 1.0" > temp2/manifest
	echo "Main-Class: org.jmlspecs.openjml.Main" >> temp2/manifest
	rm -r temp/tests
	(cd temp; jar -cfm ../openjml.jar ../temp2/manifest . )
	rm -rf temp temp2

## Builds jmlruntime.jar
jmlruntime.jar:
	rm -rf temp
	mkdir  -p temp/org/jmlspecs
	cp -r bin/org/jmlspecs/annotations bin/org/jmlspecs/lang bin/org/jmlspecs/models temp/org/jmlspecs
	(cd temp; jar -cf ../jmlruntime.jar . ) 
	rm -rf temp

## Separate target for jmlspecs.jar, though it is normally built along with
## openjml.jar
jmlspecs:
	mkdir temp
	mkdir temp/specs14 temp/specs15 temp/specs16
	cp -r ${SPECS}/java4/* temp/specs14
	find temp/specs14 -name .svn -exec rm -rf \{\} +
	cp -r temp/specs14/* temp/specs15
	cp -r ${SPECS}/java5/* temp/specs15
	find temp/specs15 -name .svn -exec rm -rf \{\} +
	cp -r temp/specs15/* temp/specs16
	cp -r ${SPECS}/java6/* temp/specs16
	find temp/specs16 -name .svn -exec rm -rf \{\} +
	(cd temp/specs16; jar -cf ../../jmlspecs.jar . )
	rm -rf temp
