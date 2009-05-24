## This makefile builds releases
## The default target builds the release and tests it
## The release is named according to the current date.  Thus subsequent
## builds on the same day will overwrite the release (by design).
##
## Other targets:
##	release - just build the release
##	test - just test the current release
ROOT=..
SPECS=../../../JMLspecs/trunk
VERSION:=$(shell date +%Y%m%d)
NAME=jml-${VERSION}.tar.gz

## Default - build and test the release
.PHONY: release-and-test
release-and-test: release test

## Just build a release named ${NAME}
.PHONY: release
release: other alljars jmlruntime.jar tar
	@echo Release complete

${NAME}: release

other:
	diff ../OpenJMLUI/plugin.xml ../OpenJML-DevUI/plugin.xml || echo "PLUGINS ARE DIFFERENT - RESOLVE!!!!!"
	diff -r ../OpenJMLUI/icons ../OpenJML-DevUI/icons || echo "ICON DIRECTORIES ARE DIFFERENT - RESOLVE!!!!!"
	diff -r ../OpenJMLUI/html ../OpenJML-DevUI/html || echo "HTML DIRECTORIES ARE DIFFERENT - RESOLVE!!!!!"


## Test the release named ${NAME}
.PHONY: test
test: 
	@echo Testing
	releaseTests/runTests  ${NAME} 
	@echo Testing Complete

## Builds a tar file of the release components
.PHONY: tar
tar:
	(cd jars; cp ../README . ; tar -zcf ../${NAME} README openjml.jar jmlruntime.jar jmlspecs.jar )
	##rm -rf jars  ## We don't delete them because some tests use them
	
## Builds the individual jar files that constitute the release
## namely jmlspecs.jar and openjml.jar
.PHONY: alljars
alljars jmlspecs.jar openjml.jar:
	echo `pwd`
	rm -rf temp temp2
	(cd src/com/sun/tools/javac/resources; cat version.template | sed s/VERSION/JML-${VERSION}/ > version.properties )
	cp src/com/sun/tools/javac/resources/version.properties bin/com/sun/tools/javac/resources/version.properties
	echo "jml JML-${VERSION}" > releaseTests/testJmlVersion/expected
	mkdir temp
	mkdir -p jars
	rm -f jars/jmlspecs.jar jars/openjml.jar
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
	(cd temp/specs16; jar -cf ../../jars/jmlspecs.jar . )
	mkdir temp2
	echo "Manifest-Version: 1.0" > temp2/manifest
	echo "Main-Class: org.jmlspecs.openjml.Main" >> temp2/manifest
	rm -r temp/tests
	(cd temp; jar -cfm ../jars/openjml.jar ../temp2/manifest . )
	cp jars/openjml.jar ../OpenJMLUI
	rm -rf temp temp2

## Builds jmlruntime.jar
jmlruntime.jar:
	rm -rf temp
	mkdir -p temp/org/jmlspecs
	mkdir -p jars
	rm -f jars/jmlruntime.jar
	cp -r bin/org/jmlspecs/annotations bin/org/jmlspecs/lang bin/org/jmlspecs/models bin/org/jmlspecs/utils temp/org/jmlspecs
	(cd temp; jar -cf ../jars/jmlruntime.jar . ) 
	cp jars/jmlruntime.jar ../OpenJMLUI
	rm -rf temp

## Separate target for jmlspecs.jar, though it is normally built along with
## openjml.jar
jmlspecs:
	mkdir temp
	mkdir temp/specs14 temp/specs15 temp/specs16
	mkdir jars
	rm -f jars/jmlspecs.jar
	cp -r ${SPECS}/java4/* temp/specs14
	find temp/specs14 -name .svn -exec rm -rf \{\} +
	cp -r temp/specs14/* temp/specs15
	cp -r ${SPECS}/java5/* temp/specs15
	find temp/specs15 -name .svn -exec rm -rf \{\} +
	cp -r temp/specs15/* temp/specs16
	cp -r ${SPECS}/java6/* temp/specs16
	find temp/specs16 -name .svn -exec rm -rf \{\} +
	(cd temp; jar -cf ../jars/jmlspecs.jar specs16 specs15 specs14 )
	rm -rf temp
