## This makefile builds releases
## The default target builds the release and tests it
## The release is named according to the current date.  Thus subsequent
## builds on the same day will overwrite the release (by design).
##
## Other targets:
##	release - just build the release
##	test - just test the current release

## The following file defines ROOT, SPECS, ANNOTATIONS per the local file system
include Makefile.local

VERSION:=$(shell date +%Y%m%d)
NAME=openjml-${VERSION}.tar.gz

## Default - build and test the release
.PHONY: release-and-test
release-and-test: release test

## Just build a release named ${NAME}
.PHONY: release
release: other alljars jmlruntime.jar tar copy
	@echo Release complete

${NAME}: release

other:
	diff ../OpenJMLUI/plugin.xml ../OpenJML-DevUI/plugin.xml || echo "PLUGINS ARE DIFFERENT - RESOLVE!!!!!"
	diff -r -x ".svn" ../OpenJMLUI/icons ../OpenJML-DevUI/icons || echo "ICON DIRECTORIES ARE DIFFERENT - RESOLVE!!!!!"
	diff -r -x ".svn" ../OpenJMLUI/html ../OpenJML-DevUI/html || echo "HTML DIRECTORIES ARE DIFFERENT - RESOLVE!!!!!"


## Test the release named ${NAME}
.PHONY: test
test: 
	@echo Testing
	##( source ~/mybin/java15.sh; releaseTests/runTests  ${NAME} ) 
	( source ~/mybin/java16.sh; releaseTests/runTests  ${NAME} ) 
	@echo Testing Complete `date`

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
	-rm -rf temp temp2
	(cd src/com/sun/tools/javac/resources; cat version.template | sed s/VERSION/OpenJML-${VERSION}/ > version.properties )
	cp src/com/sun/tools/javac/resources/version.properties bin/com/sun/tools/javac/resources/version.properties
	echo "openjml OpenJML-${VERSION}" > releaseTests/testJmlVersion/expected
	mkdir -p temp
	mkdir -p jars
	rm -f jars/jmlspecs.jar jars/openjml.jar
	(cd temp; for j in ${ROOT}/../OpenJML/otherlibs/* ; do jar xf $$j; echo $$j; done; rm -rf META-INF )
	cp -r ${ROOT}/OpenJDK/bin/* temp
	cp -r ${ROOT}/OpenJML/bin/* temp
	cp -r ${ROOT}/OpenJML/bin-runtime/* temp
	cp -r ${ANNOTATIONS}/bin/* temp
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
	mkdir -p temp2
	echo "Manifest-Version: 1.0" > temp2/manifest
	echo "Main-Class: org.jmlspecs.openjml.Main" >> temp2/manifest
	(cd temp; jar -cfm ../jars/openjml.jar ../temp2/manifest . )
	##cp jars/openjml.jar ../OpenJMLUI
	
copy:
	(cd ../OpenJMLUI; rm -rf runtime openjml specs ; )
	(cd ../OpenJMLUI; mkdir -p specs ;)
	cp -rf ${SPECS}/java7 ../OpenJMLUI/specs
	cp -rf ${SPECS}/java6 ../OpenJMLUI/specs
	cp -rf ${SPECS}/java5 ../OpenJMLUI/specs
	cp -rf ${SPECS}/java4 ../OpenJMLUI/specs
	find ../OpenJMLUI/specs -name .svn -exec rm -rf \{\} +
	mkdir -p ../OpenJMLUI/openjml
	mkdir -p ../OpenJMLUI/runtime
	cp -r ${ROOT}/OpenJDK/bin/* ../OpenJMLUI/openjml
	cp -r ${ROOT}/OpenJML/bin/* ../OpenJMLUI/openjml
	cp -r ${ROOT}/OpenJML/bin-runtime/* ../OpenJMLUI/runtime
	cp -r ${ANNOTATIONS}/bin/* ../OpenJMLUI/runtime
	echo "Copy to OpenJMLUI complete"
	
## Builds jmlruntime.jar
jmlruntime.jar:
	mkdir -p temp2
	mkdir -p jars
	rm -f jars/jmlruntime.jar
	cp -r bin-runtime/* temp2
	cp -r ${ANNOTATIONS}/bin/* temp2
	(cd temp2; jar -cf ../jars/jmlruntime.jar . ) 
	rm -rf temp2

## Separate target for jmlspecs.jar, though it is normally built along with
## openjml.jar
jmlspecs:
	mkdir -p temp
	mkdir temp/specs14 temp/specs15 temp/specs16
	mkdir -p jars
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
	-rm -rf temp
	
jdkbin:
	java -jar jars/openjml.jar -classpath "jdksrc;jars/openjml.jar" -d jdkbin -nullableByDefault -target 1.5 jdksrc/java/io/File.java -noPurityCheck -rac -specspath ${SPECS}/java5
