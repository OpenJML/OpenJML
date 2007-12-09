ROOT=..

jar: jars jmlruntime tar
	@echo Release complete

tar:
	tar -zcf jml-`date +%Y%m%d`.tar.gz README openjml.jar jmlruntime.jar jmlspecs.jar 

jars:
	echo `pwd`
	rm -rf temp temp2
	(cd src/com/sun/tools/javac/resources; cat version.template | sed s/VERSION/JML-`date +%Y%m%d`/ > version.properties )
	mkdir temp
	cp -r ${ROOT}/OpenJML/bin/* temp
	cp -r ${ROOT}/OpenJDK/bin/* temp
	cp -r ${ROOT}/FreeBoogie/bin/* temp
	mkdir temp/specs14 temp/specs15 temp/specs16
	cp -r ${ROOT}/OpenJML/specs/specs14/* temp/specs14
	find temp/specs14 -name .svn -exec rm -rf \{\} +
	cp -r temp/specs14/* temp/specs15
	cp -r ${ROOT}/OpenJML/specs/specs15/* temp/specs15
	find temp/specs15 -name .svn -exec rm -rf \{\} +
	cp -r temp/specs15/* temp/specs16
	cp -r ${ROOT}/OpenJML/specs/specs16/* temp/specs16
	find temp/specs16 -name .svn -exec rm -rf \{\} +
	(cd temp/specs16; jar -cf ../../jmlspecs.jar . )
	mkdir temp2
	echo "Manifest-Version: 1.0" > temp2/manifest
	echo "Main-Class: org.jmlspecs.openjml.Main" >> temp2/manifest
	rm -r temp/tests
	(cd temp; jar -cfm ../openjml.jar ../temp2/manifest . )
	rm -rf temp temp2

jmlruntime:
	rm -rf temp
	mkdir  -p temp/org/jmlspecs
	cp -r bin/org/jmlspecs/annotations bin/org/jmlspecs/lang bin/org/jmlspecs/models temp/org/jmlspecs
	(cd temp; jar -cf ../jmlruntime.jar . ) 
	rm -rf temp

jmlspecs:
	rm -rf temp2
	mkdir temp2
	cp -r specs/specs14/* temp2
	cp -rf specs/specs15/* temp2
	cp -rf specs/specs16/* temp2
	(cd temp2; jar -cf ../jmlspecs.jar . )
	rm -rf temp temp2
