

jmlruntime.jmod:
	(cd $(dir $(lastword $(MAKEFILE_LIST))) ; \
	  pwd ; rm -rf bin out jmlruntime.jmod ; \
	  javac -d out --module-source-path src `find src -name '*.java'` ; \
	  jmod create --class-path out/org.openjml.runtime jmlruntime.jmod )
