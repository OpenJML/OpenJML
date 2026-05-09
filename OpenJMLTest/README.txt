This OpenJMLTest project contains the test cases for OpenJML.
Information about the organization and running of the tests is found in the project wiki.

Quick info on the contents of the folder:

src - the JUnit tests
test - the folder containing the source files and expected results for unittests, used by the files in src
testspecs - material for testing the library specifications
releaseTests - material for smoke-testing a release
apitests - old (FIXME - obsolete?) tests of the api

libs - libraries used in the unittests
jacoco - the Jacoco release for doing coverage measurement

unittests - scripts for running all the JUnit unittests
scripttests - convenience scripts for running individual file-based tests

Makefile - the Makefile for the tests, including some convenience targets that call make in the OpenJML source folder

setup-coverage - a script used to setup for coverage measurement during testing (cf. make cov-test )
RunOpenJML.java - a wrapper program needed when running coverage, profiling or any program using the OpenJML programmatic API

Temporary files:
testcompiles - a folder holding all the (temporary) .class files generated when testing RAC
smt - a folder holding (temporary) smt files generated during ESC
temp-release - a temp folder that holds an expanded release for testing
cov - a folder holding (intermediate) results of coverage testing

launchConfigs - FIXME obsolete
