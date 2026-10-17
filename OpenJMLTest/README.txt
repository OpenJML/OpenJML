This OpenJMLTest project contains the test cases for OpenJML.
Information about the organization and running of the tests is found in the project wiki.

Quick info on the contents of the folder:

src - the JUnit tests
test - the folder containing the source files and expected results for unittests, used by the files in src
testspecs - material for testing the library specifications
releaseTests - material for smoke-testing a release
apitests - old (FIXME - obsolete?) tests of the api

libs - libraries used in the unittests
jacoco - the Jacoco release for doing coverage measurement (a customized build), and coverage-analyzer
    with the org.jacoco.core and ASM jars it runs on, for finding redundant tests (make cov-test-by-test)

unittests - scripts for running all the JUnit unittests
scripttests - convenience scripts for running individual file-based tests

Makefile - the Makefile for the tests, including some convenience targets that call make in the OpenJML source folder

setup-coverage - a script used to setup for coverage measurement during testing (cf. make cov-test )
    make cov-test-by-test records each unit test's coverage in its own file (cov/by-test) and then
    runs coverage-analyzer (make cov-analyze-by-test), which reports empty, duplicate and subsumed
    tests and a minimum-run-time set of tests covering everything the suite covers
    (cov/by-test-report.txt, and CSV files in cov/by-test-report); SUITES="..." limits the run to
    some test suites. make cov-report-by-test merges the per-test data into one HTML report.
RunOpenJML.java - a wrapper program needed when running coverage, profiling or any program using the OpenJML programmatic API

Temporary files:
testcompiles - a folder holding all the (temporary) .class files generated when testing RAC
smt - a folder holding (temporary) smt files generated during ESC
temp-release - a temp folder that holds an expanded release for testing
cov - a folder holding (intermediate) results of coverage testing

launchConfigs - FIXME obsolete
