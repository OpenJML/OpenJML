#!/bin/bash


## This script runs tests on a release build.
## The working directory in running the script is expected to be the OpenJMLTest
## directory of the source tree and where the Eclipse test data is located


## It tests a build with today's date - i.e. the build just created by
## ./buildRelease.sh

## You should have the appropriate version of Java on your path

## Within Eclipse (in Cygwin at least), the paths that are defined do not work
## here, so we just set them.
export ROOT=..
export ANNOTATIONS=../JMLAnnotations
export SPECS=../Specs



VERSION=`date +%Y%m%d`
NAME=openjml-${VERSION}.zip

echo Testing
chmod ugo+x releaseTests/runTests releaseTests/releaseTestHelper 
/bin/bash releaseTests/runTests  ${NAME}
echo Testing Complete `date`
