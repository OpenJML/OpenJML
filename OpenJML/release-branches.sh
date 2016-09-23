#! /bin/bash

if [ $# -ne 1 ]; then
	echo "Please give the desired release number as the one argument"
    exit 1
fi

REL=$1

if [ -z "$REL" ]; then
    echo "Please give the desired release number as the one argument"
    exit 1
fi

cd "$( dirname "${BASH_SOURCE[0]}" )"
( ( ls openjml.properties > /dev/null ) || ( echo "Not in correct directory"; pwd; exit 1 ) )

git checkout -b $REL
cd ../../JMLAnnotations
git checkout -b $REL
cd ../OpenJMLDemo
git checkout -b $REL
cd ../Specs
git checkout -b $REL
cd ../OpenJML-UpdateSite -b $REL
git checkout -b $REL
cd ../OpenJML/OpenJML

ant -f build-bash.xml release

