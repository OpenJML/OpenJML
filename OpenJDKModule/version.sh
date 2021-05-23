#! /bin/bash

## Creates the version resource file based on the content of version.txt

VFILE=src/jdk.compiler/share/classes/org/jmlspecs/openjml/version.properties

cd $(dirname $BASH_SOURCE)

VER=`cat ../version.txt`
echo "jdk=16" > $VFILE
echo "full=$VER" >> $VFILE
echo "release=$VER" >> $VFILE
