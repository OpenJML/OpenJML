#! /bin/bash

## Creates the version resource file based on the content of version.txt

VFILE=src/jdk.compiler/share/classes/org/jmlspecs/openjml/version.properties
TFILE=temp
cd "$(dirname $BASH_SOURCE)"

VER=`cat ../version.txt`
rm -f $TFILE
echo "jdk=16" > $TFILE
echo "full=$VER" >> $TFILE
echo "release=$VER" >> $TFILE
cmp -s $TFILE $VFILE || cp $TFILE $VFILE
