#! /bin/bash

## Creates the version resource file based on the content of version.txt
## Used in the Makefile

VFILE=src/jdk.compiler/share/classes/org/jmlspecs/openjml/version.properties
TFILE=temp
D=$(dirname "$BASH_SOURCE")
cd "$D"

VER=`cat ../version.txt`
rm -f $TFILE
echo "jdk=21" > $TFILE
echo "full=$VER" >> $TFILE
echo "release=$VER" >> $TFILE
cmp -s $TFILE $VFILE || cp $TFILE $VFILE
echo $VER
