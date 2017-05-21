#! /bin/bash

REFBRANCH=`git rev-parse --abbrev-ref HEAD`
echo REFBRANCH is $REFBRANCH
if [ $# -gt 1 ]; then
  echo 'Expected at most one argument'
  exit 1
elif [ $# -ne 1 ]; then
  REL=`cat ../OpenJMLFeature/feature.xml | grep version | grep -v xml | head -1 | sed -e  's/version=//' | tr -d '" \r\n\t'`
  echo 'Current version is' $REL
else
  REL=$1
fi


if [ -z "$REL" ]; then
    echo "Please give the desired release number as the one argument"
    exit 1
fi

cd "$( dirname "${BASH_SOURCE[0]}" )"
( ( ls openjml.properties > /dev/null ) || ( echo "Not in correct directory"; pwd; exit 1 ) )

git checkout -B "$REL"
cd ../../JMLAnnotations
git checkout -B "$REL"
cd ../OpenJMLDemo
git checkout -B "$REL"
cd ../Specs
git checkout -B "$REL"
#cd ../OpenJML-UpdateSite
#git checkout -B "$REL"
cd ../OpenJML/OpenJML

## FIXME - make platform independent - Eclipse does not set path
if [ -e ~/apps/ant ]; then
  ~/apps/ant -f build-bash.xml release
elif [ -e /opt/local/bin/ant ]; then
  ant -f build-bash.xml release
else
  C:/cygwin/home/dcok/mybin/ant -f build-bash.xml release
fi

## Starting in .../OpenJML/OpenJML
## Should be in the release branch

git add .
git commit -a -m "$REL"
git push --set-upstream origin "$REL"
git checkout $REFBRANCH
git push

cd ../../Specs
git add .
git commit -a -m "$REL"
git push --set-upstream origin "$REL"
git checkout $REFBRANCH
git push

cd ../JMLAnnotations
git add .
git commit -a -m "$REL"
git push --set-upstream origin "$REL"
git checkout $REFBRANCH
git push

cd ../OpenJMLDemo
git add .
git commit -a -m "$REL"
git push --set-upstream origin "$REL"
git checkout $REFBRANCH
git push

cd ../OpenJML-UpdateSite
#git add .
#git commit -a -m "$REL"
#git push --set-upstream origin "$REL"

echo Push to plugin site
chmod ugo+x web/toSF web/publish
web/toSF

cd ../OpenJML/OpenJML

