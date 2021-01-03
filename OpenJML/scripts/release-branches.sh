#! /bin/bash
##  This script takes a release number (x.y.z format).
##  It changes to the directory containing this file
##  then does a git checkout on all the pieces of the release to be sure that 
##    the working tree is current with the release tag
##  Then builds the release
##  Then pushes all changes to origin
##  Then uploads 
##      - the release files to sourceforge
##      - the Eclipse GUI files to sourceforge

cd "$( dirname "${BASH_SOURCE[0]}" )"
cd ..

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
pushd ../../../*UpdateSite*
git add -u
git commit -m "Adding artifacts for version $REL"
git push
popd

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

## FIXME - make platform independent - Eclipse does not set $PATH
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

