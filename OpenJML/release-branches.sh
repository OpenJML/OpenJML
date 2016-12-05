#! /bin/bash

REFBRANCH=`git rev-parse --abbrev-ref HEAD`
if [ $# -gt 1 ]; then
  echo 'Expected at most one argument'
  exit 1
elif [ $# -ne 1 ]; then
  REL=`cat ../OpenJMLFeature/feature.xml | grep version | grep -v xml | head -1 | sed -e  's/version=//' | tr -d '"'`
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

git checkout -b "$REL"
cd ../../JMLAnnotations
git checkout -b "$REL"
cd ../OpenJMLDemo
git checkout -b "$REL"
cd ../Specs
git checkout -b "$REL"
#cd ../OpenJML-UpdateSite -b "$REL"
#git checkout -b "$REL"
cd ../OpenJML/OpenJML

ant -f build-bash.xml release

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

cd ../JmlOpenJMLDemo
git add .
git commit -a -m "$REL"
git push --set-upstream origin "$REL"
git checkout $REFBRANCH
git push

cd ../OpenJML-UpdateSite
git add .
git commit -a -m "$REL"
git push --set-upstream origin "$REL"

echo Push to plugin site
chmod ugo+x web/toSF web/publish
web/toSF

cd ../OpenJML/OpenJML

