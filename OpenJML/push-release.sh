#! /bin/bash

git add .
git commit -a -m "$1"
git push --set-upstream origin "$1"
git checkout master

cd ../../Specs
git add .
git commit -a -m "$1"
git push --set-upstream origin "$1"
git checkout master

cd ../JMLAnnotations
git add .
git commit -a -m "$1"
git push --set-upstream origin "$1"
git checkout master

cd ../JmlOpenJMLDemo
git add .
git commit -a -m "$1"
git push --set-upstream origin "$1"
git checkout master

cd ../OpenJML-UpdateSite
git add .
git commit -a -m "$1"
git push --set-upstream origin "$1"
git checkout master

cd ../OpenJML/OpenJML

