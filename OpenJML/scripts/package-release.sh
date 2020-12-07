#! /bin/bash

ECLIPSE_HOME=/Users/davidcok/eclipse/committers-2018-09/Eclipse.app/Contents/Eclipse/
WORKSPACE=/Users/davidcok/cok/workspaces/OpenJML-workspaceA

token=`cat ~/github.token | head -n 1`
draft=false
if [ "$1" == "-draft" ]; then draft=true; shift; fi

ver=$1
vsolver=$2

if [ -z "$ver" ]; then
  echo "Requires a (numeric) version number for the first argument"
  exit 1
fi
if [ $# -gt 2 ]; then
  echo "Requires one or two arguments"
  exit 1
fi

echo New version: $1
echo "Is a draft release?" $draft

cd $(dirname $BASH_SOURCE[0])
cd ../../..

for f in OpenJML/OpenJMLFeature/feature.xml ; do
  sed -e "s/^\([ ]*\)version=\"[0-9a-zA-Z_\.]*\"/\1version=\"$ver\"/" < $f > /tmp/t
  mv /tmp/t $f
done
for d in Specs JMLAnnotations OpenJML/*; do
 f=$d/META-INF/MANIFEST.MF
 if [ -e $f ]; then
  sed -e "s/Bundle-Version: [0-9a-zA-Z_\.]*/Bundle-Version: $ver/" < $f > /tmp/t
  mv /tmp/t $f
 fi
done

lines=$( wc -l < */site.xml )
head -n $(( $lines - 6 )) */site.xml > /tmp/t
echo "   <feature url=\"features/org.jmlspecs.openjml.OpenJMLFeature_$ver.jar\" id=\"org.jmlspecs.openjml.OpenJMLFeature\" version=\"$ver\">" >> /tmp/t
tail -n 8 */site.xml >> /tmp/t

echo Building all projects
java -jar ${ECLIPSE_HOME}/plugins/org.eclipse.equinox.launcher_*.jar -noSplash -data "$WORKSPACE" -application org.eclipse.jdt.apt.core.aptBuild > /tmp/build 
## TODO - catch and report any errors

echo Assemble and test
ant -f OpenJML/OpenJML/scripts/build-bash.xml release-test | tee /tmp/t | grep 'Branch'
if [ $? != 0 ] ; then
  echo "Assemble and test failed"
  cat /tmp/t
  exit 1
fi
echo Successful release assembly and test

echo Builtin version:
(cd OpenJML/OpenJML/tempjars; java -jar openjml.jar -version)

echo Committing changes
cd OpenJML
git status
git add OpenJMLFeature/feature.xml */META-INF/MANIFEST.MF
git commit -m "Changing version to $ver"
cd ..
for d in Specs JMLAnnotations; do
  cd $d
  git add META-INF/MANIFEST.MF
  git commit -m "Changing version to $ver"
  cd ..
done

echo Create github release

curl -s -X POST -H "Authorization: token $token" -d "{\"tag_name\":\"$ver\", \"name\":\"V$ver\", \"draft\":true, \"body\":\"Publishing release V$ver\"}" "https://api.github.com/repos/OpenJML/OpenJML/releases" > /tmp/post
 
upload_url=`jq -r '.upload_url' < /tmp/post`
upload_url="${upload_url%\{*}"
id=`jq -r '.id' < /tmp/post`

file=`ls -t OpenJML/OpenJML/releaseBuilds | head -n 1`

echo Uploading file $file
curl -s -X POST -H "Authorization: token $token"  \
        -H "Content-Type: application/zip" \
        --data-binary @OpenJML/OpenJML/releaseBuilds/$file  \
        "$upload_url?name=$file&label=$file" > /tmp/upload
if [ $? -ne 0 ]; then echo Upload failed; fi

echo Publishing release
curl -s -X PATCH -H "Authorization: token $token" -d "{ \"draft\":$draft}" "https://api.github.com/repos/OpenJML/OpenJML/releases/$id" > /tmp/patch

#echo Build plugins
#( cd OpenJML/OpenJMLFeature; jar cMf ../../OpenJML-UpdateSite/features/org.jmlspecs.openjml.OpenJMLFeature_${ver}.jar feature.xml )

#echo Finished
