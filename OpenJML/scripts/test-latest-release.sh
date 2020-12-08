#! /bin/bash

rm -rf temp-test
mkdir temp-test
cd temp-test
echo "Downloading latest release from github -- may take a few minutes"
curl -s https://api.github.com/repos/OpenJML/OpenJML/releases/latest  | grep "browser_download_url" | cut -d : -f 2,3 | tr -d \" | wget -qi -

if [ $? -eq 0 ]; then
  echo "Release downloaded successfully"
  unzip -q *.zip
  java -jar openjml.jar -version
  echo "class Test { public static void m(int i) { /*@ assume i > 0; assert i >= 0; @*/ }}" > Test.java
  java -jar openjml.jar -esc -Werror Test.java
  if [ $? -eq 0 ]; then echo "OK"; else echo "FAILED"; fi
  echo "class Test { public static void m(int i) { /*@ assert i > 0; @*/ }}" > Test.java
  java -jar openjml.jar -esc -Werror Test.java
  if [ $? -ne 0 ]; then echo "OK"; else echo "FAILED"; fi
else echo "Download FAILED"
fi
cd ..
#rm -rf temp-test

echo Download test complete
