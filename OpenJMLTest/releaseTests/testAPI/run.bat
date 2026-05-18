@echo off
:: Keep in sync with run (bash equivalent).
:: Tests the OpenJML programmatic API using Windows .bat scripts.
:: Set OJBIN to the OpenJML installation directory before calling;
:: defaults to the development-environment location.

setlocal
cd /d "%~dp0"

if not defined OJBIN set "OJBIN=..\..\..\OpenJMLsrc"

del /q *.class 2>nul

call "%OJBIN%\openjml-compile.bat" Run.java
call "%OJBIN%\openjml-run.bat" Run --esc A.java
call "%OJBIN%\openjml-run.bat" Run --rac A.java
call "%OJBIN%\openjml-java.bat" A

exit /b 0
