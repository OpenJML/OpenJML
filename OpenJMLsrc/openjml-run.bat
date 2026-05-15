@echo off
:: Runs (like java) compiled programs that have OpenJML programmatically linked in.
:: Use this to run programs compiled with openjml-compile.bat.

:: Resolve the directory containing this script as an absolute path (no trailing backslash)
for %%i in ("%~dp0.") do set "INSTALL=%%~fi"

call "%INSTALL%\setup-exports.bat"

call "%INSTALL%\openjml-java.bat" %OPENJML_EXPORTS% %*
