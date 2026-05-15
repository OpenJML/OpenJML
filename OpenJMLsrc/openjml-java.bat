@echo off
:: Runs the openjml-modified java (analogous to java), including the jmlruntime.jar.
:: Use this instead of plain java to run RAC-compiled programs.

:: Resolve the directory containing this script as an absolute path (no trailing backslash)
for %%i in ("%~dp0.") do set "INSTALL=%%~fi"

call "%INSTALL%\setup-vars.bat"

"%BINJAVA%" %OPENJML_JVM% %*
