@echo off
:: Keep in sync with openjml (bash equivalent).
:: Runs the openjml compilation/esc/rac tool (analogous to javac).

:: Resolve the directory containing this script as an absolute path (no trailing backslash)
for %%i in ("%~dp0.") do set "INSTALL=%%~fi"

call "%INSTALL%\setup-vars.bat"

if not defined OPENJML_JVM (
    "%BINJAVAC%" "-J--patch-module=jdk.compiler=%JSMTLIB_JAR%" %*
) else (
    "%BINJAVA%" "--patch-module=jdk.compiler=%JSMTLIB_JAR%" %OPENJML_JVM% -cp ".;%INSTALL%" org.openjml.RunOpenJML %* %OPENJML_EXPORTS%
)
