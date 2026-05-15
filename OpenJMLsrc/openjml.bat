@echo off
:: Runs the openjml compilation/esc/rac tool (analogous to javac).

:: Resolve the directory containing this script as an absolute path (no trailing backslash)
for %%i in ("%~dp0.") do set "INSTALL=%%~fi"

call "%INSTALL%\setup-vars.bat"

if not defined OPENJML_JVM (
    "%BINJAVAC%" %*
) else (
    "%BINJAVA%" %OPENJML_JVM% -cp ".;%INSTALL%" org.openjml.RunOpenJML %* %OPENJML_EXPORTS%
)
