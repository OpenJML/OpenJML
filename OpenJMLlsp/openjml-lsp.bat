@echo off
:: Keep in sync with openjml-lsp (bash equivalent).
:: Launches the OpenJML LSP server, which talks to the editor client over stdin/stdout:
:: nothing else may write to stdout. Stderr goes to a log file (override with OPENJML_LSP_LOG).

setlocal
:: Resolve the directory containing this script as an absolute path (no trailing backslash)
for %%i in ("%~dp0.") do set "DIR=%%~fi"
set "LSP4J_VERSION=1.0.0"

if exist "%DIR%\jdk\" (
    rem Release layout (installed from openjml.zip)
    set "INSTALL=%DIR%"
    set "JARFILE=%DIR%\lsp\openjml-lsp.jar"
    set "LSP4J_JAR=%DIR%\lsp\org.eclipse.lsp4j-%LSP4J_VERSION%.jar"
    set "LSP4J_RPC_JAR=%DIR%\lsp\org.eclipse.lsp4j.jsonrpc-%LSP4J_VERSION%.jar"
    set "LOGDIR=%USERPROFILE%\.openjml\logs"
) else (
    rem Development layout (sibling OpenJMLsrc folder)
    for %%i in ("%DIR%\..\OpenJMLsrc") do set "INSTALL=%%~fi"
    set "JARFILE=%DIR%\build\openjml-lsp.jar"
    set "LSP4J_JAR=%DIR%\libs\org.eclipse.lsp4j-%LSP4J_VERSION%.jar"
    set "LSP4J_RPC_JAR=%DIR%\libs\org.eclipse.lsp4j.jsonrpc-%LSP4J_VERSION%.jar"
    set "LOGDIR=%TEMP%"
)

call "%INSTALL%\setup-vars.bat"
call "%INSTALL%\setup-exports.bat"

if not defined OPENJML_LSP_LOG (
    if not exist "%LOGDIR%\" mkdir "%LOGDIR%"
    rem Delete logs older than a day; a running server's log is locked, so it stays.
    forfiles /p "%LOGDIR%" /m openjml-lsp-*.log /d -1 /c "cmd /c del @path" >nul 2>&1
    set "OPENJML_LSP_LOG=%LOGDIR%\openjml-lsp-%RANDOM%%RANDOM%.log"
)
echo %DATE% %TIME%: openjml-lsp.bat invoked> "%OPENJML_LSP_LOG%"

for %%f in ("%BINJAVA%" "%JARFILE%" "%JSMTLIB_JAR%" "%LSP4J_JAR%") do if not exist %%f (
    echo ERROR: missing %%~f 1>&2
    exit /b 1
)

:: jSMTLIB is not built into jdk.compiler; it is patched in, as the openjml scripts do.
"%BINJAVA%" "--patch-module=jdk.compiler=%JSMTLIB_JAR%" %OPENJML_JVM% %OPENJML_EXPORTS% ^
    -cp "%JARFILE%;%LSP4J_JAR%;%LSP4J_RPC_JAR%" org.openjml.lsp.ServerLauncher %* 2>>"%OPENJML_LSP_LOG%"
exit /b %ERRORLEVEL%
