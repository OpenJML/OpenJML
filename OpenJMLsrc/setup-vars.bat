@echo off
:: Keep in sync with setup-vars (bash equivalent).
:: Sets OPENJML_INSTALL BINJAVA BINJAVAC OPENJML_SOLVERS OPENJML_SPECS SMT_SOLVER_DIR
:: Requires %INSTALL% to be set by the calling script.
:: Usage: call "%INSTALL%\setup-vars.bat"

if not defined OPENJML_INSTALL set "OPENJML_INSTALL=%INSTALL%"

set "JSMTLIB_JAR=%INSTALL%\libs\jSMTLIB.jar"

if exist "%INSTALL%\version-info.txt" (
    :: In a release
    if not defined OPENJML_SPECS   set "OPENJML_SPECS=%INSTALL%\specs"
    if not defined OPENJML_SOLVERS set "OPENJML_SOLVERS=%INSTALL%"
    set "BINJAVA=%INSTALL%\jdk\bin\java.exe"
    set "BINJAVAC=%INSTALL%\jdk\bin\javac.exe"
) else (
    :: In development environment
    if not defined OPENJML_SOLVERS (
        for %%i in ("%INSTALL%\..\..\Solvers") do set "OPENJML_SOLVERS=%%~fi"
    )
    if not defined OPENJML_SPECS (
        for %%i in ("%INSTALL%\..\..\Specs\specs") do set "OPENJML_SPECS=%%~fi"
    )
    for /d %%d in ("%INSTALL%\build\*") do (
        if exist "%%d\jdk\bin\java.exe" (
            set "BINJAVA=%%d\jdk\bin\java.exe"
            set "BINJAVAC=%%d\jdk\bin\javac.exe"
        )
    )
)

:: SMT_SOLVER_DIR is the folder in which jSMTLIB finds the solver executables: those named by the
:: .exec properties in its jsmtlib.properties, or else the solver name itself.
:: Unless it is already set, it is the Solvers-windows folder of the solvers location.
if not defined SMT_SOLVER_DIR set "SMT_SOLVER_DIR=%OPENJML_SOLVERS%\Solvers-windows"
