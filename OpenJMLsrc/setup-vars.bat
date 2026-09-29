@echo off
:: Keep in sync with setup-vars (bash equivalent).
:: Sets OPENJML_INSTALL BINJAVA BINJAVAC OPENJML_SPECS SMT_SOLVER_DIR
:: Requires %INSTALL% to be set by the calling script.
:: Usage: call "%INSTALL%\setup-vars.bat"

if not defined OPENJML_INSTALL set "OPENJML_INSTALL=%INSTALL%"

set "JSMTLIB_JAR=%INSTALL%\libs\jSMTLIB.jar"

if exist "%INSTALL%\version-info.txt" (
    :: In a release
    if not defined OPENJML_SPECS   set "OPENJML_SPECS=%INSTALL%\specs"
    if not defined SMT_SOLVER_DIR  set "SMT_SOLVER_DIR=%INSTALL%\Solvers-windows"
    set "BINJAVA=%INSTALL%\jdk\bin\java.exe"
    set "BINJAVAC=%INSTALL%\jdk\bin\javac.exe"
) else (
    :: In development environment
    if not defined SMT_SOLVER_DIR (
        for %%i in ("%INSTALL%\..\..\Solvers\Solvers-windows") do set "SMT_SOLVER_DIR=%%~fi"
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

:: SMT_SOLVER_DIR (set above unless already set) is the folder in which jSMTLIB finds the solver
:: executables: those named by the .exec properties in its jsmtlib.properties, or else the solver
:: name itself. It is the Solvers-windows folder: in the installation for a release, or in the
:: sibling Solvers repository for the development environment.
