@echo off
:: Keep in sync with setup-vars (bash equivalent).
:: Sets OPENJML_INSTALL BINJAVA BINJAVAC OPENJML_SOLVERS OPENJML_SPECS
:: Requires %INSTALL% to be set by the calling script.
:: Usage: call "%INSTALL%\setup-vars.bat"

if not defined OPENJML_INSTALL set "OPENJML_INSTALL=%INSTALL%"

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
