@echo off
:: Keep in sync with openjml-compile (bash equivalent).
:: Runs openjml with options that permit linking in openjdk/openjml code for programmatic
:: access to openjdk/openjml internals (analogous to javac).

setlocal enabledelayedexpansion

:: Resolve the directory containing this script as an absolute path (no trailing backslash)
for %%i in ("%~dp0.") do set "INSTALL=%%~fi"

call "%INSTALL%\setup-exports.bat"

if exist "%INSTALL%\version-info.txt" (
    :: In a release
    set "CL="
    for /d %%m in ("%INSTALL%\jdk\modules\*") do (
        if not defined CL (set "CL=%%m") else (set "CL=!CL!;%%m")
    )
    set "MODULES=%INSTALL%\jdk\modules"
) else (
    :: In development environment
    set "CL="
    for /d %%b in ("%INSTALL%\build\*") do (
        for /d %%m in ("%%b\jdk\modules\*") do (
            if not defined CL (set "CL=%%m") else (set "CL=!CL!;%%m")
        )
    )
    for /d %%b in ("%INSTALL%\build\*release") do set "MODULES=%%b\jdk\modules"
)

:: Pass CL, MODULES, OPENJML_EXPORTS, and INSTALL out of the setlocal scope.
:: All %VAR% references on this line expand before endlocal executes, so the
:: local values are captured correctly.  INSTALL must be included because it is
:: used on the very next line after the local scope is gone.
endlocal & set "CL=%CL%" & set "MODULES=%MODULES%" & set "OPENJML_EXPORTS=%OPENJML_EXPORTS%" & set "INSTALL=%INSTALL%"

call "%INSTALL%\openjml.bat" -cp ".;%CL%" -p "%MODULES%" %OPENJML_EXPORTS% --compile %*
