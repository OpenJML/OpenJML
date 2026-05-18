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

:: Pass CL and MODULES out of the setlocal scope so the call can use them
endlocal & set "CL=%CL%" & set "MODULES=%MODULES%" & set "OPENJML_EXPORTS=%OPENJML_EXPORTS%"

call "%INSTALL%\openjml.bat" -cp ".;%CL%" -p "%MODULES%" %OPENJML_EXPORTS% --compile %*
