#!/usr/bin/env bash
## Prints the OS/architecture suffix used for naming Solvers directories
## (e.g. "macos", "linux", "linux-arm64", "windows").
## Usage: os-name.sh [jdk-bin-folder]; the optional folder is the JDK that will run, which under WSL
## decides between windows (a Windows JDK, java.exe) and the Linux names.
##
## This is the single authoritative source for that suffix. Keep in sync with:
##   - Utils.identifyOS in src/jdk.compiler/.../openjml/Utils.java
##   - The actual subdirectory names in the sibling Solvers/ repository
##
## Used by: OpenJMLsrc/Makefile (via OS_NAME), OpenJMLTest/releaseTests/runtests,
##          and copied into each release zip so release scripts can call it.

case "$(uname -s)" in
    Darwin)
        case "$(uname -m)" in
            arm64|aarch64) echo "macos-arm64" ;;
            *)             echo "macos" ;;
        esac ;;
    Linux)
        ## Under WSL: windows, unless the JDK bin folder given as $1 has a Linux JDK (#1007)
        if grep -qi microsoft /proc/version 2>/dev/null && { [ -z "$1" ] || [ -e "$1/java.exe" ]; }; then
            echo "windows"
        else
            case "$(uname -m)" in
                aarch64|arm64) echo "linux-arm64" ;;
                *)             echo "linux" ;;
            esac
        fi ;;
    CYGWIN*|MINGW*|MSYS*) echo "windows" ;;
    *) echo "$(uname -s | tr '[:upper:]' '[:lower:]')-$(uname -m)" ;;
esac
