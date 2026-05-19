#!/usr/bin/env bash
## Prints the OS/architecture suffix used for naming Solvers directories
## (e.g. "macos", "linux", "linux-arm64", "windows").
##
## This is the single authoritative source for that suffix. Keep in sync with:
##   - Utils.identifyOS in src/jdk.compiler/.../openjml/Utils.java
##   - The actual subdirectory names in the sibling Solvers/ repository
##
## Used by: OpenJMLsrc/Makefile (via OS_NAME), OpenJMLTest/releaseTests/runtests,
##          and copied into each release zip so release scripts can call it.

case "$(uname -s)" in
    Darwin) echo "macos" ;;
    Linux)
        if grep -qi microsoft /proc/version 2>/dev/null; then
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
