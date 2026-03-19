#!/usr/bin/env bash
# eclipse-utils.sh — shared Eclipse-detection helpers.
# Source this file; do not execute it directly.
#
# Provides:
#   find_eclipse_home  — sets ECLIPSE_HOME to the Eclipse installation dir
#                        (the directory that contains plugins/).
#   find_eclipse_app   — prints the path to Eclipse.app on macOS (for gui-test).

# Sets ECLIPSE_HOME if not already set.
# Returns 0 on success, 1 if not found.
find_eclipse_home() {
    [ -n "${ECLIPSE_HOME-}" ] && return 0

    # 1. 'eclipse' binary on PATH
    if command -v eclipse >/dev/null 2>&1; then
        local bin
        bin="$(command -v eclipse)"
        if command -v realpath >/dev/null 2>&1; then
            bin="$(realpath "$bin")"
        fi
        local bindir
        bindir="$(dirname "$bin")"
        local candidate
        for candidate in \
                "$bindir/../Eclipse" \
                "$bindir/../../Contents/Eclipse" \
                "$bindir"; do
            candidate="$(cd "$candidate" 2>/dev/null && pwd -P || true)"
            if [ -d "$candidate/plugins" ]; then
                ECLIPSE_HOME="$candidate"
                echo "Auto-detected ECLIPSE_HOME from PATH: $ECLIPSE_HOME"
                return 0
            fi
        done
    fi

    # 2. macOS /Applications/Eclipse*.app
    if [ "$(uname)" = "Darwin" ]; then
        local app
        for app in /Applications/Eclipse*.app /Applications/eclipse*.app; do
            [ -d "$app/Contents/Eclipse/plugins" ] || continue
            ECLIPSE_HOME="$app/Contents/Eclipse"
            echo "Auto-detected ECLIPSE_HOME from Applications: $ECLIPSE_HOME"
            return 0
        done
    fi

    return 1
}

# Prints the path to an Eclipse.app bundle on macOS.
# Returns 0 on success, 1 if not found.
find_eclipse_app() {
    # 1. Resolve 'eclipse' binary on PATH back to its .app bundle
    if command -v eclipse >/dev/null 2>&1; then
        local bin
        bin="$(command -v eclipse)"
        bin="$(realpath "$bin" 2>/dev/null || readlink -f "$bin" 2>/dev/null || echo "$bin")"
        local candidate
        candidate="${bin%/Contents/MacOS/eclipse}"
        candidate="${candidate%/Contents/Eclipse/eclipse}"
        if [ -d "$candidate" ] && [[ "$candidate" == *.app ]]; then
            echo "$candidate"
            return 0
        fi
    fi

    # 2. /Applications/Eclipse*.app
    local app
    for app in /Applications/Eclipse*.app; do
        [ -d "$app" ] && echo "$app" && return 0
    done

    return 1
}
