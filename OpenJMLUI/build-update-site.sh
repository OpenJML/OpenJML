#!/usr/bin/env bash
# build-update-site.sh
# Purpose:
#   Optionally compile OpenJMLUI from source, then assemble the plugin and
#   feature into the OpenJMLUpdateSite directory as a standard Eclipse
#   update-site layout (plugins/ and features/).
#
# Usage:
#   Run from OpenJML/OpenJMLUI/ or anywhere; paths are resolved relative to
#   the script location.
#
#     ./build-update-site.sh [OPTIONS]
#
# Options:
#   --build              Compile OpenJMLUI/src before packaging (default).
#                        Requires ECLIPSE_HOME to be set so Eclipse platform
#                        JARs can be found for the javac classpath.
#   --no-build           Skip compilation; package whatever is already in bin/.
#   --version VERSION    Set the Bundle/Feature version to VERSION before
#                        building.  Updates MANIFEST.MF, feature.xml, and
#                        category.xml in-source.
#   --overwrite          Allow replacing an existing output JAR of the same
#                        version.
#   --help               Show this help and exit.
#
# Environment:
#   ECLIPSE_HOME   Path to an Eclipse installation.  Required when --build is
#                  in effect (the default).  Used to find Eclipse platform JARs
#                  for compilation and, optionally, the p2 publisher.
#   JAVA_HOME      Path to a JDK 21+ installation.  Defaults to whatever
#                  'java'/'javac' are on PATH.
#   EXPECTED_BRANCH  When set, aborts unless the current git branch matches.
#
# Outputs (inside OpenJMLUpdateSite/):
#   plugins/org.openjml.OpenJMLUI_<version>.jar
#   features/org.openjml.OpenJMLFeature_<version>.jar
#
# Non-interactive: the script never launches the Eclipse GUI.

set -euo pipefail

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------
ROOT_DIR="$(cd "$(dirname "$0")" && pwd -P)"   # OpenJMLUI/
UI_DIR="$ROOT_DIR"
FEATURE_DIR="$ROOT_DIR/../OpenJMLFeature"
UPDATESITE_DIR="$ROOT_DIR/../OpenJMLUpdateSite"
PLUGIN_ID="org.openjml.OpenJMLUI"
FEATURE_ID="org.openjml.OpenJMLFeature"
MANIFEST="$UI_DIR/META-INF/MANIFEST.MF"
SRC_DIR="$UI_DIR/src"
BIN_DIR="$UI_DIR/bin"

# Library JARs that are part of Bundle-ClassPath (must be present inside the
# plugin JAR).  Keep in sync with MANIFEST.MF Bundle-ClassPath.
LIBS=("jSMTLIB.jar" "jpaul-2.5.1.jar" "gson-2.8.1.jar")

# ---------------------------------------------------------------------------
# CLI parsing
# ---------------------------------------------------------------------------
VERSION_ARG=""
OVERWRITE=0
DO_BUILD=1      # --build is the default

usage() {
    cat <<EOF
Usage: $(basename "$0") [--build|--no-build] [--version VERSION] [--overwrite] [--help]

  --build              Compile src/ before packaging (default; needs ECLIPSE_HOME).
  --no-build           Skip compilation; use existing bin/ contents.
  --version VERSION    Set Bundle/Feature version before building.
  --overwrite          Allow overwriting an existing output JAR of the same version.
  --help               Show this help and exit.
EOF
}

while [ $# -gt 0 ]; do
    case "$1" in
        --build)       DO_BUILD=1;  shift ;;
        --no-build)    DO_BUILD=0;  shift ;;
        --version)     VERSION_ARG="$2"; shift 2 ;;
        --overwrite)   OVERWRITE=1; shift ;;
        --help|-h)     usage; exit 0 ;;
        *) echo "Unknown option: $1" >&2; usage >&2; exit 1 ;;
    esac
done

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

# Read a single-line value from MANIFEST.MF (e.g. "Bundle-Version: 1.2.3" → "1.2.3")
get_manifest_value() {
    local key="$1"
    grep "^${key}:" "$MANIFEST" | head -n1 | sed "s/^${key}:[[:space:]]*//" | tr -d '\r'
}

# Update version strings in source files.
set_version_in_sources() {
    local newv="$1"
    echo "Setting source bundle/feature version to: $newv"

    sed -i.bak "s/^Bundle-Version:.*/Bundle-Version: ${newv}/" "$MANIFEST"
    rm -f "$MANIFEST.bak"

    sed -i.bak -E \
        -e 's/(<feature[^>]* version=")[^"]*(")/\1'"${newv}"'\2/' \
        -e 's/(<plugin[^>]* version=")[^"]*(")/\1'"${newv}"'\2/' \
        "$FEATURE_DIR/feature.xml"
    rm -f "$FEATURE_DIR/feature.xml.bak"

    local cat_xml="$UPDATESITE_DIR/category.xml"
    if [ -f "$cat_xml" ]; then
        sed -i.bak -E \
            -e "s|(features/[^_]+_)[^\"]+(\.jar\")|\1${newv}\2|g" \
            -e 's/(<feature[^>]* version=")[^"]*(")/\1'"${newv}"'\2/' \
            "$cat_xml"
        rm -f "$cat_xml.bak"
    fi
}

# ---------------------------------------------------------------------------
# Eclipse auto-detection: sets ECLIPSE_HOME if not already set.
# Searches (in order):
#   1. 'eclipse' binary on PATH  → derive home from its real location
#   2. macOS /Applications/Eclipse*.app bundles
# ---------------------------------------------------------------------------
find_eclipse_home() {
    [ -n "${ECLIPSE_HOME-}" ] && return 0   # already set

    # 1. eclipse on PATH
    if command -v eclipse >/dev/null 2>&1; then
        local bin
        bin="$(command -v eclipse)"
        # Resolve symlinks so we find the real directory
        if command -v realpath >/dev/null 2>&1; then
            bin="$(realpath "$bin")"
        fi
        local bindir
        bindir="$(dirname "$bin")"
        # macOS app bundle: binary is in Contents/MacOS/, plugins in Contents/Eclipse/plugins/
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

    # 2. macOS /Applications — pick the newest Eclipse*.app
    if [ "$(uname)" = "Darwin" ]; then
        local app
        for app in /Applications/Eclipse*.app /Applications/eclipse*.app; do
            [ -d "$app/Contents/Eclipse/plugins" ] || continue
            ECLIPSE_HOME="$app/Contents/Eclipse"
            echo "Auto-detected ECLIPSE_HOME from Applications: $ECLIPSE_HOME"
            return 0
        done
    fi

    return 1   # not found
}

# ---------------------------------------------------------------------------
# Build step: compile OpenJMLUI/src using javac + Eclipse platform JARs
# ---------------------------------------------------------------------------
build_plugin() {
    echo "--- Compiling OpenJMLUI ---"

    find_eclipse_home || true

    if [ -z "${ECLIPSE_HOME-}" ]; then
        echo "ERROR: --build requires ECLIPSE_HOME (Eclipse not found on PATH or in /Applications)." >&2
        exit 1
    fi

    if [ ! -d "$ECLIPSE_HOME" ]; then
        echo "ERROR: ECLIPSE_HOME=$ECLIPSE_HOME does not exist." >&2
        exit 1
    fi

    # Locate javac (prefer JAVA_HOME)
    if [ -n "${JAVA_HOME-}" ] && [ -x "$JAVA_HOME/bin/javac" ]; then
        JAVAC="$JAVA_HOME/bin/javac"
    elif command -v javac >/dev/null 2>&1; then
        JAVAC="$(command -v javac)"
    else
        echo "ERROR: javac not found; set JAVA_HOME or add JDK 21 to PATH." >&2
        exit 1
    fi
    echo "Using javac: $JAVAC ($("$JAVAC" -version 2>&1 || true))"

    # Build the compilation classpath from all non-source Eclipse plugin JARs.
    # This "kitchen-sink" approach is reliable and avoids having to list each
    # required bundle individually.
    local ECLIPSE_PLUGINS=""
    for pd in "$ECLIPSE_HOME/plugins" "$ECLIPSE_HOME/Contents/Eclipse/plugins"; do
        [ -d "$pd" ] && ECLIPSE_PLUGINS="$pd" && break
    done

    if [ -z "$ECLIPSE_PLUGINS" ]; then
        echo "ERROR: could not find plugins/ under ECLIPSE_HOME=$ECLIPSE_HOME" >&2
        exit 1
    fi

    # Collect platform JARs (skip *source* JARs)
    CP=""
    while IFS= read -r jar; do
        case "$(basename "$jar")" in *source*|*src*) continue ;; esac
        CP="${CP:+$CP:}$jar"
    done < <(find "$ECLIPSE_PLUGINS" -maxdepth 1 -name "*.jar" 2>/dev/null | sort)

    # Add our own library JARs
    for lib in "${LIBS[@]}"; do
        [ -f "$UI_DIR/$lib" ] && CP="${CP:+$CP:}$UI_DIR/$lib"
    done

    if [ -z "$CP" ]; then
        echo "ERROR: no JARs found under $ECLIPSE_PLUGINS" >&2
        exit 1
    fi

    # Collect source files into a @argfile (avoids command-line length limits
    # and works on both macOS bash 3.2 and Linux bash 4+)
    local SRC_LIST
    SRC_LIST=$(mktemp)
    find "$SRC_DIR" -name "*.java" > "$SRC_LIST" 2>/dev/null || true

    if [ ! -s "$SRC_LIST" ]; then
        rm -f "$SRC_LIST"
        echo "Warning: no .java files found in $SRC_DIR; skipping compilation."
        return
    fi

    local COUNT
    COUNT=$(wc -l < "$SRC_LIST" | tr -d ' ')
    echo "Compiling $COUNT source file(s) to $BIN_DIR ..."

    rm -rf "$BIN_DIR"
    mkdir -p "$BIN_DIR"

    "$JAVAC" \
        --release 21 \
        -cp "$CP" \
        -d "$BIN_DIR" \
        "@$SRC_LIST" \
        && echo "Compilation succeeded." \
        || { echo "ERROR: compilation failed." >&2; rm -f "$SRC_LIST"; exit 1; }

    rm -f "$SRC_LIST"
}

# ---------------------------------------------------------------------------
# Optional: git branch check
# ---------------------------------------------------------------------------
GIT_BRANCH=""
if command -v git >/dev/null 2>&1; then
    GIT_BRANCH=$(git -C "$ROOT_DIR" symbolic-ref --short HEAD 2>/dev/null \
                 || git -C "$ROOT_DIR" branch --show-current 2>/dev/null || true)
fi
[ -n "$GIT_BRANCH" ] && echo "Git branch: $GIT_BRANCH"

if [ -n "${EXPECTED_BRANCH-}" ]; then
    if [ -z "$GIT_BRANCH" ]; then
        echo "ERROR: EXPECTED_BRANCH=$EXPECTED_BRANCH but git branch not detected." >&2; exit 1
    fi
    if [ "$GIT_BRANCH" != "$EXPECTED_BRANCH" ]; then
        echo "ERROR: EXPECTED_BRANCH=$EXPECTED_BRANCH but current branch is $GIT_BRANCH." >&2; exit 1
    fi
fi

# ---------------------------------------------------------------------------
# Apply --version if requested (before build so source is correct)
# ---------------------------------------------------------------------------
if [ -n "$VERSION_ARG" ]; then
    set_version_in_sources "$VERSION_ARG"
fi

# ---------------------------------------------------------------------------
# Read version from (possibly updated) manifest
# ---------------------------------------------------------------------------
BUNDLE_VERSION=$(get_manifest_value "Bundle-Version")
if [ -z "$BUNDLE_VERSION" ]; then
    echo "ERROR: Could not read Bundle-Version from $MANIFEST" >&2; exit 1
fi
echo "Plugin ID:   $PLUGIN_ID"
echo "Feature ID:  $FEATURE_ID"
echo "Version:     $BUNDLE_VERSION"
echo "Update site: $UPDATESITE_DIR"

# ---------------------------------------------------------------------------
# Preflight checks
# ---------------------------------------------------------------------------
MISSING=()
[ -f "$MANIFEST" ]               || MISSING+=("$MANIFEST")
[ -f "$FEATURE_DIR/feature.xml" ] || MISSING+=("$FEATURE_DIR/feature.xml")
if [ ${#MISSING[@]} -ne 0 ]; then
    echo "ERROR: missing required files:" >&2
    printf "  - %s\n" "${MISSING[@]}" >&2
    exit 1
fi

for lib in "${LIBS[@]}"; do
    [ -f "$UI_DIR/$lib" ] || echo "Warning: expected library $lib not found in $UI_DIR"
done

# ---------------------------------------------------------------------------
# Compile (unless --no-build)
# ---------------------------------------------------------------------------
if [ "$DO_BUILD" -eq 1 ]; then
    build_plugin
else
    echo "--- Skipping compilation (--no-build) ---"
    [ -d "$BIN_DIR" ] || echo "Warning: $BIN_DIR not found; plugin JAR will contain no compiled classes."
fi

# ---------------------------------------------------------------------------
# Prepare output directories
# ---------------------------------------------------------------------------
PLUGINS_OUT="$UPDATESITE_DIR/plugins"
FEATURES_OUT="$UPDATESITE_DIR/features"
mkdir -p "$PLUGINS_OUT" "$FEATURES_OUT"

PLUGIN_JAR="$PLUGINS_OUT/${PLUGIN_ID}_${BUNDLE_VERSION}.jar"
FEATURE_JAR="$FEATURES_OUT/${FEATURE_ID}_${BUNDLE_VERSION}.jar"

if [ -f "$PLUGIN_JAR" ] || [ -f "$FEATURE_JAR" ]; then
    if [ "$OVERWRITE" -eq 1 ]; then
        echo "--overwrite: removing existing JARs for version $BUNDLE_VERSION"
        rm -f "$PLUGIN_JAR" "$FEATURE_JAR"
    else
        echo "ERROR: output JARs for version $BUNDLE_VERSION already exist; use --overwrite to replace." >&2
        exit 1
    fi
fi

# ---------------------------------------------------------------------------
# Build plugin JAR
# ---------------------------------------------------------------------------
echo "--- Packaging plugin JAR ---"

STAGE=$(mktemp -d)
trap 'rm -rf "$STAGE"' EXIT

# Compiled classes
if [ -d "$BIN_DIR" ]; then
    cp -a "$BIN_DIR/." "$STAGE/"
fi

# Library JARs (at root of plugin JAR, matching Bundle-ClassPath entries)
for lib in "${LIBS[@]}"; do
    [ -f "$UI_DIR/$lib" ] && cp "$UI_DIR/$lib" "$STAGE/"
done

# Bundle metadata and resources
mkdir -p "$STAGE/META-INF"
cp "$MANIFEST" "$STAGE/META-INF/MANIFEST.MF"
for item in plugin.xml icons html OSGI-INF; do
    [ -e "$UI_DIR/$item" ] && cp -a "$UI_DIR/$item" "$STAGE/"
done

(cd "$STAGE" && jar --create --file="$PLUGIN_JAR" .)
echo "  -> $PLUGIN_JAR"

# ---------------------------------------------------------------------------
# Build feature JAR
# ---------------------------------------------------------------------------
echo "--- Packaging feature JAR ---"

FSTAGE=$(mktemp -d)
trap 'rm -rf "$STAGE" "$FSTAGE"' EXIT

cp "$FEATURE_DIR/feature.xml" "$FSTAGE/"
(cd "$FSTAGE" && jar --create --file="$FEATURE_JAR" feature.xml)
echo "  -> $FEATURE_JAR"

# ---------------------------------------------------------------------------
# Optional: p2 publisher (headless, via equinox launcher JAR)
# ---------------------------------------------------------------------------
LAUNCHER_JAR=""
if [ -n "${ECLIPSE_HOME-}" ]; then
    for pd in "$ECLIPSE_HOME/plugins" "$ECLIPSE_HOME/Contents/Eclipse/plugins"; do
        [ -d "$pd" ] || continue
        while IFS= read -r cand; do
            case "$(basename "$cand")" in *source*|*src*) continue ;; esac
            ls "$pd"/org.eclipse.equinox.p2.publisher_*.jar >/dev/null 2>&1 || continue
            LAUNCHER_JAR="$cand"
            break 2
        done < <(find "$pd" -maxdepth 1 -name "org.eclipse.equinox.launcher_*.jar" 2>/dev/null)
    done
fi

if [ -n "$LAUNCHER_JAR" ]; then
    JAVACMD="${JAVA_HOME:+$JAVA_HOME/bin/}java"
    echo "--- Running p2 publisher ---"
    SITE_URI="file:$(cd "$UPDATESITE_DIR" && pwd -P)"
    "$JAVACMD" -jar "$LAUNCHER_JAR" -nosplash \
        -application org.eclipse.equinox.p2.publisher.FeaturesAndBundlesPublisher \
        -metadataRepository "$SITE_URI" \
        -artifactRepository "$SITE_URI" \
        -source "$SITE_URI" \
        -publishArtifacts -compress -consolelog \
        && echo "p2 metadata written to $UPDATESITE_DIR" \
        || echo "Warning: p2 publisher exited with errors; basic plugins/features layout is still valid." >&2
else
    if [ -n "${ECLIPSE_HOME-}" ]; then
        echo "p2 publisher bundle not found in ECLIPSE_HOME; skipping p2 metadata generation."
    else
        echo "ECLIPSE_HOME not set; skipping p2 metadata generation."
        echo "(Set ECLIPSE_HOME to generate p2 metadata for install-via-URL support.)"
    fi
fi

# ---------------------------------------------------------------------------
echo "--- Done ---"
echo "  plugins/ : $PLUGIN_JAR"
echo "  features/: $FEATURE_JAR"
echo "  site     : $UPDATESITE_DIR"
