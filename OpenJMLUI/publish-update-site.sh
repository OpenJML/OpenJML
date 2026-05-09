#!/usr/bin/env bash
# publish-update-site.sh
# Purpose:
#   Copy the newly built plugin and feature JARs from OpenJMLUpdateSite/ into
#   the openjml.github.io/eclipse-update-site/ directory, then regenerate p2
#   repository metadata in place so that Eclipse can install directly from the
#   GitHub Pages URL.
#
# Typical workflow:
#   1.  ./build-update-site.sh --overwrite   (or with --version X)
#   2.  ./publish-update-site.sh             (copies + regenerates metadata)
#  This step is manual:
#   3.  cd ../../openjml.github.io && git add -A && git commit && git push
#
# Usage:
#   ./publish-update-site.sh --version VERSION [--overwrite] [--help]
#
# Options:
#   --version VERSION  Version of the JARs to copy from OpenJMLUpdateSite (required).
#   --overwrite        Allow overwriting existing JARs of the same version.
#   --help             Show this help and exit.
#
# Environment:
#   ECLIPSE_HOME   Path to an Eclipse installation.  Required for p2 metadata regeneration.
#   JAVA_HOME      Path to a JDK.  Defaults to 'java' on PATH.
#
# Non-interactive: the script never launches the Eclipse GUI.

set -euo pipefail

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd -P)"   # OpenJMLUI/
SOURCE_DIR="$SCRIPT_DIR/../OpenJMLUpdateSite"     # where build-update-site.sh wrote output
DEST_DIR="$SCRIPT_DIR/../../openjml.github.io/eclipse-update-site"

# ---------------------------------------------------------------------------
# CLI parsing
# ---------------------------------------------------------------------------
VERSION=""
OVERWRITE=0

usage() {
    cat <<EOF
Usage: $(basename "$0") --version VERSION [--overwrite] [--help]

  --version VERSION  Version of the JARs to copy from OpenJMLUpdateSite (required).
  --overwrite        Allow overwriting existing JARs of the same version in the destination.
  --help             Show this help and exit.

Environment:
  ECLIPSE_HOME   Eclipse installation directory (required for p2 metadata regeneration).
  JAVA_HOME      JDK directory (defaults to 'java' on PATH).
EOF
}

while [ $# -gt 0 ]; do
    case "$1" in
        --version)  VERSION="$2"; shift 2 ;;
        --overwrite) OVERWRITE=1; shift ;;
        --help|-h)  usage; exit 0 ;;
        *) echo "Unknown option: $1" >&2; usage >&2; exit 1 ;;
    esac
done

if [ -z "$VERSION" ]; then
    echo "ERROR: --version is required." >&2
    usage >&2
    exit 1
fi

# shellcheck source=eclipse-utils.sh
. "$SCRIPT_DIR/eclipse-utils.sh"

find_eclipse_home || true

# ---------------------------------------------------------------------------
# Validate source
# ---------------------------------------------------------------------------
if [ ! -d "$SOURCE_DIR/plugins" ] && [ ! -d "$SOURCE_DIR/features" ]; then
    echo "ERROR: no plugins/ or features/ found under $SOURCE_DIR" >&2
    echo "       Run build-update-site.sh first." >&2
    exit 1
fi

# ---------------------------------------------------------------------------
# Show what we are about to copy
# ---------------------------------------------------------------------------
echo "Source:      $SOURCE_DIR"
echo "Destination: $DEST_DIR"
echo "Version:     $VERSION"
echo ""

# ---------------------------------------------------------------------------
# Clean up stale artifacts from old p2 publisher runs
#
# Old scripts used separate -metadataRepositoryLocation/-artifactRepositoryLocation
# flags pointing to metadata/ and artifacts/ subdirectories, leaving stale
# sub-repositories that confuse Eclipse.  Remove them unconditionally.
# Also remove any expanded feature directories (keep only feature JARs).
# ---------------------------------------------------------------------------
echo "--- Cleaning up stale p2 sub-repositories ---"
# Always remove existing metadata JARs so the publisher generates them fresh.
# Without this, -append keeps old artifact entries with stale SHA hashes when
# a JAR is rebuilt at the same version, causing p2 hash-mismatch errors.
for stale_file in "$DEST_DIR/artifacts.jar" "$DEST_DIR/content.jar"; do
    if [ -f "$stale_file" ]; then
        echo "  Removing stale metadata: $stale_file"
        rm -f "$stale_file"
    fi
done
for stale_dir in "$DEST_DIR/artifacts" "$DEST_DIR/metadata"; do
    if [ -d "$stale_dir" ]; then
        echo "  Removing stale subdir: $stale_dir"
        rm -rf "$stale_dir"
    fi
done
# Remove expanded feature dirs (those without a .jar extension alongside the same name .jar)
if [ -d "$DEST_DIR/features" ]; then
    for d in "$DEST_DIR/features"/*/; do
        [ -d "$d" ] || continue
        bn="$(basename "$d")"
        # If a JAR with the same name exists, the dir is the expanded form — remove it
        if [ -f "$DEST_DIR/features/${bn}.jar" ]; then
            echo "  Removing expanded feature dir (JAR exists): $bn"
            rm -rf "$d"
        fi
    done
fi

# ---------------------------------------------------------------------------
# Copy version-matching JARs into the live site (accumulates older versions)
# ---------------------------------------------------------------------------
mkdir -p "$DEST_DIR/plugins" "$DEST_DIR/features"

copy_versioned_jars() {
    local src_subdir="$1" dest_subdir="$2" label="$3"
    local found=0
    echo "--- Copying $label ---"
    for jar in "$src_subdir"/*_"${VERSION}".jar; do
        [ -f "$jar" ] || continue
        found=1
        local name dest
        name="$(basename "$jar")"
        dest="$dest_subdir/$name"
        if [ -f "$dest" ]; then
            if [ "$OVERWRITE" -eq 1 ]; then
                echo "  (overwriting) $name"
            else
                echo "ERROR: $name already exists in destination; use --overwrite to replace." >&2
                exit 1
            fi
        else
            echo "  + $name"
        fi
        cp "$jar" "$dest"
    done
    if [ "$found" -eq 0 ]; then
        echo "ERROR: no $label JARs matching version $VERSION found in $(basename "$src_subdir")." >&2
        exit 1
    fi
}

copy_versioned_jars "$SOURCE_DIR/plugins"  "$DEST_DIR/plugins"  "plugins"
copy_versioned_jars "$SOURCE_DIR/features" "$DEST_DIR/features" "features"

# Copy category.xml (always keep it current)
if [ -f "$SOURCE_DIR/category.xml" ]; then
    echo "--- Copying category.xml ---"
    cp "$SOURCE_DIR/category.xml" "$DEST_DIR/category.xml"
fi

# ---------------------------------------------------------------------------
# Regenerate p2 metadata
# ---------------------------------------------------------------------------
if [ -z "${ECLIPSE_HOME-}" ]; then
    echo "" >&2
    echo "ERROR: ECLIPSE_HOME is required for p2 metadata regeneration." >&2
    echo "       Set ECLIPSE_HOME to your Eclipse installation." >&2
    exit 1
fi

# Find the equinox launcher JAR (non-source) that has a p2 publisher bundle alongside it
LAUNCHER_JAR=""
for pd in "$ECLIPSE_HOME/plugins" "$ECLIPSE_HOME/Contents/Eclipse/plugins"; do
    [ -d "$pd" ] || continue
    while IFS= read -r cand; do
        case "$(basename "$cand")" in *source*|*src*) continue ;; esac
        # Verify the p2 publisher bundle is in the same plugins dir
        ls "$pd"/org.eclipse.equinox.p2.publisher_*.jar >/dev/null 2>&1 || continue
        LAUNCHER_JAR="$cand"
        break 2
    done < <(find "$pd" -maxdepth 1 -name "org.eclipse.equinox.launcher_*.jar" 2>/dev/null | sort -r)
done

if [ -z "$LAUNCHER_JAR" ]; then
    echo "" >&2
    echo "ERROR: equinox launcher JAR not found under ECLIPSE_HOME=$ECLIPSE_HOME" >&2
    echo "       Ensure ECLIPSE_HOME points to an Eclipse installation that includes" >&2
    echo "       org.eclipse.equinox.p2.publisher, or use --no-p2." >&2
    exit 1
fi

JAVA_CMD="${JAVA_HOME:+$JAVA_HOME/bin/}java"
if ! command -v "$JAVA_CMD" >/dev/null 2>&1; then
    echo "ERROR: java not found; set JAVA_HOME or add java to PATH." >&2
    exit 1
fi

DEST_URI="file:$(cd "$DEST_DIR" && pwd -P)"

echo ""
echo "--- Regenerating p2 metadata ---"
echo "Launcher: $LAUNCHER_JAR"
echo "Site URI: $DEST_URI"

PUBLISH_LOG=$(mktemp)
trap 'rm -f "$PUBLISH_LOG"' EXIT

set +e
"$JAVA_CMD" -jar "$LAUNCHER_JAR" -nosplash \
    -application org.eclipse.equinox.p2.publisher.FeaturesAndBundlesPublisher \
    -metadataRepository  "$DEST_URI" \
    -artifactRepository  "$DEST_URI" \
    -source              "$(cd "$DEST_DIR" && pwd -P)" \
    -publishArtifacts -append -compress -consolelog \
    >"$PUBLISH_LOG" 2>&1
P2_STATUS=$?
set -e

if [ $P2_STATUS -eq 0 ]; then
    echo "p2 FeaturesAndBundlesPublisher succeeded."
else
    echo "" >&2
    echo "WARNING: p2 FeaturesAndBundlesPublisher exited with status $P2_STATUS." >&2
    echo "Publisher output (last 30 lines):" >&2
    tail -n 30 "$PUBLISH_LOG" >&2
    echo "" >&2
    echo "The JARs were copied but metadata regeneration failed." >&2
    echo "Eclipse will not be able to discover installable units." >&2
fi

# ---------------------------------------------------------------------------
# Step 2: CategoryPublisher — adds category grouping to content.jar so that
# features appear in Eclipse's "Install New Software" grouped view.
# Without this step, features are invisible when "Group items by category" is on.
# ---------------------------------------------------------------------------
if [ $P2_STATUS -eq 0 ] && [ -f "$DEST_DIR/category.xml" ]; then
    echo ""
    echo "--- Running CategoryPublisher ---"
    CATEGORY_URI="file://$(cd "$DEST_DIR" && pwd -P)/category.xml"

    set +e
    "$JAVA_CMD" -jar "$LAUNCHER_JAR" -nosplash \
        -application org.eclipse.equinox.p2.publisher.CategoryPublisher \
        -metadataRepository  "$DEST_URI" \
        -categoryDefinition  "$CATEGORY_URI" \
        -compress -consolelog \
        >>"$PUBLISH_LOG" 2>&1
    CAT_STATUS=$?
    set -e

    if [ $CAT_STATUS -eq 0 ]; then
        echo "CategoryPublisher succeeded — feature will appear in grouped view."
    else
        echo "" >&2
        echo "WARNING: CategoryPublisher exited with status $CAT_STATUS." >&2
        echo "Publisher output (last 20 lines):" >&2
        tail -n 20 "$PUBLISH_LOG" >&2
        echo "" >&2
        echo "Feature may not appear in Eclipse 'Install New Software' grouped view." >&2
        echo "Users can still install if they uncheck 'Group items by category'." >&2
    fi
fi

# Remove the log file the publisher may have written into DEST_DIR
rm -f "$DEST_DIR/publish.log" 2>/dev/null || true

echo ""
echo "--- Done ---"
echo "  Site: $DEST_DIR"
echo ""
echo "Next step (manual): cd ../../openjml.github.io && git add -A && git commit -m 'Update Eclipse update site' && git push"
