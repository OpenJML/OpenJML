#!/usr/bin/env bash
# remove-version.sh
# Purpose:
#   Remove a specific version of the OpenJMLUI plugin and feature JARs from
#   both the local OpenJMLUpdateSite staging area and the openjml.github.io
#   eclipse-update-site, then regenerate p2 metadata for the GH pages site.
#
# Typical use: remove a development/test build before publishing.
#
# Usage:
#   ./remove-version.sh --version VERSION [--no-p2] [--help]
#
# Options:
#   --version VERSION   Version to remove (required), e.g. 0.21.0-SNAPSHOT.
#   --no-p2             Skip p2 metadata regeneration for the GH pages site.
#   -h, --help          Show this help and exit.
#
# Environment:
#   ECLIPSE_HOME   Eclipse installation (required for p2 regeneration).
#   JAVA_HOME      JDK directory (defaults to 'java' on PATH).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"

# shellcheck source=eclipse-utils.sh
. "$SCRIPT_DIR/eclipse-utils.sh"

STAGING_DIR="$SCRIPT_DIR/../OpenJMLUpdateSite"
PAGES_DIR="$SCRIPT_DIR/../../openjml.github.io/eclipse-update-site"
PLUGIN_ID="org.openjml.OpenJMLUI"
FEATURE_ID="org.openjml.OpenJMLFeature"

# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
VERSION=""
DO_P2=1
P2_EXPLICIT=""

usage() {
    cat <<EOF
Usage: $(basename "$0") --version VERSION [--no-p2] [--help]

  --version VERSION   Version string to remove (required), e.g. 0.21.0.
  --no-p2             Skip p2 metadata regeneration for the GH pages site.
  -h, --help          Show this help and exit.

Environment:
  ECLIPSE_HOME   Eclipse installation directory (required for p2).
  JAVA_HOME      JDK directory (defaults to 'java' on PATH).
EOF
}

while [ $# -gt 0 ]; do
    case "$1" in
        --version) VERSION="$2"; shift 2 ;;
        --no-p2)   DO_P2=0; P2_EXPLICIT=1; shift ;;
        -h|--help) usage; exit 0 ;;
        *) echo "Unknown option: $1" >&2; usage >&2; exit 1 ;;
    esac
done

if [ -z "$VERSION" ]; then
    echo "ERROR: --version is required." >&2
    usage >&2
    exit 1
fi

# ---------------------------------------------------------------------------
# Resolve directories
# ---------------------------------------------------------------------------
STAGING_DIR="$(cd "$STAGING_DIR" 2>/dev/null && pwd -P)" || {
    echo "ERROR: OpenJMLUpdateSite not found at $SCRIPT_DIR/../OpenJMLUpdateSite" >&2
    exit 1
}
PAGES_DIR="$(cd "$PAGES_DIR" 2>/dev/null && pwd -P)" || {
    echo "ERROR: GH pages update site not found at $PAGES_DIR" >&2
    exit 1
}

echo "Removing version: $VERSION"
echo "  Staging : $STAGING_DIR"
echo "  GH pages: $PAGES_DIR"
echo ""

REMOVED=0
MISSING=0

# ---------------------------------------------------------------------------
# Helper: remove one JAR, report found/missing
# ---------------------------------------------------------------------------
remove_jar() {
    local path="$1"
    local label="$2"
    if [ -f "$path" ]; then
        rm -f "$path"
        echo "  REMOVED: $label"
        REMOVED=$((REMOVED + 1))
    else
        echo "  NOT FOUND: $label"
        MISSING=$((MISSING + 1))
    fi
}

# ---------------------------------------------------------------------------
# Remove from staging (OpenJMLUpdateSite)
# ---------------------------------------------------------------------------
echo "--- OpenJMLUpdateSite ---"
remove_jar "$STAGING_DIR/plugins/${PLUGIN_ID}_${VERSION}.jar"  "plugins/${PLUGIN_ID}_${VERSION}.jar"
remove_jar "$STAGING_DIR/features/${FEATURE_ID}_${VERSION}.jar" "features/${FEATURE_ID}_${VERSION}.jar"
echo ""

# ---------------------------------------------------------------------------
# Remove from GH pages site
# ---------------------------------------------------------------------------
echo "--- GH pages eclipse-update-site ---"
remove_jar "$PAGES_DIR/plugins/${PLUGIN_ID}_${VERSION}.jar"  "plugins/${PLUGIN_ID}_${VERSION}.jar"
remove_jar "$PAGES_DIR/features/${FEATURE_ID}_${VERSION}.jar" "features/${FEATURE_ID}_${VERSION}.jar"
echo ""

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo "--- Summary ---"
echo "  Removed  : $REMOVED JAR(s)"
echo "  Not found: $MISSING JAR(s)"
echo ""

# ---------------------------------------------------------------------------
# Resolve p2 tooling
# ---------------------------------------------------------------------------
find_eclipse_home || true
if [ -n "${ECLIPSE_HOME-}" ] && [ "$DO_P2" -eq 0 ] && [ -z "$P2_EXPLICIT" ]; then
    DO_P2=1
fi

if [ "$DO_P2" -eq 0 ]; then
    echo "Skipping p2 metadata regeneration (--no-p2)."
    exit 0
fi

if [ -z "${ECLIPSE_HOME-}" ]; then
    echo "WARNING: ECLIPSE_HOME not set and Eclipse not auto-detected." >&2
    echo "  p2 metadata not regenerated.  Eclipse may still offer the removed version." >&2
    echo "  Set ECLIPSE_HOME and rerun with --version $VERSION." >&2
    exit 0
fi

LAUNCHER_JAR=""
for pd in "$ECLIPSE_HOME/plugins" "$ECLIPSE_HOME/Contents/Eclipse/plugins"; do
    [ -d "$pd" ] || continue
    while IFS= read -r cand; do
        case "$(basename "$cand")" in *source*|*src*) continue ;; esac
        ls "$pd"/org.eclipse.equinox.p2.publisher_*.jar >/dev/null 2>&1 || continue
        LAUNCHER_JAR="$cand"
        break 2
    done < <(find "$pd" -maxdepth 1 -name "org.eclipse.equinox.launcher_*.jar" 2>/dev/null | sort -r)
done

if [ -z "$LAUNCHER_JAR" ]; then
    echo "WARNING: equinox launcher not found under ECLIPSE_HOME=$ECLIPSE_HOME" >&2
    echo "  p2 metadata not regenerated." >&2
    exit 0
fi

JAVA_CMD="${JAVA_HOME:+$JAVA_HOME/bin/}java"
if ! command -v "$JAVA_CMD" >/dev/null 2>&1; then
    echo "ERROR: java not found; set JAVA_HOME or add java to PATH." >&2
    exit 1
fi

PUBLISH_LOG=$(mktemp)
trap 'rm -f "$PUBLISH_LOG"' EXIT
echo "  Launcher: $LAUNCHER_JAR"

# ---------------------------------------------------------------------------
# Regenerate p2 metadata helper
# Deletes existing content.jar/artifacts.jar then rebuilds from remaining JARs.
# (Removal requires a fresh scan — append would preserve the deleted version's IUs.)
# ---------------------------------------------------------------------------
regenerate_p2() {
    local site_dir="$1"
    local label="$2"
    local site_uri="file:$(cd "$site_dir" && pwd -P)"
    local category_uri="file://$(cd "$site_dir" && pwd -P)/category.xml"

    echo ""
    echo "--- Regenerating p2 metadata: $label ---"
    echo "  Site: $site_uri"

    rm -f "$site_dir/content.jar" "$site_dir/artifacts.jar"

    set +e
    "$JAVA_CMD" -jar "$LAUNCHER_JAR" -nosplash \
        -application org.eclipse.equinox.p2.publisher.FeaturesAndBundlesPublisher \
        -metadataRepository  "$site_uri" \
        -artifactRepository  "$site_uri" \
        -source              "$(cd "$site_dir" && pwd -P)" \
        -publishArtifacts -append -compress -consolelog \
        >"$PUBLISH_LOG" 2>&1
    local status=$?
    set -e

    if [ $status -ne 0 ]; then
        echo "  WARNING: FeaturesAndBundlesPublisher failed (exit $status)." >&2
        tail -n 20 "$PUBLISH_LOG" >&2
        return
    fi

    if [ -f "$site_dir/category.xml" ]; then
        set +e
        "$JAVA_CMD" -jar "$LAUNCHER_JAR" -nosplash \
            -application org.eclipse.equinox.p2.publisher.CategoryPublisher \
            -metadataRepository  "$site_uri" \
            -categoryDefinition  "$category_uri" \
            -compress -consolelog \
            >>"$PUBLISH_LOG" 2>&1
        local cat_status=$?
        set -e
        [ $cat_status -eq 0 ] \
            && echo "  p2 metadata regenerated successfully." \
            || { echo "  WARNING: CategoryPublisher failed (exit $cat_status)." >&2
                 tail -n 10 "$PUBLISH_LOG" >&2; }
    else
        echo "  p2 metadata regenerated (no category.xml found)."
    fi

    rm -f "$site_dir/publish.log" 2>/dev/null || true
}

regenerate_p2 "$STAGING_DIR" "OpenJMLUpdateSite"
regenerate_p2 "$PAGES_DIR"   "GH pages eclipse-update-site"

echo ""
echo "Next: review changes, then commit and push the GH pages repo:"
echo "  cd $PAGES_DIR && git add -A && git commit -m 'Remove version $VERSION' && git push"
