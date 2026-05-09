#!/usr/bin/env bash
# remove-version.sh
# Purpose:
#   Remove one or more versions of the OpenJMLUI plugin and feature JARs from
#   the openjml.github.io eclipse-update-site, then regenerate p2 metadata.
#
# Typical use: remove development/test builds before publishing a public release.
#
# Usage:
#   ./remove-version.sh --version VERSION [--version VERSION ...] [--help]
#   ./remove-version.sh --all-qualified [--help]
#
# Options:
#   --version VERSION    Version string to remove, e.g. 21.0.25.a.
#                        May be repeated to remove multiple versions at once.
#   --all-qualified      Remove all versions whose version string has an OSGi
#                        qualifier (fourth dot-component), e.g. 21.0.25.a.
#                        Leaves bare major.minor.patch releases untouched.
#   -h, --help           Show this help and exit.
#
# Environment:
#   ECLIPSE_HOME   Eclipse installation (required for p2 regeneration).
#   JAVA_HOME      JDK directory (defaults to 'java' on PATH).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"

# shellcheck source=eclipse-utils.sh
. "$SCRIPT_DIR/eclipse-utils.sh"

PAGES_DIR="$SCRIPT_DIR/../../openjml.github.io/eclipse-update-site"
PLUGIN_ID="org.openjml.OpenJMLUI"
FEATURE_ID="org.openjml.OpenJMLFeature"

# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
VERSIONS=()
ALL_QUALIFIED=0

usage() {
    cat <<EOF
Usage: $(basename "$0") (--version VERSION [--version VERSION ...] | --all-qualified) [--help]

  --version VERSION    Version to remove, e.g. 21.0.25.a (repeatable).
  --all-qualified      Remove all versions with an OSGi qualifier (fourth dot-component).
  -h, --help           Show this help and exit.

Environment:
  ECLIPSE_HOME   Eclipse installation directory (required for p2 regeneration).
  JAVA_HOME      JDK directory (defaults to 'java' on PATH).
EOF
}

while [ $# -gt 0 ]; do
    case "$1" in
        --version)       VERSIONS+=("$2"); shift 2 ;;
        --all-qualified) ALL_QUALIFIED=1; shift ;;
        -h|--help)       usage; exit 0 ;;
        *) echo "Unknown option: $1" >&2; usage >&2; exit 1 ;;
    esac
done

if [ "$ALL_QUALIFIED" -eq 0 ] && [ ${#VERSIONS[@]} -eq 0 ]; then
    echo "ERROR: --version or --all-qualified is required." >&2
    usage >&2
    exit 1
fi

# ---------------------------------------------------------------------------
# Resolve directories
# ---------------------------------------------------------------------------
PAGES_DIR="$(cd "$PAGES_DIR" 2>/dev/null && pwd -P)" || {
    echo "ERROR: GH pages update site not found at $PAGES_DIR" >&2
    exit 1
}

# ---------------------------------------------------------------------------
# Collect versions to remove
# ---------------------------------------------------------------------------
if [ "$ALL_QUALIFIED" -eq 1 ]; then
    # Qualified versions have four dot-separated components: major.minor.micro.qualifier
    while IFS= read -r jar; do
        ver="${jar##*_}"; ver="${ver%.jar}"
        # A version is qualified if it contains more than two dots (i.e. has a qualifier)
        dots="${ver//[^.]}"
        if [ ${#dots} -ge 3 ]; then
            VERSIONS+=("$ver")
        fi
    done < <(find "$PAGES_DIR/features" -maxdepth 1 -name "${FEATURE_ID}_*.jar" 2>/dev/null | sort)
    # Deduplicate
    mapfile -t VERSIONS < <(printf '%s\n' "${VERSIONS[@]}" | sort -u)
    if [ ${#VERSIONS[@]} -eq 0 ]; then
        echo "No qualified versions found in $PAGES_DIR/features/."
        exit 0
    fi
    echo "Qualified versions to remove: ${VERSIONS[*]}"
fi

echo "GH pages: $PAGES_DIR"
echo ""

REMOVED=0
MISSING=0

# ---------------------------------------------------------------------------
# Helper: remove one JAR
# ---------------------------------------------------------------------------
remove_jar() {
    local path="$1" label="$2"
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
# Remove from GH pages site
# ---------------------------------------------------------------------------
echo "--- GH pages eclipse-update-site ---"
for ver in "${VERSIONS[@]}"; do
    echo "  Version: $ver"
    remove_jar "$PAGES_DIR/plugins/${PLUGIN_ID}_${ver}.jar"   "plugins/${PLUGIN_ID}_${ver}.jar"
    remove_jar "$PAGES_DIR/features/${FEATURE_ID}_${ver}.jar" "features/${FEATURE_ID}_${ver}.jar"
done
echo ""

echo "--- Summary ---"
echo "  Removed  : $REMOVED JAR(s)"
echo "  Not found: $MISSING JAR(s)"
echo ""

# ---------------------------------------------------------------------------
# Resolve p2 tooling
# ---------------------------------------------------------------------------
find_eclipse_home || true

if [ -z "${ECLIPSE_HOME-}" ]; then
    echo "WARNING: ECLIPSE_HOME not set and Eclipse not auto-detected." >&2
    echo "  p2 metadata not regenerated.  Eclipse may still offer the removed version(s)." >&2
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
echo "Launcher: $LAUNCHER_JAR"

# ---------------------------------------------------------------------------
# Regenerate p2 metadata for the GH pages site.
# Deletes content.jar/artifacts.jar first so removed versions don't linger.
# ---------------------------------------------------------------------------
SITE_URI="file:$(cd "$PAGES_DIR" && pwd -P)"
CATEGORY_URI="file://$(cd "$PAGES_DIR" && pwd -P)/category.xml"

echo ""
echo "--- Regenerating p2 metadata ---"
rm -f "$PAGES_DIR/content.jar" "$PAGES_DIR/artifacts.jar"

set +e
"$JAVA_CMD" -jar "$LAUNCHER_JAR" -nosplash \
    -application org.eclipse.equinox.p2.publisher.FeaturesAndBundlesPublisher \
    -metadataRepository  "$SITE_URI" \
    -artifactRepository  "$SITE_URI" \
    -source              "$(cd "$PAGES_DIR" && pwd -P)" \
    -publishArtifacts -append -compress -consolelog \
    >"$PUBLISH_LOG" 2>&1
P2_STATUS=$?
set -e

if [ $P2_STATUS -ne 0 ]; then
    echo "WARNING: FeaturesAndBundlesPublisher failed (exit $P2_STATUS)." >&2
    tail -n 20 "$PUBLISH_LOG" >&2
    exit 1
fi
echo "FeaturesAndBundlesPublisher succeeded."

if [ -f "$PAGES_DIR/category.xml" ]; then
    set +e
    "$JAVA_CMD" -jar "$LAUNCHER_JAR" -nosplash \
        -application org.eclipse.equinox.p2.publisher.CategoryPublisher \
        -metadataRepository  "$SITE_URI" \
        -categoryDefinition  "$CATEGORY_URI" \
        -compress -consolelog \
        >>"$PUBLISH_LOG" 2>&1
    CAT_STATUS=$?
    set -e
    if [ $CAT_STATUS -eq 0 ]; then
        echo "CategoryPublisher succeeded."
    else
        echo "WARNING: CategoryPublisher failed (exit $CAT_STATUS)." >&2
        tail -n 10 "$PUBLISH_LOG" >&2
    fi
fi

rm -f "$PAGES_DIR/publish.log" 2>/dev/null || true

echo ""
echo "Next: review changes, then commit and push the GH pages repo:"
echo "  cd $PAGES_DIR && git add -A && git commit -m 'Remove development versions: ${VERSIONS[*]}' && git push"
