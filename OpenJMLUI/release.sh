#!/usr/bin/env bash
# release.sh
# Purpose:
#   Bump the version, build the plugin/feature JARs, and copy them into the
#   openjml.github.io/eclipse-update-site directory.
#
# Committing and pushing (both the OpenJML repo and the GH Pages repo) are
# always done as a separate manual step after reviewing the results.
#
# Typical usage:
#   ./release.sh --version 0.22.0 --overwrite
#
# Actions (in order):
#   1. Update version in MANIFEST.MF, feature.xml, category.xml  (via build-update-site.sh --version)
#   2. Compile OpenJMLUI and package plugin + feature JARs into OpenJMLUpdateSite/
#   3. Copy JARs into openjml.github.io/eclipse-update-site/ and regenerate p2 metadata
#
# Environment:
#   ECLIPSE_HOME   Eclipse installation (required for compilation and p2).
#   JAVA_HOME      JDK directory.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd -P)"
UI_DIR="$SCRIPT_DIR"
BUILD_SCRIPT="$UI_DIR/build-update-site.sh"
PUBLISH_SCRIPT="$UI_DIR/publish-update-site.sh"

# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
usage() {
    cat <<EOF
Usage: $(basename "$0") --version VERSION [options]

Required:
  --version VERSION   Release version (e.g. 0.22.0)

Options:
  --overwrite         Allow overwriting existing output JARs of the same version.
  --no-build          Skip compilation; package whatever is already in bin/.
  --no-p2             Skip p2 metadata regeneration in the pages site.
  -h, --help          Show this help and exit.

Environment:
  ECLIPSE_HOME   Eclipse installation directory (required for compilation and p2).
  JAVA_HOME      JDK directory.
EOF
}

VERSION=""
OVERWRITE_FLAG=""
BUILD_FLAG=""
P2_FLAG=""

while [ $# -gt 0 ]; do
    case "$1" in
        --version)   VERSION="$2"; shift 2 ;;
        --overwrite) OVERWRITE_FLAG="--overwrite"; shift ;;
        --no-build)  BUILD_FLAG="--no-build"; shift ;;
        --no-p2)     P2_FLAG="--no-p2"; shift ;;
        -h|--help)   usage; exit 0 ;;
        *) echo "Unknown option: $1" >&2; usage >&2; exit 1 ;;
    esac
done

if [ -z "$VERSION" ]; then
    echo "ERROR: --version is required." >&2
    usage >&2
    exit 1
fi

[ -x "$BUILD_SCRIPT" ]   || { echo "ERROR: not found/executable: $BUILD_SCRIPT" >&2; exit 1; }
[ -x "$PUBLISH_SCRIPT" ] || { echo "ERROR: not found/executable: $PUBLISH_SCRIPT" >&2; exit 1; }

echo "=== OpenJML release $VERSION ==="

# ---------------------------------------------------------------------------
# Step 1 + 2: version bump, compile, package
# ---------------------------------------------------------------------------
BUILD_CMD=("$BUILD_SCRIPT" "--version" "$VERSION")
[ -n "$OVERWRITE_FLAG" ] && BUILD_CMD+=("$OVERWRITE_FLAG")
[ -n "$BUILD_FLAG" ]     && BUILD_CMD+=("$BUILD_FLAG")

echo ""
echo "--- Step 1/2: build ---"
( cd "$UI_DIR" && "${BUILD_CMD[@]}" )

# ---------------------------------------------------------------------------
# Step 3: copy JARs to pages site, regenerate p2 metadata
# ---------------------------------------------------------------------------
PUBLISH_CMD=("$PUBLISH_SCRIPT")
[ -n "$P2_FLAG" ] && PUBLISH_CMD+=("$P2_FLAG")

echo ""
echo "--- Step 3: publish ---"
( cd "$UI_DIR" && "${PUBLISH_CMD[@]}" )

# ---------------------------------------------------------------------------
echo ""
echo "=== Release $VERSION complete ==="
echo ""
echo "Next: review changes, then commit and push manually:"
echo "  OpenJML repo  — MANIFEST.MF, feature.xml, category.xml"
echo "  GH Pages repo — eclipse-update-site/"
