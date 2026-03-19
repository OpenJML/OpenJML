#!/usr/bin/env bash
# headless-check.sh
# Headless verification that the OpenJMLUI plugin JAR is correctly packaged.
#
# Does NOT launch Eclipse or a GUI.  Finds the plugin JAR in the update site,
# unpacks it, and inspects its contents for required plugin.xml contributions
# and MANIFEST.MF headers.  Reports PASS/FAIL for each check.
#
# Usage:
#   ./headless-check.sh [--site UPDATE_SITE_DIR] [--verbose] [--help]
#
# Options:
#   --site DIR    Path to the update site (default: ../OpenJMLUpdateSite/).
#   -v, --verbose Show extra detail.
#   -h, --help    Show this help and exit.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd -P)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd -P)"

# Default to the locally-built update site
UPDATE_SITE_DIR="$REPO_ROOT/../OpenJMLUpdateSite"
VERBOSE=0
PLUGIN_ID="org.openjml.OpenJMLUI"

log() { [ "$VERBOSE" -eq 1 ] && printf "+ %s\n" "$*"; }

usage() {
    cat <<EOF
Usage: $(basename "$0") [--site UPDATE_SITE_DIR] [--verbose] [--help]

  --site DIR    Update site directory to inspect (default: OpenJMLUpdateSite/).
  -v, --verbose Verbose output.
  -h, --help    Show this help and exit.
EOF
}

while [ $# -gt 0 ]; do
    case "$1" in
        --site)       UPDATE_SITE_DIR="$2"; shift 2 ;;
        -v|--verbose) VERBOSE=1; shift ;;
        -h|--help)    usage; exit 0 ;;
        *) echo "Unknown arg: $1" >&2; usage >&2; exit 1 ;;
    esac
done

UPDATE_SITE_DIR="$(cd "$UPDATE_SITE_DIR" && pwd -P)"
echo "Update site: $UPDATE_SITE_DIR"

# ---------------------------------------------------------------------------
# Find the plugin JAR
# ---------------------------------------------------------------------------
PLUGIN_JAR=""
for j in "$UPDATE_SITE_DIR/plugins/${PLUGIN_ID}"_*.jar; do
    [ -f "$j" ] && PLUGIN_JAR="$j" && break
done

if [ -z "$PLUGIN_JAR" ]; then
    echo "ERROR: plugin JAR not found under $UPDATE_SITE_DIR/plugins/" >&2
    echo "       Expected: ${PLUGIN_ID}_<version>.jar" >&2
    echo "       Run build-update-site.sh first." >&2
    exit 1
fi
echo "Plugin JAR: $PLUGIN_JAR"

# ---------------------------------------------------------------------------
# Find the feature JAR
# ---------------------------------------------------------------------------
FEATURE_JAR=""
for j in "$UPDATE_SITE_DIR/features/"*.jar; do
    [ -f "$j" ] && FEATURE_JAR="$j" && break
done
[ -n "$FEATURE_JAR" ] && echo "Feature JAR: $FEATURE_JAR" \
                      || echo "WARNING: no feature JAR found under $UPDATE_SITE_DIR/features/"

# ---------------------------------------------------------------------------
# Unpack plugin JAR into temp dir
# ---------------------------------------------------------------------------
WORK_DIR="$(mktemp -d)"
trap 'rm -rf "$WORK_DIR"' EXIT

unzip -q "$PLUGIN_JAR" -d "$WORK_DIR"
log "Unpacked plugin JAR to $WORK_DIR"

# ---------------------------------------------------------------------------
# Checks
# ---------------------------------------------------------------------------
PASS=0
FAIL=0

check_pass() { echo "  PASS: $1"; PASS=$((PASS + 1)); }
check_fail() { echo "  FAIL: $1" >&2; FAIL=$((FAIL + 1)); }

echo ""
echo "--- MANIFEST.MF checks ---"

MF="$WORK_DIR/META-INF/MANIFEST.MF"
if [ ! -f "$MF" ]; then
    check_fail "META-INF/MANIFEST.MF not present"
else
    check_pass "META-INF/MANIFEST.MF present"

    grep -q "^Bundle-SymbolicName:.*${PLUGIN_ID}" "$MF" \
        && check_pass "Bundle-SymbolicName is $PLUGIN_ID" \
        || check_fail "Bundle-SymbolicName does not contain $PLUGIN_ID"

    grep -q "^Bundle-Activator:" "$MF" \
        && check_pass "Bundle-Activator is present" \
        || check_fail "Bundle-Activator missing"

    grep -q "^Bundle-Version:" "$MF" \
        && check_pass "Bundle-Version is present" \
        || check_fail "Bundle-Version missing"

    grep -q "^Require-Bundle:.*org\.eclipse\.lsp4e" "$MF" \
        && check_pass "Requires org.eclipse.lsp4e" \
        || check_fail "org.eclipse.lsp4e not in Require-Bundle"

    if [ "$VERBOSE" -eq 1 ]; then
        echo "  MANIFEST.MF contents:"
        sed 's/^/    /' "$MF"
    fi
fi

echo ""
echo "--- plugin.xml checks ---"

PX="$WORK_DIR/plugin.xml"
if [ ! -f "$PX" ]; then
    check_fail "plugin.xml not present in plugin JAR"
else
    check_pass "plugin.xml present"

    grep -q "org\.eclipse\.ui\.commands\|org\.eclipse\.ui\.handlers\|org\.eclipse\.ui\.menus\|org\.eclipse\.ui\.toolbar" "$PX" \
        && check_pass "plugin.xml contains UI contribution extension points" \
        || check_fail "plugin.xml has no UI contribution extension points"

    grep -q "org\.eclipse\.lsp4e\.languageServer" "$PX" \
        && check_pass "plugin.xml registers org.eclipse.lsp4e.languageServer extension" \
        || check_fail "plugin.xml missing org.eclipse.lsp4e.languageServer extension"

    if [ "$VERBOSE" -eq 1 ]; then
        echo "  Toolbar/menu/command/handler lines in plugin.xml:"
        grep -n "toolbar\|menu\|command\|handler\|label\|icon\|lsp4e" "$PX" | sed 's/^/    /' || true
    fi
fi

echo ""
echo "--- Library JAR checks ---"

for lib in gson-2.8.1.jar; do
    [ -f "$WORK_DIR/$lib" ] \
        && check_pass "$lib present" \
        || check_fail "$lib missing from plugin JAR"
done

echo ""
echo "--- Feature JAR check ---"

if [ -n "$FEATURE_JAR" ]; then
    FWORK="$(mktemp -d)"
    trap 'rm -rf "$WORK_DIR" "$FWORK"' EXIT
    unzip -q "$FEATURE_JAR" -d "$FWORK"
    if [ -f "$FWORK/feature.xml" ]; then
        check_pass "feature.xml present inside feature JAR"
        grep -q "id=\"org\.openjml\.OpenJMLFeature\"" "$FWORK/feature.xml" \
            && check_pass "feature.xml has correct id" \
            || check_fail "feature.xml id does not match org.openjml.OpenJMLFeature"
        grep -q "id=\"${PLUGIN_ID}\"" "$FWORK/feature.xml" \
            && check_pass "feature.xml references plugin $PLUGIN_ID" \
            || check_fail "feature.xml does not reference plugin $PLUGIN_ID"
        grep -q "unpack=\"false\"" "$FWORK/feature.xml" \
            && check_pass "feature.xml has unpack=\"false\"" \
            || check_fail "feature.xml missing unpack=\"false\""
    else
        check_fail "feature.xml not found inside feature JAR"
    fi
fi

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo ""
echo "--- Summary ---"
echo "  PASS: $PASS"
echo "  FAIL: $FAIL"
echo ""

if [ "$FAIL" -gt 0 ]; then
    echo "RESULT: FAILED ($FAIL check(s) failed)" >&2
    exit 1
else
    echo "RESULT: PASSED (all $PASS checks)"
    exit 0
fi
