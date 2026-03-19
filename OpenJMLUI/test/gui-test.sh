#!/usr/bin/env bash
# gui-test.sh
# GUI-driven test for OpenJMLUI on macOS using an isolated Eclipse app copy and AppleScript UI scripting.
# Copies a temporary Eclipse.app, installs the plugin from the local update site, launches Eclipse
# with a temp workspace, clicks the ESC/RAC toolbar buttons, and checks the workspace log.
#
# Usage:
#   ./gui-test.sh [--eclipse-app PATH] [--site DIR] [--tmp DIR] [--verbose] [--help]
#
# Options:
#   --eclipse-app PATH  Path to source Eclipse.app bundle (auto-detected if omitted).
#   --site DIR          Update site directory (default: ../../OpenJMLUpdateSite).
#   --tmp DIR           Temp base directory (default: /tmp/openjml-gui-test).
#   -v, --verbose       Show extra detail.
#   -h, --help          Show this help and exit.
#
# Requirements:
#   - macOS with AppleScript / Accessibility permissions granted to Terminal.
#   - java on PATH (for p2 director).
#   - rsync on PATH (for fast app copy; falls back to cp -a).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd -P)"

# ---------------------------------------------------------------------------
# Defaults
# ---------------------------------------------------------------------------
ECLIPSE_APP_SRC="/Users/davidcok/eclipse/eclipse-committers-2026-03-R-macosx-cocoa-x86_64-pure/Eclipse.app"
UPDATE_SITE_DIR="$REPO_ROOT/../OpenJMLUpdateSite"
TMP_BASE="/tmp/openjml-gui-test"
VERBOSE=0

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
log()  { [ "$VERBOSE" -eq 1 ] && printf "+ %s\n" "$*"; }
err()  { printf "ERROR: %s\n" "$*" >&2; }

usage() {
  cat <<EOF
Usage: $(basename "$0") [--eclipse-app PATH] [--site DIR] [--tmp DIR] [--verbose] [--help]

  --eclipse-app PATH  Source Eclipse.app bundle (auto-detected if omitted).
  --site DIR          Update site directory (default: OpenJMLUpdateSite/).
  --tmp DIR           Temp base directory (default: /tmp/openjml-gui-test).
  -v, --verbose       Verbose output.
  -h, --help          Show this help and exit.

Grant Accessibility permission to Terminal in:
  System Settings → Privacy & Security → Accessibility
EOF
}

# shellcheck source=../eclipse-utils.sh
. "$SCRIPT_DIR/../eclipse-utils.sh"

# ---------------------------------------------------------------------------
# Parse arguments
# ---------------------------------------------------------------------------
while [ $# -gt 0 ]; do
  case "$1" in
    --eclipse-app) ECLIPSE_APP_SRC="$2"; shift 2 ;;
    --site)        UPDATE_SITE_DIR="$2"; shift 2 ;;
    --tmp)         TMP_BASE="$2"; shift 2 ;;
    -v|--verbose)  VERBOSE=1; shift ;;
    -h|--help)     usage; exit 0 ;;
    *) err "Unknown arg: $1"; usage >&2; exit 1 ;;
  esac
done

TMP_APP="$TMP_BASE/Eclipse.app"
TMP_WS="$TMP_BASE/workspace"

# ---------------------------------------------------------------------------
# Resolve Eclipse source app
# ---------------------------------------------------------------------------
if [ ! -d "$ECLIPSE_APP_SRC" ]; then
  # Default not found — try auto-detection
  if DETECTED="$(find_eclipse_app 2>/dev/null)"; then
    ECLIPSE_APP_SRC="$DETECTED"
    echo "Auto-detected Eclipse: $ECLIPSE_APP_SRC"
  fi
fi

if [ ! -d "$ECLIPSE_APP_SRC" ]; then
  err "Eclipse app not found at: $ECLIPSE_APP_SRC"
  exit 2
fi

UPDATE_SITE_DIR="$(cd "$UPDATE_SITE_DIR" 2>/dev/null && pwd -P)" || {
  err "Update site not found: $UPDATE_SITE_DIR"
  exit 2
}
echo "Update site: $UPDATE_SITE_DIR"

# ---------------------------------------------------------------------------
# Cleanup trap — quit Eclipse, remove temp files
# ---------------------------------------------------------------------------
SCPT_FILES=()   # accumulate temp AppleScript paths for cleanup

cleanup() {
  # Ask Eclipse to quit (ignore errors — it may already be gone)
  osascript -e 'tell application "Eclipse" to quit' 2>/dev/null || true
  sleep 2
  # Remove temp AppleScript files
  for scpt in "${SCPT_FILES[@]:-}"; do
    [ -f "$scpt" ] && rm -f "$scpt"
  done
  log "Cleanup done."
}
trap cleanup EXIT

# ---------------------------------------------------------------------------
# Prepare temp directory
# ---------------------------------------------------------------------------
if [ -d "$TMP_BASE" ]; then
  log "Removing existing temp dir: $TMP_BASE"
  rm -rf "$TMP_BASE"
fi
mkdir -p "$TMP_BASE" "$TMP_WS"

# ---------------------------------------------------------------------------
# Copy Eclipse app bundle
# ---------------------------------------------------------------------------
echo "Copying Eclipse app to $TMP_APP (may take a minute)..."
if command -v rsync >/dev/null 2>&1; then
  rsync -a --exclude=configuration/org.eclipse.osgi -E "$ECLIPSE_APP_SRC/" "$TMP_APP/" 2>/dev/null \
    || cp -a "$ECLIPSE_APP_SRC" "$TMP_APP"
else
  cp -a "$ECLIPSE_APP_SRC" "$TMP_APP"
fi
echo "Eclipse copied."

# ---------------------------------------------------------------------------
# Find equinox launcher JAR inside temp app
# ---------------------------------------------------------------------------
LAUNCHER_JAR=""
for j in "$TMP_APP/Contents/Eclipse/plugins/org.eclipse.equinox.launcher"*.jar; do
  [[ "$j" == *source* || "$j" == *-src* ]] && continue
  [ -f "$j" ] && LAUNCHER_JAR="$j" && break
done
if [ -z "$LAUNCHER_JAR" ]; then
  for j in "$TMP_APP/Contents/Eclipse/plugins/org.eclipse.equinox.launcher"*.jar; do
    [ -f "$j" ] && LAUNCHER_JAR="$j" && break
  done
fi
if [ -z "$LAUNCHER_JAR" ]; then
  err "Could not find equinox launcher jar in copied Eclipse app"
  exit 3
fi
log "Using equinox launcher: $LAUNCHER_JAR"

# ---------------------------------------------------------------------------
# Detect IU from update site features/
# JAR-based features (modern): features/org.openjml.OpenJMLFeature_1.2.3.jar
# Expanded features (legacy):  features/org.openjml.OpenJMLFeature_1.2.3/feature.xml
# ---------------------------------------------------------------------------
IU=""
if [ -d "$UPDATE_SITE_DIR/features" ]; then
  # JAR-based features
  for j in "$UPDATE_SITE_DIR/features"/*.jar; do
    [ -f "$j" ] || continue
    bn="$(basename "$j" .jar)"       # e.g. org.openjml.OpenJMLFeature_0.21.0
    id="${bn%_*}"                    # e.g. org.openjml.OpenJMLFeature
    [ -n "$id" ] && IU="${id}.feature.group" && break
  done
  # Fallback: expanded feature dirs
  if [ -z "$IU" ]; then
    for d in "$UPDATE_SITE_DIR/features"/*/; do
      [ -f "$d/feature.xml" ] || continue
      id="$(sed -n 's/.*<feature[^>]*id="\([^"]*\)".*/\1/p' "$d/feature.xml" | head -1)"
      [ -n "$id" ] && IU="${id}.feature.group" && break
    done
  fi
fi
log "Feature IU: ${IU:-(none detected)}"

# ---------------------------------------------------------------------------
# Install plugin/feature into copied Eclipse via p2 director
# ---------------------------------------------------------------------------
JAVA_CMD="$(command -v java 2>/dev/null || true)"
if [ -z "$JAVA_CMD" ]; then err "java not found on PATH"; exit 4; fi

SITE_URI="file://$UPDATE_SITE_DIR"

if [ -n "$IU" ]; then
  echo "Installing $IU into temporary Eclipse..."
  "$JAVA_CMD" -Dfile.encoding=UTF-8 -jar "$LAUNCHER_JAR" \
    -nosplash -application org.eclipse.equinox.p2.director \
    -repository "$SITE_URI" \
    -installIU "$IU" \
    -destination "$TMP_APP/Contents/Eclipse" \
    -profile SDKProfile \
    -consolelog || {
      err "p2 director failed (exit $?). Check update site contents."
      exit 5
    }
else
  echo "No feature IU detected; attempting to install plugin jars individually..."
  for pj in "$UPDATE_SITE_DIR/plugins"/*.jar; do
    [ -f "$pj" ] || continue
    bn="$(basename "$pj" .jar)"
    id="${bn%_*}"
    echo "  Installing bundle $id"
    "$JAVA_CMD" -Dfile.encoding=UTF-8 -jar "$LAUNCHER_JAR" \
      -nosplash -application org.eclipse.equinox.p2.director \
      -repository "$SITE_URI" \
      -installIU "$id" \
      -destination "$TMP_APP/Contents/Eclipse" \
      -profile SDKProfile \
      -consolelog || true
  done
fi

# ---------------------------------------------------------------------------
# Launch Eclipse with temp workspace
# ---------------------------------------------------------------------------
echo "Launching temporary Eclipse (workspace: $TMP_WS)..."
open "$TMP_APP" --args -data "$TMP_WS"
echo "Eclipse launch initiated. Waiting for UI..."

# Wait for Eclipse window to appear (retry up to ~60 seconds)
WAITED=0
READY=0
while [ $WAITED -lt 60 ]; do
  if osascript -e '
    tell application "System Events"
      set n to count (windows of process "Eclipse")
      return n > 0
    end tell' 2>/dev/null | grep -q "true"; then
    READY=1
    break
  fi
  sleep 5
  WAITED=$((WAITED + 5))
  log "Waited ${WAITED}s for Eclipse window..."
done

if [ "$READY" -eq 0 ]; then
  echo "WARNING: Eclipse window did not appear within 60s. Continuing anyway..."
fi
echo "Eclipse appears ready (${WAITED}s)."

# Give Eclipse a couple more seconds to finish rendering toolbars
sleep 3

# ---------------------------------------------------------------------------
# Dump toolbar UI elements (aids selector tuning)
# ---------------------------------------------------------------------------
TOOLBAR_DUMP="/tmp/openjml-toolbar-elements-$$.txt"
SCPT_DUMP="/tmp/openjml-dump-toolbar-$$.scpt"
SCPT_FILES+=("$SCPT_DUMP")

cat > "$SCPT_DUMP" <<'APPSCRIPT'
on run argv
  set outPath to item 1 of argv
  set s to ""
  tell application "System Events"
    try
      tell application process "Eclipse"
        set frontmost to true
        delay 0.5
        repeat with w in windows
          set s to s & "Window: " & (index of w as string) & "\n"
          try
            set tbIdx to 0
            repeat with tb in tool bars of w
              set tbIdx to tbIdx + 1
              set s to s & "  ToolBar #" & (tbIdx as string) & "\n"
              set eIdx to 0
              try
                set elems to every UI element of tb
              on error
                set elems to every button of tb
              end try
              repeat with e in elems
                set eIdx to eIdx + 1
                set nm to "<no-name>"
                set desc to ""
                set roleName to ""
                try
                  set nm to name of e
                end try
                try
                  set desc to description of e
                end try
                try
                  set roleName to role of e
                end try
                set s to s & "    [" & (eIdx as string) & "] role=" & roleName & " name=" & nm & " desc=" & desc & "\n"
              end repeat
            end repeat
          end try
        end repeat
      end tell
    on error errMsg
      set s to s & "ERROR: " & errMsg & "\n"
    end try
  end tell
  do shell script "printf %s " & quoted form of s & " > " & quoted form of outPath
end run
APPSCRIPT

osascript "$SCPT_DUMP" "$TOOLBAR_DUMP" 2>/dev/null || true
if [ -f "$TOOLBAR_DUMP" ]; then
  echo "Toolbar UI dump: $TOOLBAR_DUMP"
  [ "$VERBOSE" -eq 1 ] && sed -n '1,200p' "$TOOLBAR_DUMP" || true
fi

# ---------------------------------------------------------------------------
# Click ESC and RAC toolbar buttons
# ---------------------------------------------------------------------------
SCPT_CLICK="/tmp/openjml-click-buttons-$$.scpt"
SCPT_FILES+=("$SCPT_CLICK")

cat > "$SCPT_CLICK" <<'APPCLICK'
on run argv
  set btn_names to {"ESC", "RAC"}
  tell application "System Events"
    repeat with i from 1 to count of btn_names
      set bname to item i of btn_names
      try
        tell application process "Eclipse"
          set frontmost to true
          delay 0.5
          -- Try by button name first
          try
            click button bname of tool bar 1 of window 1
          on error
            -- Fallback: scan all UI elements for name match
            repeat with e in every UI element of tool bar 1 of window 1
              try
                if (name of e) is bname then
                  click e
                  exit repeat
                end if
              end try
            end repeat
          end try
        end tell
      on error errMsg
        do shell script "echo 'Click error for " & bname & ": ' & quoted form of errMsg >> /tmp/openjml-apple-errors.log"
      end try
      delay 1
    end repeat
  end tell
end run
APPCLICK

echo "Clicking ESC and RAC toolbar buttons..."
osascript "$SCPT_CLICK" 2>/dev/null || echo "WARNING: button click script failed (Accessibility permission required)"

sleep 3

# ---------------------------------------------------------------------------
# Check workspace log
# ---------------------------------------------------------------------------
WSLOG="$TMP_WS/.metadata/.log"
echo ""
echo "--- Workspace log (OpenJML-related entries) ---"
if [ -f "$WSLOG" ]; then
  grep -i "openjml\|jmlspecs\|ESC\|RAC\|OpenJML" "$WSLOG" || echo "(no OpenJML matches)"
else
  echo "Workspace log not found at $WSLOG (Eclipse may not have written it yet)"
fi

echo ""
echo "GUI test finished. Temp app/workspace at: $TMP_BASE"
