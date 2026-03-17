#!/usr/bin/env bash
# gui-test.sh
# GUI-driven test for OpenJMLUI on macOS using an isolated Eclipse app copy and AppleScript UI scripting.
# It will copy a temporary Eclipse.app, install plugin from local update-site, launch Eclipse with a temp workspace,
# dump toolbar UI elements to help tuning AppleScript selectors, attempt clicks on named buttons, and check the workspace log.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd -P)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd -P)"

# Defaults
ECLIPSE_APP_SRC="/Users/davidcok/eclipse/eclipse-committers-2026-03-R-macosx-cocoa-x86_64-pure/Eclipse.app"
# Default update site: workspace root's openjml.github.io/eclipse-update-site
UPDATE_SITE_DIR_DEFAULT="$(cd "$SCRIPT_DIR/../../.." && pwd -P)/openjml.github.io/eclipse-update-site"
UPDATE_SITE_DIR="$UPDATE_SITE_DIR_DEFAULT"
TMP_BASE="/tmp/openjml-gui-test"
TMP_APP="$TMP_BASE/Eclipse.app"
TMP_WS="$TMP_BASE/workspace"
VERBOSE=0

usage() {
  cat <<EOF
Usage: $(basename "$0") [--eclipse-app PATH] [--site PATH] [--tmp DIR] [--verbose]

Example (use defaults):
  $(basename "$0")

Or explicitly override defaults:
  $(basename "$0") --eclipse-app "$ECLIPSE_APP_SRC" --site "$UPDATE_SITE_DIR"

Note: grant Accessibility permission to Terminal (System Settings → Privacy & Security → Accessibility).
EOF
}

# parse args
while [ $# -gt 0 ]; do
  case "$1" in
    --eclipse-app) ECLIPSE_APP_SRC="$2"; shift 2;;
    --site) UPDATE_SITE_DIR="$2"; shift 2;;
    --tmp) TMP_BASE="$2"; TMP_APP="$TMP_BASE/Eclipse.app"; TMP_WS="$TMP_BASE/workspace"; shift 2;;
    -v|--verbose) VERBOSE=1; shift;;
    -h|--help) usage; exit 0;;
    *) echo "Unknown arg: $1"; usage; exit 1;;
  esac
done

log() { [ "$VERBOSE" -eq 1 ] && echo "+ $*"; }
err() { echo "ERROR: $*" >&2; }

if [ ! -d "$ECLIPSE_APP_SRC" ]; then
  err "Eclipse app not found at: $ECLIPSE_APP_SRC"
  exit 2
fi

if [ ! -d "$UPDATE_SITE_DIR" ]; then
  echo "WARNING: update site not found at: $UPDATE_SITE_DIR" >&2
fi

# prepare temp dirs: remove existing and recreate
if [ -d "$TMP_BASE" ]; then
  log "Removing existing temp base: $TMP_BASE"
  rm -rf "$TMP_BASE"
fi
mkdir -p "$TMP_BASE" "$TMP_WS"

# copy Eclipse app bundle
echo "Copying Eclipse app to temp location (this may take a minute)..."
rsync -a --exclude=configuration/org.eclipse.osgi -E "$ECLIPSE_APP_SRC/" "$TMP_APP/" >/dev/null 2>&1 || cp -a "$ECLIPSE_APP_SRC" "$TMP_APP"

# find equinox launcher jar inside temp app (prefer non-source)
LAUNCHER_JAR="$(ls "$TMP_APP/Contents/Eclipse/plugins/org.eclipse.equinox.launcher"*.jar 2>/dev/null | grep -v "source" | grep -v "-src" | head -n1 || true)"
if [ -z "$LAUNCHER_JAR" ]; then
  LAUNCHER_JAR="$(ls "$TMP_APP/Contents/Eclipse/plugins/org.eclipse.equinox.launcher"*.jar 2>/dev/null | head -n1 || true)"
fi
if [ -z "$LAUNCHER_JAR" ]; then
  err "Could not find equinox launcher jar inside copied Eclipse app"
  exit 3
fi
log "Using equinox launcher: $LAUNCHER_JAR"

# detect IU from features
IU=""
if [ -d "$UPDATE_SITE_DIR/features" ]; then
  for f in "$UPDATE_SITE_DIR/features"/*; do
    [ -e "$f" ] || continue
    if [ -f "$f/feature.xml" ]; then
      id=$(tr '\n' ' ' < "$f/feature.xml" | sed -n 's/.*<feature[^>]*id="\([^"]*\)".*/\1/p' || true)
      if [ -n "$id" ]; then
        IU="${id}.feature.group"
        break
      fi
    fi
  done
fi

JAVA_CMD="$(command -v java || true)"
if [ -z "$JAVA_CMD" ]; then err "java not found"; exit 4; fi

if [ -n "$IU" ]; then
  echo "Installing IU $IU into temporary Eclipse..."
  "$JAVA_CMD" -Dfile.encoding=UTF-8 -jar "$LAUNCHER_JAR" -nosplash -application org.eclipse.equinox.p2.director \
    -repository "file:$(cd "$UPDATE_SITE_DIR" && pwd -P)" -installIU "$IU" -destination "$TMP_APP/Contents/Eclipse" -profile SDKProfile -consolelog || true
else
  echo "No feature IU detected; attempting to install plugin jars individually"
  for pj in "$UPDATE_SITE_DIR/plugins"/*.jar; do
    [ -f "$pj" ] || continue
    echo "Installing bundle $pj"
    "$JAVA_CMD" -Dfile.encoding=UTF-8 -jar "$LAUNCHER_JAR" -nosplash -application org.eclipse.equinox.p2.director \
      -metadataRepository "file:$(cd "$UPDATE_SITE_DIR" && pwd -P)" -artifactRepository "file:$(cd "$UPDATE_SITE_DIR" && pwd -P)" \
      -installIU "$(basename "$pj")" -destination "$TMP_APP/Contents/Eclipse" -profile SDKProfile -consolelog || true
  done
fi

# Launch copied Eclipse with temp workspace
echo "Launching temporary Eclipse (workspace: $TMP_WS)"
open "$TMP_APP" --args -data "$TMP_WS" &
ECLIPSE_PID=$!
echo "Eclipse launched (pid $ECLIPSE_PID). Waiting for UI to appear..."

sleep 8

# Dump toolbar UI element names/attributes to file to aid selector tuning
TOOLBAR_DUMP="/tmp/openjml-toolbar-elements-$$.txt"
cat > /tmp/openjml-dump-toolbar.scpt <<'APPSCRIPT'
-- AppleScript: dump toolbar UI elements for Eclipse into a readable format
on run argv
  set outPath to item 1 of argv
  set s to ""
  tell application "System Events"
    try
      tell application process "Eclipse"
        set frontmost to true
        delay 0.5
        repeat with w in windows
          set s to s & "Window index: " & (index of w as string) & "\n"
          try
            set tbs to tool bars of w
            set tbIndex to 0
            repeat with tb in tbs
              set tbIndex to tbIndex + 1
              set s to s & "  ToolBar #" & (tbIndex as string) & "\n"
              try
                set elems to every UI element of tb
              on error
                set elems to every button of tb
              end try
              set idx to 0
              repeat with e in elems
                set idx to idx + 1
                try
                  set nm to name of e
                on error
                  set nm to "<no-name>"
                end try
                try
                  set desc to description of e
                on error
                  set desc to ""
                end try
                try
                  set roleName to role of e
                on error
                  set roleName to ""
                end try
                set s to s & "    [" & (idx as string) & "] role=" & roleName & " name=" & (nm as string) & " desc=" & (desc as string) & "\n"
              end repeat
            end repeat
          end try
        end repeat
      end tell
    on error errMsg
      set s to s & "ERROR enumerating toolbar elements: " & (errMsg as string) & "\n"
    end try
  end tell
  do shell script "mkdir -p /tmp && printf %s " & quoted form of s & " > " & quoted form of outPath
end run
APPSCRIPT

osascript /tmp/openjml-dump-toolbar.scpt "$TOOLBAR_DUMP" || true
if [ -f "$TOOLBAR_DUMP" ]; then
  echo "Toolbar UI dump written to: $TOOLBAR_DUMP"
  sed -n '1,200p' "$TOOLBAR_DUMP" || true
else
  echo "Toolbar dump not created; AppleScript may have failed or Accessibility not granted." >&2
fi

# AppleScript to press the ESC and RAC buttons and an icon-only button
APPLE_SCRIPT="/tmp/openjml-cli-apple-$$_press.scpt"
cat > "$APPLE_SCRIPT" <<'APPCLICK'
-- AppleScript to click toolbar buttons in Eclipse
on run argv
  set btn_names to {"ESC", "RAC"}
  tell application "System Events"
    repeat with i from 1 to count of btn_names
      set bname to item i of btn_names
      try
        tell application process "Eclipse"
          set frontmost to true
          delay 0.5
          try
            click button bname of tool bar 1 of window 1
          on error
            repeat with tb in every UI element of tool bar 1 of window 1
              try
                if (name of tb) is bname then click tb
              end try
            end repeat
          end try
        end tell
      on error errMsg
        do shell script "echo 'AppleScript error: ' & quoted form of errMsg >> /tmp/openjml-apple-errors.log"
      end try
      delay 1
    end repeat
    try
      tell application process "Eclipse"
        repeat with tb in every button of tool bar 1 of window 1
          try
            if (name of tb) is missing value then click tb
            exit repeat
          end try
        end repeat
      end tell
    end try
  end tell
end run
APPCLICK

osascript "$APPLE_SCRIPT"

sleep 3

WSLOG="$TMP_WS/.metadata/.log"
if [ -f "$WSLOG" ]; then
  echo "Workspace log entries containing 'OpenJML' or expected markers:"
  grep -i "openjml\|ESC\|RAC\|Open JML\|OpenJML" "$WSLOG" || echo "(no matches)"
else
  echo "Workspace log not found at $WSLOG"
fi

echo "GUI test finished. Temp app/workspace at: $TMP_BASE"
exit 0
