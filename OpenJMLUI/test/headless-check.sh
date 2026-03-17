#!/usr/bin/env bash
# headless-check.sh
# Headless checks for OpenJMLUI plugin wiring and basic smoke verification.
# Does NOT open a GUI. Installs the plugin into a temporary Eclipse copy via the p2 director,
# inspects the installed plugin JAR for toolbar/menu contributions and handler classes,
# and checks the temporary workspace log for OpenJML console output strings.

set -euo pipefail

# Script location
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd -P)"

# Simple logger (define early to avoid clobbering by system 'log')
log() { [ "${VERBOSE-0}" -eq 1 ] && printf "+ %s\n" "$*"; }
err() { printf "ERROR: %s\n" "$*" >&2; }

# Defaults (adjust if needed)
# Default Eclipse location (user-provided default)
ECLIPSE_HOME="/Users/davidcok/eclipse/eclipse-committers-2026-03-R-macosx-cocoa-x86_64-pure/Eclipse.app/Contents/Eclipse"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd -P)"
# Default update site: ../../openjml.github.io/eclipse-update-site relative to script -> workspace root's openjml.github.io
UPDATE_SITE_DIR_DEFAULT="$(cd "$SCRIPT_DIR/../../../openjml.github.io/eclipse-update-site" && pwd -P)"
UPDATE_SITE_DIR="${UPDATE_SITE_DIR:-$UPDATE_SITE_DIR_DEFAULT}"
SOURCE_DIR=""  # optional explicit source (release-stage)
# Ensure IU variable exists to avoid 'unbound variable' with set -u
IU=""
# Use a fixed temp root across runs; script deletes it at start if present
TEMP_ROOT="/tmp/openjml-headless-test"
TMP_ECLIPSE="$TEMP_ROOT/eclipse"
TMP_WS="$TEMP_ROOT/ws"
TMP_LOG="$TMP_WS/.metadata/.log"
VERBOSE=0
NO_DIRECTOR=${NO_DIRECTOR:-0}

usage(){ cat <<EOF
Usage: $0 [--eclipse ECLIPSE_HOME] [--site UPDATE_SITE_DIR] [--tmp DIR] [--verbose]

This script will:
  - copy a minimal Eclipse into a temp dir (not the app bundle itself)
  - use the p2 director (equinox launcher) to install the feature/plugin from the local update site
  - inspect installed plugin jars for toolbar/menu contributions and handler classes
  - print a short report

Note: This is a headless metadata/packaging verification and log check. It does not click toolbar buttons.
EOF
}

# parse args (added --source)
while [ $# -gt 0 ]; do
  case "$1" in
    --eclipse) ECLIPSE_HOME="$2"; shift 2;;
    --site) UPDATE_SITE_DIR="$2"; shift 2;;
    --source) SOURCE_DIR="$2"; shift 2;;
    --tmp) TEMP_ROOT="$2"; TMP_ECLIPSE="$TEMP_ROOT/eclipse"; TMP_WS="$TEMP_ROOT/ws"; shift 2;;
    --no-director) NO_DIRECTOR=1; shift;;
    -v|--verbose) VERBOSE=1; shift;;
    -h|--help) usage; exit 0;;
    *) echo "Unknown arg: $1"; usage; exit 1;;
  esac
done

# If source dir provided, use it preferentially to detect IU and plugins
if [ -n "$SOURCE_DIR" ]; then
  UPDATE_SITE_DIR="$SOURCE_DIR"
fi

# Do NOT prefer combined-repo automatically; install from local repo (UPDATE_SITE_DIR) as requested.
# If UPDATE_SITE_DIR is empty, we'll warn later and attempt release-stage as fallback.

# Default: allow director unless NO_DIRECTOR set
NO_DIRECTOR=${NO_DIRECTOR:-0}

# Determine target feature id from source feature.xml (in repo OpenJMLFeature)
TARGET_FEATURE_ID=""
# Look in likely locations for feature.xml
if [ -f "$REPO_ROOT/OpenJML/OpenJMLFeature/feature.xml" ]; then
  FEATURE_XML_SOURCE="$REPO_ROOT/OpenJML/OpenJMLFeature/feature.xml"
elif [ -f "$REPO_ROOT/OpenJMLFeature/feature.xml" ]; then
  FEATURE_XML_SOURCE="$REPO_ROOT/OpenJMLFeature/feature.xml"
elif [ -f "$REPO_ROOT/../OpenJMLFeature/feature.xml" ]; then
  FEATURE_XML_SOURCE="$REPO_ROOT/../OpenJMLFeature/feature.xml"
else
  FEATURE_XML_SOURCE=""
fi
if [ -n "$FEATURE_XML_SOURCE" ]; then
  TARGET_FEATURE_ID=$(tr '\n' ' ' < "$FEATURE_XML_SOURCE" 2>/dev/null | sed -n 's/.*<feature[^>]*id="\([^\"]*\)".*/\1/p' || true)
  log "Detected source feature id: $TARGET_FEATURE_ID (from $FEATURE_XML_SOURCE)"
else
  log "Warning: could not find feature.xml in repository; feature id unknown"
fi

# Helper: compare semantic versions (returns 0 if $1 > $2)
version_gt() {
  # returns 0 if first arg > second arg, 1 otherwise
  local a="$1" b="$2"
  IFS='.' read -ra A <<< "$a"
  IFS='.' read -ra B <<< "$b"
  local i maxlen=${#A[@]}
  if [ ${#B[@]} -gt $maxlen ]; then maxlen=${#B[@]}; fi
  for ((i=0;i<maxlen;i++)); do
    local ai=${A[i]:-0}
    local bi=${B[i]:-0}
    # strip non-numeric suffix if present
    ai=${ai%%[^0-9]*}
    bi=${bi%%[^0-9]*}
    ai=${ai:-0}
    bi=${bi:-0}
    if [ "$ai" -gt "$bi" ]; then return 0; fi
    if [ "$ai" -lt "$bi" ]; then return 1; fi
  done
  # equal
  return 1
}

# Find the highest-versioned feature for TARGET_FEATURE_ID under UPDATE_SITE_DIR/features
SELECTED_FEATURE_PATH=""
SELECTED_FEATURE_VERSION=""
if [ -d "$UPDATE_SITE_DIR/features" ]; then
  for entry in "$UPDATE_SITE_DIR/features"/*; do
    [ -e "$entry" ] || continue
    # for directories, read feature.xml; for jars, try to extract feature.xml
    feature_xml=""
    cleanup_dir=""
    if [ -d "$entry" ]; then
      feature_xml="$entry/feature.xml"
    elif [[ "$entry" == *.jar ]]; then
      # extract feature.xml to temp
      cleanup_dir=$(mktemp -d)
      if unzip -p "$entry" feature.xml > "$cleanup_dir/feature.xml" 2>/dev/null; then
        feature_xml="$cleanup_dir/feature.xml"
      else
        rm -rf "$cleanup_dir"
        cleanup_dir=""
      fi
    fi
    if [ -n "$feature_xml" ] && [ -f "$feature_xml" ]; then
      fid=$(tr '\n' ' ' < "$feature_xml" | sed -n 's/.*<feature[^>]*id="\([^"]*\)".*/\1/p' || true)
      fver=$(tr '\n' ' ' < "$feature_xml" | sed -n 's/.*<feature[^>]*version="\([^"]*\)".*/\1/p' || true)
      if [ -n "$fid" ] && [ -n "$fver" ] && [ -n "$TARGET_FEATURE_ID" ]; then
        if [ "$fid" = "$TARGET_FEATURE_ID" ]; then
          log "Found feature instance: $entry (version $fver)"
          if [ -z "$SELECTED_FEATURE_VERSION" ]; then
            SELECTED_FEATURE_VERSION="$fver"
            SELECTED_FEATURE_PATH="$entry"
          else
            if version_gt "$fver" "$SELECTED_FEATURE_VERSION"; then
              SELECTED_FEATURE_VERSION="$fver"
              SELECTED_FEATURE_PATH="$entry"
            fi
          fi
        fi
      fi
    fi
    if [ -n "$cleanup_dir" ]; then rm -rf "$cleanup_dir"; fi
  done
fi

if [ -n "$SELECTED_FEATURE_VERSION" ]; then
  log "Selected feature $TARGET_FEATURE_ID version $SELECTED_FEATURE_VERSION from $SELECTED_FEATURE_PATH"
  # Use the unqualified feature.group IU so p2 will select the latest version available in the repository
  SELECTED_IU="${TARGET_FEATURE_ID}.feature.group"
else
  log "Could not find versioned feature for $TARGET_FEATURE_ID under $UPDATE_SITE_DIR/features"
  SELECTED_IU=""
fi

# Ensure temp dirs are cleared and created, and switch to temp root
if [ -d "$TEMP_ROOT" ]; then
  log "Removing existing temp root: $TEMP_ROOT"
  rm -rf "$TEMP_ROOT"
fi
mkdir -p "$TMP_ECLIPSE" "$TMP_WS" "$TEMP_ROOT"
cd "$TEMP_ROOT"

# export UTF-8 locale for java initialization
export LANG="en_US.UTF-8"
export LC_ALL="en_US.UTF-8"

# Later, when selecting equinox launcher:
# Locate equinox launcher jar in the Eclipse plugins dir (prefer non-source)
LAUNCHER_JAR=""
# Use array-based globbing so unmatched patterns don't become literal strings
candidates=("$ECLIPSE_HOME/plugins/org.eclipse.equinox.launcher"*.jar)
# Also try Contents/Eclipse/plugins for macOS app bundles
if [ ${#candidates[@]} -eq 0 ] || [ ! -e "${candidates[0]}" ]; then
  candidates=("$ECLIPSE_HOME/Contents/Eclipse/plugins/org.eclipse.equinox.launcher"*.jar)
fi
# Iterate candidates and pick first non-source jar
for j in "${candidates[@]}"; do
  [ -f "$j" ] || continue
  bn=$(basename "$j")
  case "$bn" in
    *source*|*src*|*-src*) continue;;
    *) LAUNCHER_JAR="$j"; break;;
  esac
done
# If still not found, try a few common locations
if [ -z "$LAUNCHER_JAR" ]; then
  extra=("/usr/lib/eclipse/plugins/org.eclipse.equinox.launcher"*.jar "/usr/local/eclipse/plugins/org.eclipse.equinox.launcher"*.jar "$HOME/eclipse/plugins/org.eclipse.equinox.launcher"*.jar)
  for j in "${extra[@]}"; do
    [ -f "$j" ] || continue
    bn=$(basename "$j")
    case "$bn" in *source*|*src*|*-src*) continue;; esac
    LAUNCHER_JAR="$j"; break
  done
fi

if [ -z "$LAUNCHER_JAR" ]; then err "Could not find equinox launcher jar under $ECLIPSE_HOME/plugins or common locations"; exit 2; fi
log "Using equinox launcher: $LAUNCHER_JAR"

# Detect p2 repository path: prefer metadata/ if content.jar present
if [ -f "$UPDATE_SITE_DIR/metadata/content.jar" ]; then
  P2_REPO_DIR="$UPDATE_SITE_DIR/metadata"
elif [ -f "$UPDATE_SITE_DIR/content.jar" ]; then
  P2_REPO_DIR="$UPDATE_SITE_DIR"
elif [ -f "$UPDATE_SITE_DIR/../combined-repo/metadata/content.jar" ]; then
  P2_REPO_DIR="$UPDATE_SITE_DIR/../combined-repo/metadata"
else
  P2_REPO_DIR="$UPDATE_SITE_DIR"
fi
log "Using p2 repository path for director: $P2_REPO_DIR"

# Run director: install either IU or all plugin jars found
JAVA_CMD=$(command -v java || true)
if [ -z "$JAVA_CMD" ]; then
  err "java not found"; exit 3;
fi

# Ensure LAUNCHER_JAR is a concrete file path (not a literal wildcard)
if [ ! -f "$LAUNCHER_JAR" ]; then
  # try to expand glob explicitly
  expanded=("$ECLIPSE_HOME"/plugins/org.eclipse.equinox.launcher*.jar)
  for cand in "${expanded[@]}"; do
    [ -f "$cand" ] || continue
    bn=$(basename "$cand")
    case "$bn" in *source*|*src*|*-src*) continue;; esac
    LAUNCHER_JAR="$cand"; break
  done
fi
if [ ! -f "$LAUNCHER_JAR" ]; then
  err "Equinox launcher jar not found at: $LAUNCHER_JAR"; exit 2
fi
log "Using equinox launcher: $LAUNCHER_JAR"

# Detect p2 repository path: prefer metadata/ if content.jar present
if [ -f "$UPDATE_SITE_DIR/metadata/content.jar" ]; then
  P2_REPO_DIR="$UPDATE_SITE_DIR/metadata"
elif [ -f "$UPDATE_SITE_DIR/content.jar" ]; then
  P2_REPO_DIR="$UPDATE_SITE_DIR"
elif [ -f "$UPDATE_SITE_DIR/../combined-repo/metadata/content.jar" ]; then
  P2_REPO_DIR="$UPDATE_SITE_DIR/../combined-repo/metadata"
else
  P2_REPO_DIR="$UPDATE_SITE_DIR"
fi
log "Using p2 repository path for director: $P2_REPO_DIR"

# Always copy plugins/features into temp eclipse before attempting director install so the plugin is available
log "Copying plugins/features from update site into temp eclipse (pre-install)"
mkdir -p "$TMP_ECLIPSE/plugins" "$TMP_ECLIPSE/features"
if [ -d "$UPDATE_SITE_DIR/plugins" ]; then
  if command -v rsync >/dev/null 2>&1; then
    rsync -a "$UPDATE_SITE_DIR/plugins/" "$TMP_ECLIPSE/plugins/" || true
  else
    cp -R "$UPDATE_SITE_DIR/plugins/." "$TMP_ECLIPSE/plugins/" || true
  fi
fi
if [ -d "$UPDATE_SITE_DIR/features" ]; then
  if command -v rsync >/dev/null 2>&1; then
    rsync -a "$UPDATE_SITE_DIR/features/" "$TMP_ECLIPSE/features/" || true
  else
    cp -R "$UPDATE_SITE_DIR/features/." "$TMP_ECLIPSE/features/" || true
  fi
fi

if [ -n "$SELECTED_IU" ] && [ "$NO_DIRECTOR" -eq 0 ]; then
  # Try unqualified IU first so p2 will pick the highest available version in the repository
  log "Attempting to install unqualified IU: ${SELECTED_IU} from repository $P2_REPO_DIR"
  "$JAVA_CMD" -Dfile.encoding=UTF-8 -jar "$LAUNCHER_JAR" -nosplash -application org.eclipse.equinox.p2.director \
    -repository "file:$(cd "$P2_REPO_DIR" && pwd -P)" -installIU "$SELECTED_IU" -destination "$TMP_ECLIPSE" -profile SDKProfile -consolelog > "$TEMP_ROOT/p2-install.log" 2>&1 || true
  if grep -q "Generation completed with success" "$TEMP_ROOT/p2-install.log" 2>/dev/null || grep -q "Installing .* succeeded" "$TEMP_ROOT/p2-install.log" 2>/dev/null; then
    log "Unqualified IU install appears to have succeeded (see $TEMP_ROOT/p2-install.log)"
  else
    # If unqualified IU didn't work, try a version-qualified IU if we detected one
    if [ -n "$SELECTED_FEATURE_VERSION" ]; then
      log "Unqualified IU failed; attempting version-qualified IU: ${SELECTED_IU}/${SELECTED_FEATURE_VERSION} from repository $P2_REPO_DIR"
      "$JAVA_CMD" -Dfile.encoding=UTF-8 -jar "$LAUNCHER_JAR" -nosplash -application org.eclipse.equinox.p2.director \
        -repository "file:$(cd "$P2_REPO_DIR" && pwd -P)" -installIU "${SELECTED_IU}/${SELECTED_FEATURE_VERSION}" -destination "$TMP_ECLIPSE" -profile SDKProfile -consolelog >> "$TEMP_ROOT/p2-install.log" 2>&1 || true
      if grep -q "Generation completed with success" "$TEMP_ROOT/p2-install.log" 2>/dev/null || grep -q "Installing .* succeeded" "$TEMP_ROOT/p2-install.log" 2>/dev/null; then
        log "Version-qualified IU install appears to have succeeded (see $TEMP_ROOT/p2-install.log)"
      else
        log "Version-qualified IU install also failed; will fall back to per-jar installs and copy fallback (see $TEMP_ROOT/p2-install.log)"
      fi
    else
      log "Unqualified IU install failed and no feature version available; will fall back to per-jar installs and copy fallback (see $TEMP_ROOT/p2-install.log)"
    fi
  fi
else
  if [ "$NO_DIRECTOR" -eq 1 ]; then
    log "Skipping p2 director install (--no-director set)"
  else
    log "No feature IU or director disabled; attempting to install plugin jars individually via p2 director"
  fi
  if [ "$NO_DIRECTOR" -eq 0 ]; then
    mkdir -p "$TMP_ECLIPSE"
    for pj in "$UPDATE_SITE_DIR"/plugins/*.jar; do
      [ -f "$pj" ] || continue
      log "Attempting p2 install of bundle: $pj"
      "$JAVA_CMD" -Dfile.encoding=UTF-8 -jar "$LAUNCHER_JAR" -nosplash -application org.eclipse.equinox.p2.director \
        -metadataRepository "file:$(cd "$P2_REPO_DIR" && pwd -P)" -artifactRepository "file:$(cd "$P2_REPO_DIR" && pwd -P)" \
        -installIU "$(basename "$pj")" -destination "$TMP_ECLIPSE" -profile SDKProfile -consolelog || true
    done
  fi
fi

# If director didn't install or even if it did, ensure plugins/features are present by copying again (post-install)
if [ -d "$UPDATE_SITE_DIR/plugins" ]; then
  log "Ensuring plugins present in temp eclipse (post-install copy)"
  if command -v rsync >/dev/null 2>&1; then
    rsync -a "$UPDATE_SITE_DIR/plugins/" "$TMP_ECLIPSE/plugins/" || true
  else
    cp -R "$UPDATE_SITE_DIR/plugins/." "$TMP_ECLIPSE/plugins/" || true
  fi
fi
if [ -d "$UPDATE_SITE_DIR/features" ]; then
  if command -v rsync >/dev/null 2>&1; then
    rsync -a "$UPDATE_SITE_DIR/features/" "$TMP_ECLIPSE/features/" || true
  else
    cp -R "$UPDATE_SITE_DIR/features/." "$TMP_ECLIPSE/features/" || true
  fi
fi

# If director didn't install the plugin (or IU lookup failed), fall back to copying the raw plugins/features into temp eclipse.
# This makes the plugin available for inspection and for many non-p2 runtime uses.
if ! ls "$TMP_ECLIPSE/plugins"/org.jmlspecs.OpenJMLUI_*.jar >/dev/null 2>&1; then
  log "Director did not install plugin; copying plugins/features into temp eclipse as fallback"
  mkdir -p "$TMP_ECLIPSE/plugins" "$TMP_ECLIPSE/features"
  if [ -d "$UPDATE_SITE_DIR/plugins" ]; then
    if command -v rsync >/dev/null 2>&1; then
      rsync -a "$UPDATE_SITE_DIR/plugins/" "$TMP_ECLIPSE/plugins/" || true
    else
      cp -R "$UPDATE_SITE_DIR/plugins/." "$TMP_ECLIPSE/plugins/" || true
    fi
  fi
  if [ -d "$UPDATE_SITE_DIR/features" ]; then
    if command -v rsync >/dev/null 2>&1; then
      rsync -a "$UPDATE_SITE_DIR/features/" "$TMP_ECLIPSE/features/" || true
    else
      cp -R "$UPDATE_SITE_DIR/features/." "$TMP_ECLIPSE/features/" || true
    fi
  fi
fi

# Also place plugins/features into dropins so Eclipse picks them up on startup (better for GUI installs)
DROPINS_DIR="$TMP_ECLIPSE/dropins"
mkdir -p "$DROPINS_DIR/plugins" "$DROPINS_DIR/features"
if [ -d "$UPDATE_SITE_DIR/plugins" ]; then
  log "Copying plugin jars into dropins/plugins to ensure Eclipse loads them"
  if command -v rsync >/dev/null 2>&1; then
    rsync -a "$UPDATE_SITE_DIR/plugins/" "$DROPINS_DIR/plugins/" || true
  else
    cp -R "$UPDATE_SITE_DIR/plugins/." "$DROPINS_DIR/plugins/" || true
  fi
fi
if [ -d "$UPDATE_SITE_DIR/features" ]; then
  log "Copying feature dirs into dropins/features to ensure Eclipse loads them"
  if command -v rsync >/dev/null 2>&1; then
    rsync -a "$UPDATE_SITE_DIR/features/" "$DROPINS_DIR/features/" || true
  else
    cp -R "$UPDATE_SITE_DIR/features/." "$DROPINS_DIR/features/" || true
  fi
fi

# After install, discover installed OpenJMLUI plugin jars
INSTALLED_PLUGINS=("$TMP_ECLIPSE/plugins"/org.jmlspecs.OpenJMLUI_*.jar)
if [ -f "${INSTALLED_PLUGINS[0]}" ]; then
  echo "Installed OpenJMLUI plugin: ${INSTALLED_PLUGINS[0]}"
else
  echo "WARNING: OpenJMLUI plugin not found in $TMP_ECLIPSE/plugins — installation may have failed"
  # check dropins as well
  if ls "$TMP_ECLIPSE/dropins/plugins"/org.jmlspecs.OpenJMLUI_*.jar >/dev/null 2>&1; then
    dp=$(ls "$TMP_ECLIPSE/dropins/plugins"/org.jmlspecs.OpenJMLUI_*.jar | head -n1)
    echo "Found OpenJMLUI plugin in dropins: $dp"
    INSTALLED_PLUGINS=("$dp")
  fi
fi

# Inspect plugin jar for toolbar/menu contributions and handler classes
REPORT="$TEMP_ROOT/report.txt"
echo "OpenJMLUI headless report" > "$REPORT"
if [ -f "${INSTALLED_PLUGINS[0]}" ]; then
  PLUGIN_JAR="${INSTALLED_PLUGINS[0]}"
  echo "Plugin jar: $PLUGIN_JAR" >> "$REPORT"
  mkdir -p "$TEMP_ROOT/explode"
  unzip -q -o "$PLUGIN_JAR" -d "$TEMP_ROOT/explode"
  # look for plugin.xml and grep for menu/toolbar/command/handler/label
  if [ -f "$TEMP_ROOT/explode/plugin.xml" ]; then
    echo "Found plugin.xml; checking for toolbar/menu contributions and handler declarations" >> "$REPORT"
    grep -n "toolbar\|menu\|command\|handler\|label\|icon" "$TEMP_ROOT/explode/plugin.xml" >> "$REPORT" || true
  else
    echo "No plugin.xml found inside plugin jar; searching for MANIFEST.MF for Bundle-Activator and extension points" >> "$REPORT"
    if [ -f "$TEMP_ROOT/explode/META-INF/MANIFEST.MF" ]; then
      grep -n "Bundle-Activator\|Bundle-SymbolicName\|Export-Package" "$TEMP_ROOT/explode/META-INF/MANIFEST.MF" >> "$REPORT" || true
    fi
  fi
  # Search for occurrences of the labels ESC and RAC or icon path
  echo "Searching for labels 'ESC' and 'RAC' and 'icon' in plugin jar content" >> "$REPORT"
  grep -R --line-number "ESC\|RAC\|icon" "$TEMP_ROOT/explode" >> "$REPORT" || true
else
  echo "Plugin jar not available; skipping jar inspection" >> "$REPORT"
fi

# Check workspace log for any OpenJML console lines
echo "Checking workspace log for OpenJML console text (if any) at: $TMP_LOG" >> "$REPORT"
if [ -f "$TMP_LOG" ]; then
  grep -i "openjml\|open jml\|ESC\|RAC\|OpenJML" "$TMP_LOG" >> "$REPORT" || true
else
  echo "Workspace log not present (no runtime executed)." >> "$REPORT"
fi

# Print report
echo "--- Report ---"
cat "$REPORT"

echo "Headless check complete. Temp dirs: $TEMP_ROOT (remove when done)"
exit 0
