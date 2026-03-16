#!/usr/bin/env bash
# build-update-site.sh
# Purpose:
#   Assemble the OpenJML UI Eclipse plugin and feature into an update-site-style
#   layout suitable for publishing. This script packages the plugin classes and
#   bundled library JARs into a versioned plugin JAR and copies the feature
#   definition into a features/ directory under the release-stage output.
#
# Usage:
#   Run from the `OpenJML/OpenJMLUI` directory or anywhere; the script resolves
#   paths relative to its location. Example:
#     ./build-update-site.sh
#   Optional environment variables:
#     EXPECTED_BRANCH - when set, the script aborts unless the current git
#                       branch matches this value.
#     ECLIPSE_HOME     - path to an Eclipse installation (used when trying to
#                       run the p2 publisher headlessly; otherwise the script
#                       falls back to producing a simple plugins/features layout).
#
# Effects / outputs:
#   - Creates or updates: ../OpenJMLUpdateSite/release-stage/plugins/
#       org.jmlspecs.OpenJMLUI_${BUNDLE_VERSION}.jar
#   - Copies the feature XML into ../OpenJMLUpdateSite/release-stage/features/
#   - Attempts to run the p2 publisher headlessly (via Equinox launcher JAR)
#     to produce metadata (metadata/ and artifacts/ under release-stage).
#     If headless publishing is not possible the script falls back to a simple
#     features/plugins layout and creates minimal artifacts.jar/content.jar
#     placeholders.
#
# Non-interactive guarantee:
#   The script never launches the Eclipse GUI. When it runs the p2 publisher
#   it does so via `java -jar <equinox-launcher.jar>` (headless). If a GUI-capable
#   `eclipse` binary is present, it will not be used to avoid interactive prompts.
#
# Example quick run:
#   EXPECTED_BRANCH=dev-21 ./build-update-site.sh

# Builds the OpenJMLUI plugin artifact and assembles an Eclipse update site layout.
# Places results in ../OpenJMLUpdateSite/release-stage by default.
# Run from the OpenJMLUI directory or anywhere; script resolves project root.
set -euo pipefail

# Default configurations
ROOT_DIR="$(cd "$(dirname "$0")" && pwd -P)"
UI_DIR="$ROOT_DIR"
FEATURE_DIR="$ROOT_DIR/../OpenJMLFeature"
UPDATESITE_DIR="$ROOT_DIR/../OpenJMLUpdateSite/release-stage"
PLUGIN_ID="org.jmlspecs.OpenJMLUI"
MANIFEST="$UI_DIR/META-INF/MANIFEST.MF"
BIN_DIR="$UI_DIR/bin"
LIBS=("jmlruntime.jar" "jSMTLIB.jar" "jpaul-2.5.1.jar" "gson-2.8.1.jar")

# CLI: accept --version and --overwrite
VERSION_ARG=""
OVERWRITE=0
usage() {
    cat <<EOF
Usage: $(basename "$0") [--version VERSION] [--overwrite] [--help]

Options:
  --version VERSION    Set the Bundle/Feature version to VERSION before building.
                       When provided, the script will update source manifests
                       and the feature.xml to use this version before packaging.
  --overwrite          If an output plugin or feature with the same version
                       already exists in the release-stage, allow overwriting.
  --help               Show this help and exit.

Note: The script is non-interactive and will never launch the Eclipse GUI.
EOF
}

# parse simple CLI args
while [ $# -gt 0 ]; do
    case "$1" in
        --version) VERSION_ARG="$2"; shift 2;;
        --overwrite) OVERWRITE=1; shift;;
        --help|-h) usage; exit 0;;
        *) break;;
    esac
done

# Helper: read manifest value (needed by version-setting code)
get_manifest_value() {
    local key="$1"
    awk -v key="$key" 'BEGIN{FS=": ";IGNORECASE=0} $1==key{print substr($0,index($0,$2))}' "$MANIFEST" | tr -d '\r' || true
}

# --- Version helpers (moved earlier so --version takes effect before reading manifest) ---
# Function to update version strings in relevant files (manifests and feature.xml)
set_version_in_sources() {
    local newv="$1"
    echo "Setting source bundle/feature versions to: $newv"
    # Update OpenJMLUI manifest
    if [ -f "$UI_DIR/META-INF/MANIFEST.MF" ]; then
        awk -v v="$newv" 'BEGIN{FS=OFS=":"} /^Bundle-Version:/{print $1":"" " v; next} {print}' "$UI_DIR/META-INF/MANIFEST.MF" > "$UI_DIR/META-INF/MANIFEST.MF.tmp" && mv "$UI_DIR/META-INF/MANIFEST.MF.tmp" "$UI_DIR/META-INF/MANIFEST.MF"
    fi
    # Update OpenJMLTest manifest (if present)
    if [ -f "$ROOT_DIR/../OpenJMLTest/META-INF/MANIFEST.MF" ]; then
        awk -v v="$newv" 'BEGIN{FS=OFS=":"} /^Bundle-Version:/{print $1":"" " v; next} {print}' "$ROOT_DIR/../OpenJMLTest/META-INF/MANIFEST.MF" > "$ROOT_DIR/../OpenJMLTest/META-INF/MANIFEST.MF.tmp" && mv "$ROOT_DIR/../OpenJMLTest/META-INF/MANIFEST.MF.tmp" "$ROOT_DIR/../OpenJMLTest/META-INF/MANIFEST.MF"
    fi
    # Update Specs manifest (if present)
    if [ -f "$ROOT_DIR/../Specs/META-INF/MANIFEST.MF" ]; then
        awk -v v="$newv" 'BEGIN{FS=OFS=":"} /^Bundle-Version:/{print $1":"" " v; next} {print}' "$ROOT_DIR/../Specs/META-INF/MANIFEST.MF" > "$ROOT_DIR/../Specs/META-INF/MANIFEST.MF.tmp" && mv "$ROOT_DIR/../Specs/META-INF/MANIFEST.MF.tmp" "$ROOT_DIR/../Specs/META-INF/MANIFEST.MF"
    fi
    # Update feature.xml version and plugin entries
    if [ -f "$FEATURE_DIR/feature.xml" ]; then
        # Only replace version attributes on <feature ...> and <plugin ...> lines (avoid XML declaration)
        awk -v v="$newv" '
            /<feature[^>]*>/ { gsub(/version="[^"]*"/, "version=\"" v "\""); print; next }
            /<plugin[^>]*>/ { gsub(/version="[^"]*"/, "version=\"" v "\""); print; next }
            { print }
        ' "$FEATURE_DIR/feature.xml" > "$FEATURE_DIR/feature.xml.tmp" && mv "$FEATURE_DIR/feature.xml.tmp" "$FEATURE_DIR/feature.xml"
    fi
}

# Function to detect if the version already exists in release-stage
check_version_exists_in_release_stage() {
    local v="$1"
    # plugin jar
    local plugin_jar="$UPDATESITE_DIR/plugins/${PLUGIN_ID}_${v}.jar"
    if [ -f "$plugin_jar" ]; then
        echo "Found existing plugin jar: $plugin_jar"
        return 0
    fi
    # feature dir (attempt to extract feature id)
    if [ -f "$FEATURE_DIR/feature.xml" ]; then
        local fid
        fid=$(tr '\n' ' ' < "$FEATURE_DIR/feature.xml" 2>/dev/null | sed -n 's/.*<feature[^>]*id=\"\([^\"]*\)\".*/\1/p' || true)
        if [ -n "$fid" ] && [ -d "$UPDATESITE_DIR/features/${fid}_${v}" ]; then
            echo "Found existing feature dir: $UPDATESITE_DIR/features/${fid}_${v}"
            return 0
        fi
    fi
    return 1
}

# If a version was provided, update sources now and check for conflicts
if [ -n "$VERSION_ARG" ]; then
    set_version_in_sources "$VERSION_ARG"
    # refresh BUNDLE_VERSION from updated manifest
    BUNDLE_VERSION=$(get_manifest_value "Bundle-Version")
    if [ -z "$BUNDLE_VERSION" ]; then
        echo "ERROR: version update failed; manifest has no Bundle-Version" >&2
        exit 1
    fi
    # Check if release-stage already has this version
    if check_version_exists_in_release_stage "$BUNDLE_VERSION"; then
        if [ "$OVERWRITE" -eq 1 ]; then
            echo "--overwrite specified: removing existing artifacts for version $BUNDLE_VERSION"
            rm -f "$UPDATESITE_DIR/plugins/${PLUGIN_ID}_${BUNDLE_VERSION}.jar" || true
            # remove versioned feature dir if present
            fid=$(tr '\n' ' ' < "$FEATURE_DIR/feature.xml" 2>/dev/null | sed -n 's/.*<feature[^>]*id=\\"\\([^\\\"]*\\)\\".*/\\1/p' || true)
            if [ -n "$fid" ]; then
                rm -rf "$UPDATESITE_DIR/features/${fid}_${BUNDLE_VERSION}" || true
            fi
        else
            echo "ERROR: version $BUNDLE_VERSION already exists in release-stage; use --overwrite to replace it." >&2
            exit 1
        fi
    fi
fi

# Helper: absolute path for files and dirs (portable)
abspath() {
    # $1 may be a file or dir
    if [ -z "${1-}" ]; then
        return 1
    fi
    if [ -d "$1" ]; then
        (cd "$1" 2>/dev/null && pwd -P) || printf "%s" "$1"
        return 0
    fi
    local dir
    dir=$(cd "$(dirname "$1")" 2>/dev/null && pwd -P || printf "%s" "$(dirname "$1")")
    printf "%s/%s" "$dir" "$(basename "$1")"
}

# Git detection: find repo root and branch if present
GIT_ROOT=""
GIT_BRANCH=""
if command -v git >/dev/null 2>&1; then
    if GIT_ROOT_RAW=$(git -C "$ROOT_DIR" rev-parse --show-toplevel 2>/dev/null || true); then
        GIT_ROOT="$GIT_ROOT_RAW"
        # attempt to get current branch
        GIT_BRANCH=$(git -C "$ROOT_DIR" symbolic-ref --short HEAD 2>/dev/null || git -C "$ROOT_DIR" branch --show-current 2>/dev/null || true)
    fi
fi

if [ -n "${GIT_BRANCH}" ]; then
    echo "Git repository detected at: $GIT_ROOT"
    echo "Current branch: $GIT_BRANCH"
else
    echo "Note: no git branch detected for $ROOT_DIR (not a git working copy or git unavailable)"
fi

# If EXPECTED_BRANCH is set, ensure we are on that branch
if [ -n "${EXPECTED_BRANCH-}" ]; then
    if [ -z "$GIT_BRANCH" ]; then
        echo "ERROR: EXPECTED_BRANCH is set to '$EXPECTED_BRANCH' but this directory is not a git repo or branch could not be determined. Aborting." >&2
        exit 1
    fi
    if [ "$GIT_BRANCH" != "$EXPECTED_BRANCH" ]; then
        echo "ERROR: EXPECTED_BRANCH is set to '$EXPECTED_BRANCH' but current branch is '$GIT_BRANCH'. Aborting." >&2
        exit 1
    fi
fi

# Audit materials used by the script
MISSING_ITEMS=()
[ -f "$MANIFEST" ] || MISSING_ITEMS+=("$MANIFEST")
[ -f "$FEATURE_DIR/feature.xml" ] || MISSING_ITEMS+=("$FEATURE_DIR/feature.xml")
[ -d "$BIN_DIR" ] || echo "Warning: bin dir not found at $BIN_DIR (this may be fine if classes are packaged elsewhere)"
for lib in "${LIBS[@]}"; do
    if [ ! -f "$UI_DIR/$lib" ]; then
        echo "Warning: expected library $lib not found in $UI_DIR"
    fi
done

if [ ${#MISSING_ITEMS[@]} -ne 0 ]; then
    echo "ERROR: missing required files:" >&2
    for it in "${MISSING_ITEMS[@]}"; do echo "  - $it" >&2; done
    echo "Please ensure you are on the correct branch or that the files exist. Aborting." >&2
    exit 1
fi

if [ ! -f "$MANIFEST" ]; then
    echo "ERROR: Manifest not found at $MANIFEST"
    exit 1
fi

BUNDLE_VERSION=$(get_manifest_value "Bundle-Version")
if [ -z "$BUNDLE_VERSION" ]; then
    echo "ERROR: Could not read Bundle-Version from $MANIFEST"
    exit 1
fi

# Prepare output layout
PLUGINS_OUT="$UPDATESITE_DIR/plugins"
FEATURES_OUT="$UPDATESITE_DIR/features"
mkdir -p "$PLUGINS_OUT" "$FEATURES_OUT"

echo "Using plugin id: $PLUGIN_ID"
echo "Using bundle version: $BUNDLE_VERSION"
echo "Output update site directory: $UPDATESITE_DIR"

# Build plugin jar: package bin/ classes and include required library jars on Bundle-ClassPath
# We will create a jar named ${PLUGIN_ID}_${BUNDLE_VERSION}.jar
OUT_JAR="$PLUGINS_OUT/${PLUGIN_ID}_${BUNDLE_VERSION}.jar"

echo "Creating plugin jar: $OUT_JAR"

# Create a temporary staging directory
STAGE_DIR=$(mktemp -d)
trap 'rm -rf "$STAGE_DIR"' EXIT

# Copy classes
if [ -d "$BIN_DIR" ]; then
    cp -a "$BIN_DIR/" "$STAGE_DIR/"
else
    echo "Warning: bin directory $BIN_DIR not found; continuing with empty classes directory"
fi

# Copy libraries next to jar (they are referenced in Bundle-ClassPath).
# If not found locally, search common alternate locations inside the workspace.
ALT_LIB_DIRS=("$ROOT_DIR/../OpenJMLsrc" "$ROOT_DIR/../../openjml.github.io/tutorial" "$ROOT_DIR/../openjml.github.io/tutorial")
for lib in "${LIBS[@]}"; do
    if [ -f "$UI_DIR/$lib" ]; then
        cp "$UI_DIR/$lib" "$STAGE_DIR/"
    else
        # search alternate dirs
        FOUND=0
        for d in "${ALT_LIB_DIRS[@]}"; do
            if [ -f "$d/$lib" ]; then
                echo "Found $lib in $d; including it"
                cp "$d/$lib" "$STAGE_DIR/"
                FOUND=1
                break
            fi
        done
        if [ "$FOUND" -eq 0 ]; then
            echo "Warning: library $lib not found in $UI_DIR or alternate locations; it won't be included in the plugin jar"
        fi
    fi
done

# Create the jar
pushd "$STAGE_DIR" >/dev/null
# ensure META-INF/MANIFEST.MF from UI_DIR is used (preserve bundle metadata)
mkdir -p META-INF
if [ -f "$MANIFEST" ]; then
    cp "$MANIFEST" META-INF/MANIFEST.MF
fi
jar cf "$OUT_JAR" .
popd >/dev/null

# Copy the feature directory (feature.xml and related) into features output; keep versioned name
# Use a robust parsing method that joins lines so attributes split across lines are found
FEATURE_CONTENT=$(tr '\n' ' ' < "$FEATURE_DIR/feature.xml" 2>/dev/null || true)
FEATURE_ID=$(printf "%s" "$FEATURE_CONTENT" | sed -n 's/.*<feature[^>]*id="\([^"]*\)".*/\1/p' || true)
FEATURE_VER=$(printf "%s" "$FEATURE_CONTENT" | sed -n 's/.*<feature[^>]*version="\([^"]*\)".*/\1/p' || true)

if [ -z "$FEATURE_ID" ]; then
    echo "Warning: could not determine feature id from $FEATURE_DIR/feature.xml; copying raw feature dir"
    cp -a "$FEATURE_DIR" "$FEATURES_OUT/"
else
    FEATURE_OUT_DIR="$FEATURES_OUT/${FEATURE_ID}_${FEATURE_VER}"
    mkdir -p "$FEATURE_OUT_DIR"
    # copy feature.xml and other files
    cp -a "$FEATURE_DIR/feature.xml" "$FEATURE_OUT_DIR/"
    # if there are extras (license, readme) copy them
    cp -a $(find "$FEATURE_DIR" -maxdepth 1 -type f ! -name feature.xml -print 2>/dev/null) "$FEATURE_OUT_DIR/" || true
fi

# Attempt to publish a full p2 repository using Eclipse p2 publisher if available
# NOTE: never invoke the eclipse binary directly (it can spawn a GUI). Always run headless via the equinox launcher JAR using `java -jar`.
# You can override the launcher explicitly by setting ECLIPSE_LAUNCHER to the path of an equinox launcher jar.
find_launcher_and_publisher() {
    # Candidate plugin directories to search for the launcher and publisher jars
    local cand_dirs=()
    # If ECLIPSE_LAUNCHER is set and exists (explicit override), return it only if it looks like a usable launcher
    if [ -n "${ECLIPSE_LAUNCHER-}" ] && [ -f "$ECLIPSE_LAUNCHER" ]; then
        # reject source jars by name
        case "$(basename "$ECLIPSE_LAUNCHER")" in
            *source*|*src*|*-src*) return 1;;
            *) printf "%s\n" "$ECLIPSE_LAUNCHER"; return 0;;
        esac
    fi
    # Look in ECLIPSE_HOME if set
    if [ -n "${ECLIPSE_HOME-}" ]; then
        cand_dirs+=("$ECLIPSE_HOME/plugins" "$ECLIPSE_HOME/Contents/Eclipse/plugins")
    fi
    # If an eclipse binary was found earlier, use its likely plugin dirs (but do not run it)
    if [ -n "${ECLIPSE_BIN-}" ]; then
        cand_dirs+=("$(dirname "$ECLIPSE_BIN")/plugins" "$(cd "$(dirname "$ECLIPSE_BIN")/.." 2>/dev/null && printf '%s' "$(pwd -P)/plugins" || true)")
    fi
    # Also check common workspace-relative locations
    cand_dirs+=("$ROOT_DIR/../OpenJML/OpenJMLlsp/release-stage/plugins" "$ROOT_DIR/../OpenJML/OpenJMLlsp/build/plugins" "$ROOT_DIR/../OpenJML/OpenJMLlsp/bin/plugins")

    for pd in "${cand_dirs[@]}"; do
        if [ -d "$pd" ]; then
            # Prefer non-source launcher jars. Exclude filenames containing 'source', 'src', or '-src'.
            for cand in "$pd"/org.eclipse.equinox.launcher*.jar; do
                [ -e "$cand" ] || continue
                bn="$(basename "$cand")"
                case "$bn" in
                    *source*|*src*|*-src*) continue ;;
                    *)
                        # Check that a p2 publisher bundle exists in the same plugins dir
                        pub=$(ls "$pd"/org.eclipse.equinox.p2.publisher* 2>/dev/null | head -n1 || true)
                        if [ -n "$pub" ]; then
                            printf "%s\n" "$cand"
                            return 0
                        else
                            # publisher bundle not found in this plugins dir; skip
                            continue
                        fi
                esac
            done
        fi
    done
    return 1
}

# Find equinox launcher jar (headless runner). Do NOT use the eclipse executable to avoid GUI.
LAUNCHER_JAR=""
if LAUNCHER_CAND=$(find_launcher_and_publisher 2>/dev/null || true); then
    LAUNCHER_JAR="$LAUNCHER_CAND"
fi

if [ -n "$LAUNCHER_JAR" ]; then
    echo "Equinox launcher jar found: $LAUNCHER_JAR"
    # Find java
    if [ -n "${JAVA_HOME-}" ] && [ -x "${JAVA_HOME}/bin/java" ]; then
        JAVA_CMD="${JAVA_HOME}/bin/java"
    else
        JAVA_CMD="$(command -v java || true)"
    fi
    if [ -z "$JAVA_CMD" ] || [ ! -x "$JAVA_CMD" ]; then
        echo "Java runtime not found; cannot run p2 publisher headlessly. Falling back to simple layout." >&2
    else
        echo "Using java executable: $JAVA_CMD for headless p2 publisher"
        METADATA_REPO_ABS=$(abspath "$UPDATESITE_DIR/metadata")
        ARTIFACT_REPO_ABS=$(abspath "$UPDATESITE_DIR/artifacts")
        mkdir -p "$METADATA_REPO_ABS" "$ARTIFACT_REPO_ABS"
        METADATA_URI="file:$METADATA_REPO_ABS"
        ARTIFACT_URI="file:$ARTIFACT_REPO_ABS"

        PUBLISH_LOG=$(mktemp)
        set +e
        # Run the publisher headlessly via the Equinox launcher JAR. This does not start the Eclipse GUI.
        "$JAVA_CMD" -jar "$LAUNCHER_JAR" -nosplash -application org.eclipse.equinox.p2.publisher.FeaturesAndBundlesPublisher \
            -metadataRepository "$METADATA_URI" \
            -artifactRepository "$ARTIFACT_URI" \
            -publishArtifacts -compress \
            -feature file:$(abspath "$FEATURE_DIR") \
            -bundle file:$(abspath "$OUT_JAR") \
            -consolelog >"$PUBLISH_LOG" 2>&1
        PUBLISH_STATUS=$?
        set -e
        if [ $PUBLISH_STATUS -eq 0 ]; then
            echo "p2 publisher completed successfully via equinox launcher. Repositories written to:"
            echo "  metadata: $METADATA_REPO_ABS"
            echo "  artifacts: $ARTIFACT_REPO_ABS"
            cp -a "$METADATA_REPO_ABS/" "$UPDATESITE_DIR/" 2>/dev/null || true
            cp -a "$ARTIFACT_REPO_ABS/" "$UPDATESITE_DIR/" 2>/dev/null || true
        else
            echo "p2 publisher failed (exit code $PUBLISH_STATUS). See publisher log below:" >&2
            sed -n '1,200p' "$PUBLISH_LOG" >&2 || true
            echo "Falling back to simple plugins/features layout (no p2 metadata)." >&2
        fi
        rm -f "$PUBLISH_LOG" || true
    fi
else
    echo "No Equinox launcher jar located; will not attempt to start Eclipse. Falling back to simple plugins/features layout." >&2
fi

# Create a simple artifacts.jar and content.jar to make the update site browsable by Eclipse p2 (basic minimal metadata)
# This is used as a fallback; if p2 publisher run succeeded above it may have already generated these.
ARTIFACTS_JAR="$UPDATESITE_DIR/artifacts.jar"
CONTENT_JAR="$UPDATESITE_DIR/content.jar"

# Generate simple content.jar and artifacts.jar using zip with minimal structure if they don't exist
pushd "$UPDATESITE_DIR" >/dev/null
if [ ! -f "$ARTIFACTS_JAR" ] || [ ! -f "$CONTENT_JAR" ]; then
    cat > artifacts.xml <<'EOF'
<?xml version="1.0" encoding="UTF-8"?>
<artifacts>
</artifacts>
EOF
    zip -q -r "$ARTIFACTS_JAR" artifacts.xml >/dev/null || true
    cat > content.xml <<'EOF'
<?xml version="1.0" encoding="UTF-8"?>
<repository>
</repository>
EOF
    zip -q -r "$CONTENT_JAR" content.xml >/dev/null || true
    rm -f artifacts.xml content.xml
fi
popd >/dev/null

echo "Update site assembled in: $UPDATESITE_DIR"
echo "Plugin jar: $OUT_JAR"

echo "Done. Note: This script creates a simple update-site layout (plugins/ and features/).
If Eclipse with p2 publisher was found the script attempted to create a full p2 repository under the release-stage directory."

exit 0
