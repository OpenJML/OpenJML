#!/usr/bin/env bash
# publish-update-site.sh
# Purpose:
#   Headless helper to publish the result of a newly-built update-site (features/
#   and plugins/) into a p2 repository. Designed for CI and automation.
#
# What it does:
#   - Assembles features/ and plugins/ from the newly-built site (and an
#     optional existing site) into a temporary staging area.
#   - Locates a non-source Equinox launcher JAR (by default under ECLIPSE_HOME)
#     and invokes the p2 publisher headlessly via:
#       java -jar <equinox-launcher.jar> -nosplash -application org.eclipse.equinox.p2.publisher.FeaturesAndBundlesPublisher ...
#   - Writes a combined p2 repository to the directory specified by --out.
#   - If headless publishing is not possible (no launcher, no Java, or no p2
#     publisher bundle), falls back to writing a simple combined features/
#     and plugins/ layout to the output directory. In all cases the script is
#     non-interactive and will not launch the Eclipse GUI.
#
# Usage (quick):
#   ./publish-update-site.sh --source <new-release-stage> --out <combined-repo> [--launcher <path>] [--existing <site>] [--backup]
#
# Important defaults and notes:
#   - Default source: ../OpenJMLUpdateSite/release-stage (relative to this script)
#   - Default out:    ../OpenJMLUpdateSite/combined-repo
#   - Default ECLIPSE_HOME (if not set):
#       /Users/davidcok/eclipse/eclipse-committers-2025-06-R-macosx-cocoa-x86_64/Eclipse.app/Contents/Eclipse
#   - The script rejects source-only launcher jars (filenames containing
#     'source', 'src', or '-src') because they cannot be invoked with
#     `java -jar`.
#   - The launcher JAR and the p2 publisher bundle should be from the same
#     Eclipse installation plugins/ directory for maximal compatibility.
#
# Examples:
#   # Publish new site into a new combined repo (recommended):
#   ./publish-update-site.sh --source ../OpenJMLUpdateSite/release-stage --out /tmp/openjml-combined-repo --launcher /path/to/org.eclipse.equinox.launcher_1.6.0.jar
#
#   # Merge into an existing site and republish in-place (with backup):
#   ./publish-update-site.sh --source ../OpenJMLUpdateSite/release-stage --existing /opt/my-update-site --out /opt/my-update-site --backup --launcher /path/to/launcher.jar
#
# Non-interactive guarantee:
#   This script never calls the Eclipse GUI binary. It always attempts a
#   headless invocation via the Equinox launcher JAR (java -jar). If that
#   cannot be done, it performs a non-p2 copy merge to the output path.

set -euo pipefail

# Defaults
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd -P)"
DEFAULT_SOURCE="$SCRIPT_DIR/../OpenJMLUpdateSite/release-stage"
DEFAULT_OUT="$SCRIPT_DIR/../OpenJMLUpdateSite/combined-repo"
# Use user's requested default Eclipse install if ECLIPSE_HOME not set
: "${ECLIPSE_HOME:=/Users/davidcok/eclipse/eclipse-committers-2025-06-R-macosx-cocoa-x86_64/Eclipse.app/Contents/Eclipse}"
VERBOSE=0

usage() {
  cat <<EOF
Usage: $0 [options]

Options:
  --source DIR           Path to the newly built update-site (features/ and plugins/) (default: $DEFAULT_SOURCE)
  --existing DIR         Path to an existing update-site to merge into (optional). If provided, contents will be included.
  --out DIR              Output combined p2 repository directory (default: $DEFAULT_OUT)
  --launcher PATH        Explicit path to an equinox launcher JAR (non-source). If unset the script searches common locations and ECLIPSE_HOME.
  --java PATH            Explicit java binary to use. Defaults to JAVA_HOME/bin/java or java on PATH.
  --backup               When merging in-place, back up the existing site (if --existing equals --out).
  --deploy-site          Path to deploy the published site (default: user's openjml.github.io/eclipse-update-site)
  --deploy               Deploy the site after publishing
  -v, --verbose          Enable verbose logging
  -h, --help             Show this help

Examples:
  # Publish new site to a new combined repo (recommended)
  $0 --source $DEFAULT_SOURCE --out /tmp/combined-site --launcher /path/to/org.eclipse.equinox.launcher_1.6.0.jar

  # Merge new site into an existing file-based site and republish in-place (backup recommended):
  $0 --source $DEFAULT_SOURCE --existing /path/to/existing-site --out /path/to/existing-site --backup --launcher /path/to/launcher.jar

Notes:
  - This script never launches the Eclipse GUI. It uses the Equinox launcher JAR via java -jar to run the p2 publisher headlessly.
  - Ensure the launcher JAR is a non-source launcher (filename should not contain 'source' or '-src') and that a p2 publisher bundle
    (org.eclipse.equinox.p2.publisher*) is available in the same Eclipse plugins directory as the launcher.
EOF
}

# Simple logger
log() { [ "$VERBOSE" -eq 1 ] && printf "%s\n" "$*"; }
err() { printf "ERROR: %s\n" "$*" >&2; }

# Make absolute path
abspath() {
    if [ -z "${1-}" ]; then
        return 1
    fi
    if [ -d "$1" ]; then (cd "$1" 2>/dev/null && pwd -P) || printf "%s" "$1"; return 0; fi
    local d; d=$(cd "$(dirname "$1")" 2>/dev/null && pwd -P || printf "%s" "$(dirname "$1")")
    printf "%s/%s" "$d" "$(basename "$1")"
}

# Search for an equinox launcher jar (non-source) and ensure p2 publisher bundle exists in same dir
find_launcher_jar() {
    if [ -n "${ECLIPSE_LAUNCHER-}" ]; then
        if [ -f "$ECLIPSE_LAUNCHER" ]; then
            bn=$(basename "$ECLIPSE_LAUNCHER")
            case "$bn" in *source*|*src*|*-src*) return 1;; esac
            printf "%s" "$ECLIPSE_LAUNCHER"
            return 0
        else
            return 1
        fi
    fi
    local cand_dirs=()
    if [ -n "${ECLIPSE_HOME-}" ]; then
        cand_dirs+=("$ECLIPSE_HOME/plugins" "$ECLIPSE_HOME/Contents/Eclipse/plugins")
    fi
    # common locations to check relative to workspace and script
    cand_dirs+=("/usr/lib/eclipse/plugins" "/usr/local/eclipse/plugins" "$HOME/eclipse/plugins")
    cand_dirs+=("$SCRIPT_DIR/../OpenJML/OpenJMLlsp/build/plugins" "$SCRIPT_DIR/../OpenJML/OpenJMLlsp/release-stage/plugins")

    for pd in "${cand_dirs[@]}"; do
        [ -d "$pd" ] || continue
        for cand in "$pd"/org.eclipse.equinox.launcher*.jar; do
            [ -e "$cand" ] || continue
            bn=$(basename "$cand")
            case "$bn" in *source*|*src*|*-src*) continue ;; esac
            # check for publisher bundle in same dir
            pub=$(ls "$pd"/org.eclipse.equinox.p2.publisher* 2>/dev/null | head -n1 || true)
            if [ -n "$pub" ]; then printf "%s" "$cand"; return 0; fi
        done
    done
    return 1
}

publish_headless() {
    local launcher_j=$1; shift
    local metadata_repo=$1; shift
    local artifact_repo=$1; shift
    local args=("$@")

    # determine java
    if [ -n "${JAVA_OVERRIDE-}" ] && [ -x "$JAVA_OVERRIDE" ]; then
        JAVA_CMD="$JAVA_OVERRIDE"
    elif [ -n "${JAVA_HOME-}" ] && [ -x "${JAVA_HOME}/bin/java" ]; then
        JAVA_CMD="$JAVA_HOME/bin/java"
    else
        JAVA_CMD=$(command -v java || true)
    fi
    if [ -z "$JAVA_CMD" ] || [ ! -x "$JAVA_CMD" ]; then
        err "Java runtime not found. Set JAVA_HOME or pass --java PATH. Cannot run headless publisher."
        return 2
    fi

    log "Running p2 publisher with: $JAVA_CMD -jar $launcher_j -nosplash -application org.eclipse.equinox.p2.publisher.FeaturesAndBundlesPublisher"
    PUBLISH_LOG="$metadata_repo/publish.log"
    "$JAVA_CMD" -jar "$launcher_j" -nosplash -application org.eclipse.equinox.p2.publisher.FeaturesAndBundlesPublisher \
        -metadataRepository "file:$metadata_repo" \
        -artifactRepository  "file:$artifact_repo" \
        -publishArtifacts -compress "${args[@]}" -consolelog >"$PUBLISH_LOG" 2>&1 || return $?
    return 0
}

# Parse args
SOURCE="$DEFAULT_SOURCE"
EXISTING=""
OUT="$DEFAULT_OUT"
ECLIPSE_LAUNCHER=""
JAVA_OVERRIDE=""
DO_BACKUP=0
DEPLOY_SITE="${DEPLOY_SITE:-/Users/davidcok/projects/OpenJML21/openjml.github.io/eclipse-update-site}"
DO_DEPLOY=0

while [ $# -gt 0 ]; do
    case "$1" in
        --source) SOURCE="$2"; shift 2;;
        --existing) EXISTING="$2"; shift 2;;
        --out) OUT="$2"; shift 2;;
        --launcher) ECLIPSE_LAUNCHER="$2"; shift 2;;
        --java) JAVA_OVERRIDE="$2"; shift 2;;
        --backup) DO_BACKUP=1; shift;;
        --deploy-site) DEPLOY_SITE="$2"; DO_DEPLOY=1; shift 2;;
        --deploy) DO_DEPLOY=1; shift;;
        -v|--verbose) VERBOSE=1; shift;;
        -h|--help) usage; exit 0;;
        *) err "Unknown arg: $1"; usage; exit 1;;
    esac
done

SOURCE_ABS=$(abspath "$SOURCE") || { err "Invalid --source: $SOURCE"; exit 1; }
OUT_ABS=$(abspath "$OUT") || { err "Invalid --out: $OUT"; exit 1; }

# Validate source layout
[ -d "$SOURCE_ABS" ] || { err "Source directory not found: $SOURCE_ABS"; exit 1; }

# Create a temp assembly area
TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

# Copy features/plugins from source
if [ -d "$SOURCE_ABS/features" ]; then cp -a "$SOURCE_ABS/features" "$TMPDIR/"; fi
if [ -d "$SOURCE_ABS/plugins" ]; then cp -a "$SOURCE_ABS/plugins" "$TMPDIR/"; fi

# If existing site provided, copy its features/plugins too
if [ -n "$EXISTING" ]; then
    EXISTING_ABS=$(abspath "$EXISTING") || { err "Invalid --existing: $EXISTING"; exit 1; }
    [ -d "$EXISTING_ABS" ] || { err "Existing site not found: $EXISTING_ABS"; exit 1; }
    # If out equals existing and backup requested, do backup
    if [ "$DO_BACKUP" -eq 1 ] && [ "$OUT_ABS" = "$EXISTING_ABS" ]; then
        BACKUP_DIR="${EXISTING_ABS}.bak-$(date +%Y%m%d%H%M%S)"
        log "Backing up existing site to $BACKUP_DIR"
        cp -a "$EXISTING_ABS" "$BACKUP_DIR"
    fi
    # copy existing features/plugins into tmp (merge)
    if [ -d "$EXISTING_ABS/features" ]; then cp -a "$EXISTING_ABS/features/." "$TMPDIR/features/" 2>/dev/null || true; fi
    if [ -d "$EXISTING_ABS/plugins" ]; then cp -a "$EXISTING_ABS/plugins/." "$TMPDIR/plugins/" 2>/dev/null || true; fi
fi

# Prepare output
mkdir -p "$OUT_ABS"

# Find launcher jar
LAUNCHER_JAR=""
if [ -n "$ECLIPSE_LAUNCHER" ]; then
    LAUNCHER_JAR="$ECLIPSE_LAUNCHER"
else
    if LAUNCHER_CAND=$(find_launcher_jar); then LAUNCHER_JAR="$LAUNCHER_CAND"; fi
fi

if [ -z "$LAUNCHER_JAR" ]; then
    log "No suitable Equinox launcher jar found; will not attempt headless p2 publishing."
    # fallback: just copy assembled features/plugins to OUT
    cp -a "$TMPDIR/." "$OUT_ABS/"
    printf "Wrote fallback combined update-site layout to %s\n" "$OUT_ABS"
    exit 0
fi

# Build publisher args: include all features and bundles found in TMPDIR
PUBLISH_ARGS=()
if [ -d "$TMPDIR/features" ]; then
    for f in "$TMPDIR/features"/*; do [ -d "$f" ] || continue; PUBLISH_ARGS+=( -feature "file:$(abspath "$f")" ); done
fi
if [ -d "$TMPDIR/plugins" ]; then
    for b in "$TMPDIR/plugins"/*; do
        case "$b" in
            *.jar) PUBLISH_ARGS+=( -bundle "file:$(abspath "$b")" );;
            *) :;;
        esac
    done
fi

if [ ${#PUBLISH_ARGS[@]} -eq 0 ]; then
    err "No features or bundles found to publish. Aborting."
    exit 1
fi

# Run headless publisher to OUT_ABS
mkdir -p "$OUT_ABS"
if publish_headless "$LAUNCHER_JAR" "$OUT_ABS" "$OUT_ABS" "${PUBLISH_ARGS[@]}"; then
    printf "Published combined p2 repository to %s\n" "$OUT_ABS"
    printf "Publisher log (first 200 lines):\n"
    sed -n '1,200p' "$OUT_ABS/publish.log" || true

    # Deploy to local openjml.github.io site if requested
    if [ "$DO_DEPLOY" -eq 1 ]; then
        DEPLOY_ABS=$(abspath "$DEPLOY_SITE")
        echo "Deploying published site to: $DEPLOY_ABS"
        # ensure OUT_ABS exists
        if [ ! -d "$OUT_ABS" ]; then
            err "Publish output not found: $OUT_ABS"; exit 1
        fi
        # Backup existing site if present
        if [ -d "$DEPLOY_ABS" ]; then
            BK="${DEPLOY_ABS}.bak-$(date +%Y%m%d%H%M%S)"
            echo "Backing up existing deploy site to: $BK"
            rm -rf "$BK" || true
            mv "$DEPLOY_ABS" "$BK" || { err "Failed to backup existing deploy site"; exit 1; }
        fi
        # Create deploy dir and copy contents
        mkdir -p "$DEPLOY_ABS"
        cp -a "$OUT_ABS/." "$DEPLOY_ABS/"
        # ensure nojekyll to allow files starting with _ to be served
        touch "$DEPLOY_ABS/.nojekyll"
        echo "Deployed combined p2 repository to: $DEPLOY_ABS"
    fi

    exit 0
else
    err "Headless publisher failed; falling back to writing raw features/plugins layout to $OUT_ABS"
    cp -a "$TMPDIR/." "$OUT_ABS/"
    # if deploy requested, still copy fallback layout
    if [ "$DO_DEPLOY" -eq 1 ]; then
        DEPLOY_ABS=$(abspath "$DEPLOY_SITE")
        echo "Deploying fallback layout to: $DEPLOY_ABS"
        if [ -d "$DEPLOY_ABS" ]; then
            BK="${DEPLOY_ABS}.bak-$(date +%Y%m%d%H%M%S)"
            echo "Backing up existing deploy site to: $BK"
            rm -rf "$BK" || true
            mv "$DEPLOY_ABS" "$BK" || { err "Failed to backup existing deploy site"; exit 1; }
        fi
        mkdir -p "$DEPLOY_ABS"
        cp -a "$OUT_ABS/." "$DEPLOY_ABS/"
        touch "$DEPLOY_ABS/.nojekyll"
        echo "Deployed fallback combined layout to: $DEPLOY_ABS"
    fi
    exit 2
fi
