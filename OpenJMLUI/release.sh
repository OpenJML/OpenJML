#!/usr/bin/env bash
# release.sh
# Purpose:
#   Automate the release procedure for OpenJML UI update-site.
#   Usage: run from OpenJML/OpenJMLUI directory or anywhere; script resolves paths.
#
# Actions performed (configurable via flags):
#   - Create/checkout a release branch `release-<version>` (if absent, created from current HEAD)
#   - Update source manifests/feature to the given version and build the release-stage via build-update-site.sh
#   - Commit the version bump and tag the release (v<version>) locally
#   - Assemble and publish the combined p2 repo via publish-update-site.sh and deploy to the local Pages folder
#   - Optionally push branch and tag to origin and push the Pages repo changes (only if --push provided)
#
# Safety: nothing is pushed unless --push is passed. Overwrite behavior is only enabled if --overwrite is passed.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd -P)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd -P)"  # root of OpenJML project
UI_DIR="$SCRIPT_DIR"
BUILD_SCRIPT="$UI_DIR/build-update-site.sh"
PUBLISH_SCRIPT="$UI_DIR/publish-update-site.sh"
# Default pages site location: ../../openjml.github.io/eclipse-update-site relative to this script
PAGES_SITE_DIR_DEFAULT="$(cd "$SCRIPT_DIR/../.." && pwd -P)/openjml.github.io/eclipse-update-site"
PAGES_SITE_DIR="$PAGES_SITE_DIR_DEFAULT"
PAGES_DIR="$(dirname "$PAGES_SITE_DIR")"

usage() {
  cat <<EOF
Usage: $(basename "$0") --version VERSION [options]

Required:
  --version VERSION     Release version (e.g., 0.21.0)

Options:
  --branch BRANCH       Branch to create/use for the release (default: release-VERSION)
  --overwrite           Pass --overwrite to build script (allow overwriting existing release-stage artifacts)
  --deploy              Run publish step and deploy to local Pages folder (default: yes)
  --push                Push the release branch and tag to origin and push Pages changes (only if set)
  --pages-branch BR     Branch to push pages to (default: main)
  --commit              Create a commit and tag locally (default: no)
  -v --verbose          Verbose output
  -h --help             Show this help and exit

Example:
  # From anywhere, create a release 0.21.0, build, deploy locally, but do not push
  ./release.sh --version 0.21.0 --overwrite --deploy

Notes:
  - This script modifies MANIFEST.MF and feature.xml (via build-update-site.sh --version).
  - It will commit only a small set of known files by default. You can inspect changes before pushing.
  - By default this script will NOT commit or tag the version bump locally.
    Use --commit to enable committing and tagging (safer for testing and CI).
EOF
}

# Defaults
VERSION=""
BRANCH=""
OVERWRITE_FLAG=""
DO_DEPLOY=1
DO_PUSH=0
PAGES_BRANCH="master"
DO_COMMIT=0   # default: do not create commits or tags unless explicitly enabled
VERBOSE=0

# parse args
while [ $# -gt 0 ]; do
  case "$1" in
    --version) VERSION="$2"; shift 2;;
    --branch) BRANCH="$2"; shift 2;;
    --overwrite) OVERWRITE_FLAG="--overwrite"; shift;;
    --deploy) DO_DEPLOY=1; shift;;
    --no-deploy) DO_DEPLOY=0; shift;;
    --push) DO_PUSH=1; shift;;
    --pages-branch) PAGES_BRANCH="$2"; shift 2;;
    --commit) DO_COMMIT=1; shift;;
    -v|--verbose) VERBOSE=1; shift;;
    -h|--help) usage; exit 0;;
    *) echo "Unknown arg: $1"; usage; exit 1;;
  esac
done

if [ -z "$VERSION" ]; then
  echo "ERROR: --version is required" >&2
  usage
  exit 1
fi

if [ -z "$BRANCH" ]; then
##  BRANCH="release-$VERSION"
  BRANCH="master"
fi

# Print a start banner so the script always emits output even without -v
echo "Starting release procedure for version: $VERSION (branch: $BRANCH)"

log() { [ "$VERBOSE" -eq 1 ] && echo "+ $*"; }
err() { echo "ERROR: $*" >&2; }

# Ensure build and publish scripts exist
[ -x "$BUILD_SCRIPT" ] || { err "Build script not found or not executable: $BUILD_SCRIPT"; exit 1; }
[ -x "$PUBLISH_SCRIPT" ] || { err "Publish script not found or not executable: $PUBLISH_SCRIPT"; exit 1; }

# Verify we are inside a git repo
if ! git -C "$REPO_ROOT" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  err "Repository root not a git repo: $REPO_ROOT"
  exit 1
fi

# Ensure we are running with a valid current working directory inside the repo
# This avoids `getcwd: cannot access parent directories` errors when the shell's cwd disappears.
if ! cd "$REPO_ROOT" 2>/dev/null; then
  err "Could not change current directory to repository root: $REPO_ROOT";
  exit 1
fi

# Save current branch to restore later
CUR_BRANCH=$(git -C "$REPO_ROOT" symbolic-ref --short HEAD 2>/dev/null || git -C "$REPO_ROOT" branch --show-current || true)
log "Current branch is: $CUR_BRANCH"

# Create or checkout release branch
if git -C "$REPO_ROOT" rev-parse --verify --quiet "$BRANCH" >/dev/null; then
  log "Checking out existing branch $BRANCH"
  git -C "$REPO_ROOT" checkout "$BRANCH"
else
  log "Creating new branch $BRANCH from current HEAD ($CUR_BRANCH)"
  git -C "$REPO_ROOT" checkout -b "$BRANCH"
fi

# Run the build script with version (and optional overwrite)
BUILD_CMD=("$BUILD_SCRIPT" "--version" "$VERSION")
if [ -n "$OVERWRITE_FLAG" ]; then BUILD_CMD+=("$OVERWRITE_FLAG"); fi
log "Running build: ${BUILD_CMD[*]}"
# run from UI_DIR so relative paths resolve
( cd "$UI_DIR" && "${BUILD_CMD[@]}" ) || {
  err "Build script failed. If the failure was 'version already exists' consider re-running with --overwrite."
  exit 1
}

# Which files to commit (best-effort list)
COMMIT_FILES=(
  "$UI_DIR/META-INF/MANIFEST.MF"
  "$REPO_ROOT/OpenJMLFeature/feature.xml"
  "$REPO_ROOT/OpenJMLTest/META-INF/MANIFEST.MF"
)

# Stage only files that exist and are changed
STAGED=()
for f in "${COMMIT_FILES[@]}"; do
  if [ -f "$f" ]; then
    # only add if changed
    if git -C "$REPO_ROOT" status --porcelain "$f" | grep -qE '^[ MADRC]'; then
      git -C "$REPO_ROOT" add "$f"
      STAGED+=("$f")
      log "Staged $f"
    else
      log "No change in $f"
    fi
  fi
done

if [ "$DO_COMMIT" -eq 1 ] && [ ${#STAGED[@]} -gt 0 ]; then
  COMMIT_MSG="Bump version to $VERSION for release"
  git -C "$REPO_ROOT" commit -m "$COMMIT_MSG"
  log "Committed version bump"
else
  log "No files staged for commit or commits disabled"
fi

# Tag the release
TAG="v$VERSION"
if git -C "$REPO_ROOT" rev-parse --verify --quiet "$TAG" >/dev/null; then
  log "Tag $TAG already exists locally"
else
  git -C "$REPO_ROOT" tag -a "$TAG" -m "OpenJML release $VERSION"
  log "Created tag $TAG"
fi

# Assemble combined p2 repo and deploy to local pages dir if requested
if [ "$DO_DEPLOY" -eq 1 ]; then
  log "Publishing and deploying combined p2 repository"
  ( cd "$UI_DIR" && "$PUBLISH_SCRIPT" --source "$REPO_ROOT/OpenJMLUpdateSite/release-stage" --out "$REPO_ROOT/OpenJMLUpdateSite/combined-repo" --deploy --deploy-site "$PAGES_SITE_DIR" -v )
else
  log "Skipping deploy step (--no-deploy)"
fi

# If push requested, push branch and tag and push pages repo contents
if [ "$DO_PUSH" -eq 1 ]; then
  echo "Pushing branch $BRANCH and tag $TAG to origin"
  git -C "$REPO_ROOT" push origin "$BRANCH"
  git -C "$REPO_ROOT" push origin "$TAG"

  # Commit & push pages site if changes exist
  if [ -d "$PAGES_DIR" ]; then
    log "Preparing pages site push under $PAGES_DIR"
    # copy combined-repo into pages site dir (overwrite)
    rsync -av --delete "$REPO_ROOT/OpenJMLUpdateSite/combined-repo/" "$PAGES_SITE_DIR/"
    ( cd "$PAGES_DIR" && git add eclipse-update-site .nojekyll || true )
    if ( cd "$PAGES_DIR" && git status --porcelain | grep -q . ); then
      ( cd "$PAGES_DIR" && git commit -m "Publish OpenJML update site $VERSION" )
      ( cd "$PAGES_DIR" && git push origin "$PAGES_BRANCH" )
      log "Pushed pages to $PAGES_BRANCH"
    else
      log "No changes to pages repo"
    fi
  else
    err "Pages directory not found: $PAGES_DIR";
  fi
fi

# Restore original branch if different
if [ -n "$CUR_BRANCH" ] && [ "$CUR_BRANCH" != "$BRANCH" ]; then
  git -C "$REPO_ROOT" checkout "$CUR_BRANCH"
  log "Restored branch to $CUR_BRANCH"
fi

echo "Release procedure for $VERSION completed."

echo "Next steps: inspect changes, run tests, and push if you used --push."

exit 0
