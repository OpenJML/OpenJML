#!/usr/bin/env bash
# download-counts.sh
# Purpose:
#   Report the GitHub download count for each asset in a given release.
#
# Usage:
#   ./download-counts.sh <version>   -- report counts for one release
#   ./download-counts.sh -all        -- report counts for all releases, newest first
#
# Example:
#   ./download-counts.sh 21.0.25
#   ./download-counts.sh -all
#
# Authentication:
#   Set GITHUB_TOKEN in the environment for authenticated requests (higher
#   rate limit).  For a public repo, unauthenticated requests also work but
#   are limited to 60/hour.

set -euo pipefail

REPO="OpenJML/OpenJML"

if [[ $# -ne 1 ]]; then
    echo "Usage: $0 <version> | -all" >&2
    exit 1
fi

ARG="$1"

curl --silent \
    ${GITHUB_TOKEN:+-H "Authorization: Bearer $GITHUB_TOKEN"} \
    "https://api.github.com/repos/$REPO/releases?per_page=100" \
| python3 -c "
import json, sys

arg = sys.argv[1]
data = json.load(sys.stdin)

if isinstance(data, dict) and 'message' in data:
    print(f'API error: {data[\"message\"]}', file=sys.stderr)
    sys.exit(1)

def print_release(release):
    draft_flag = '  [DRAFT]' if release['draft'] else ''
    date = (release.get('published_at') or release.get('created_at') or '')[:10]
    print(f'Release: {release[\"name\"]}  (tag: {release[\"tag_name\"]})  {date}{draft_flag}')
    assets = release.get('assets', [])
    if not assets:
        print('  No assets.')
    else:
        total = 0
        for a in assets:
            count = a['download_count']
            total += count
            print(f'  {count:6d}  {a[\"name\"]}')
        print(f'         ------')
        print(f'  {total:6d}  total')
    print()

if arg == '-all':
    for release in data:
        print_release(release)
else:
    release = next((r for r in data if r['tag_name'] == arg), None)
    if release is None:
        print(f'No release found for version {arg}', file=sys.stderr)
        sys.exit(1)
    print_release(release)
" "$ARG"
