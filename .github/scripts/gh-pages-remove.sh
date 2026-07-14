#!/usr/bin/env bash
#
# Remove a PR preview directory from the `gh-pages` branch.
#
# Usage:
#   gh-pages-remove.sh <dest_subdir>
#
#   dest_subdir   The preview directory to delete (e.g. "pr-preview-42").
#
# Requires the GH_TOKEN environment variable (a token with `contents: write`).
set -euo pipefail

DEST="${1:?dest_subdir is required}"

: "${GH_TOKEN:?GH_TOKEN must be set}"
: "${GITHUB_REPOSITORY:?GITHUB_REPOSITORY must be set}"

REPO_URL="https://x-access-token:${GH_TOKEN}@github.com/${GITHUB_REPOSITORY}.git"
WORK="$(mktemp -d)"

if ! git clone --depth 1 --branch gh-pages "$REPO_URL" "$WORK" 2>/dev/null; then
  echo "gh-pages branch does not exist; nothing to remove."
  exit 0
fi

cd "$WORK"

if [ ! -d "$DEST" ]; then
  echo "No preview directory '${DEST}' to remove."
  exit 0
fi

git rm -rqf "${DEST:?}"
git -c user.name='github-actions[bot]' \
    -c user.email='41898282+github-actions[bot]@users.noreply.github.com' \
    commit -m "Remove preview ${DEST}"

for attempt in 1 2 3 4 5; do
  if git push origin gh-pages; then
    echo "Removed ${DEST} from gh-pages."
    exit 0
  fi
  echo "Push rejected (attempt ${attempt}/5); syncing with remote and retrying."
  git fetch origin gh-pages || true
  git rebase origin/gh-pages || git rebase --abort || true
  sleep $(( attempt * 2 ))
done

echo "ERROR: could not push to gh-pages after several attempts." >&2
exit 1
