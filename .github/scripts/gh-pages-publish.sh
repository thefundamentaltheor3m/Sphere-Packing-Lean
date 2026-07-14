#!/usr/bin/env bash
#
# Publish built documentation (the home page, blueprint, dependency graph and,
# for production deploys, the API docs) to the `gh-pages` branch.
#
# Usage:
#   gh-pages-publish.sh <source_dir> <dest_subdir> <commit_message>
#
#   source_dir     Absolute path to the built content (e.g. the staged site or
#                  the blueprint web output).
#   dest_subdir    Where to place it on gh-pages:
#                    ""               -> the branch root (production deploy from
#                                        `main`); existing pr-preview-* and
#                                        `gauss2` directories are preserved.
#                    "gauss2"         -> the gauss2 development deploy.
#                    "pr-preview-42"  -> that PR's preview directory.
#                                        Everything else on the branch is left
#                                        untouched.
#   commit_message  Message for the gh-pages commit.
#
# Requires the GH_TOKEN environment variable (a token with `contents: write`).
#
# The script is deliberately self-contained and shared by every deploy path
# (production, gauss2 and PR previews) so there is a single source of truth for
# how anything reaches gh-pages. It mirrors the approach used by the website
# repo (thefundamentaltheor3m.github.io).
set -euo pipefail

SRC="${1:?source_dir is required}"
DEST="${2-}"
MSG="${3:-Deploy to gh-pages}"

: "${GH_TOKEN:?GH_TOKEN must be set}"
: "${GITHUB_REPOSITORY:?GITHUB_REPOSITORY must be set}"

REPO_URL="https://x-access-token:${GH_TOKEN}@github.com/${GITHUB_REPOSITORY}.git"
WORK="$(mktemp -d)"

# Check out the existing gh-pages branch, or start a fresh orphan if it is the
# very first deploy.
if git clone --depth 1 --branch gh-pages "$REPO_URL" "$WORK" 2>/dev/null; then
  echo "Checked out existing gh-pages branch."
else
  echo "gh-pages branch not found; creating it."
  git clone --depth 1 "$REPO_URL" "$WORK"
  git -C "$WORK" checkout --orphan gh-pages
  git -C "$WORK" rm -rqf . 2>/dev/null || true
fi

cd "$WORK"

if [ -z "$DEST" ]; then
  # Production: replace the root, but keep every pr-preview-* directory and the
  # gauss2 development deploy so they stay live alongside the released site.
  find . -mindepth 1 -maxdepth 1 \
    ! -name '.git' ! -name 'pr-preview-*' ! -name 'gauss2' -exec rm -rf {} +
  cp -a "$SRC"/. .
else
  # Named deploy (gauss2 or a PR preview): replace just that directory.
  rm -rf "${DEST:?}"
  mkdir -p "$DEST"
  cp -a "$SRC"/. "$DEST"/
fi

# Tell GitHub Pages to serve these files as-is (do not re-run Jekyll).
touch .nojekyll

git add -A
if git diff --cached --quiet; then
  echo "No changes to publish."
  exit 0
fi

git -c user.name='github-actions[bot]' \
    -c user.email='41898282+github-actions[bot]@users.noreply.github.com' \
    commit -m "$MSG"

# Serialised by workflow concurrency, but retry on the off-chance of a race.
for attempt in 1 2 3 4 5; do
  if git push origin gh-pages; then
    echo "Published to gh-pages."
    exit 0
  fi
  echo "Push rejected (attempt ${attempt}/5); syncing with remote and retrying."
  git fetch origin gh-pages || true
  git rebase origin/gh-pages || git rebase --abort || true
  sleep $(( attempt * 2 ))
done

echo "ERROR: could not push to gh-pages after several attempts." >&2
exit 1
