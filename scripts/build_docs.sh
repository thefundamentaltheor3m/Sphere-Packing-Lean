#!/usr/bin/env bash

# Exit immediately if a command exits with a non-zero status,
# treat unset variables as an error, and ensure errors in pipelines are not masked.
set -euo pipefail

# Create a temporary docbuild folder
mkdir -p docbuild

# Template lakefile.toml
cat << EOF > docbuild/lakefile.toml
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "SpherePacking"
path = "../"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "$(< lean-toolchain cut -f 2 -d: )"
EOF

# Initialise docbuild as a Lean project
cd docbuild

# Disable an error message due to a non-blocking bug. See Zulip
MATHLIB_NO_CACHE_ON_UPDATE=1 ~/.elan/bin/lake update doc-gen4

# Build the docs
~/.elan/bin/lake build SpherePacking:docs
