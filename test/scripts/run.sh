#!/bin/sh
# Score a tactic on a file of examples. Run from the root of the repository.
#
#   test/scripts/run.sh <src.lean> <work dir> [tactic] [module] [score|corpus|mark]
#
# <src.lean> is either Mathlib's goal suite (`MathlibTest/IntegrabilityTactic.lean` of Mathlib PR
# #39323, head f121c1c, which is not copied here) with the mode `score`, or
# `test/IntegrabilityCorpus.lean` with the mode `corpus` (print the scores) or `mark` (rewrite its
# `status:` lines). The generated file and the log are written to <work dir>.
set -e
src=$1; work=$2
tac=${3:-endpoint_integrability}
mod=${4:-SpherePacking.Tactic.EndpointIntegrability.Tactic}
mode=${5:-score}
here=$(dirname "$0")
mkdir -p "$work"
python3 -I "$here/bench.py" make "$src" "$work/Bench.lean" "$tac" "$mod" > /dev/null
lake env lean -DmaxErrors=100000 "$work/Bench.lean" > "$work/Bench.log" 2>&1 || true
if [ "$mode" = score ]; then
  python3 -I "$here/bench.py" score "$work/Bench.lean" "$work/Bench.log"
else
  python3 -I "$here/bench.py" "$mode" "$src" "$work/Bench.lean" "$work/Bench.log"
fi
