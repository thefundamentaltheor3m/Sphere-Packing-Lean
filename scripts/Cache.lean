/-
Copyright (c) 2026 The Sphere Packing Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Data.HashSet

/-!
# `lake exe cache`

This project's `cache` executable shadows Mathlib's, so `lake exe cache get` downloads prebuilt
oleans for both Mathlib and Tau Ceti. Mathlib's own tool remains available as
`lake exe mathlib/cache`.

Every invocation is forwarded unchanged to `lake exe mathlib/cache`. After a successful `get`,
`get!` or `get-`, this tool also fetches Tau Ceti's oleans from its public Lake artifact cache,
configured in `scripts/tauceti-cache.toml`:

1. `lake cache get --mappings-only` downloads the input-to-output mappings for the pinned Tau Ceti
   revision (no oleans yet);
2. for `get` and `get!`, `lake build` on the Tau Ceti modules imported anywhere in `SpherePacking`
   downloads exactly the oleans those modules need, without compiling anything.

The oleans land in `.lake/packages/TauCeti`, where a plain `lake build` and the editor find them.

This file imports only core Lean, so it compiles in seconds and does not depend on Mathlib.
-/

open System

/-- The `lake` binary to call back into: the one running us, if Lake told us, else `lake`. -/
def lakeCmd : IO String := return (← IO.getEnv "LAKE").getD "lake"

/-- Print a line tagged as coming from this tool, not from Mathlib's cache. -/
def say (msg : String) : IO Unit := IO.println s!"[Tau Ceti cache] {msg}"

/-- Run `lake args` with inherited stdio and optional extra environment, returning its exit code. -/
def runLake (args : Array String) (env : Array (String × Option String) := #[])
    (cwd : Option FilePath := none) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd := ← lakeCmd, args, env, cwd }
  child.wait

/-- The workspace root: the nearest ancestor of the working directory containing
`scripts/tauceti-cache.toml`. -/
partial def findRoot (dir : FilePath) : IO (Option FilePath) := do
  if ← (dir / "scripts" / "tauceti-cache.toml").pathExists then
    return some dir
  match dir.parent with
  | some p => if p == dir then return none else findRoot p
  | none => return none

/-- If `line` is an import of a Tau Ceti module, that module's name. Accepts the
`public`/`private`/`meta` prefixes of the module system. -/
def tauCetiImport? (line : String) : Option String := Id.run do
  let mut ws := (line.trimAscii.toString.splitOn " ").filter (· ≠ "")
  while ws.head? ∈ [some "public", some "private", some "meta"] do
    ws := ws.tail
  match ws with
  | ["import", m] => if m.startsWith "TauCeti." then some m else none
  | _ => none

/-- Every Tau Ceti module imported by `SpherePacking.lean` or a file under `SpherePacking/`. -/
def tauCetiImports (root : FilePath) : IO (Array String) := do
  let dir := root / "SpherePacking"
  let mut files : Array FilePath := #[root / "SpherePacking.lean"]
  if ← dir.isDir then
    files := files ++ (← dir.walkDir).filter (·.extension == some "lean")
  let mut mods : Std.HashSet String := {}
  for f in files do
    if ← f.pathExists then
      for line in (← IO.FS.lines f) do
        if let some m := tauCetiImport? line then mods := mods.insert m
  return mods.toArray.qsort (· < ·)

/-- Fetch Tau Ceti's mappings, then (unless `buildImports` is false) the oleans of the imported
Tau Ceti modules. -/
def getTauCeti (root : FilePath) (force buildImports : Bool) : IO UInt32 := do
  let env := #[("LAKE_CONFIG", some (root / "scripts" / "tauceti-cache.toml").toString)]
  say "fetching Tau Ceti's cache mappings"
  let mut args := #["cache", "get", "--package", "TauCeti", "--service", "tauceti-public",
    "--repo", "TauCetiProject/TauCeti", "--mappings-only"]
  if force then args := args.push "--force-download"
  let rc ← runLake args env root
  if rc != 0 then
    say "fetching the mappings failed; Tau Ceti modules will be compiled from source"
    return rc
  unless buildImports do return 0
  let mods ← tauCetiImports root
  if mods.isEmpty then
    say "no Tau Ceti modules are imported yet; nothing more to fetch"
    return 0
  say s!"fetching oleans for the {mods.size} imported Tau Ceti module(s)"
  let rc ← runLake (#["build"] ++ mods) env root
  if rc != 0 then say "fetching Tau Ceti oleans failed"
  return rc

def main (args : List String) : IO UInt32 := do
  let rc ← runLake (#["exe", "mathlib/cache"] ++ args.toArray)
  if rc != 0 then return rc
  -- Mathlib's tool takes its options anywhere; the first non-option argument is the command.
  let cmd := args.find? (!·.startsWith "--")
  unless cmd ∈ [some "get", some "get!", some "get-"] do return 0
  let some root ← findRoot (← IO.currentDir)
    | say "could not find scripts/tauceti-cache.toml above the working directory"; return 1
  getTauCeti root (force := cmd == some "get!") (buildImports := cmd != some "get-")
