#!/usr/bin/env python3
"""
lean_import_tree.py
-------------------
Scans a Lean 4 project and prints an import dependency tree.

Usage:
    python lean_import_tree.py [project_root] [options]

Arguments:
    project_root        Path to the Lean project root
                        (default: current directory)

Options:
    --root MODULE       Start the tree from a specific module (e.g. MyProject)
    --no-color          Disable ANSI color output
    --show-cycles       Highlight cyclic imports (instead of silently skipping)
    --max-depth N       Limit tree depth (default: unlimited)
    --ignore MODULE     Exclude a module prefix
                        (repeatable, e.g. --ignore Mathlib)

No third-party packages required — only the Python standard library.
"""

import argparse
# import os
import re
import sys
from collections import defaultdict  # , deque
from pathlib import Path

# ── ANSI colors ──────────────────────────────────────────────────────────────

RESET  = "\033[0m"
BOLD   = "\033[1m"
DIM    = "\033[2m"
RED    = "\033[31m"
YELLOW = "\033[33m"
CYAN   = "\033[36m"
GREEN  = "\033[32m"


def colorize(text: str, *codes: str, use_color: bool = True) -> str:
    if not use_color:
        return text
    return "".join(codes) + text + RESET


# ── Lean file discovery ─────────────────────────────────────────────────────-

IMPORT_RE = re.compile(r"^\s*import\s+([\w.]+)", re.MULTILINE)


def find_lean_files(root: Path) -> list[Path]:
    """Return all .lean files under root, excluding build / lake-packages."""
    excluded = {".lake", "build", ".git"}
    results = []
    for path in root.rglob("*.lean"):
        parts = set(path.relative_to(root).parts)
        if parts & excluded:
            continue
        results.append(path)
    return results


def path_to_module(path: Path, root: Path) -> str:
    """Convert a file path to a dotted Lean module name."""
    rel = path.relative_to(root).with_suffix("")
    return ".".join(rel.parts)


def parse_imports(path: Path) -> list[str]:
    """Extract all `import Foo.Bar` module names from a Lean file."""
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []
    return IMPORT_RE.findall(text)


# ── Build the dependency graph ─────────────────────────────────────────────────

def build_graph(root: Path, ignore_prefixes: list[str]) -> dict[str, list[str]]:
    """
    Returns adjacency list: module -> [imported modules that exist in the project].
    External imports (Mathlib, Init, …) are recorded but marked as external.
    """
    lean_files = find_lean_files(root)
    local_modules: set[str] = {path_to_module(f, root) for f in lean_files}

    graph: dict[str, list[str]] = defaultdict(list)
    external: dict[str, list[str]] = defaultdict(list)

    for f in lean_files:
        mod = path_to_module(f, root)
        if any(mod.startswith(p) for p in ignore_prefixes):
            continue
        for imp in parse_imports(f):
            if any(imp.startswith(p) for p in ignore_prefixes):
                continue
            if imp in local_modules:
                graph[mod].append(imp)
            else:
                external[mod].append(imp)

    # Ensure every local module appears as a key
    for mod in local_modules:
        if mod not in graph:
            graph[mod] = []

    return dict(graph), dict(external)


# ── Cycle detection ────────────────────────────────────────────────────────────

def find_cycles(graph: dict[str, list[str]]) -> set[frozenset]:
    """Return a set of frozensets, each containing the nodes of one SCC cycle."""
    # Kosaraju's algorithm
    order = []
    visited = set()

    def dfs1(v):
        stack = [(v, iter(graph.get(v, [])))]
        visited.add(v)
        while stack:
            node, children = stack[-1]
            try:
                child = next(children)
                if child not in visited and child in graph:
                    visited.add(child)
                    stack.append((child, iter(graph.get(child, []))))
            except StopIteration:
                order.append(node)
                stack.pop()

    for node in graph:
        if node not in visited:
            dfs1(node)

    rev: dict[str, list[str]] = defaultdict(list)
    for u, neighbors in graph.items():
        for v in neighbors:
            rev[v].append(u)

    visited2 = set()
    cycles = set()

    def dfs2(v):
        component = []
        stack = [v]
        visited2.add(v)
        while stack:
            node = stack.pop()
            component.append(node)
            for child in rev.get(node, []):
                if child not in visited2:
                    visited2.add(child)
                    stack.append(child)
        return component

    for node in reversed(order):
        if node not in visited2:
            comp = dfs2(node)
            if len(comp) > 1:
                cycles.add(frozenset(comp))

    return cycles


# ── Tree printing ──────────────────────────────────────────────────────────────

BRANCH = "├── "
LAST   = "└── "
PIPE   = "│   "
SPACE  = "    "


def print_tree(
    module: str,
    graph: dict[str, list[str]],
    external: dict[str, list[str]],
    cycle_members: set[str],
    *,
    prefix: str = "",
    visited: set[str] | None = None,
    depth: int = 0,
    max_depth: int | None = None,
    use_color: bool = True,
    show_cycles: bool = False,
    is_last: bool = True,
):
    if visited is None:
        visited = set()

    connector = LAST if is_last else BRANCH

    # Format the module name
    label = module.split(".")[-1]  # short name
    full  = module

    if module in cycle_members and show_cycles:
        display = colorize(f"{label}  ⟳ CYCLE ({full})", RED, BOLD, use_color=use_color)
    elif depth == 0:
        display = colorize(full, BOLD, CYAN, use_color=use_color)
    else:
        display = colorize(label, GREEN, use_color=use_color) + colorize(f"  ({full})", DIM, use_color=use_color)

    print(prefix + connector + display)

    if max_depth is not None and depth >= max_depth:
        return

    child_prefix = prefix + (SPACE if is_last else PIPE)

    if module in visited:
        print(child_prefix + LAST + colorize("(already expanded above)", DIM, YELLOW, use_color=use_color))
        return

    visited.add(module)

    local_deps = graph.get(module, [])
    ext_deps   = external.get(module, [])
    all_items  = [(d, False) for d in sorted(local_deps)] + \
                 [(d, True)  for d in sorted(ext_deps)]

    for i, (dep, is_ext) in enumerate(all_items):
        last = (i == len(all_items) - 1)
        conn = LAST if last else BRANCH
        ext_prefix = child_prefix

        if is_ext:
            ext_label = colorize(dep, DIM, use_color=use_color) + \
                        colorize("  [external]", DIM, YELLOW, use_color=use_color)
            print(ext_prefix + conn + ext_label)
        else:
            print_tree(
                dep, graph, external, cycle_members,
                prefix=child_prefix,
                visited=visited,
                depth=depth + 1,
                max_depth=max_depth,
                use_color=use_color,
                show_cycles=show_cycles,
                is_last=last,
            )

    visited.discard(module)


# ── Entry point ────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Print an import dependency tree for a Lean 4 project.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("project_root", nargs="?", default=".",
                        help="Path to Lean project root (default: current directory)")
    parser.add_argument("--root", metavar="MODULE",
                        help="Start tree from a specific module")
    parser.add_argument("--no-color", action="store_true",
                        help="Disable ANSI color output")
    parser.add_argument("--show-cycles", action="store_true",
                        help="Highlight nodes involved in import cycles")
    parser.add_argument("--max-depth", type=int, default=None, metavar="N",
                        help="Maximum tree depth to display")
    parser.add_argument("--ignore", action="append", default=[], metavar="MODULE",
                        help="Ignore modules with this prefix (e.g. Mathlib)")
    args = parser.parse_args()

    use_color = not args.no_color and sys.stdout.isatty()
    root = Path(args.project_root).resolve()

    if not root.is_dir():
        print(f"Error: {root} is not a directory.", file=sys.stderr)
        sys.exit(1)

    print(colorize(f"Scanning {root} …", DIM, use_color=use_color), file=sys.stderr)

    graph, external = build_graph(root, args.ignore)

    if not graph:
        print("No Lean files found.", file=sys.stderr)
        sys.exit(0)

    cycles = find_cycles(graph)
    cycle_members: set[str] = {m for c in cycles for m in c}

    if cycles and args.show_cycles:
        print(colorize(f"\n⚠  {len(cycles)} import cycle(s) detected:", BOLD, RED, use_color=use_color))
        for i, cycle in enumerate(cycles, 1):
            print(colorize(f"  Cycle {i}: ", YELLOW, use_color=use_color) +
                  " ↔ ".join(sorted(cycle)))
        print()

    # Determine root modules to display
    if args.root:
        roots = [m for m in graph if m == args.root or m.startswith(args.root + ".")]
        if not roots:
            print(f"No modules found matching '{args.root}'.", file=sys.stderr)
            sys.exit(1)
        # Find the single top-level one if it exists, else list all
        top_roots = [args.root] if args.root in graph else roots
    else:
        # Modules that are not imported by anyone else = true roots
        imported_by_someone = {dep for deps in graph.values() for dep in deps}
        top_roots = sorted(m for m in graph if m not in imported_by_someone)
        if not top_roots:
            top_roots = sorted(graph.keys())[:1]  # fallback: first alphabetically

    print(colorize(f"Project root: {root}", BOLD, use_color=use_color))
    print(colorize(f"Modules found: {len(graph)}  |  "
                   f"External imports: {sum(len(v) for v in external.values())}  |  "
                   f"Cycles: {len(cycles)}",
                   DIM, use_color=use_color))
    print()

    for i, mod in enumerate(top_roots):
        last = (i == len(top_roots) - 1)
        print_tree(
            mod, graph, external, cycle_members,
            prefix="",
            depth=0,
            max_depth=args.max_depth,
            use_color=use_color,
            show_cycles=args.show_cycles,
            is_last=last,
        )


if __name__ == "__main__":
    main()
