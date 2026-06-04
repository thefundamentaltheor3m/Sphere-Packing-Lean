#!/usr/bin/env python3
"""
lean_graph.py
-------------
Scans a Lean 4 project and generates an interactive HTML dependency graph.

The output is a single self-contained HTML file that uses vis.js (loaded from
CDN) to render a clickable, zoomable graph of all module imports.

Features:
  - Click a node to focus it and highlight its direct dependencies
  - Sidebar shows full import/imported-by lists for the selected module
  - Color-coded: local modules vs external (Mathlib, etc.)
  - Search box to jump to any module
  - Toggle physics simulation on/off
  - ASCII tree view also available via --ascii flag

Usage:
    python lean_graph.py [project_root] [options]

Options:
    --output FILE       Output HTML file (default: lean_imports.html)
    --ascii             Also print an ASCII tree to stdout
    --no-browser        Don't open the browser automatically after generating
    --ignore MODULE     Exclude a module prefix (repeatable, e.g. --ignore Mathlib)
    --root MODULE       Only include modules reachable from this module

Requirements: networkx (pip install networkx)
"""

import argparse
import json
import re
import sys
import webbrowser
from collections import defaultdict, deque
from pathlib import Path

import networkx as nx

# ── Project / lakefile detection ───────────────────────────────────────────────

_LEAN_LIB_RE     = re.compile(r'lean_lib\s+[«\"]?([\w]+)[»\"]?')
_TOML_TARGETS_RE = re.compile(r'defaultTargets\s*=\s*\["([\w]+)"')
_TOML_NAME_RE    = re.compile(r'^name\s*=\s*"([\w]+)"', re.MULTILINE)


def detect_source_root(project_root: Path) -> tuple[Path, str | None]:
    namespace = None
    for lakefile, pattern in [
        (project_root / "lakefile.lean", _LEAN_LIB_RE),
        (project_root / "lakefile.toml", _TOML_TARGETS_RE),
        (project_root / "lakefile.toml", _TOML_NAME_RE),
    ]:
        if lakefile.exists() and namespace is None:
            text = lakefile.read_text(encoding="utf-8", errors="replace")
            m = pattern.search(text)
            if m:
                namespace = m.group(1)

    if namespace is None:
        return project_root, None

    if (project_root / namespace).is_dir():
        return project_root, namespace

    for child in project_root.iterdir():
        if child.is_dir() and (child / namespace).is_dir():
            return child, namespace

    return project_root, namespace


# ── File discovery & parsing ───────────────────────────────────────────────────

IMPORT_RE = re.compile(r"^\s*import\s+([\w.]+)", re.MULTILINE)
EXCLUDED  = {".lake", "build", ".git"}


def find_lean_files(source_root: Path) -> list[Path]:
    results = []
    for path in source_root.rglob("*.lean"):
        parts = set(path.relative_to(source_root).parts)
        if not (parts & EXCLUDED):
            results.append(path)
    return results


def path_to_module(path: Path, source_root: Path) -> str:
    return ".".join(path.relative_to(source_root).with_suffix("").parts)


def parse_imports(path: Path) -> list[str]:
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []
    return IMPORT_RE.findall(text)


# ── Graph construction ─────────────────────────────────────────────────────────

def build_nx_graph(
    source_root: Path,
    ignore_prefixes: list[str],
) -> nx.DiGraph:
    lean_files    = find_lean_files(source_root)
    local_modules = {path_to_module(f, source_root) for f in lean_files}

    G = nx.DiGraph()

    for mod in local_modules:
        G.add_node(mod, kind="local")

    for f in lean_files:
        mod = path_to_module(f, source_root)
        if any(mod.startswith(p) for p in ignore_prefixes):
            continue
        for imp in parse_imports(f):
            if any(imp.startswith(p) for p in ignore_prefixes):
                continue
            if imp not in G:
                G.add_node(imp, kind="external")
            G.add_edge(mod, imp)

    return G


def filter_from_root(G: nx.DiGraph, root_module: str) -> nx.DiGraph:
    if root_module not in G:
        print(f"Error: module '{root_module}' not found in graph.", file=sys.stderr)
        sys.exit(1)
    reachable = nx.descendants(G, root_module) | {root_module}
    return G.subgraph(reachable).copy()


# ── ASCII tree ─────────────────────────────────────────────────────────────────

def print_ascii_tree(G: nx.DiGraph) -> None:
    imported_by_someone = {v for _, v in G.edges()}
    roots = sorted(n for n in G.nodes() if n not in imported_by_someone
                   and G.nodes[n].get("kind") == "local")
    if not roots:
        roots = sorted(n for n in G.nodes() if G.nodes[n].get("kind") == "local")[:1]

    BRANCH, LAST, PIPE, SPACE = "├── ", "└── ", "│   ", "    "

    def _draw(node, prefix="", visited=None, is_last=True):
        if visited is None:
            visited = set()
        conn = LAST if is_last else BRANCH
        print(prefix + conn + node)
        child_prefix = prefix + (SPACE if is_last else PIPE)
        if node in visited:
            print(child_prefix + LAST + "(already expanded above)")
            return
        visited.add(node)
        children = sorted(G.successors(node))
        for i, child in enumerate(children):
            _draw(child, child_prefix, visited, is_last=(i == len(children) - 1))
        visited.discard(node)

    for i, root in enumerate(roots):
        _draw(root, is_last=(i == len(roots) - 1))


# ── HTML generation ────────────────────────────────────────────────────────────

def build_html(G: nx.DiGraph, project_root: Path, namespace: str | None) -> str:
    # Compute some metrics per node for display
    metrics = {}
    for node in G.nodes():
        metrics[node] = {
            "in_degree":  G.in_degree(node),
            "out_degree": G.out_degree(node),
            "kind":       G.nodes[node].get("kind", "local"),
        }

    # Assign numeric IDs
    node_list  = list(G.nodes())
    node_index = {n: i for i, n in enumerate(node_list)}

    # Build vis.js node/edge data
    vis_nodes = []
    for node in node_list:
        kind  = metrics[node]["kind"]
        indeg = metrics[node]["in_degree"]
        # Size scales with how many things import this module
        size = 18 + indeg * 4

        if kind == "external":
            color = {"background": "#1e3a2f", "border": "#2ecc71",
                     "highlight": {"background": "#2ecc71", "border": "#a8f0c6"}}
            font_color = "#7fcea0"
        else:
            # Local modules: shade by depth / importance
            color = {"background": "#1a2540", "border": "#4a7fd4",
                     "highlight": {"background": "#4a7fd4", "border": "#a0c4ff"}}
            font_color = "#c8d8f8"

        short_label = node.split(".")[-1]
        vis_nodes.append({
            "id":    node_index[node],
            "label": short_label,
            "title": node,  # tooltip
            "size":  size,
            "color": color,
            "font":  {"color": font_color, "size": 13, "face": "JetBrains Mono, monospace"},
            "kind":  kind,
            "full":  node,
        })

    vis_edges = []
    for src, dst in G.edges():
        vis_edges.append({
            "from":   node_index[src],
            "to":     node_index[dst],
            "arrows": "to",
            "color":  {"color": "#2a3a5c", "highlight": "#4a7fd4", "opacity": 0.7},
            "width":  1,
        })

    # Build adjacency for sidebar
    adjacency = {}
    for node in node_list:
        adjacency[node] = {
            "imports":     sorted(G.successors(node)),
            "imported_by": sorted(G.predecessors(node)),
        }

    nodes_json = json.dumps(vis_nodes)
    edges_json = json.dumps(vis_edges)
    adj_json   = json.dumps(adjacency)
    proj_name  = namespace or project_root.name
    n_local    = sum(1 for n in G.nodes() if G.nodes[n].get("kind") == "local")
    n_ext      = G.number_of_nodes() - n_local
    n_edges    = G.number_of_edges()

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>{proj_name} — Lean Import Graph</title>
<script src="https://cdnjs.cloudflare.com/ajax/libs/vis-network/9.1.9/standalone/umd/vis-network.min.js"></script>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=JetBrains+Mono:wght@300;400;500;700&family=Syne:wght@400;700;800&display=swap" rel="stylesheet">
<style>
  *, *::before, *::after {{ box-sizing: border-box; margin: 0; padding: 0; }}

  :root {{
    --bg:        #0a0e1a;
    --panel:     #0f1628;
    --border:    #1e2d4a;
    --accent:    #4a7fd4;
    --accent2:   #2ecc71;
    --text:      #c8d8f8;
    --text-dim:  #4a6080;
    --text-mid:  #7a9abf;
    --danger:    #e05c5c;
    --radius:    8px;
    --mono:      'JetBrains Mono', monospace;
    --sans:      'Syne', sans-serif;
  }}

  html, body {{ height: 100%; overflow: hidden; background: var(--bg); color: var(--text); font-family: var(--mono); }}

  /* ── Layout ── */
  #app {{ display: grid; grid-template-columns: 280px 1fr 300px; grid-template-rows: 52px 1fr; height: 100vh; }}

  /* ── Topbar ── */
  #topbar {{
    grid-column: 1 / -1;
    display: flex; align-items: center; gap: 16px;
    padding: 0 20px;
    background: var(--panel);
    border-bottom: 1px solid var(--border);
  }}
  #topbar h1 {{
    font-family: var(--sans); font-weight: 800; font-size: 16px;
    color: var(--text); letter-spacing: -0.02em; white-space: nowrap;
  }}
  #topbar h1 span {{ color: var(--accent); }}
  .tb-sep {{ width: 1px; height: 24px; background: var(--border); flex-shrink: 0; }}
  .tb-stat {{ font-size: 11px; color: var(--text-mid); white-space: nowrap; }}
  .tb-stat b {{ color: var(--text); font-weight: 500; }}
  #search-wrap {{ position: relative; margin-left: auto; }}
  #search {{
    background: var(--bg); border: 1px solid var(--border); border-radius: var(--radius);
    color: var(--text); font-family: var(--mono); font-size: 12px;
    padding: 6px 12px 6px 30px; width: 200px; outline: none;
    transition: border-color .2s;
  }}
  #search:focus {{ border-color: var(--accent); }}
  #search-wrap::before {{
    content: '⌕'; position: absolute; left: 9px; top: 50%; transform: translateY(-50%);
    color: var(--text-dim); font-size: 14px; pointer-events: none;
  }}
  #search-results {{
    position: absolute; top: calc(100% + 4px); right: 0;
    width: 280px; background: var(--panel); border: 1px solid var(--border);
    border-radius: var(--radius); max-height: 200px; overflow-y: auto;
    z-index: 100; display: none;
  }}
  .sr-item {{
    padding: 7px 12px; font-size: 11px; cursor: pointer;
    border-bottom: 1px solid var(--border); color: var(--text-mid);
    transition: background .1s, color .1s;
  }}
  .sr-item:last-child {{ border-bottom: none; }}
  .sr-item:hover {{ background: var(--border); color: var(--text); }}
  .sr-item .sr-full {{ font-size: 10px; color: var(--text-dim); margin-top: 2px; }}

  /* ── Left panel ── */
  #left-panel {{
    background: var(--panel);
    border-right: 1px solid var(--border);
    display: flex; flex-direction: column;
    overflow: hidden;
  }}
  .panel-header {{
    padding: 14px 16px 10px;
    font-size: 10px; font-weight: 700; letter-spacing: .12em;
    text-transform: uppercase; color: var(--text-dim);
    border-bottom: 1px solid var(--border); flex-shrink: 0;
  }}
  #controls {{ padding: 14px 16px; display: flex; flex-direction: column; gap: 10px; }}
  .ctrl-btn {{
    background: var(--bg); border: 1px solid var(--border); border-radius: var(--radius);
    color: var(--text-mid); font-family: var(--mono); font-size: 11px;
    padding: 8px 12px; cursor: pointer; text-align: left;
    transition: border-color .15s, color .15s, background .15s;
    display: flex; align-items: center; gap: 8px;
  }}
  .ctrl-btn:hover {{ border-color: var(--accent); color: var(--text); background: #131c33; }}
  .ctrl-btn.active {{ border-color: var(--accent); color: var(--accent); background: #131c33; }}
  .ctrl-icon {{ font-size: 14px; width: 16px; text-align: center; }}

  .legend {{ padding: 0 16px 14px; display: flex; flex-direction: column; gap: 6px; }}
  .legend-item {{ display: flex; align-items: center; gap: 8px; font-size: 11px; color: var(--text-mid); }}
  .legend-dot {{ width: 10px; height: 10px; border-radius: 50%; flex-shrink: 0; }}
  .legend-dot.local    {{ background: #4a7fd4; }}
  .legend-dot.external {{ background: #2ecc71; }}

  .panel-section {{ border-top: 1px solid var(--border); }}

  /* ── Graph canvas ── */
  #graph-wrap {{
    position: relative;
    overflow: hidden;
  }}
  #graph-canvas {{ width: 100%; height: 100%; }}
  #loading {{
    position: absolute; inset: 0; display: flex; flex-direction: column;
    align-items: center; justify-content: center; gap: 12px;
    background: var(--bg); z-index: 10;
  }}
  .spinner {{
    width: 32px; height: 32px; border: 2px solid var(--border);
    border-top-color: var(--accent); border-radius: 50%;
    animation: spin .7s linear infinite;
  }}
  @keyframes spin {{ to {{ transform: rotate(360deg); }} }}
  #loading p {{ font-size: 12px; color: var(--text-dim); }}

  /* ── Right panel / sidebar ── */
  #sidebar {{
    background: var(--panel);
    border-left: 1px solid var(--border);
    display: flex; flex-direction: column;
    overflow: hidden;
  }}
  #sidebar-empty {{
    flex: 1; display: flex; flex-direction: column;
    align-items: center; justify-content: center; gap: 8px;
    color: var(--text-dim); font-size: 11px; text-align: center; padding: 24px;
  }}
  #sidebar-empty .hint-icon {{ font-size: 28px; opacity: .4; }}
  #sidebar-content {{ display: none; flex-direction: column; flex: 1; overflow: hidden; }}

  #mod-name {{
    padding: 14px 16px 8px;
    font-family: var(--sans); font-size: 14px; font-weight: 700;
    color: var(--text); border-bottom: 1px solid var(--border);
    word-break: break-all; line-height: 1.4; flex-shrink: 0;
  }}
  #mod-name .mod-kind {{
    font-family: var(--mono); font-size: 10px; font-weight: 400;
    padding: 2px 7px; border-radius: 4px; margin-bottom: 4px;
    display: inline-block;
  }}
  .kind-local    {{ background: #1a2540; color: var(--accent); border: 1px solid #2a3f6a; }}
  .kind-external {{ background: #1e3a2f; color: var(--accent2); border: 1px solid #2a5a40; }}

  #mod-stats {{
    display: grid; grid-template-columns: 1fr 1fr;
    gap: 1px; background: var(--border);
    border-bottom: 1px solid var(--border); flex-shrink: 0;
  }}
  .stat-cell {{
    background: var(--panel); padding: 10px 14px;
    font-size: 10px; color: var(--text-dim);
  }}
  .stat-cell b {{ display: block; font-size: 20px; font-weight: 300; color: var(--text); margin-bottom: 2px; }}

  .dep-section {{ display: flex; flex-direction: column; flex: 1; overflow: hidden; min-height: 0; }}
  .dep-tab-bar {{
    display: flex; border-bottom: 1px solid var(--border); flex-shrink: 0;
  }}
  .dep-tab {{
    flex: 1; padding: 9px 8px; font-size: 10px; font-weight: 500;
    text-align: center; cursor: pointer; color: var(--text-dim);
    border-bottom: 2px solid transparent; transition: color .15s, border-color .15s;
    letter-spacing: .05em; text-transform: uppercase;
  }}
  .dep-tab.active {{ color: var(--accent); border-bottom-color: var(--accent); }}
  .dep-list {{
    flex: 1; overflow-y: auto; padding: 8px 0;
  }}
  .dep-item {{
    padding: 7px 16px; font-size: 11px; cursor: pointer;
    display: flex; align-items: center; gap: 8px;
    transition: background .1s;
    border-left: 2px solid transparent;
  }}
  .dep-item:hover {{ background: var(--border); border-left-color: var(--accent); }}
  .dep-item .dep-short {{ color: var(--text); font-weight: 500; flex-shrink: 0; }}
  .dep-item .dep-ns {{ color: var(--text-dim); font-size: 10px; overflow: hidden;
    text-overflow: ellipsis; white-space: nowrap; }}
  .dep-item .dep-ext {{ color: var(--accent2); font-size: 10px; flex-shrink: 0; }}
  .dep-empty {{ padding: 20px 16px; font-size: 11px; color: var(--text-dim); }}

  /* Scrollbars */
  ::-webkit-scrollbar {{ width: 4px; }}
  ::-webkit-scrollbar-track {{ background: transparent; }}
  ::-webkit-scrollbar-thumb {{ background: var(--border); border-radius: 2px; }}
</style>
</head>
<body>
<div id="app">
  <!-- Topbar -->
  <div id="topbar">
    <h1>lean<span>graph</span> — {proj_name}</h1>
    <div class="tb-sep"></div>
    <div class="tb-stat"><b>{n_local}</b> local modules</div>
    <div class="tb-sep"></div>
    <div class="tb-stat"><b>{n_ext}</b> external</div>
    <div class="tb-sep"></div>
    <div class="tb-stat"><b>{n_edges}</b> imports</div>
    <div id="search-wrap">
      <input id="search" type="text" placeholder="Search modules…" autocomplete="off">
      <div id="search-results"></div>
    </div>
  </div>

  <!-- Left panel -->
  <div id="left-panel">
    <div class="panel-header">Controls</div>
    <div id="controls">
      <button class="ctrl-btn active" id="btn-physics" onclick="togglePhysics()">
        <span class="ctrl-icon">⚛</span> Physics simulation
      </button>
      <button class="ctrl-btn" id="btn-fit" onclick="network.fit()">
        <span class="ctrl-icon">⊡</span> Fit to screen
      </button>
      <button class="ctrl-btn" id="btn-reset" onclick="resetSelection()">
        <span class="ctrl-icon">↺</span> Reset selection
      </button>
    </div>
    <div class="panel-section">
      <div class="panel-header">Legend</div>
      <div class="legend">
        <div class="legend-item">
          <div class="legend-dot local"></div>
          Local module
        </div>
        <div class="legend-item">
          <div class="legend-dot external"></div>
          External dependency
        </div>
      </div>
    </div>
  </div>

  <!-- Graph -->
  <div id="graph-wrap">
    <div id="loading">
      <div class="spinner"></div>
      <p>Laying out graph…</p>
    </div>
    <div id="graph-canvas"></div>
  </div>

  <!-- Sidebar -->
  <div id="sidebar">
    <div class="panel-header">Module details</div>
    <div id="sidebar-empty">
      <div class="hint-icon">◎</div>
      <div>Click any node<br>to explore its dependencies</div>
    </div>
    <div id="sidebar-content">
      <div id="mod-name"></div>
      <div id="mod-stats">
        <div class="stat-cell"><b id="stat-imports">0</b>imports</div>
        <div class="stat-cell"><b id="stat-importedby">0</b>imported by</div>
      </div>
      <div class="dep-section">
        <div class="dep-tab-bar">
          <div class="dep-tab active" id="tab-imports" onclick="switchTab('imports')">Imports</div>
          <div class="dep-tab" id="tab-importedby" onclick="switchTab('importedby')">Imported by</div>
        </div>
        <div id="dep-list" class="dep-list"></div>
      </div>
    </div>
  </div>
</div>

<script>
const NODES_DATA = {nodes_json};
const EDGES_DATA = {edges_json};
const ADJACENCY  = {adj_json};

// Index: id -> full module name
const idToFull = {{}};
NODES_DATA.forEach(n => {{ idToFull[n.id] = n.full; }});

// Index: full name -> id
const fullToId = {{}};
NODES_DATA.forEach(n => {{ fullToId[n.full] = n.id; }});

// ── vis.js setup ──────────────────────────────────────────────────────────────
const container = document.getElementById('graph-canvas');
const nodes = new vis.DataSet(NODES_DATA);
const edges = new vis.DataSet(EDGES_DATA);

const options = {{
  physics: {{
    enabled: true,
    solver: 'forceAtlas2Based',
    forceAtlas2Based: {{
      gravitationalConstant: -60,
      centralGravity: 0.008,
      springLength: 130,
      springConstant: 0.05,
      damping: 0.4,
    }},
    stabilization: {{ iterations: 200, updateInterval: 25 }},
  }},
  interaction: {{
    hover: true,
    tooltipDelay: 150,
    navigationButtons: false,
    keyboard: true,
  }},
  nodes: {{
    shape: 'dot',
    borderWidth: 1.5,
    shadow: {{ enabled: true, color: 'rgba(0,0,0,0.5)', size: 8, x: 2, y: 2 }},
  }},
  edges: {{
    smooth: {{ type: 'continuous', roundness: 0.2 }},
    shadow: false,
  }},
}};

const network = new vis.Network(container, {{ nodes, edges }}, options);

network.once('stabilizationIterationsDone', () => {{
  document.getElementById('loading').style.display = 'none';
}});
// Safety fallback
setTimeout(() => {{ document.getElementById('loading').style.display = 'none'; }}, 5000);

// ── Selection & highlighting ──────────────────────────────────────────────────
let selectedModule = null;
let currentTab = 'imports';
let physicsOn = true;

function highlightNeighbours(fullName) {{
  const directImports   = new Set(ADJACENCY[fullName]?.imports   || []);
  const directImportedBy = new Set(ADJACENCY[fullName]?.imported_by || []);
  const related = new Set([fullName, ...directImports, ...directImportedBy]);

  nodes.forEach(n => {{
    const isSelf    = n.full === fullName;
    const isImport  = directImports.has(n.full);
    const isImportedBy = directImportedBy.has(n.full);
    const isRelated = related.has(n.full);

    let border = n.kind === 'external' ? '#2ecc71' : '#4a7fd4';
    let bg     = n.kind === 'external' ? '#1e3a2f' : '#1a2540';
    let opacity = isRelated ? 1 : 0.12;
    let size    = n.size;

    if (isSelf)        {{ border = '#ffffff'; bg = '#2a3f6a'; size = n.size + 6; }}
    else if (isImport) {{ border = '#4a7fd4'; bg = '#1f2f4f'; }}
    else if (isImportedBy) {{ border = '#e09020'; bg = '#3a2a10'; }}

    nodes.update({{
      id: n.id,
      color: {{ background: bg, border, opacity }},
      size,
      opacity,
    }});
  }});

  edges.forEach(e => {{
    const srcFull = idToFull[e.from];
    const dstFull = idToFull[e.to];
    const active  = srcFull === fullName || dstFull === fullName;
    edges.update({{
      id: e.id,
      color: {{ color: active ? '#4a7fd4' : '#111827', opacity: active ? 1 : 0.08 }},
      width: active ? 2 : 1,
    }});
  }});
}}

function resetHighlight() {{
  nodes.forEach(n => {{
    const border = n.kind === 'external' ? '#2ecc71' : '#4a7fd4';
    const bg     = n.kind === 'external' ? '#1e3a2f' : '#1a2540';
    nodes.update({{ id: n.id, color: {{ background: bg, border }}, opacity: 1, size: n.size }});
  }});
  edges.forEach(e => {{
    edges.update({{ id: e.id, color: {{ color: '#2a3a5c', opacity: 0.7 }}, width: 1 }});
  }});
}}

function selectModule(fullName) {{
  selectedModule = fullName;
  highlightNeighbours(fullName);
  showSidebar(fullName);
}}

function resetSelection() {{
  selectedModule = null;
  resetHighlight();
  document.getElementById('sidebar-empty').style.display  = 'flex';
  document.getElementById('sidebar-content').style.display = 'none';
}}

network.on('click', params => {{
  if (params.nodes.length > 0) {{
    const fullName = idToFull[params.nodes[0]];
    selectModule(fullName);
  }} else {{
    resetSelection();
  }}
}});

// ── Sidebar ───────────────────────────────────────────────────────────────────
function showSidebar(fullName) {{
  const adj  = ADJACENCY[fullName] || {{ imports: [], imported_by: [] }};
  const nodeData = NODES_DATA.find(n => n.full === fullName);
  const kind = nodeData?.kind || 'local';

  document.getElementById('sidebar-empty').style.display   = 'none';
  document.getElementById('sidebar-content').style.display = 'flex';

  const kindLabel = kind === 'external' ? 'external' : 'local';
  const kindClass = kind === 'external' ? 'kind-external' : 'kind-local';
  document.getElementById('mod-name').innerHTML =
    `<div class="mod-kind ${{kindClass}}">${{kindLabel}}</div>${{fullName}}`;

  document.getElementById('stat-imports').textContent    = adj.imports.length;
  document.getElementById('stat-importedby').textContent = adj.imported_by.length;

  renderDepList(currentTab === 'imports' ? adj.imports : adj.imported_by);
}}

function switchTab(tab) {{
  currentTab = tab;
  document.getElementById('tab-imports').classList.toggle('active', tab === 'imports');
  document.getElementById('tab-importedby').classList.toggle('active', tab === 'importedby');
  if (selectedModule) {{
    const adj = ADJACENCY[selectedModule] || {{ imports: [], imported_by: [] }};
    renderDepList(tab === 'imports' ? adj.imports : adj.imported_by);
  }}
}}

function renderDepList(items) {{
  const list = document.getElementById('dep-list');
  if (!items.length) {{
    list.innerHTML = '<div class="dep-empty">None</div>';
    return;
  }}
  list.innerHTML = items.map(full => {{
    const parts = full.split('.');
    const short = parts[parts.length - 1];
    const ns    = parts.slice(0, -1).join('.');
    const isExt = !fullToId.hasOwnProperty(full) ||
                  (NODES_DATA.find(n => n.full === full)?.kind === 'external');
    const extTag = isExt ? '<span class="dep-ext">[ext]</span>' : '';
    return `<div class="dep-item" onclick="jumpTo('${{full}}')">
      <span class="dep-short">${{short}}</span>
      ${{extTag}}
      <span class="dep-ns">${{ns}}</span>
    </div>`;
  }}).join('');
}}

function jumpTo(fullName) {{
  const id = fullToId[fullName];
  if (id === undefined) return;
  network.focus(id, {{ scale: 1.4, animation: {{ duration: 500, easingFunction: 'easeInOutQuad' }} }});
  network.selectNodes([id]);
  selectModule(fullName);
}}

// ── Controls ──────────────────────────────────────────────────────────────────
function togglePhysics() {{
  physicsOn = !physicsOn;
  network.setOptions({{ physics: {{ enabled: physicsOn }} }});
  document.getElementById('btn-physics').classList.toggle('active', physicsOn);
}}

// ── Search ────────────────────────────────────────────────────────────────────
const searchInput   = document.getElementById('search');
const searchResults = document.getElementById('search-results');

searchInput.addEventListener('input', () => {{
  const q = searchInput.value.trim().toLowerCase();
  if (!q) {{ searchResults.style.display = 'none'; return; }}
  const matches = NODES_DATA.filter(n => n.full.toLowerCase().includes(q)).slice(0, 12);
  if (!matches.length) {{ searchResults.style.display = 'none'; return; }}
  searchResults.innerHTML = matches.map(n => {{
    const hi = n.full.replace(new RegExp(q, 'gi'), s => `<b style="color:var(--accent)">${{s}}</b>`);
    return `<div class="sr-item" onclick="jumpTo('${{n.full}}'); searchResults.style.display='none'; searchInput.value='';">
      <div>${{hi}}</div>
    </div>`;
  }}).join('');
  searchResults.style.display = 'block';
}});

document.addEventListener('click', e => {{
  if (!e.target.closest('#search-wrap')) searchResults.style.display = 'none';
}});
</script>
</body>
</html>"""


# ── ASCII tree ─────────────────────────────────────────────────────────────────

def ascii_tree(G: nx.DiGraph) -> None:
    imported_by_someone = {v for _, v in G.edges()}
    roots = sorted(n for n in G.nodes()
                   if n not in imported_by_someone and G.nodes[n].get("kind") == "local")
    if not roots:
        roots = sorted(n for n in G.nodes() if G.nodes[n].get("kind") == "local")[:1]

    BRANCH, LAST, PIPE, SPACE = "├── ", "└── ", "│   ", "    "

    def _draw(node, prefix="", visited=None, is_last=True):
        if visited is None:
            visited = set()
        print(prefix + (LAST if is_last else BRANCH) + node)
        cp = prefix + (SPACE if is_last else PIPE)
        if node in visited:
            print(cp + LAST + "(already expanded above)")
            return
        visited.add(node)
        children = sorted(G.successors(node))
        for i, child in enumerate(children):
            _draw(child, cp, visited, is_last=(i == len(children) - 1))
        visited.discard(node)

    for i, root in enumerate(roots):
        _draw(root, is_last=(i == len(roots) - 1))


# ── Main ───────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Generate an interactive HTML import graph for a Lean 4 project.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("project_root", nargs="?", default=".",
                        help="Path to the Lean project root (default: current directory)")
    parser.add_argument("--output", default="lean_imports.html", metavar="FILE",
                        help="Output HTML file (default: lean_imports.html)")
    parser.add_argument("--ascii", action="store_true",
                        help="Also print an ASCII tree to stdout")
    parser.add_argument("--no-browser", action="store_true",
                        help="Don't open the browser after generating")
    parser.add_argument("--ignore", action="append", default=[], metavar="MODULE",
                        help="Ignore modules with this prefix (repeatable)")
    parser.add_argument("--root", metavar="MODULE",
                        help="Only include modules reachable from this module")
    args = parser.parse_args()

    project_root = Path(args.project_root).resolve()
    if not project_root.is_dir():
        print(f"Error: {project_root} is not a directory.", file=sys.stderr)
        sys.exit(1)

    print(f"Scanning {project_root} …", file=sys.stderr)
    source_root, namespace = detect_source_root(project_root)

    if namespace:
        print(f"Detected namespace: {namespace}", file=sys.stderr)
    else:
        print(
            "Warning: could not read namespace from lakefile.lean / lakefile.toml.\n"
            "Module names may be wrong if the script is not run from the directory\n"
            "that directly contains your top-level namespace folder.",
            file=sys.stderr,
        )

    G = build_nx_graph(source_root, args.ignore)

    if args.root:
        G = filter_from_root(G, args.root)

    n_local = sum(1 for n in G.nodes() if G.nodes[n].get("kind") == "local")
    print(f"Found {n_local} local modules, {G.number_of_edges()} import edges.", file=sys.stderr)

    if args.ascii:
        print("\n── ASCII tree ──────────────────────────────")
        ascii_tree(G)
        print()

    html = build_html(G, project_root, namespace)
    out  = Path(args.output)
    out.write_text(html, encoding="utf-8")
    print(f"Written to {out.resolve()}", file=sys.stderr)

    if not args.no_browser:
        webbrowser.open(out.resolve().as_uri())


if __name__ == "__main__":
    main()
