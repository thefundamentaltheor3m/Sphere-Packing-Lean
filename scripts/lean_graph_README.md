# Generate an Interactive Import Tree

One dependency: `networkx` (used for graph analysis — cycle detection, subgraph filtering, degree calculation). Install it with:

```pip install -r requirements.txt```

The `vis.js` graph library is loaded from a CDN in your browser when you open the HTML, so nothing else needs installing.

## Usage

Basic — generates lean_imports.html and opens it in your browser
```python lean_graph.py ~/my-lean-project```

Custom output path, also print ASCII tree

```python lean_graph.py ~/my-lean-project --output graph.html --ascii```

Only show modules reachable from one root

```python lean_graph.py . --root MyProject.Algebra```

Exclude external libraries from the graph

```python lean_graph.py . --ignore Mathlib --ignore Init```

Skip auto-opening the browser

```python lean_graph.py . --no-browser```

What the interactive graph gives you

* Click any node to highlight its direct imports (blue) and the modules that import it (orange), dimming everything else. The sidebar shows the full lists.
* Click items in the sidebar to jump to that module in the graph.
* Search box (top right) for instant filtering across all module names.
* Physics toggle to freeze the layout once you've arranged it.
* Fit to screen button to zoom back out.
* Nodes are sized by how many things import them — heavily-used modules appear larger.
* Local modules are blue, external dependencies (Mathlib etc.) are green.
