# Mathlib PR-overlap report: `CoordCube.lean`

*Prepared June 2026. PR data verified directly against the GitHub REST API; `gh` was unavailable in
the build environment.*

## What this file contributes

`SpherePacking/ForMathlib/CoordCube.lean` packages the scaled integer lattice `L·ℤ^d` and its
coordinate cube in `EuclideanSpace ℝ (Fin d)`:

- `cubeIco d L = [0,L)^d` (the fundamental domain) and `cubeIcc d L r = [r,L−r]^d` (the
  boundary-safe core), with membership/preimage API;
- the scaled standard basis `cubeBasis d L hL` (via `Basis.isUnitSMul`) and the lattice
  `cubeLattice d L hL = span ℤ (range (cubeBasis …))`, with `DiscreteTopology`/`IsZLattice`
  instances;
- the geometry/measure: `cubeIco` is the fundamental domain of `cubeBasis`
  (`fundamentalDomain_cubeBasis_eq_cubeIco`), unique covering, boundedness, volumes `L^d` and
  `(L−2r)^d`, and finiteness of lattice points in a ball.

It is the period-lattice/fundamental-domain machinery of the cube sphere packing used by the
Cohn–Elkies density approximation in `LPBound.lean`.

## Relationship to existing Mathlib (`ZSpan`)

The generic lattice facts here are **thin specialisations of Mathlib's `ZSpan` API** for an arbitrary
basis (`Mathlib/Algebra/Module/ZLattice/Basic.lean`): `fundamentalDomain` (line 92),
`fundamentalDomain_isBounded` (248), `exist_unique_vadd_mem_fundamentalDomain` (261),
`setFinite_inter` (331), `measure_fundamentalDomain`/`volume_fundamentalDomain` (372/388),
`isAddFundamentalDomain` (353). Indeed `cubeIco d L` *is* `ZSpan.fundamentalDomain (cubeBasis d L hL)`
(proved here), and our unique-covering / boundedness / finiteness lemmas are already one-line
delegations to the corresponding `ZSpan` lemmas.

What is **irreducibly cube-specific** is only:

1. the explicit coordinate cube `[0,L)^d` and inner cube `[r,L−r]^d` (coordinate access, needed for
   the LP boundary analysis);
2. the explicit volumes `L^d` and `(L−2r)^d`, and the boundary-shell asymptotics
   `((L+1)^d − (L−2)^d)/L^d → 0`.

This is the answer to the natural "why so much for `L·ℤ^n`?" question: the *counting / fundamental
domain* content is generic (and should ultimately be consumed from `ZSpan` directly, not re-derived),
while the *boundary geometry* genuinely requires the cube — see the "Two missing Mathlib lemmas"
section below.

## Adjacent open PRs (`Algebra/Module/ZLattice`)

Two open PRs touch the same fundamental-domain / `ZSpan` area:

- **#10345 — "feat(Algebra.Module.Zlattice): Add Voronoi Domain"** —
  <https://github.com/leanprover-community/mathlib4/pull/10345> (author **newell**, open). A Voronoi
  domain is an alternative fundamental domain of a lattice. This is the closest neighbour: it
  develops fundamental-domain theory for lattices and is the place where a *general* (non-cube)
  fundamental-domain volume/boundary API would most naturally live.
- **#33746 — "feat(Algebra/Module/ZLattice): align `ZSpan.floor` to `Int.floor` API"** —
  <https://github.com/leanprover-community/mathlib4/pull/33746> (author **ster-oc**, open). API
  alignment on the `ZSpan.floor`/`fract` functions underlying `fundamentalDomain`. Worth tracking so
  any cube lemmas we upstream use the post-alignment names.

No open PR adds a scaled-integer-lattice cube or its volume specifically; that part is uncontested.

## Two missing Mathlib lemmas (future contributions)

A planned general-basis refactor of `LPBound.lean` showed that the cube cannot be eliminated from the
density argument without two lemmas that **do not currently exist in Mathlib**. Both are natural
additions to `Mathlib/Algebra/Module/ZLattice/` (and would also serve PR #10345's Voronoi-domain
theory):

1. **`ZSpan.ball_subset_fundamentalDomain_of_mem_inner`** — an inradius / boundary-safe inner core:
   for a basis `b` and radius `r`, a suitable inner region of `fundamentalDomain b` has the property
   that a Euclidean ball of radius `r` around any of its points stays inside the fundamental
   parallelepiped. For a non-orthogonal basis this inner core is *not* a coordinate shrink (it depends
   on the dual-basis norms / parallelepiped inradius), which is why the cube case is currently special.
2. **`ZSpan.tendsto_volume_boundaryThickening_div_volume_fundamentalDomain_zero`** — a Minkowski-content
   statement: the relative volume of the `r`-thickening of the fundamental-domain boundary vanishes
   under lattice homothety (`t → ∞`), because the boundary thickening scales like `t^{d−1}` and the
   cell like `t^d`. The cube proof replaces this with the explicit algebraic identity
   `(L+1)^d − (L−2)^d` over `L^d`.

These are recorded as TODOs in the module docstring of `CoordCube.lean`.

## Collaboration avenues

1. **Coordinate the general fundamental-domain volume/boundary API with PR #10345.** The two missing
   lemmas above belong in the same Voronoi/fundamental-domain development; offering them as additions
   to (or a follow-up of) #10345 avoids fragmenting the lattice-geometry API.
2. **Upstream only the genuinely cube-specific content** — the scaled basis `cubeBasis`, the
   identification `cubeIco = fundamentalDomain (cubeBasis …)`, and the explicit volumes — into
   `Mathlib/Algebra/Module/ZLattice/`, consuming `ZSpan` for everything generic rather than
   re-deriving it.
3. **Track #33746** for the `ZSpan.floor`/`fract` naming so the upstreamed cube lemmas match.

## Recommendation

Most of this file is `ZSpan` plumbing and should not be upstreamed as-is; only the scaled cube and
its volumes are new. The higher-value contribution is the **two missing general lemmas**, ideally
coordinated with the Voronoi-domain PR #10345.

**Upstream target:** `Mathlib/Algebra/Module/ZLattice/` (scaled-cube specialisation + the two general
boundary lemmas).
