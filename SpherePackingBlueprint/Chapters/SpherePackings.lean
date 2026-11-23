import Verso
import VersoManual
import VersoBlueprint
import SpherePacking
import SpherePackingBlueprint.Macros

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Sphere packings" =>

The Sphere Packing problem is a classic optimisation problem with widespread applications that go
well beyond mathematics. The task is to determine the “densest” possible arrangement of spheres in
a given space. It remains unsolved in all but finitely many dimensions.

It was famously determined, in \[Via2017\], that the optimal arrangement in $`\mathbb{R}^8` is
given by the $`E_8` lattice. The result is strongly dependent on the Cohn-Elkies linear
programming bound (Theorem 3.1 in \[ElkiesCohn\]), which, if a $`\R^d \to \R` function satisfying
certain conditions exists, bounds the optimal density of sphere packings in $`\R^d` in terms of it.
The proof in \[Via2017\] uses the theory of modular forms to construct a function that can be used
to bound the density of all sphere packings in $`\R^8` above by the density of the $`E_8` lattice
packing. This then allows us to conclude that no packing in $`\R^8` can be denser than the $`E_8`
lattice packing.

# The Setup

This subsection gives an overview for the setup of the problem, both informally and in Lean.
Throughout this blueprint, $`\R^d` will denote the Euclidean vector space equipped with distance
$`\|\cdot\|` and Lebesgue measure $`\mathrm{Vol}(\cdot)`. For any $`x\in\R^d` and
$`r\in\R_{>0}`, we denote by $`B_d(x,r)` the open ball in $`\R^d` with center $`x` and radius
$`r`. While we will give a more formal definition of a sphere packing below (and in Lean), the
underlying idea is that it is a union of balls of equal radius centred at points that are far
enough from each other that the balls do not overlap.

Arguably the most important definition in this subsection is that of *packing density*, which
measures which portion of $`d`-dimensional Euclidean space is covered by a given sphere packing.
Taking the supremum over all packings gives what we refer to as the *sphere packing constant*,
which is the quantity we are interested in optimising.

:::definition "SpherePacking.balls" (lean := "SpherePacking.balls")
Given a set $`X \subset \R^d` and a real number $`r > 0` (known as the *separation radius*) such
that $`\|x - y\| \geq r` for all distinct $`x, y \in X`, we define the *sphere packing*
$`\Pa(X)` with centres at $`X` to be the union of all open balls of radius $`r` centred at points
in $`X`:
$$`\Pa(X) := \bigcup_{x \in X} B_d(x, r)`
:::

:::definition "SpherePacking" (lean := "SpherePacking")
Note that a sphere packing is uniquely defined from a given set of centres (which, in order to be a
valid set of centres, must admit a corresponding separation radius). Therefore, as a conscious
choice during the formalisation process, we will define everything that depends on sphere packings
in terms of `SpherePacking`, a `structure` that bundles all the identifying information of a
packing, but not the actual balls themselves. For the purposes of this blueprint, however, we will
refrain from making this distinction.
:::

We now define a notion of density for bounded regions of space by considering the density inside
balls of finite radius.

:::definition "SpherePacking.finiteDensity" (lean := "SpherePacking.finiteDensity") (uses := "SpherePacking, SpherePacking.balls")
The *finite density* of a packing $`\mathcal{P}` is defined as
$$`\Delta_{\mathcal{P}}(R):=\frac{\mathrm{Vol}(\mathcal{P}\cap B_d(0,R))}{\mathrm{Vol}(B_d(0,R))},\quad R>0.`
:::

As intuitive as it seems to take the density of a packing to be the limit of the finite densities
as the radius of the ball goes to infinity, it is not immediately clear that this limit exists.
Therefore, we define the density of a sphere packing as a limit superior instead.

:::definition "SpherePacking.density" (lean := "SpherePacking.density") (uses := "SpherePacking, SpherePacking.finiteDensity")
We define the *density* of a packing $`\mathcal{P}` as the limit superior
$$`\Delta_{\mathcal{P}}:=\limsup\limits_{R\to\infty}\Delta_{\mathcal{P}}(R).`
:::

We may now define the sphere packing constant, the quantity that the sphere packing problem
requires us to compute.

:::definition "SpherePackingConstant" (lean := "SpherePackingConstant") (uses := "SpherePacking.balls, SpherePacking.density")
The *sphere packing constant* is defined as supremum of packing densities over all possible
packings:
$$`\Delta_d:=\sup\limits_{\substack{\mathcal{P}\subset\R^d\\ \scriptscriptstyle\mathrm{sphere}\;\mathrm{packing}}}\Delta_{\mathcal{P}}.`
:::

# Scaling Sphere Packings

Given that the problem involves the *arrangement* of balls in space, it is intuitive not to worry
about the radius of the balls (so long as they are all equal to each other). However,
{bpref "SpherePacking.balls"}[] involves a choice of separation radius. In principle, we would want
two sphere packing configurations that differ only in separation radii to “encode the same
information”. In this brief subsection, we will describe how to change the separation radius of a
sphere packing by *scaling* the packing by a positive real number and prove that this does not
affect its density. This will give us the freedom to choose any separation radius we like when
attempting to define the optimal sphere packing in $`\R^d`.

:::definition "SpherePacking.scale" (lean := "SpherePacking.scale") (uses := "SpherePacking")
Given a sphere packing $`\Pa(X)` with separation radius $`r`, we defined the *scaled packing*
with respect to a real number $`c > 0` to be the packing $`\Pa(cX)`, where
$`cX = \setof{cx \in V}{x \in X}` has separation radius $`cr`.
:::

:::lemma_ "SpherePacking.scale_finiteDensity" (lean := "SpherePacking.scale_finiteDensity") (uses := "SpherePacking.finiteDensity, SpherePacking.scale")
Let $`\Pa(X)` be a sphere packing and $`c` a positive real number. Then, for all $`R > 0`,
$$`\Delta_{\Pa(cX)}(cR) = \Delta_{\Pa(X)}(R).`
:::

:::proof "SpherePacking.scale_finiteDensity"
The proof follows by direct computation:
$$`\Delta_{\Pa(cX)}(cR) = \frac{\Vol{\Pa(cX) \cap B_d(0, cR)}}{\Vol{B_d(0, cR)}} = \frac{c^d \cdot \Vol{\Pa(X) \cap B_d(0, R)}}{c^d \cdot \Vol{B_d(0, R)}} = \Delta_{\Pa(X)}(R)`
where the second equality follows from applying the fact that scaling a (measurable) set by a
factor of $`c` scales its volume by a factor of $`c^d` to the fact that
$`\Pa(cX) \cap B_d(0, cR) = c \cdot (\Pa(X) \cap B_d(0, cR))`.
:::

:::lemma_ "SpherePacking.scale_density" (lean := "SpherePacking.scale_density") (uses := "SpherePacking.scale")
Let $`\Pa(X)` be a sphere packing and $`c` a positive real number. Then, the density of the
scaled packing $`\Pa(cX)` is equal to the density of the original packing $`\Pa(X)`.
:::

:::proof "SpherePacking.scale_density" (uses := "SpherePacking.scale_finiteDensity")
One can show, using relatively unsophisticated real analysis, that
$$`\limsup_{R \to \infty} \Delta_{\Pa(cX)}(R) = \limsup_{cR \to \infty} \Delta_{\Pa(cX)}(cR)`
{bpref "SpherePacking.scale_finiteDensity"}[] tells us that
$`\Delta_{\Pa(cX)}(cR) = \Delta_{\Pa(X)}(R)` for every $`R > 0`. Therefore,
$$`\limsup_{cR \to \infty} \Delta_{\Pa(cX)}(cR) = \limsup_{cR \to \infty} \Delta_{\Pa(X)}(R) = \limsup_{R \to \infty} \Delta_{\Pa(X)}(R)`
where the second equality is the result of a similar change of variables to the one done above.
:::

Therefore, as expected, we do not need to worry about the separation radius when constructing
sphere packings. This will be useful when we attempt to construct the optimal sphere packing in
$`\R^8`—and even more so when attempting to *formalise* this construction—because the underlying
structure of the packing is given by a set known as the $`E_8` lattice, which has separation
radius $`\sqrt{2}`.

We can also use {bpref "SpherePacking.scale_density"}[] to simplify the computation of the sphere
packing constant by taking the supremum not over *all* sphere packings but only over those with
density $`1`.

:::lemma_ "SpherePacking.constant_eq_constant_normalized" (lean := "SpherePacking.constant_eq_constant_normalized") (uses := "SpherePackingConstant, SpherePacking.density")
$$`\Delta_d = \sup\limits_{\substack{\Pa \subset \R^d \\ \text{sphere packing} \\ \text{sep.~rad.} = 1}} \Delta_{\Pa}`
:::

:::proof "SpherePacking.constant_eq_constant_normalized" (uses := "SpherePacking.scale_density")
That the supremum over packings of unit density is at most the sphere packing constant is obvious.
For the reverse inequality, let $`\Pa(X)` be any sphere packing with separation radius $`r`. We
know, from {bpref "SpherePacking.scale_density"}[], that the density of $`\Pa(X)` is equal to that
of the scaled packing $`\Pa\!\left(\frac{X}{r}\right)`. Since the scaled packing has separation
radius $`1`, its density is naturally at most the supremum over all packings of unit density,
meaning that the same is true of $`\Pa(X)`.
:::

# Lattices and Periodic packings

We begin by defining what a lattice is in Euclidean space.

:::definition "IsZLattice" (lean := "IsZLattice")
We say that an additive subgroup $`\Lambda \leq \R^d` is a *lattice* if it is discrete and its
$`\R`-span contains all the elements of $`\R^d`.
:::

There is also a corresponding dual notion, which will become relevant when we start doing Fourier
analysis on functions over lattices.

:::definition "def:dual-lattice" (lean := "LinearMap.BilinForm.dualSubmodule")
The *dual lattice* of a lattice $`\Lambda` is the set
$$`\Lambda^* := \setof{v \in \R^d}{\forall l \in \Lambda, \left\langle v,l \right\rangle \in \Z}`
:::

We can now define periodic sphere packings.

:::definition "PeriodicSpherePacking" (lean := "PeriodicSpherePacking") (uses := "SpherePacking, IsZLattice")
We say that a sphere packing $`\Pa(X)` is ($`\Lambda`-)*periodic* if there exists a lattice
$`\Lambda \subset \R^d` such that for all $`x \in X` and $`y \in \Lambda`, $`x + y \in X` (ie,
$`X` is $`\Lambda`-periodic).
:::

There is a natural definition of density for periodic sphere packings, namely the “local” density
of balls in a fundamental domain. However, _a priori_ the density of sphere packing above need not
to coincide with this alternative definition. In {bpref "theorem:psp-density"}[], we will prove
that this is the case.

Now that we have simplified the process of computing the packing densities of specific packings, we
can simplify that of computing the sphere packing constant. It turns out that once again,
periodicity is key.

:::definition "def:Periodic-sphere-packing-constant" (lean := "PeriodicSpherePackingConstant") (uses := "SpherePacking.density, PeriodicSpherePacking")
The periodic sphere packing constant is defined to be
$$`\Delta_{d}^{\text{periodic}} := \sup_{\substack{P \subset \R^d \\ \text{periodic packing}}} \Delta_P`
:::

:::theorem "thm:periodic-packing-optimal" (lean := "periodic_constant_eq_constant") (uses := "SpherePacking.density, def:Periodic-sphere-packing-constant")
For all $`d`, the periodic sphere packing constant in $`\R^d` is equal to the sphere packing
constant in $`\R^d`.
:::

:::proof "thm:periodic-packing-optimal"
The following proof was written by Junyan Xu in the thread for
[Issue #80](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/issues/80) of the
repository.

Given an arbitrary packing $`P` of upper density $`\Delta` and an arbitrary $`\epsilon > 0`, we
want to produce a periodic packing with density at least $`\Delta - \epsilon`. Given a set $`S`
(of nonzero volume), we shall call the quantity $`\frac{\left| S \cap P \right|}{\left| S \right|}`
the density of $`P` in $`S`, where $`\left| S \right|` denotes the volume of $`S`.

Choose $`\ell > 0` such that
$$`\frac{(\ell - 4r)^d}{\ell^d} > 1 - \frac{\epsilon}{3}`
(where $`r` is the radius of the balls in $`P` and $`d` is the dimension). Then choose $`R_0 > 0`
such that for all $`R > R_0`, we have
$$`\frac{\left( R + \sqrt{d}\,\ell \right)^d - \left( R - \sqrt{d}\,\ell \right)^d}{R^d} < \frac{\epsilon}{3}`
By definition of upper density, there exists $`R > R_0` such that the density of $`P` in
$`B(0,R)` is at least $`\Delta - \frac{\epsilon}{3}`.

The Euclidean space is covered by disjoint hypercubes of side length $`\ell` of the form
$`\prod_{i=1}^d \left[ n_i\ell, (n_i+1)\ell \right)` with $`n_i \in \mathbb{Z}`. Since these
hypercubes have diameter $`\sqrt{d}\ell`, those that intersect $`B(0,R)` must be contained in
$`B(0,R+\sqrt{d}\ell)`. Thus the hypercubes contained in $`B(0,R+\sqrt{d}\ell)` cover
$`B(0,R)`. Similarly, the hypercubes not contained in $`B(0,R)` cannot intersect
$`B(0,R-\sqrt{d}\ell)`. Denote the union of hypercubes contained in $`B(0,R+\sqrt{d}\ell)` by
$`T` and the union of those contained in $`B(0,R)` by $`S`, we then have
$$`S \subseteq B(0,R) \subseteq T \subseteq B(0,R+\sqrt{d}\ell)`
and
$$`T \setminus S \subseteq B(0,R+\sqrt{d}\ell) \setminus B(0,R-\sqrt{d}\ell)`
The density of $`P` in $`S` is
$$`\begin{aligned} \frac{\left| S \cap P \right|}{\left| S \right|} &\ge \frac{\left| B(0,R) \cap P \right| - \left| B(0,R) \setminus S \right|}{\left| B(0,R) \right|} \\ &> \left( \Delta - \frac{\epsilon}{3} \right) - \frac{\left| T \setminus S \right|}{\left| B(0,R) \right|} \\ &> \left( \Delta - \frac{\epsilon}{3} \right) - \frac{\epsilon}{3} \end{aligned}`
Therefore, the density of $`P` in some hypercube $`C \subseteq S` is at least
$`\Delta - \frac{2\epsilon}{3}`. If a ball in $`P` (thus of diameter $`2r`) is not completely
contained in $`C`, it cannot intersect the hypercube $`C'` with the same center as $`C` with side
length $`\ell-4r`, so excluding these balls from $`C\cap P` decreases the density in $`C` by at
most
$`\frac{\left| C \setminus C' \right|}{\left| C \right|} = \frac{\ell^d - (\ell-4r)^d}{\ell^d} < \frac{\epsilon}{3}`,
and gives rise to a periodic packing of density $`> \Delta - \epsilon` with $`C` as a fundamental
domain.
:::

Thus, one can show a sphere packing to be optimal by showing its density to be equal to the
*periodic* sphere packing constant instead of the regular sphere packing constant. The
determination of the periodic constant is easier than that of the general constant, as we shall see
when investigating the Linear Programming bounds derived by Cohn and Elkies in \[ElkiesCohn\].

# Main Result

With the terminologies above, we can state the main theorem of this project.

:::theorem "theorem:CE_Main" (uses := "E8-Lattice, SpherePackingConstant, SpherePacking.density, E8Packing-density, thm:g, thm:Cohn-Elkies-general")
All *periodic* packing $`\mathcal{P} \subseteq \R^8` has density satisfying
$`\Delta_{\mathcal{P}} \leq \Delta_{E_8} = \frac{\pi^4}{384}`, the density of the $`E_8` sphere
packing (see {bpref "E8Packing"}[]).
:::

:::proof "theorem:CE_Main"
Directly follows from {bpref "thm:Cohn-Elkies-general"}[] applied to the function
$`f(x)=g(x/\sqrt{2})` of {bpref "thm:g"}[].
:::

:::corollary "corollary:upper-bound-E8" (uses := "thm:periodic-packing-optimal, theorem:CE_Main")
All packing $`\mathcal{P} \subseteq \R^8` has density satisfying
$`\Delta_{\mathcal{P}} \leq \Delta_{E_8}`.
:::

:::proof "corollary:upper-bound-E8"
This is a direct consequence of {bpref "thm:periodic-packing-optimal"}[] and
{bpref "theorem:CE_Main"}[].
:::

:::corollary "MainTheorem" (lean := "SpherePacking.MainTheorem") (uses := "corollary:upper-bound-E8")
$`\Delta_8 = \Delta_{E_8}`.
:::

:::proof "MainTheorem"
By definition, $`\Delta_{E_8} \leq \Delta_8`, while {bpref "corollary:upper-bound-E8"}[] shows
$`\Delta_8 = \sup_{\mathrm{packing} \, \mathcal{P}} \leq \Delta_{E_8}`, and the result follows.
:::
