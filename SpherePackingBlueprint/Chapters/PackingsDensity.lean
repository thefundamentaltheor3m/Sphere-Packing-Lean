import Verso
import VersoManual
import VersoBlueprint
import SpherePacking
import SpherePackingBlueprint.Macros

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Density of packings" =>

The definition of density given in the chapter on sphere packings is inconvenient to work with,
especially when our packing is a structured one, such as a periodic/lattice packing. This section
fixes this problem.

Note that some of the proofs in this section have only been sketched. The finer details are
formalised in Lean.

Observe that the finite density evaluated at some $`R > 0` measures the density of sphere packings
within a bounded, open ball of radius $`R`. As one might expect, there is a relationship between
the finite density and the number of centers in the ball of radius $`R`.

:::lemma_ "lemma:sp-finite-density-bound" (lean := "SpherePacking.finiteDensity_le, SpherePacking.finiteDensity_ge") (uses := "SpherePacking.finiteDensity")
For any $`R > 0`,
$$`\left|X \cap \mathcal{B}_d\left(R - \frac{r}{2}\right)\right| \cdot \frac{\mathrm{Vol}\left(\mathcal{B}_d\left(\frac{r}{2}\right)\right)}{\mathrm{Vol}(\mathcal{B}_d(R))} \leq \Delta_{\mathcal{P}}(R) \leq \left|X \cap \mathcal{B}_d\left(R + \frac{r}{2}\right)\right| \cdot \frac{\mathrm{Vol}\left(\mathcal{B}_d\left(\frac{r}{2}\right)\right)}{\mathrm{Vol}(\mathcal{B}_d(R))}`
:::

:::proof "lemma:sp-finite-density-bound" (uses := "SpherePacking")
The high level idea is to prove that
$`\mathcal{P} \cap \mathcal{B}_d(R) = \left(\bigcup_{x \in X} \mathcal{B}_d\left(x, \frac{r}{2}\right)\right) \subseteq \bigcup_{x \in X \cap \mathcal{B}_d\left(R + \frac{r}{2}\right)} \mathcal{B}_d\left(x, \frac{r}{2}\right)`,
and a similar inequality for the upper bound. The rest follows by rearranging and using the fact
that the balls are pairwise disjoint.
:::

Suppose further that $`X` is a periodic packing w.r.t. the lattice $`\Lambda \subseteq \R^d`. Let
$`\mathcal{D}` be a (bounded) fundamental region of $`\Lambda`, say the parallelopiped
$`[0, 1]^n\Lambda`, and let $`L` be the bound on the norm of vectors in $`\mathcal{D}`, i.e. a
number satisfying $`\forall x \in \mathcal{D}, \|x\| \leq L`.

:::lemma_ "lemma:lattice-points-bound" (lean := "PeriodicSpherePacking.aux2_ge', PeriodicSpherePacking.aux2_le'")
For all $`R`, we have the following inequality relating the number of lattice points from
$`\Lambda` in a ball with the volume of the ball and the fundamental region $`\mathcal{D}`:

$$`\frac{\mathrm{Vol}(\mathcal{B}_d(R - L))}{\mathrm{Vol}(\mathcal{D})} \leq \left|\Lambda \cap \mathcal{B}_d(R)\right| \leq \frac{\mathrm{Vol}(\mathcal{B}_d(R + L))}{\mathrm{Vol}(\mathcal{D})}`
:::

:::proof "lemma:lattice-points-bound"
For the first inequality, it suffices to prove that
$`\mathcal{B}_d(R - L) \subseteq \bigcup_{x \in \Lambda \cap \mathcal{B}_d(R)} (x + \mathcal{D})`,
since the cosets on the right are disjoint. For a vector $`v \in \mathcal{B}_d(R - L)`, we have
$`\|v\| < R - L` by definition. Since $`\mathcal{D}` is a fundamental domain, there exists a
lattice point $`x \in \Lambda` such that $`v \in x + \mathcal{D}`. Rearranging gives
$`v - x \in \mathcal{D}`, which means $`\|v - x\| \leq L`. By the triangle inequality,
$`\|x\| < R`, i.e. $`x \in \mathcal{B}_d(L)`, concluding the proof.

For the second inequality, we prove that
$`\bigcup_{x \in \Lambda \cap \mathcal{B}_d(R)} (x + \mathcal{D}) \subseteq \mathcal{B}_d(R + L)`.
Consider a vector $`x \in \Lambda \cap \mathcal{B}_d(R)` and a vector $`y \in x + \mathcal{D}`.
From above, we know $`\|x\| < R` and $`\|y - x\| \leq L`, so $`\|y\| < R + L`, concluding the
proof.
:::

To link {bpref "lemma:sp-finite-density-bound"}[] and {bpref "lemma:lattice-points-bound"}[], we
need a lemma relating $`|\Lambda \cap \mathcal{B}|` with $`|X \cap \mathcal{B}|`, which is what the
following lemma does:

:::lemma_ "lemma:periodic-points-bounds" (lean := "PeriodicSpherePacking.aux_ge, PeriodicSpherePacking.aux_le")
For all $`R`, we have the following inequality relating the number of points from $`X` (periodic
w.r.t. $`\Lambda`) in a ball with the number of points from $`\Lambda`:
$$`\left|\Lambda \cap \mathcal{B}_d(R - L)\right|\left|X / \Lambda\right| \leq \left|X \cap \mathcal{B}_d(R)\right| \leq \left|\Lambda \cap \mathcal{B}_d(R + L)\right|\left|X / \Lambda\right|`
:::

:::proof "lemma:periodic-points-bounds"
For the first inequality, we notice that
$`\bigcup_{x \in \Lambda \cap \mathcal{B}_d(R - L)} (x + \mathcal{D}) \subseteq \mathcal{B}_d(R)`,
because for $`x \in \Lambda \cap \mathcal{B}_d(R - L)` and $`y \in x + \mathcal{D}`, we have
$`\|x\| < R - L` and $`\|y - x\| \leq L`, so $`\|y\| < R` by triangle inequality. Intersecting
both sides with $`X` and simplifying, we have

$$`\left(\bigcup_{x \in \Lambda \cap \mathcal{B}_d(R - L)} (x + \mathcal{D})\right) \cap X = \bigcup_{x \in \Lambda \cap \mathcal{B}_d(R - L)} ((x + \mathcal{D}) \cap X) \subseteq \mathcal{B}_d(R) \cap X`

Consider the (finite) cardinality on both sides and noting that
$`|(x + \mathcal{D}) \cap X| = |X / \Lambda|` for all $`x`, we see that
$`|\Lambda \cap \mathcal{B}_d(R - L)||X / \Lambda| \leq |X \cap \mathcal{B}_d(R)|`, as desired.

The proof of the second inequality is similar. We again observe that
$`\mathcal{B}_d(R) \subseteq \bigcup_{x \in \Lambda \cap \mathcal{B}_d(R + L)} (x + \mathcal{D})`,
which follows from the tiling property of fundamental domain (i.e. every point can be translated by
a $`\Lambda` lattice point into $`\mathcal{D}`). Intersecting both sides with $`X` and considering
cardinality of both sides concludes the proof.

There are several technicalities when formalising in Lean, such as having to prove
$`|\Lambda \cap \mathcal{B}_d(R)|` is countable and finite. Those are handled at `aux3`.
:::

When we combine the inequalities above, we need one additional computational lemma.

:::lemma_ "lemma:volume-ball-ratio-limit" (lean := "volume_ball_ratio_tendsto_nhds_one''")
For any constant $`C > 0`, we have

$$`\lim_{R \to \infty} \frac{\mathrm{Vol}(\mathcal{B}_d(R))}{\mathrm{Vol}(\mathcal{B}_d(R + C))} = 1`
:::

:::proof "lemma:volume-ball-ratio-limit"
Write out the formula for volume of a ball and simplify. More specifically, we have
$`\mathrm{Vol}(\mathcal{B}_d(R)) = R^d \pi^{d / 2} / \Gamma\left(\frac{d}{2} + 1\right)`, so
$`\mathrm{Vol}(\mathcal{B}_d(R)) / \mathrm{Vol}(\mathcal{B}_d(R + C)) = R^d / (R + C)^d = \left(1 - \frac{1}{R + C}\right)^d = 1`.
:::

Finally, we can relate the density of a periodic sphere packing to the natural definition of
density given by any of its fundamental domain:

:::theorem "theorem:psp-density" (lean := "PeriodicSpherePacking.density_eq") (uses := "SpherePacking.density")
For a periodic sphere packing $`\mathcal{P} = \mathcal{P}(X)` with centers $`X` periodic to the
lattice $`\Lambda` and separation $`r`,

$$`\Delta_{\mathcal{P}} = |X / \Lambda| \cdot \frac{\Vol{\mathcal{B}_d(r / 2)}}{\Vol{\R^d / \Lambda}}`
:::

:::proof "theorem:psp-density" (uses := "lemma:sp-finite-density-bound, lemma:lattice-points-bound, lemma:periodic-points-bounds, lemma:volume-ball-ratio-limit")
Fix any fundamental domain $`\mathcal{D}` (induced by any basis) of the lattice $`\Lambda`.
Combining {bpref "lemma:sp-finite-density-bound"}[], {bpref "lemma:lattice-points-bound"}[] and
{bpref "lemma:periodic-points-bounds"}[], we get the following inequality for the *finite* density:

$$`|X / \Lambda| \cdot \frac{\Vol{\mathcal{B}_d(r / 2)}}{\Vol{\R^d / \Lambda}} \cdot \frac{\Vol{\mathcal{B}_d(R - r / 2 - 2L)}}{\Vol{\mathcal{B}_d(R)}} \leq \Delta_{\mathcal{P}}(R) \leq |X / \Lambda| \cdot \frac{\Vol{\mathcal{B}_d(r / 2)}}{\Vol{\R^d / \Lambda}} \cdot \frac{\Vol{\mathcal{B}_d(R + r / 2 + 2L)}}{\Vol{\mathcal{B}_d(R)}}`

Taking limit on both sides as $`R \to \infty` and apply the Sandwich theorem and
{bpref "lemma:volume-ball-ratio-limit"}[], we get

$$`\Delta_{\mathcal{P}} = \limsup_{R \to \infty} \Delta_{\mathcal{P}}(R) = \lim_{R \to \infty} \Delta_{\mathcal{P}}(R) = |X / \Lambda| \cdot \frac{\Vol{\mathcal{B}_d(r / 2)}}{\Vol{\R^d / \Lambda}}`
:::
