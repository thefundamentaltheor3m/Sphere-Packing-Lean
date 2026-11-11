import Verso
import VersoManual
import VersoBlueprint
import SpherePacking
import SpherePackingBlueprint.Macros

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Cohn–Elkies linear programming bounds" =>

In 2003 Cohn and Elkies \[ElkiesCohn\] developed linear programming bounds that apply directly to
sphere packings. The goal of this section is to formalize the Cohn–Elkies linear programming
bound.

The following theorem is the key result of \[ElkiesCohn\]. (Note that the original theorem is
stated for a class of functions more general then Schwartz functions.)

:::theorem "thm:Cohn-Elkies-periodic" (lean := "LinearProgrammingBound'") (uses := "def:Fourier-Transform, SpherePacking.density")
*(Cohn–Elkies \[ElkiesCohn\])*

Let $`X\subset\mathbb{R}^d` be a discrete subset such that $`\|x-y\|\geq 1` for any distinct
$`x,y\in X`. Suppose that $`X` is $`\Lambda`-periodic with respect to some lattice
$`\Lambda\subset\mathbb{R}^d`. Let $`f:\R^d\to\R` be a Schwartz function that is not identically
zero and satisfies the following conditions:
$$`f(x)\leq 0\text{ for } \|x\|\geq 1 \tag{5.1}`
and
$$`\widehat{f}(x)\geq0\text{ for all } x\in\R^d. \tag{5.2}`
Then the density of any $`\Lambda`-periodic sphere packing is bounded above by
$$`\frac{f(0)}{\widehat{f}(0)}\cdot \mathrm{vol}(B_d(0,1/2)).`
:::

:::proof "thm:Cohn-Elkies-periodic" (uses := "thm:Poisson-summation-formula")
Here we reproduce the proof given in \[ElkiesCohn\].

The inequality
$$`\sharp (X/\Lambda)\cdot f(0)\geq \sum_{x\in X}\sum_{y\in X/\Lambda}f(x-y)=\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\sum_{\ell\in  \Lambda}f(x-y+l) \tag{5.3}`
follows from the condition (5.1) of the theorem and the assumption on the distances between points
in $`X`. The equality
$$`\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\sum_{\ell\in  \Lambda}f(x-y+l)=\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\,e^{2\pi i m(x-y)}.`
follows from the Poisson summation formula. The right hand side of the above equation can be
written as
$$`\sum_{x\in X/\Lambda}\sum_{y\in X/\Lambda}\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\,e^{2\pi i m(x-y)}=\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\cdot\big|\sum_{x\in X/\Lambda}e^{2\pi i m x}\big|^2.`
Note that $`\big|\sum_{x\in X/\Lambda}e^{2\pi i m x}\big|^2\geq0` for all $`m\in\Lambda^*`.
Moreover, the term corresponding to $`m=0` satisfies
$`\big|\sum_{x\in X/\Lambda}e^{2\pi i 0 x}\big|^2=\sharp (X/\Lambda)^2`. Now we use the condition
(5.2) and estimate
$$`\frac{1}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\,\sum_{m\in \Lambda^*} \widehat{f}(m)\cdot\big|\sum_{x\in X/\Lambda}e^{2\pi i m(x-y)}\big|^2 \geq \frac{\sharp (X/\Lambda)^2}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\cdot \widehat{f}(0). \tag{5.4}`
Comparing inequalities (5.3) and (5.4) we arrive at
$$`\frac{\sharp (X/\Lambda)}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\leq \frac{f(0)}{\widehat{f}(0)}.`
Now we see that the density of the periodic packing $`\mathcal{P}_X` with balls of radius
$`1/2` is bounded by
$$`\Delta(\mathcal{P}_X)=\frac{\sharp (X/\Lambda)}{\mathrm{vol}(\mathbb{R}^d/\Lambda)}\cdot{\mathrm{vol}(B_d(0,1/2))}\leq \frac{f(0)}{\widehat{f}(0)}\cdot \mathrm{vol}(B_d(0,1/2)).`
This finishes the proof of the theorem for periodic packings.
:::

:::theorem "thm:Cohn-Elkies-general" (lean := "LinearProgrammingBound")
*(Cohn–Elkies \[ElkiesCohn\])*

Let $`f:\R^d\to\R` be a Schwartz function that is not identically zero and satisfies (5.1) and
(5.2). Then the density of any $`\Lambda`-periodic sphere packing is bounded above by
$$`\frac{f(0)}{\widehat{f}(0)}\cdot \mathrm{vol}(B_d(0,1/2)).`
:::

:::proof "thm:Cohn-Elkies-general" (lean := "periodic_constant_eq_constant, periodic_constant_eq_periodic_constant_normalized") (uses := "thm:Cohn-Elkies-periodic, thm:periodic-packing-optimal")
The result follows immediately from {bpref "thm:periodic-packing-optimal"}[] and
{bpref "thm:Cohn-Elkies-periodic"}[].
:::

# The Shape of an Optimal Function

The main step in our proof of {bpref "MainTheorem"}[] is the explicit construction of an optimal
function for $`d = 8`. Before stating what we shall prove, we record what *optimality* forces upon
such a function; this analysis, which follows the discussion in \[CohnICM, p. 8\], dictates the
entire construction of the section “Fourier eigenfunctions with double zeroes at lattice points”.

Suppose $`f` is a Schwartz function satisfying (5.1) and (5.2) whose bound in
{bpref "thm:Cohn-Elkies-periodic"}[] is attained by some $`\Lambda`-periodic packing with centres
$`X`. Then every inequality in the proof of {bpref "thm:Cohn-Elkies-periodic"}[] must be an
equality. Equality in (5.3) forces $`f(x - y) = 0` for all distinct $`x \in X`,
$`y \in X/\Lambda`; when $`X = \Lambda`, this says that *$`f` vanishes at all non-zero lattice
points*. Moreover, $`f(0) \geq 0` (else the bound would be negative), so (5.1) forces these
vanishing points of norm $`\geq 1` to be *double* zeroes of the radial profile of $`f`: a sign
change there would contradict $`f \leq 0` on $`\{\|x\| \geq 1\}`. Finally, equality in (5.4)
forces $`\widehat{f}(m) = 0` for all non-zero $`m \in \Lambda^*`; for $`\Lambda = \Lambda_8`,
which is self-dual, these are the same points again.

Since the conditions (5.1) and (5.2) depend only on $`\norm{x}`, we may restrict our search to
*radial* functions ({bpref "def:radial-function"}[]), and by
{bpref "lemma:eigenfunction-decomposition"}[] it suffices to construct a $`+1`- and a
$`-1`-eigenfunction of the Fourier transform, each with (double) zeroes at the appropriate lattice
points, and take a suitable linear combination.

It will be convenient to work at the scale of $`\Lambda_8` itself, whose non-zero vectors have
norms $`\sqrt{2n}`, $`n \geq 1`, rather than rescaling the lattice to separation $`1`. We
therefore aim for the following.

:::theorem "thm:g" (uses := "thm:g1")
There exists a radial Schwartz function $`g:\R^8\to\R` which satisfies:
$$`g(x)\leq 0\text{ for } \|x\|\geq \sqrt{2} \tag{5.5}`
$$`\widehat{g}(x)\geq0\text{ for all } x\in\R^8 \tag{5.6}`
$$`g(0)=\widehat{g}(0)=1. \tag{5.7}`
:::

{bpref "thm:Cohn-Elkies-general"}[] applied to the rescaled function $`f(x):=g(\sqrt{2}\, x)`,
which satisfies (5.1) and (5.2) with $`f(0)/\widehat{f}(0) = 16\, g(0)/\widehat{g}(0) = 16`,
immediately implies {bpref "MainTheorem"}[]: recalling that
$`\Vol{B_{2k}(0, r)} = r^{2k}\pi^k/k!` (a fact already available in Mathlib), the resulting bound
is
$$`16 \cdot \Vol{B_8(0, 1/2)} = 16 \cdot \frac{1}{2^8}\cdot\frac{\pi^4}{24} = \frac{\pi^4}{384},`
which is precisely the density of the $`E_8` packing. In general the bound is
$`g(0)/\widehat{g}(0)` times this density, so it is sharp precisely because of the normalisation
(5.7): an optimal $`g` must satisfy $`g(0) = \widehat{g}(0)`.
