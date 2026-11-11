import Verso
import VersoManual
import VersoBlueprint
import SpherePacking
import SpherePackingBlueprint.Macros

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Facts from Fourier analysis" =>

Recall the definition of a Fourier transform.

:::definition "def:Fourier-Transform" (lean := "FourierTransform.fourier")
The Fourier transform of an $`L^1`-function $`f:\R^d\to\C` is defined as

$$`\mathcal{F}(f)(y) = \widehat{f}(y) := \int_{\R^d} f(x)e^{-2\pi i \langle x, y \rangle} \,\mathrm{d}x, \quad y \in \R^d`

where $`\langle x, y \rangle = \frac12\|x\|^2 + \frac12\|y\|^2 - \frac12\|x - y\|^2` is the standard
scalar product in $`\R^d`.
:::

The following computational result will be of use later on.

:::lemma_ "lemma:Gaussian-Fourier" (lean := "fourier_gaussian_innerProductSpace") (uses := "def:Fourier-Transform")
For every $`z \in \h`, the Gaussian $`x \mapsto e^{\pi i \|x\|^2 z}` on $`\R^8` satisfies
$$`\mathcal{F}(e^{\pi i \|x\|^2 z})(y) = z^{-4}\,e^{\pi i \|y\|^2 \,(\frac{-1}{z}) }.`
:::

:::proof "lemma:Gaussian-Fourier"
Mathlib knows the Fourier transform of the Gaussian $`x \mapsto e^{-b\|x\|^2}` on a
$`d`-dimensional inner product space for any $`b \in \C` with $`\Re(b) > 0`: it equals
$`y \mapsto (\pi/b)^{d/2}\,e^{-\pi^2\|y\|^2/b}` (see `fourier_gaussian_innerProductSpace`). Taking
$`d = 8` and $`b = -\pi i z`, which satisfies $`\Re(b) = \pi \Im(z) > 0`, we obtain
$$`\left(\frac{\pi}{-\pi i z}\right)^{4} e^{-\pi^2\|y\|^2/(-\pi i z)} = z^{-4}\, e^{\pi i \|y\|^2(-1/z)},`
where no branch-cut issues arise because the exponent $`d/2 = 4` is an integer.
:::

Of great interest to us will be a specific family of functions, known as Schwartz Functions. The
Fourier transform behaves particularly well when acting on Schwartz functions. We elaborate in the
following subsections.

# On Schwartz Functions

:::definition "def:Schwartz-Space" (lean := "SchwartzMap")
A $`C^\infty` function $`f:\R^d\to\C` is called a *Schwartz function* if it decays to zero as
$`\|x\|\to\infty` faster then any inverse power of $`\|x\|`, and the same holds for all partial
derivatives of $`f`, ie, if for all $`k \in \N` and $`n \in \N^d`, there exists a constant
$`C \in \R` such that for all $`x \in \R^d`, $`\norm{x}^k \cdot \abs{f^{(n)}(x)} \leq C`, where
$`f^{(n)}` denotes the $`n`-th partial derivative of $`f`. The set of all Schwartz functions from
$`\R^d` to $`\C` is called the *Schwartz space*. It is an $`\R`-vector space. (The Mathlib
definition `SchwartzMap` is stated, more generally, for functions between normed spaces
$`E \to F`, with the $`n`-th iterated Fréchet derivative and its operator norm in place of partial
derivatives; the two formulations agree for $`\R^d \to \C`. The same generality applies to the
results below.)
:::

:::lemma_ "lemma:Fourier-transform-is-automorphism" (lean := "SchwartzMap.fourierTransformCLM") (uses := "def:Fourier-Transform, def:Schwartz-Space")
The Fourier transform is a continuous, linear automorphism of the space of Schwartz functions.
:::

:::proof "lemma:Fourier-transform-is-automorphism"
We do not elaborate here as the result already exists in Mathlib. We do, however, mention that the
Lean implementation *defines* a continuous linear equivalence on the Schwartz space *using* the
Fourier transform (see `SchwartzMap.fourierTransformCLM`). The ‘proof’ that for any Schwartz
function $`f`, its Fourier transform and its image under this continuous linear equivalence are,
indeed, the same $`\R^d \to \R` function, is stated in Mathlib solely for the purpose of `rw` and
`simp` tactics, and is proven simply by `rfl`.
:::

# Radial Functions and Fourier Eigenfunctions

The functions we construct in the section “Fourier eigenfunctions with double zeroes at lattice
points” will be *radial*, and we record here the elementary facts about radial Schwartz functions
that drive that construction.

:::definition "def:radial-function"
Let $`E` be a normed $`\R`-vector space. A function $`f : E \to \C` is *radial* if
$`f(x) = f(y)` whenever $`\norm{x} = \norm{y}`.
:::

:::lemma_ "lemma:fourier-involution" (lean := "MagicFunction.a.Fourier.fourier_involution") (uses := "def:Schwartz-Space, lemma:Fourier-transform-is-automorphism")
For every Schwartz function $`f : \R^d \to \C` and every $`x \in \R^d`,
$$`\mathcal{F}(\mathcal{F}(f))(x) = f(-x).`
:::

:::proof "lemma:fourier-involution"
Schwartz functions are integrable with integrable Fourier transforms, so the Fourier inversion
theorem (available in Mathlib as `Continuous.fourierInv_fourier_eq`, together with the identity
$`\mathcal{F}^{-1}(f)(x) = \mathcal{F}(f)(-x)`) applies.
:::

:::lemma_ "lemma:radial-fourier-inversion" (lean := "MagicFunction.a.Fourier.radial_inversion") (uses := "def:radial-function, lemma:fourier-involution")
If $`f : \R^d \to \C` is an even Schwartz function — in particular, if $`f` is radial — then
$`\mathcal{F}(\mathcal{F}(f)) = f`.
:::

:::proof "lemma:radial-fourier-inversion"
Immediate from {bpref "lemma:fourier-involution"}[], since $`f(-x) = f(x)`.
:::

{bpref "lemma:radial-fourier-inversion"}[] says that $`\mathcal{F}` is an involution on radial
Schwartz functions, so such functions decompose into eigenfunctions of $`\mathcal{F}` with
eigenvalues $`\pm 1`.

:::lemma_ "lemma:eigenfunction-decomposition" (uses := "lemma:radial-fourier-inversion")
Let $`f : \R^d \to \C` be a radial Schwartz function. Then there exist unique functions $`f_+` and
$`f_-` with $`f = f_+ + f_-`, $`\mathcal{F}(f_+) = f_+` and $`\mathcal{F}(f_-) = -f_-`, namely
$`f_\pm = \frac12 (f \pm \widehat{f})`.
:::

:::proof "lemma:eigenfunction-decomposition"
Setting $`f_\pm := \frac12(f \pm \widehat{f})`, {bpref "lemma:radial-fourier-inversion"}[] gives
$`\mathcal{F}(f_\pm) = \frac12(\widehat{f} \pm f) = \pm f_\pm`. Conversely, if $`f = f_+ + f_-`
with $`\mathcal{F}(f_\pm) = \pm f_\pm`, then $`\widehat{f} = f_+ - f_-`, and solving the two
equations recovers $`f_\pm = \frac12(f \pm \widehat{f})`.
:::

This decomposition reduces the construction of the magic function in the section “Proof of
{bpref "thm:g"}[]” to the construction of one $`+1`- and one $`-1`-eigenfunction of
$`\mathcal{F}`, which is carried out in the section “Fourier eigenfunctions with double zeroes at
lattice points”.

Another reason we are interested in Schwartz Functions is that they behave well under infinite
sums. This will be useful to us when proving the Cohn-Elkies linear programming bound.

# On the Summability of Schwartz Functions

We begin by stating a general summability result over specific subsets of $`\R^d`.

:::lemma_ "lemma:inv-power-summable"
Let $`X \subset \R^d` be a set of sphere packing centres of separation $`1` that is periodic with
some lattice $`\Lambda \subset \R^d`. Then, for any real $`k > d`,
$$`\sum_{x \in X} \frac{1}{\norm{x}^{k}} < \infty.`
:::

:::proof "lemma:inv-power-summable"
First, note that it does not matter how we number the (countably many) elements of the discrete
set $`X`: if we prove absolute convergence for one numbering, we prove absolute convergence for
*any* numbering. The idea will be to bound the sequence of partial sums by considering the volumes
of concentric $`d`-spheres of the appropriate radii (or scaled versions of a $`0`-centred
fundamental domain).

*TODO: Finish!*
:::

The decaying property of Schwartz functions means that they can be compared to the absolutely
convergent power series above.

:::lemma_ "lemma:Schwartz-summable" (uses := "def:Schwartz-Space")
Let $`f : \R^d \to \C` be a Schwartz function and let $`X \subset \R^d` be periodic with respect to
some lattice $`\Lambda \subset \R^d`. Then,
$$`\sum_{x \in X} |f(x)| < \infty.`
:::

:::proof "lemma:Schwartz-summable"
Without loss of generality, assume that $`0 \notin X`: if $`0 \in X`, then we can add the $`f(0)`
term to the sum over nonzero elements of $`X`, which, if the sum over the nonzero elements
converges absolutely, will be equal to the sum over all of $`X`. Now, we know that for all
$`k \in \N`, there exists some constant $`C` such that $`|f(x)| \leq C\norm{x}^{-k}` for all
$`x \in \R^d`. Choosing $`k` to be sufficiently large, we see that
$$`\sum_{x \in X} |f(x)| \leq \sum_{x \in X} \frac{C}{\norm{x}^{k}} = C \sum_{x \in X} \frac{1}{\norm{x}^k} < \infty.`
:::

We end with a crucial result on Schwartz functions, the statement of which only makes sense because
of the above result.

:::theorem "thm:Poisson-summation-formula" (lean := "SchwartzMap.PoissonSummation_Lattices") (uses := "def:Fourier-Transform, def:Schwartz-Space, lemma:Schwartz-summable, lemma:inv-power-summable, def:dual-lattice")
*(Poisson summation formula.)* Let $`\Lambda` be a lattice in $`\R^d`, and let $`f:\R^d\to\R` be
a Schwartz function. Then, for all $`v \in \R^d`,
$$`\sum_{\ell\in\Lambda}f(\ell + v) = \frac{1}{\Vol{\R^d/\Lambda}} \sum_{m\in\Lambda^*}\widehat{f}(m) e^{-2\pi i \ang{v, m}}.`
:::

:::proof "thm:Poisson-summation-formula"
One possible proof would be by induction on $`d`. However, there are numerous nuances involved,
particularly in manipulating nested infinite sums. Ideas would be appreciated.
:::

While the Poisson Summation Formula over lattices can be stated in greater generality (and probably
should be formalised as such in Mathlib due to the many applications it admits), we stick with
Schwartz functions because that should be sufficient for our purposes.

# Radial Schwartz Functions from One-Dimensional Data

Later, we will use {bpref "thm:Poisson-summation-formula"}[] to prove that certain functions
$`a(x)` and $`b(x)`, defined in the section “Fourier eigenfunctions with double zeroes at lattice
points”, are eigenfunctions of the Fourier transform. To apply the theorem, we need to show that
these functions are Schwartz. Both are of the form $`x \mapsto f(\|x\|^2)` for a function
$`f : \R \to \C` given by contour integrals, so we want a criterion for Schwartzness of such
compositions purely in terms of $`f`. This subsection provides one.

The first ingredient is a composition theorem already in Mathlib.

:::lemma_ "lemma:schwartz-comp-normsq" (lean := "schwartzMap_multidimensional_of_schwartzMap_real") (uses := "def:Schwartz-Space, def:radial-function")
Let $`f \in \mathcal{S}(\R, \C)` be a Schwartz function. Then, for every $`d \in \N`, the radial
function
$$`f_d : \R^d \to \C, \quad f_d(x) := f(\|x\|^2)`
is a Schwartz function.
:::

:::proof "lemma:schwartz-comp-normsq"
Mathlib's `SchwartzMap.compCLM` (due to M. Doll) shows that precomposition with a function of
temperate growth that grows at least polynomially produces a (continuous linear) map between
Schwartz spaces. The function $`x \mapsto \|x\|^2` has temperate growth
(`Function.hasTemperateGrowth_norm_sq`) and satisfies the required lower bound
$`\|x\| \le 1 + \|x\|^2`, so the composition $`f \circ \|\cdot\|^2` is Schwartz.
:::

{bpref "lemma:schwartz-comp-normsq"}[] is not directly applicable to the functions of the section
“Fourier eigenfunctions with double zeroes at lattice points”: the one-dimensional integrals
defining them are *not* Schwartz on all of $`\R` — they grow exponentially as $`r \to -\infty`, and
some of them are not even given by convergent integrals far to the left of the origin. However,
only their behaviour on $`[0, \infty)` matters, since $`\|x\|^2 \geq 0`. The remedy is to multiply
by a smooth cutoff before composing.

:::lemma_ "lemma:smooth-cutoff" (lean := "Real.smoothTransition")
There exists a smooth function $`\Theta : \R \to [0, 1]` such that $`\Theta(x) = 0` for
$`x \leq -1` and $`\Theta(x) = 1` for $`x \geq 0`.
:::

:::proof "lemma:smooth-cutoff"
Take $`\Theta(x) := \theta(x + 1)`, where $`\theta` is Mathlib's smooth transition function
`Real.smoothTransition`, which is smooth, takes values in $`[0,1]`, vanishes on $`(-\infty, 0]`
and equals $`1` on $`[1, \infty)`. Explicitly, $`\theta(x) = \frac{\rho(x)}{\rho(x) + \rho(1-x)}`
where $`\rho(x) = e^{-1/x}` for $`x > 0` and $`\rho(x) = 0` for $`x \leq 0`.
:::

Note that, being smooth and constant on both $`(-\infty, -1]` and $`[0, \infty)`, the function
$`\Theta` has all of its derivatives supported in the compact interval $`[-1, 0]`; in particular
$`\Theta` and all of its derivatives are (individually) bounded. Rescaling, for any $`\theta < 0`
we obtain a smooth cutoff $`\Theta_\theta(x) := \Theta\left(\frac{2x}{-\theta}\right)` which
vanishes for $`x \leq \theta/2`, equals $`1` for $`x \geq 0`, and transitions on
$`[\theta/2, 0]`; for $`\theta = -2` this is $`\Theta` itself.

:::theorem "thm:cutoff-schwartz" (uses := "def:Schwartz-Space, lemma:smooth-cutoff")
Let $`\theta < 0` and let $`f : \R \to \C` be smooth on $`(\theta, \infty)` and such that for all
$`k, n \in \N` there exists $`C \in \R` with
$$`x^{k} \cdot |f^{(n)}(x)| \leq C \quad \text{for all } x \geq 0.`
Then $`\Theta_\theta \cdot f` (extended by zero where $`f` is undefined) is a Schwartz function on
$`\R`; it agrees with $`f` on $`[0, \infty)` and vanishes on $`(-\infty, \theta/2]`.
:::

:::proof "thm:cutoff-schwartz" (uses := "lemma:smooth-cutoff")
Write $`g := \Theta_\theta \cdot f`. The last two assertions are immediate from the corresponding
properties of $`\Theta_\theta`.

*Smoothness.* The open sets $`(-\infty, \theta/2)` and $`(\theta, \infty)` cover $`\R`. On the
former, $`g` vanishes identically; on the latter, $`g` is a product of smooth functions. Since
smoothness is a local property, $`g` is smooth on $`\R`.

*Decay.* Fix $`k, n \in \N`. By the Leibniz rule,
$$`g^{(n)} = \sum_{j=0}^{n} \binom{n}{j}\, \Theta_\theta^{(j)}\, f^{(n-j)}.`
We bound $`|x|^k\,|g^{(n)}(x)|` on three regions. For $`x \leq \theta/2`, $`g^{(n)}(x) = 0`. For
$`x \geq 0`, the cutoff is constant, so $`\Theta_\theta^{(j)}(x) = 0` for all $`j \geq 1` and
$`g^{(n)}(x) = f^{(n)}(x)`, which satisfies the required bound by hypothesis. Finally, on the
compact interval $`[\theta/2, 0]`, the factor $`|x|^k` is bounded by $`|\theta/2|^k`, each
$`\Theta_\theta^{(j)}` is bounded, and each $`f^{(n-j)}` is continuous on the compact set
$`[\theta/2, 0] \subset (\theta, \infty)`, hence bounded. Taking the maximum of the three bounds
completes the proof.
:::

:::corollary "cor:schwartz-of-nonneg-decay" (uses := "thm:cutoff-schwartz, lemma:schwartz-comp-normsq")
Let $`\theta < 0` and let $`f : \R \to \C` be as in {bpref "thm:cutoff-schwartz"}[]. Then, for all
$`d \in \N`, the function
$$`f_d : \R^d \to \C, \quad f_d(x) := f(\|x\|^2)`
is a Schwartz function.
:::

:::proof "cor:schwartz-of-nonneg-decay" (uses := "thm:cutoff-schwartz, lemma:schwartz-comp-normsq")
Since $`\|x\|^2 \geq 0` and $`\Theta_\theta = 1` on $`[0, \infty)`, we have
$`f_d = (\Theta_\theta f) \circ \|\cdot\|^2` as functions on $`\R^d`. The inner function
$`\Theta_\theta f` is Schwartz by {bpref "thm:cutoff-schwartz"}[], so
{bpref "lemma:schwartz-comp-normsq"}[] applies.
:::

In the formalisation, the Schwartz structures on $`a` and $`b` are built exactly this way: the
one-dimensional integrals are multiplied by a smooth cutoff (with $`\theta = -2` for $`a` and
$`\theta = -1` for $`b`, matching the regions where the corresponding integrals converge; see the
section “Fourier eigenfunctions with double zeroes at lattice points”), and the resulting Schwartz
functions on $`\R` are transported to $`\R^8` via {bpref "lemma:schwartz-comp-normsq"}[]. The
cutoff is invisible after composing with $`\|\cdot\|^2`, so the resulting Schwartz functions are
*equal* to the radial functions defined in the section “Fourier eigenfunctions with double zeroes
at lattice points”.
