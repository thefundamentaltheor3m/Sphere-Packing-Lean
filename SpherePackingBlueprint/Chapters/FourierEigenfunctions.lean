import Verso
import VersoManual
import VersoBlueprint
import SpherePacking
import SpherePackingBlueprint.Macros

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Fourier eigenfunctions with double zeroes at lattice points" =>

In this section we construct two radial Schwartz functions $`a,b:\R^8\to i\R` such that
$$`\mathcal{F}(a)=a \tag{7.1}`
$$`\mathcal{F}(b)=-b \tag{7.2}`
with double zeroes at all $`\Lambda_8`-vectors of length greater than $`\sqrt{2}`. Recall that each
vector of $`\Lambda_8` has length $`\sqrt{2n}` for some $`n\in\N_{\geq 0}`.
We define $`a` and $`b` so that their values are purely imaginary because this simplifies some of
our computations.
We will show in the section “Proof of {bpref "thm:g"}[]” that an appropriate linear combination of
functions $`a` and $`b` satisfies conditions (5.5)–(5.7).

Both functions are defined as $`x \mapsto f(\|x\|^2)`, where $`f : \R \to \C` is a sum of six
contour integrals of (quasi)modular forms against the Gaussian $`e^{\pi i r z}`. The programme of
this section is as follows. Bounds on the relevant (quasi)modular forms (obtained from
{bpref "lemma:mod-div-disc-bound"}[]) yield rapid decay of the integrals and their derivatives on
$`[0, \infty)`; smoothness on a neighbourhood of $`[0,\infty)` follows by differentiation under the
integral sign; Schwartzness of $`a` and $`b` is then obtained from the smooth-cutoff criterion of
{bpref "cor:schwartz-of-nonneg-decay"}[]. The eigenfunction properties (7.1) and (7.2) follow from
the Fourier transform of the Gaussian ({bpref "lemma:Gaussian-Fourier"}[]) and the transformation
laws of the integrands, and the double zeroes are exhibited by deforming contours.

# The Integrands for $`a`

To define the function $`a`, we consider the following functions:

:::definition "def:phi4-phi2-phi0" (lean := "φ₀, φ₂', φ₄'") (uses := "def:Ek,def:E2")
$$`\phi_{-4} := \frac{E_4^2}{\Delta} \tag{7.3}`
$$`\phi_{-2} := \frac{E_4(E_2 E_4 - E_6)}{\Delta} \tag{7.4}`
$$`\phi_{0} := \frac{(E_2 E_4 - E_6)^2}{\Delta} \tag{7.5}`
:::

These functions are holomorphic on $`\h`: their numerators are built from the holomorphic functions
$`E_2`, $`E_4` and $`E_6`, and $`\Delta` does not vanish on $`\h`
({bpref "cor:disc-nonvanishing"}[]).

The function $`\phi_0(z)` is not modular; however, it satisfies the following transformation rules:

:::lemma_ "lemma:phi0-transform" (lean := "φ₀_periodic, φ₀_S_transform") (uses := "def:phi4-phi2-phi0, lemma:Ek-is-modular-form, lemma:E2-transform-S, lemma:disc-cuspform")
We have
$$`\phi_0(z + 1) = \phi_0(z) \tag{7.6}`
$$`\phi_0\left(-\frac{1}{z}\right) = \phi_0(z)-\frac{12i}{\pi}\,\frac{1}{z}\,\phi_{-2}(z)-\frac{36}{\pi^2}\,\frac{1}{z^2}\,\phi_{-4}(z). \tag{7.7}`
:::

:::proof "lemma:phi0-transform"
(7.6) easily follows from periodicity of Eisenstein series and $`\Delta(z)`.
For (7.7), we use the weight $`k` transformation laws of $`E_4`, $`E_6`, $`\Delta` (of weights
$`4`, $`6`, $`12`) and the quasimodular transformation law of $`E_2`
({bpref "lemma:E2-transform-S"}[]):
$$`\begin{aligned} \phi_{0}\left(-\frac{1}{z}\right) &= \frac{(E_2(-1/z) E_4(-1/z) - E_6(-1/z))^{2}}{\Delta(-1/z)} \\ &= \frac{((z^2 E_2(z) - 6iz / \pi) \cdot z^4 E_4(z) - z^6 E_6(z))^{2}}{z^{12} \Delta(z)} \\ &= \frac{\left(E_2(z) E_4(z) - E_6(z) - \frac{6i}{\pi z} E_4(z)\right)^2}{\Delta(z)} \\ &= \frac{(E_2(z) E_4(z) - E_6(z))^{2} - \frac{12i}{\pi z}(E_2(z) E_4(z) - E_6(z)) E_4(z) - \frac{36}{\pi^2 z^2} E_4(z)^{2}}{\Delta(z)} \\ &= \phi_0(z) - \frac{12 i}{\pi z} \phi_{-2}(z) - \frac{36}{\pi^2 z^2} \phi_{-4}(z). \end{aligned}`
:::

For our formalization, we choose rectangular contours for the first and the second integral, and
write it as follows.

:::definition "def:a-definition" (lean := "MagicFunction.a.RealIntegrals.a', MagicFunction.a.RadialFunctions.a") (uses := "def:phi4-phi2-phi0")
Define $`a_{\rad} : \R \to \C` by
$$`a_\rad(r) := I_1(r) + I_2(r) + I_3(r) + I_4(r) + I_5(r) + I_6(r) \tag{7.8}`
where
$$`I_1(r) := \int_{-1}^{-1 + i} \phi_0 \left(\frac{-1}{z+1}\right) (z + 1)^2 e^{\pi i r z} \dd z \tag{7.9}`
$$`I_2(r) := \int_{-1 + i}^{i} \phi_0 \left(\frac{-1}{z+1}\right) (z + 1)^2 e^{\pi i r z} \dd z \tag{7.10}`
$$`I_3(r) := \int_{1}^{1 + i} \phi_0 \left(\frac{-1}{z-1}\right) (z - 1)^2 e^{\pi i r z} \dd z \tag{7.11}`
$$`I_4(r) := \int_{1 + i}^{i} \phi_0 \left(\frac{-1}{z-1}\right) (z - 1)^2 e^{\pi i r z} \dd z \tag{7.12}`
$$`I_5(r) := -2 \int_{0}^{i} \phi_0 \left(\frac{-1}{z}\right) z^2 e^{\pi i r z} \dd z \tag{7.13}`
$$`I_6(r) := 2 \int_{i}^{i\infty} \phi_0(z) e^{\pi i r z} \dd z \tag{7.14}`
Here all the contours are chosen to be straight line segments.
Now, define $`a(x) := a_{\rad}(\|x\|^2)` for $`x \in \R^8`.
:::

In the original paper, the integrals $`I_1` and $`I_2` are combined, as well as $`I_3` and $`I_4`,
with the contours running from $`\mp 1` to $`i`.
Since the integrands are holomorphic on $`\h` (multiply out (7.7)), the choice of contours between
these endpoints does not matter; we choose rectangular ones because the versions of the
Cauchy–Goursat theorem available in Mathlib are stated for rectangles.
In the formalisation, each $`I_j` is realised as an integral over the real parametrising variable
$`t \in [0,1]` (or $`t \in [1, \infty)` for $`I_6`), so that the `intervalIntegral` API applies.

# Bounds for the Integrands

The key estimate is the following bound for quotients by $`\Delta`, applicable to all integrands
appearing in the definitions of $`a` and $`b`.

:::lemma_ "lemma:mod-div-disc-bound" (lean := "MagicFunction.PolyFourierCoeffBound.DivDiscBoundOfPolyFourierCoeff")
Let $`f(z)` be a holomorphic function with a Fourier expansion
$$`f(z) = \sum_{n \ge n_0} c_f(n) e^{\pi i n z}`
with $`c_f(n_0) \ne 0`.
Assume that $`c_f(n)` has a polynomial growth, i.e. $`|c_f(n)| = O(n^k)` for some $`k \in \N`.
Then there exists a constant $`C_f > 0` such that
$$`\left|\frac{f(z)}{\Delta(z)}\right| \le C_f e^{-\pi (n_0 - 2) \Im z}`
for all $`z` with $`\Im z > 1/2`.
:::

When $`f(z)` is a (quasi)modular form, we can take $`k` to be the weight of $`f`.

:::proof "lemma:mod-div-disc-bound" (uses := "def:disc-definition")
By the product formula (6.4),
$$`\begin{aligned} \left|\frac{f(z)}{\Delta(z)}\right| &= \left|\frac{\sum_{n \ge n_0} c_f(n) e^{\pi i n z}}{e^{2 \pi i z}\prod_{n \ge 1} (1 - e^{2\pi i n z})^{24}}\right| \\ &= |e^{\pi i (n_0 - 2)z}| \cdot \frac{|\sum_{n \ge n_0} c_f(n) e^{\pi i (n - n_0) z}|}{\prod_{n \ge 1} |1 - e^{2\pi i n z}|^{24}} \\ &\le e^{-\pi (n_0 - 2) \Im z} \cdot \frac{\sum_{n \ge n_0} |c_f(n)| e^{-\pi (n - n_0) \Im z}}{\prod_{n \ge 1} (1 - e^{- 2\pi n \Im z})^{24}} \\ &\le e^{-\pi (n_0 - 2) \Im z} \cdot \frac{\sum_{n \ge n_0} |c_f(n)| e^{-\pi (n - n_0) / 2}}{\prod_{n \ge 1} (1 - e^{-\pi n})^{24}} \\ &= C_f \cdot e^{-\pi (n_0 - 2) \Im z} \end{aligned}`
where
$$`C_f = \frac{\sum_{n \ge n_0} |c_f(n)| e^{-\pi (n - n_0) / 2}}{\prod_{n \ge 1} (1 - e^{-\pi n})^{24}}.`
The summation in the numerator converges absolutely because of polynomial growth, and the
denominator converges to the positive value $`e^{\pi} \cdot \Delta(i/2)` by the product formula.
The manipulations of infinite products used here (multiplicativity of the absolute value over
convergent products, and monotonicity of convergent products with nonnegative terms) are available
in Mathlib.
:::

To apply {bpref "lemma:mod-div-disc-bound"}[] to $`\phi_0`, $`\phi_{-2}` and $`\phi_{-4}` — and,
later, to the $`\psi`-functions — we need to know that the numerators have Fourier expansions with
polynomially growing coefficients, and we need their leading exponents. For a function $`f` with
Fourier expansion as in {bpref "lemma:mod-div-disc-bound"}[], write $`n_0(f)` for the smallest index
with $`c_f(n_0(f)) \neq 0`. The following closure property reduces both questions to the
corresponding facts about $`E_2`, $`E_4`, $`E_6` and the $`H`-functions.

:::lemma_ "lemma:poly-growth-mul"
Let $`f_1, f_2 : \h \to \C` have absolutely convergent Fourier expansions
$`f_i(z) = \sum_{n \geq n_0(f_i)} c_i(n)\, e^{\pi i n z}` with polynomially growing coefficients.
Then $`f_1 f_2` has an absolutely convergent Fourier expansion with polynomially growing
coefficients, and
$$`n_0(f_1 f_2) = n_0(f_1) + n_0(f_2), \qquad c_{f_1 f_2}(n_0(f_1 f_2)) = c_1(n_0(f_1))\, c_2(n_0(f_2)) \neq 0.`
The analogous statement for $`f_1 + f_2` holds with
$`n_0(f_1 + f_2) \geq \min(n_0(f_1), n_0(f_2))` (leading coefficients may cancel).
:::

:::proof "lemma:poly-growth-mul"
By absolute convergence, the product expands as a Cauchy product: the coefficient of
$`e^{\pi i \ell z}` in $`f_1 f_2` is $`c(\ell) = \sum_{m + n = \ell} c_1(n) c_2(m)`, a sum of
$`\ell - n_0(f_1) - n_0(f_2) + 1` terms each of size $`O(\ell^{k_1 + k_2})`, so
$`c(\ell) = O(\ell^{k_1 + k_2 + 1})`. The lowest-order term arises exactly once, from
$`(n, m) = (n_0(f_1), n_0(f_2))`.
:::

As corollaries, we have the following bounds for $`\phi_0`, $`\phi_{-2}`, and $`\phi_{-4}`.

:::corollary "cor:phi0-bound" (uses := "thm:ramanujan-formula, lemma:mod-div-disc-bound, lemma:Ek-Fourier, lemma:mod_form_poly_growth, lemma:poly-growth-mul")
There exists a constant $`C_0 > 0` such that
$$`|\phi_0(z)| \le C_0 e^{-2 \pi \Im z} \tag{7.15}`
for all $`z` with $`\Im z > 1/2`.
:::

:::proof "cor:phi0-bound"
The Fourier coefficients of $`E_2`, $`E_4` and $`E_6` grow polynomially
({bpref "lemma:Ek-Fourier"}[]), so by {bpref "lemma:poly-growth-mul"}[] the same holds for the
numerator $`(E_2E_4 - E_6)^2` of $`\phi_0`. By Ramanujan's formula (6.37),
$`E_2 E_4 - E_6 = 3E_4' = 720 \sum_{n \ge 1} n \sigma_3(n) e^{2 \pi i n z}`, so
$`n_0(E_2E_4 - E_6) = 2` in the convention of {bpref "lemma:mod-div-disc-bound"}[], and hence
$$`(E_2(z) E_4(z) - E_6(z))^{2} = 720^{2} e^{4 \pi i z} + O(e^{5 \pi i z}),`
i.e. $`n_0 = 4`. The result follows from {bpref "lemma:mod-div-disc-bound"}[].
:::

:::corollary "cor:phi2-bound" (uses := "def:phi4-phi2-phi0, lemma:mod-div-disc-bound, lemma:Ek-Fourier, lemma:poly-growth-mul")
There exists a constant $`C_{-2} > 0` such that
$$`|\phi_{-2}(z)| \le C_{-2} \tag{7.16}`
for all $`z` with $`\Im z > 1/2`.
:::

:::proof "cor:phi2-bound"
As in {bpref "cor:phi0-bound"}[]: the numerator of $`\phi_{-2}` is $`E_4(E_2E_4 - E_6)`, with
$`n_0 = 0 + 2 = 2`, so {bpref "lemma:mod-div-disc-bound"}[] gives the bound with exponent
$`-\pi(2-2)\Im z = 0`.
:::

:::corollary "cor:phi4-bound" (uses := "def:phi4-phi2-phi0, lemma:mod-div-disc-bound, lemma:Ek-Fourier, lemma:poly-growth-mul")
There exists a constant $`C_{-4} > 0` such that
$$`|\phi_{-4}(z)| \le C_{-4} e^{2 \pi \Im z} \tag{7.17}`
for all $`z` with $`\Im z > 1/2`.
:::

:::proof "cor:phi4-bound"
The numerator of $`\phi_{-4}` is $`E_4^2`, with $`n_0 = 0`; apply
{bpref "lemma:mod-div-disc-bound"}[].
:::

Note that we can take the constants $`C_0`, $`C_{-2}`, and $`C_{-4}` as
$$`\begin{aligned} C_0 &= 9 \cdot 240^2 \cdot e^{\pi} \cdot \frac{E_4'(i/2)^{2}}{\Delta(i/2)} \\ C_{-2} &= 3 \cdot \frac{E_4(i/2) E_4'(i/2)}{\Delta(i/2)} \\ C_{-4} &= e^{-\pi} \cdot \frac{E_4(i/2)^{2}}{\Delta(i/2)}. \end{aligned}`

# Decay of the Integrals $`I_j`

:::lemma_ "lem:bound-I1-I3-I5" (lean := "MagicFunction.a.IntegralEstimates.I₁.I₁'_bounding, MagicFunction.a.IntegralEstimates.I₃.I₃'_bounding, MagicFunction.a.IntegralEstimates.I₅.I₅'_bounding") (uses := "def:a-definition, cor:phi0-bound")
There exists $`C > 0` such that for all $`r \geq 0`,
$$`|I_1(r)|, |I_3(r)|, |I_5(r)| \leq C \int_1^{\infty} e^{-2\pi s} \, e^{-\pi r / s} \, \dd s.`
:::

:::proof "lem:bound-I1-I3-I5"
We only prove the bound for $`I_1(r)`, as the other two are similar.
By the change of variable $`z = -1 + i t` for $`t \in [0,1]`, we have
$$`I_1(r) = -i \int_0^1 \phi_0\left(\frac{-1}{i t}\right) t^2 e^{-\pi i r} \cdot e^{-\pi r t} \, \dd t.`
With the change of variable $`s = 1 / t` (an application, in the formalisation, of Mathlib's
one-dimensional change-of-variables theorem
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul`), we get
$$`I_1(r) = -i \int_1^{\infty} \phi_0(i s) \cdot s^{-4} \cdot e^{-\pi i r} \cdot e^{-\pi r / s} \, \dd s`
and, by the triangle inequality and monotonicity of the integral,
$$`|I_1(r)| \leq \int_1^{\infty} |\phi_0(i s)| \cdot s^{-4} \cdot |e^{-\pi i r}| \cdot e^{-\pi r / s} \, \dd s \le \int_1^{\infty} |\phi_0(is)| \cdot e^{-\pi r / s} \, \dd s.`
Now, {bpref "cor:phi0-bound"}[] shows
$$`|I_1(r)| \leq C_0 \int_1^{\infty} e^{-2\pi s} \, e^{-\pi r / s} \, \dd s.`
:::

For the integrals $`I_2`, $`I_4`, and $`I_6`, whose contours do not touch the real axis, the decay
is exponential.

:::lemma_ "lem:bound-I2-I4-I6" (lean := "MagicFunction.a.IntegralEstimates.I₂.I₂'_bounding, MagicFunction.a.IntegralEstimates.I₄.I₄'_bounding, MagicFunction.a.IntegralEstimates.I₆.I₆'_bounding") (uses := "def:a-definition, cor:phi0-bound")
There exist $`C_1, C_2 > 0` such that for all $`r \geq 0`,
$$`|I_2(r)|, |I_4(r)| \leq C_1 e^{-\pi r}`
and
$$`|I_6(r)| \leq C_2 \frac{e^{-\pi(r + 2)}}{r + 2}`
:::

:::proof "lem:bound-I2-I4-I6"
For $`I_2(r)`, parametrize $`z` as $`z = t + i` for $`t \in [-1,0]`, and we have
$$`I_2(r) = \int_{-1}^0 \phi_0\left(\frac{-1}{t + 1 + i}\right) (t + 1 + i)^2 e^{\pi i r t} e^{-\pi r} \, \dd t.`
Since the function $`z \mapsto \phi_0\left(\frac{-1}{z+1}\right) (z+1)^2` is holomorphic and
bounded on the contour,
there exists $`C > 0` such that $`|\phi_0\left(\frac{-1}{z+1}\right) (z + 1)^2| \leq C`, and the
absolute value of the integral can be bounded by
$$`|I_2(r)| \le \int_{-1}^{0} C e^{-\pi r} \, \dd t = C e^{-\pi r}.`
The bound for $`I_4(r)` is similar.
For $`I_6(r)`, parametrize $`z` as $`z = i t` for $`t \in [1, \infty)`, and we have
$$`I_6(r) = 2 i \int_1^{\infty} \phi_0(i t) e^{-\pi r t} \, \dd t`
and the absolute value can be bounded as (using {bpref "cor:phi0-bound"}[])
$$`|I_6(r)| \leq 2 \int_1^{\infty} |\phi_0(i t)| e^{-\pi r t} \, \dd t \leq 2C_0 \int_1^{\infty} e^{-2\pi t} e^{-\pi r t} \, \dd t = \frac{2C_0}{\pi} \frac{e^{-\pi (r + 2)}}{r + 2}.`
:::

The bound appearing in {bpref "lem:bound-I1-I3-I5"}[] decays faster than any polynomial as
$`r \to \infty`; this is a consequence of standard facts about the $`\Gamma` function. We state the
lemma for an arbitrary exponent $`\alpha > 0`, so that it also applies (with $`\alpha = \pi`) to
the analogous bounds for $`b` in {bpref "lemma:bound-J1-J3-J5"}[] below.

:::lemma_ "lem:integral-bound"
For all $`n \in \N` and $`\alpha > 0`, there exists a constant $`C'` such that for all
$`r \geq 0`,
$$`r^n \cdot \int_{1}^{\infty} e^{-\alpha s} \, e^{-\pi r /s} \, \dd s \leq C'`
:::

:::proof "lem:integral-bound"
Fix $`n \in \N`. We know there exists a constant $`C` such that for all $`x \geq 0`,
$`\abs{x}^n \cdot \abs{e^{-\pi x}} \leq C`. In particular, for all $`r \geq 0` and $`s \geq 1`,
$`r^n \cdot e^{-\pi r/s} \leq C s^n`. Hence, for all $`r \geq 0`, we can write
$$`r^n \cdot \int_{1}^{\infty} e^{-\alpha s} \, e^{-\pi r /s} \, \dd{s} = \int_{1}^{\infty} e^{-\alpha s} \, \left(\abs{r}^n \cdot e^{-\pi r /s}\right) \, \dd{s} \leq C \int_{1}^{\infty} e^{-\alpha s} \, s^n \, \dd{s}`
The $`\Gamma` function is given by
$$`\Gamma(x) = \int_{0}^{\infty} e^{-u} \, u^{x-1} \, \dd{u}`
for all $`x > 0` (in Mathlib, `Real.Gamma_eq_integral`). Hence, writing $`u = \alpha s` and using
$`\Gamma(n+1) = n!` (`Real.Gamma_nat_eq_factorial`), we get
$$`C \int_{1}^{\infty} e^{-\alpha s} \, s^n \, \dd{s} \leq C \int_{0}^{\infty} e^{-\alpha s} \, s^n \, \dd{s} = C \int_{0}^{\infty} \frac{1}{\alpha^{n+1}} e^{-u} \, u^n \, \dd{u} = \frac{C}{\alpha^{n+1}} \Gamma(n+1) = \frac{C \cdot n!}{\alpha^{n+1}}`
Defining $`C' := \frac{C \cdot n!}{\alpha^{n+1}}` finishes the proof.
:::

# Smoothness of the Integrals $`I_j`, and Schwartzness of $`a`

:::lemma_ "lem:Ij-smooth" (uses := "def:a-definition, cor:phi0-bound")
The functions $`I_1, \ldots, I_5` are smooth on $`\R`, and $`I_6` is smooth on $`(-2, \infty)`.
Moreover, for every $`j` and $`n`, the $`n`-th derivative $`I_j^{(n)}` is given by inserting the
factor $`(\pi i z)^n` into the corresponding integrand, and consequently, for all $`k, n \in \N`
there exists $`C` such that $`r^k\, |I_j^{(n)}(r)| \leq C` for all $`r \geq 0`.
:::

:::proof "lem:Ij-smooth" (uses := "lem:bound-I1-I3-I5, lem:bound-I2-I4-I6, lem:integral-bound")
Each $`I_j` is an integral of $`g_j(z)\, e^{\pi i r z}` over a fixed contour, with $`g_j`
holomorphic; formally, over the real parametrising variable. For $`j \leq 5` the contour is compact
and the integrand, together with each of its $`r`-derivatives
$`g_j(z) (\pi i z)^n e^{\pi i r z}`, is dominated locally uniformly in $`r` by an integrable
function; the Leibniz integral rule (in Mathlib,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) therefore applies repeatedly and yields
smoothness on $`\R`. For $`I_6`, {bpref "cor:phi0-bound"}[] bounds the integrand by a multiple of
$`e^{-\pi(r+2)t}` on the contour $`z = it`, $`t \geq 1`; this is integrable precisely when
$`r > -2`, and dominates all $`r`-derivatives locally uniformly on $`(-2, \infty)`, giving
smoothness there. (For $`r \leq -2` the integral defining $`I_6` diverges; this is what makes the
cutoff of {bpref "cor:schwartz-of-nonneg-decay"}[] necessary.)

For the derivative bounds on $`[0, \infty)`: the extra factor $`(\pi i z)^n` is bounded on the
compact contours, and on the unbounded contours (after the substitution $`s = 1/t` in the case of
$`I_1, I_3, I_5`) contributes a factor bounded by $`(\pi\sqrt{2})^n` resp. a polynomial in $`t`,
which is absorbed by the exponential decay of the integrand. The bounds of
{bpref "lem:bound-I1-I3-I5"}[] and {bpref "lem:bound-I2-I4-I6"}[] therefore hold, with adjusted
constants, for all derivatives, and {bpref "lem:integral-bound"}[] converts them into the stated
rapid decay.
:::

The functions $`I_j` are *not* Schwartz functions on $`\R`: the bounds above degrade into
exponential *growth* as $`r \to -\infty`, and $`I_6` is not even defined by a convergent integral
for $`r \leq -2`. This is harmless: $`a(x) = a_\rad(\|x\|^2)` only sees $`a_\rad` on
$`[0, \infty)`, and {bpref "lem:Ij-smooth"}[] shows that $`a_\rad` satisfies the hypotheses of
{bpref "cor:schwartz-of-nonneg-decay"}[] with $`\theta = -2`.

:::proposition "prop:a-schwartz" (lean := "MagicFunction.FourierEigenfunctions.a") (uses := "def:a-definition, cor:phi0-bound")
$`a(x)` is a Schwartz function.
:::

:::proof "prop:a-schwartz" (uses := "lem:bound-I1-I3-I5, lem:bound-I2-I4-I6, lem:integral-bound, lem:Ij-smooth, cor:schwartz-of-nonneg-decay")
By {bpref "lem:Ij-smooth"}[], $`a_\rad = I_1 + \cdots + I_6` is smooth on $`(-2, \infty)` and all
its derivatives decay rapidly on $`[0, \infty)`. {bpref "cor:schwartz-of-nonneg-decay"}[] (with
$`\theta = -2`) shows that $`x \mapsto a_\rad(\|x\|^2) = a(x)` is a Schwartz function on $`\R^8`.

In the formalisation, this is implemented by realising each product $`\Theta_{-2} \cdot I_j` as a
term of type $`\mathcal{S}(\R, \C)`, transporting it to $`\mathcal{S}(\R^8, \C)` via
{bpref "lemma:schwartz-comp-normsq"}[], and summing; since $`\Theta_{-2} = 1` on $`[0, \infty)`,
the resulting Schwartz function is equal to the function $`a` of {bpref "def:a-definition"}[].
:::

# The Eigenfunction Property of $`a`

We now prove that $`a` satisfies condition (7.1). The Fourier transform acts on the summands of
$`a` by permuting them: writing (by a slight abuse of notation) $`I_j` also for the radial function
$`x \mapsto I_j(\|x\|^2)` on $`\R^8`, we shall show
$$`\mathcal{F}(I_1 + I_2) = I_3 + I_4, \tag{7.18}`
$$`\mathcal{F}(I_5) = I_6. \tag{7.19}`

:::lemma_ "lemma:perm-I12" (lean := "MagicFunction.a.Fourier.perm_I₁_I₂") (uses := "def:a-definition, lemma:Gaussian-Fourier, lemma:phi0-transform, prop:a-schwartz")
(7.18) holds: $`\mathcal{F}(I_1 + I_2) = I_3 + I_4`.
:::

:::proof "lemma:perm-I12"
Fix $`\xi \in \R^8` and write $`F_j := \mathcal{F}(I_j(\|\cdot\|^2))`. The double integral defining
$`F_1(\xi)` converges absolutely — the estimates of {bpref "lem:bound-I1-I3-I5"}[] and
{bpref "lem:bound-I2-I4-I6"}[] bound the inner integral uniformly by a Schwartz-type bound in
$`x` — so by Fubini's theorem we may exchange the Fourier integral with the contour integral.
{bpref "lemma:Gaussian-Fourier"}[] then gives
$$`F_1(\xi) = \int_{-1}^{-1+i} \phi_0\left(\frac{-1}{z+1}\right) (z+1)^2\, z^{-4}\, e^{\pi i \|\xi\|^2 (\frac{-1}{z})}\, \dd z,`
and similarly for $`F_2` with contour from $`-1 + i` to $`i`. We substitute $`w = -1/z`, which maps
the two segments onto circular arcs from $`1` to $`\frac{1+i}{2}` and from $`\frac{1+i}{2}` to
$`i` respectively, and compute, using the $`1`-periodicity (7.6) of $`\phi_0`,
$$`\phi_0\left(-1-\frac{1}{w-1}\right)\left(\frac{-1}{w}+1\right)^2 w^2 = \phi_0\left(\frac{-1}{w-1}\right)(w-1)^2,`
so that $`F_1(\xi) + F_2(\xi)` is the integral of
$`\phi_0\left(\frac{-1}{w-1}\right)(w-1)^2 e^{\pi i \|\xi\|^2 w}` along the concatenated arc from
$`1` to $`i`. This integrand is holomorphic on $`\h` (multiply out (7.7)) and continuous up to the
boundary, so by the Cauchy–Goursat theorem (in the formalisation: the Mathlib version for
rectangles, together with a version for the regions between a quarter-circle and the two sides of
the enclosing square) the arc may be replaced by the rectangular path $`1 \to 1 + i \to i`. The two
resulting integrals are precisely $`I_3(\|\xi\|^2)` and $`I_4(\|\xi\|^2)`.
:::

:::lemma_ "lemma:perm-I56" (lean := "MagicFunction.a.Fourier.perm_I₅") (uses := "def:a-definition, lemma:Gaussian-Fourier, lemma:phi0-transform, prop:a-schwartz")
(7.19) holds: $`\mathcal{F}(I_5) = I_6`.
:::

:::proof "lemma:perm-I56"
As in {bpref "lemma:perm-I12"}[], exchange the integrals and apply
{bpref "lemma:Gaussian-Fourier"}[], then substitute $`w = -1/z`. Here no contour deformation is
needed: the substitution maps the segment from $`0` to $`i` onto the ray from $`i\infty` to $`i`,
reversing orientation, and
$$`-2\,\phi_0\left(\frac{-1}{z}\right) z^2\, z^{-4}\, e^{\pi i \|\xi\|^2(\frac{-1}{z})}\,\dd z \;\longmapsto\; 2\,\phi_0(w)\, e^{\pi i \|\xi\|^2 w}\,\dd w,`
which is the integrand of $`I_6`.
:::

:::lemma_ "lemma:perm-I-reverse" (lean := "MagicFunction.a.Fourier.perm_₃_I₄, MagicFunction.a.Fourier.perm_I₆") (uses := "lemma:perm-I12, lemma:perm-I56, lemma:radial-fourier-inversion")
$`\mathcal{F}(I_3 + I_4) = I_1 + I_2` and $`\mathcal{F}(I_6) = I_5`.
:::

:::proof "lemma:perm-I-reverse"
The functions $`I_1 + I_2` and $`I_5` (as functions on $`\R^8`) are radial Schwartz functions, so
$`\mathcal{F}^2` fixes them ({bpref "lemma:radial-fourier-inversion"}[]). Applying $`\mathcal{F}`
to (7.18) and (7.19) gives the claim.
:::

:::proposition "prop:a-fourier" (lean := "MagicFunction.a.Fourier.eig_a") (uses := "def:a-definition, prop:a-schwartz, lemma:perm-I12, lemma:perm-I56, lemma:perm-I-reverse")
$`a(x)` satisfies (7.1).
:::

:::proof "prop:a-fourier"
By linearity of $`\mathcal{F}` on the Schwartz space,
$$`\mathcal{F}(a) = \mathcal{F}(I_1 + I_2) + \mathcal{F}(I_3 + I_4) + \mathcal{F}(I_5) + \mathcal{F}(I_6) = (I_3 + I_4) + (I_1 + I_2) + I_6 + I_5 = a`
by {bpref "lemma:perm-I12"}[], {bpref "lemma:perm-I56"}[] and {bpref "lemma:perm-I-reverse"}[].
:::

# Double Zeroes of $`a`

Next, we check that $`a` has double zeroes at all $`\Lambda_8`-lattice points of length greater
then $`\sqrt{2}`.
The contour deformations in this argument involve unbounded contours; the following consequence of
the Cauchy–Goursat theorem, formalised as part of this project, is what we need.

:::lemma_ "lem:CG-unbounded" (lean := "Complex.tendsto_integral_boundary_open_rect_one_side_atTop_nhds_sum_other_two_sides, Complex.integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable")
*Cauchy–Goursat for unbounded rectangular contours.*
Let $`f : \C \to \C` be continuous on the closed strip
$`\{x_1 \leq \Re z \leq x_2,\ \Im z \geq y\}`, holomorphic on its interior, with $`f(z) \to 0` as
$`\Im z \to \infty` (uniformly in $`\Re z`), and integrable on the two vertical rays. Then
$$`\int_{x_1 + iy}^{x_1 + i\infty} f(z)\, \dd z = \int_{x_1 + iy}^{x_2 + iy} f(z)\, \dd z + \int_{x_2 + iy}^{x_2 + i\infty} f(z)\, \dd z.`
:::

:::proof "lem:CG-unbounded"
Apply the Cauchy–Goursat theorem for rectangles (available in Mathlib) to the truncated rectangles
with upper edge at height $`T`, and let $`T \to \infty`: the integral over the upper edge tends to
$`0` by the decay hypothesis, and the integrals over the truncated vertical sides tend to the
integrals over the rays by integrability.
:::

Using (7.15), (7.16), and (7.17), we can control the behavior of $`\phi_0` near $`0` and
$`i\infty`.

:::corollary "cor:phi0-near-0-infty" (uses := "cor:phi0-bound, cor:phi2-bound, cor:phi4-bound, lemma:phi0-transform")
We have
$$`\phi_0\left(\frac{i}{t}\right) = O(e^{-2 \pi / t}) \quad \text{as } t \to 0 \tag{7.20}`
$$`\phi_0\left(\frac{i}{t}\right) = O(t^{-2}e^{2 \pi t}) \quad \text{as } t \to \infty. \tag{7.21}`
:::

:::proof "cor:phi0-near-0-infty"
The first estimate follows from (7.15) with $`z = i/t`.
For the second estimate, by (7.7), (7.16), and (7.17), we have
$$`\left|\phi_0\left(\frac{i}{t}\right)\right| \le |\phi_0(it)| + \frac{12}{\pi t} |\phi_{-2}(it)| + \frac{36}{\pi^2 t^2} |\phi_{-4}(it)| \le C_0 e^{-2 \pi t} + \frac{12}{\pi t} \cdot C_{-2} + \frac{36}{\pi^2 t^2} \cdot C_{-4} e^{2 \pi t} = O(t^{-2}e^{2 \pi t}).`
:::

In particular, for $`r > 2` the integrand $`\phi_0(-1/z)\, z^2\, e^{\pi i r z}` is bounded by a
multiple of $`e^{\pi (2 - r)\Im z}` for $`\Im z \geq 2`, so it tends to $`0` as
$`\Im(z) \to \infty` and is integrable on vertical rays; the same applies to its translates by
$`\pm 1`. This provides the hypotheses of {bpref "lem:CG-unbounded"}[] in the following proof. (In
the radial variable, these are inputs of the form $`r = \|x\|^2 > 2`, i.e. $`\|x\| > \sqrt 2`.)

:::proposition "prop:a-double-zeros" (uses := "cor:phi0-near-0-infty, def:a-definition, cor:disc-nonvanishing, lem:CG-unbounded")
For $`r>\sqrt{2}` we can express $`a(r)` in the following form
$$`a(r)=-4\sin(\pi r^2/2)^2\,\int\limits_{0}^{i\infty}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz. \tag{7.22}`
:::

:::proof "prop:a-double-zeros"
We denote the right hand side of (7.22) by $`d(r)`.
Convergence of the integral for $`r > \sqrt{2}` follows from {bpref "cor:phi0-near-0-infty"}[].
Writing $`-4\sin(\pi r^2/2)^2 = e^{\pi i r^2} - 2 + e^{-\pi i r^2}` and absorbing the exponentials
into shifts $`z \mapsto z \pm 1` of the integration variable, we can write
$$`\begin{aligned} d(r)=&\int\limits_{-1}^{i\infty-1}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz- 2\int\limits_{0}^{i\infty}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz\\ +&\int\limits_{1}^{i\infty+1}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz. \end{aligned}`
From (7.7) we deduce that if $`r>\sqrt{2}` then
$`\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\to 0` as $`\Im(z)\to\infty`. Therefore, we
can deform the paths of integration by {bpref "lem:CG-unbounded"}[]
and rewrite
$$`\begin{aligned} d(r)=&\int\limits_{-1}^{i}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz +\int\limits_{i}^{i\infty}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz\\ -2&\int\limits_{0}^{i}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz -2\int\limits_{i}^{i\infty}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz\\ +&\int\limits_{1}^{i}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz +\int\limits_{i}^{i\infty}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz. \end{aligned}`
Now from (7.7) we find
$$`\begin{aligned}&\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2-2\phi_0\Big(\frac{-1}{z}\Big)\,z^2+ \phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2=\\ &\phi_0(z+1)\,(z+1)^2-2\phi_0(z)\,z^2+\phi_0(z-1)\,(z-1)^2\\ &-\frac{12i}{\pi}\,\Big(\phi_{-2}(z+1)\,(z+1)-2\phi_{-2}(z)\,z+\phi_{-2}(z-1)\,(z-1)\Big)\\ &-\frac{36}{\pi^2}\Big(\phi_{-4}(z+1)-2\phi_{-4}(z)+\phi_{-4}(z-1)\Big)=\\ &2\phi_0(z), \end{aligned}`
using the $`1`-periodicity of $`\phi_0`, $`\phi_{-2}`, $`\phi_{-4}`. Thus, we obtain
$$`\begin{aligned} d(r)=&\int\limits_{-1}^{i}\phi_0\Big(\frac{-1}{z+1}\Big)\,(z+1)^2\,e^{\pi i r^2 \,z}\,dz -2\int\limits_{0}^{i}\phi_0\Big(\frac{-1}{z}\Big)\,z^2\,e^{\pi i r^2 \,z}\,dz\\ +&\int\limits_{1}^{i}\phi_0\Big(\frac{-1}{z-1}\Big)\,(z-1)^2\,e^{\pi i r^2 \,z}\,dz +2\int\limits_{i}^{i\infty}\phi_0(z)\,e^{\pi i r^2 \,z}\,dz=a(r). \end{aligned}`
This finishes the proof.
:::

The factor $`\sin(\pi r^2/2)^2` vanishes to second order at $`r = \sqrt{2n}` for every integer
$`n`, so {bpref "prop:a-double-zeros"}[] exhibits the required double zeroes of $`a` at all
$`\Lambda_8`-vectors of length greater than $`\sqrt 2`.

# Special Values of $`a`

Finally, we find another convenient integral representation for $`a` and compute the value of
$`a` at $`0`.

:::proposition "prop:a-another-integral" (uses := "prop:a-double-zeros, def:phi4-phi2-phi0, lemma:phi0-transform, def:a-definition")
For $`r\geq0` we have
$$`\begin{aligned}a(r)=&4i\,\sin(\pi r^2/2)^2\,\Bigg(\frac{36}{\pi^3\,(r^2-2)}-\frac{8640}{\pi^3\,r^4}+\frac{18144}{\pi^3\,r^2}\\ +&\int\limits_0^\infty\,\left(t^2\,\phi_0\Big(\frac{i}{t}\Big)-\frac{36}{\pi^2}\,e^{2\pi t}+\frac{8640}{\pi}\,t-\frac{18144}{\pi^2}\right)\,e^{-\pi r^2 t}\,dt \Bigg) .\end{aligned} \tag{7.23}`
The integral converges absolutely for all $`r\in\R_{\geq 0}`.
:::

:::proof "prop:a-another-integral"
Suppose that $`r>\sqrt{2}`. Then by {bpref "prop:a-double-zeros"}[]
$$`a(r)=4i\,\sin(\pi r^2/2)^2\,\int\limits_{0}^{\infty}\phi_0(i/t)\,t^2\,e^{-\pi r^2 t}\,dt.`
From (7.7) we obtain
$$`\phi_0(i/t)\,t^2=\frac{36}{\pi^2}\,e^{2 \pi t}-\frac{8640}{\pi}\,t+\frac{18144}{\pi^2}+O(t^2\,e^{-2\pi t})\quad\text{as}\;t\to\infty. \tag{7.24}`
For $`r>\sqrt{2}` we have
$$`\int\limits_0^\infty \left(\frac{36}{\pi^2}\,e^{2 \pi t}-\frac{8640}{\pi}\,t+\frac{18144}{\pi^2}\right)\,e^{-\pi r^2 t}\,dt =\frac{36}{\pi^3\,(r^2-2)}-\frac{8640}{\pi^3\,r^4}+\frac{18144}{\pi^3\,r^2}.`
Therefore, the identity (7.23) holds for $`r>\sqrt{2}`.

On the other hand, from the definition (7.8) we see that $`a(r)` is analytic in some neighborhood
of $`[0,\infty)`. The asymptotic expansion (7.24) implies that the right hand side of (7.23) is
also analytic in some neighborhood of $`[0,\infty)`. Hence, by the identity principle for analytic
functions (available in Mathlib as `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`), the
identity (7.23) holds on the whole interval $`[0,\infty)`. This finishes the proof of the
proposition.
:::

From the identity (7.23) we see that the values $`a(r)` are in $`i\R` for all
$`r\in\R_{\geq0}`.

:::proposition "prop:a0" (lean := "MagicFunction.a.SpecialValues.a_zero") (uses := "prop:a-another-integral")
We have $`a(0) = \frac{-8640\, i}{\pi}`.
:::

:::proof "prop:a0"
As $`r \to 0`, the factor $`\sin(\pi r^2/2)^2` vanishes to order $`r^4`; the only term inside the
parentheses of (7.23) that blows up at that order is $`-\frac{8640}{\pi^3 r^4}`. Hence
$$`a(0) = \lim_{r \to 0} 4i\left(\frac{\pi r^2}{2}\right)^2 \cdot \left(-\frac{8640}{\pi^3 r^4}\right) = \frac{-8640\, i}{\pi}.`
:::

# The Integrands for $`b`

Now we construct function $`b`. To this end we consider the function

:::definition "def: h" (lean := "h") (uses := "def:H2-H3-H4")
$$`h(z) := 128 \frac{H_3(z) + H_4(z)}{H_2(z)^2}. \tag{7.25}`
:::

It is easy to see that $`h\in M^!_{-2}(\Gamma_0(2))`. Indeed, first we check that
$`h|_{-2}\gamma=h` for all $`\gamma\in\Gamma_0(2)`. Since the group $`\Gamma_0(2)` is generated by
elements $`\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)` and
$`\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)` it suffices to check that $`h` is
invariant under their action. This follows immediately from (6.17)–(6.19) and (7.25). Next we
analyze the poles of $`h`.
It is known \[Mumford, Chapter I Lemma 4.1\] that $`\theta_{10}` has no zeros in the upper-half
plane and hence $`h` has poles only at the cusps.
At the cusp $`i\infty` this modular form has the Fourier expansion
$$`h(z)\,=\,q^{-1} + 16 - 132 q + 640 q^2 - 2550 q^3+O(q^4).`
Let $`I=\left(\begin{smallmatrix}1&0\\0&1\end{smallmatrix}\right)`,
$`T=\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)`, and
$`S=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)` be elements of $`\Gamma_1`.

:::definition "def:psiI-psiT-psiS" (lean := "ψI, ψT, ψS") (uses := "def: h")
We define the following three functions
$$`\psi_I\,:=\,h-h|_{-2}ST \tag{7.26}`
$$`\psi_T\,:=\,\psi_I|_{-2}T \tag{7.27}`
$$`\psi_S\,:=\,\psi_I|_{-2}S. \tag{7.28}`
:::

The weight $`2` transformation laws of the $`H`-functions ({bpref "lemma:theta-transform-S-T"}[])
yield explicit expressions for the $`\psi`-functions.

:::lemma_ "lemma:psi-explicit" (lean := "ψI_eq, ψT_eq, ψS_eq") (uses := "def:psiI-psiT-psiS, lemma:theta-transform-S-T")
$$`\psi_I = 128 \left(\frac{H_3 + H_4}{H_2^2} + \frac{H_4 - H_2}{H_3^2}\right) \tag{7.29}`
$$`\psi_T = 128 \left(\frac{H_3 + H_4}{H_2^2} + \frac{H_2 + H_3}{H_4^2}\right) \tag{7.30}`
$$`\psi_S = 128 \left(\frac{H_4 - H_2}{H_3^2} - \frac{H_2 + H_3}{H_4^2}\right) \tag{7.31}`
:::

:::proof "lemma:psi-explicit"
By {bpref "lemma:theta-transform-S-T"}[] and the cocycle property of the slash action,
$$`H_2|_{2}ST = -H_3, \qquad H_3|_{2}ST = -H_4, \qquad H_4|_{2}ST = H_2,`
so, since the automorphy factors cancel in the quotient defining $`h`,
$$`h|_{-2}ST = 128\,\frac{(H_3|_2 ST) + (H_4|_2 ST)}{((H_2|_2 ST))^2} = 128\, \frac{-H_4 + H_2}{H_3^2},`
which gives (7.29). Applying $`|_{-2}T` and $`|_{-2}S` to $`\psi_I`, using
{bpref "lemma:theta-transform-S-T"}[] again, gives (7.30) and (7.31).
:::

The same computations give the following relations, which we use repeatedly; all follow from
{bpref "def:psiI-psiT-psiS"}[], {bpref "lemma:theta-transform-S-T"}[] and the cocycle property of
the slash action.

:::lemma_ "lemma:psi-slash-relations" (lean := "ψT_slash_T, ψS_slash_S, ψT_slash_S, ψS_slash_T, ψS_slash_ST, ψS_slash_TSTS") (uses := "def:psiI-psiT-psiS, lemma:psi-explicit")
We have
$$`\psi_T|_{-2}T = \psi_I, \qquad \text{i.e.}\quad \psi_I(z) = \psi_T(z+1), \tag{7.32}`
$$`\psi_S|_{-2}S = \psi_I, \qquad \psi_I(z) = z^2\,\psi_S(-1/z), \tag{7.33}`
$$`\psi_T|_{-2}S = -\psi_T, \qquad -\psi_T(z) = z^2\,\psi_T(-1/z), \tag{7.34}`
$$`\psi_S|_{-2}T = -\psi_S, \qquad -\psi_S(z) = \psi_S(z+1), \tag{7.35}`
$$`\psi_S|_{-2}ST = \psi_T, \qquad \psi_T(z) = (z+1)^2\,\psi_S\!\left(\frac{-1}{z+1}\right), \tag{7.36}`
$$`\psi_S|_{-2}TSTS = \psi_T, \qquad \psi_T(z) = (z-1)^2\,\psi_S\!\left(\frac{-1}{z-1}\right). \tag{7.37}`
:::

For the growth estimates it is convenient to express the $`\psi`-functions, like the
$`\phi`-functions, as quotients by $`\Delta`.

:::lemma_ "lemma:psi-new" (uses := "lemma:psi-explicit, lemma:jacobi-identity, lemma:lv1-lv2-identities")
$`\psi_I(z), \psi_S(z), \psi_T(z)` can be written as
$$`\psi_I(z) = \frac{H_4^3 (5 H_2^2 + 5 H_2 H_4 + 2 H_4^2)}{2\Delta}, \tag{7.38}`
$$`\psi_S(z) = -\frac{H_2^3 (2 H_2^2 + 5 H_2 H_4 + 5 H_4^2)}{2 \Delta}, \tag{7.39}`
$$`\psi_T(z) = \frac{H_3^3 (5 H_2^2 - 5 H_2 H_3 + 2 H_3^2)}{2 \Delta}. \tag{7.40}`
In particular, the $`\psi`-functions are holomorphic on $`\h`.
:::

:::proof "lemma:psi-new"
Starting from (7.29) and using the Jacobi identity $`H_3 = H_2 + H_4` (6.29) together with
$`\Delta = \frac{1}{256}(H_2 H_3 H_4)^2` (6.32), we can rewrite $`\psi_I(z)` as
$$`\begin{aligned} \psi_I &= 128\, \frac{H_3^2 (H_3 + H_4) - H_2^2 (H_2 - H_4)}{H_2^2 H_3^2} \\ &= 128\, \frac{(H_2 + H_4)^2 (H_2 + 2 H_4) - H_2^2 (H_2 - H_4)}{H_2^2 H_3^2} \\ &= 128\, \frac{H_4(5 H_2^2 + 5 H_2 H_4 + 2 H_4^2)}{ H_2^2 H_3^2} = \frac{H_4^3 (5 H_2^2 + 5 H_2 H_4 + 2 H_4^2)}{2\Delta}. \end{aligned}`
Applying $`|_{-2}S` and $`|_{-2}T` to this expression proves (7.39) and (7.40).
The final statement follows since the $`H`-functions are holomorphic and $`\Delta` is non-vanishing
on $`\h` ({bpref "cor:disc-nonvanishing"}[]).
:::

:::lemma_ "lemma:psiI-psiT-psiS-fourier" (uses := "lemma:psi-new, prop:H2-fourier, prop:H3-fourier, prop:H4-fourier")
The Fourier expansions of these functions are
$$`\psi_I(z)\,=\,q^{-1} + 144 + O(q^{1/2}) \tag{7.41}`
$$`\psi_T(z)\,=\,q^{-1} + 144 + O(q^{1/2}) \tag{7.42}`
:::

:::proof "lemma:psiI-psiT-psiS-fourier"
Direct computation from {bpref "lemma:psi-new"}[] and the $`q`-expansions of the $`H`-functions
({bpref "prop:H2-fourier"}[]–{bpref "prop:H4-fourier"}[]).
:::

Now, we are ready to define function $`b`.
Again, the definition here is slightly different from that in \[Via2017\], where all the contours
are chosen to be the straight lines.

*TODO (audit note): the Lean definition `MagicFunction.b.RealIntegrals.J₆'` currently carries the
factor $`+2` instead of the $`-2` below. The $`-2` convention used here is the one consistent with
the Lean statements `perm_J₅ : 𝓕 J₅ = -J₆` and `b_zero : b 0 = 0`, as well as with
{bpref "prop:b-double-zeros"}[]; the Lean definition should be corrected accordingly.*

:::definition "def:b-definition" (lean := "MagicFunction.b.RealIntegrals.b', MagicFunction.b.RadialFunctions.b") (uses := "def:psiI-psiT-psiS")
Define $`b_\rad : \R \to \C` by
$$`b_\rad(r) := J_1(r) + J_2(r) + J_3(r) + J_4(r) + J_5(r) + J_6(r) \tag{7.43}`
where for $`r \in \R`,
$$`J_1(r) := \int_{-1}^{-1 + i} \psi_T(z) e^{\pi i r z} \, \dd z, \tag{7.44}`
$$`J_2(r) := \int_{-1 + i}^{i} \psi_T(z) e^{\pi i r z} \, \dd z, \tag{7.45}`
$$`J_3(r) := \int_{1}^{1 + i} \psi_T(z) e^{\pi i r z} \, \dd z, \tag{7.46}`
$$`J_4(r) := \int_{1 + i}^{i} \psi_T(z) e^{\pi i r z} \, \dd z, \tag{7.47}`
$$`J_5(r) := -2 \int_{0}^{i} \psi_I(z) e^{\pi i r z} \, \dd z, \tag{7.48}`
$$`J_6(r) := -2 \int_{i}^{i \infty} \psi_S(z) e^{\pi i r z} \, \dd z. \tag{7.49}`
Here all the contours are straight line segments.
Then we define $`b : \R^8 \to \C` by $`b(x) := b_\rad(\|x\|^2)`.
:::

By {bpref "lemma:psi-slash-relations"}[], the integrands of $`J_1, \ldots, J_5` can be rewritten in
a form exactly parallel to those of $`I_1, \ldots, I_5`, with $`\psi_S` playing the role of
$`\phi_0`:
$$`\begin{aligned} J_1(r) &= \int_{-1}^{-1 + i} \psi_S\!\left(\frac{-1}{z + 1}\right) (z + 1)^2\, e^{\pi i r z} \, \dd z, & J_3(r) &= \int_{1}^{1 + i} \psi_S\!\left(\frac{-1}{z - 1}\right) (z - 1)^2\, e^{\pi i r z} \, \dd z, \\ J_2(r) &= \int_{-1 + i}^{i} \psi_S\!\left(\frac{-1}{z + 1}\right) (z + 1)^2\, e^{\pi i r z} \, \dd z, & J_4(r) &= \int_{1 + i}^{i} \psi_S\!\left(\frac{-1}{z - 1}\right) (z - 1)^2\, e^{\pi i r z} \, \dd z, \\ J_5(r) &= -2\int_{0}^{i} \psi_S\!\left(\frac{-1}{z}\right) z^2\, e^{\pi i r z} \, \dd z. \end{aligned} \tag{7.50}`
The proofs of the analytic properties of $`b` below follow those for $`a` with these expressions in
place of the $`\phi_0`-integrands; we record the statements and indicate only the differences.

# Schwartzness of $`b`

As in the case of $`a(x)`, we start with exponential bounds for the $`\psi`-functions.

:::lemma_ "lemma:psi-bound" (uses := "lemma:mod-div-disc-bound, lemma:psi-new, lemma:poly-growth-mul, prop:H2-fourier, prop:H3-fourier, prop:H4-fourier")
There exist constants $`C_I, C_S, C_T > 0` such that
$$`|\psi_I(z)| \le C_I e^{2\pi \Im z}, \tag{7.51}`
$$`|\psi_T(z)| \le C_T e^{2\pi \Im z}, \tag{7.52}`
$$`|\psi_S(z)| \le C_S e^{- \pi \Im z} \tag{7.53}`
for all $`z` with $`\Im z > 1/2`.
:::

:::proof "lemma:psi-bound"
We apply {bpref "lemma:mod-div-disc-bound"}[] to the numerators in {bpref "lemma:psi-new"}[]. The
$`H`-functions have Fourier expansions with polynomially growing coefficients
({bpref "prop:H2-fourier"}[]–{bpref "prop:H4-fourier"}[]), and, in the convention of
{bpref "lemma:mod-div-disc-bound"}[], $`n_0(H_2) = 1` (as $`H_2 = 16 q^{1/2} + O(q^{3/2})`) while
$`n_0(H_3) = n_0(H_4) = 0`. By {bpref "lemma:poly-growth-mul"}[], the numerators of $`\psi_I`,
$`\psi_T` and $`\psi_S` have $`n_0 = 0`, $`0` and $`3` respectively, which gives the three bounds.
:::

:::lemma_ "lemma:bound-J1-J3-J5" (uses := "def:b-definition, lemma:psi-bound, lemma:psi-slash-relations")
There exists a constant $`C > 0` such that for all $`r \geq 0`,
$$`|J_1(r)|, |J_3(r)|, |J_5(r)| \le C \int_1^{\infty} e^{-\pi s}\, e^{-\pi r / s}\, \dd s.`
:::

:::proof "lemma:bound-J1-J3-J5"
Identical to the proof of {bpref "lem:bound-I1-I3-I5"}[], starting from the expressions (7.50),
with $`\phi_0` replaced by $`\psi_S` and the bound $`C_0 e^{-2\pi s}` of {bpref "cor:phi0-bound"}[]
replaced by the bound $`C_S e^{-\pi s}` of (7.53).
:::

:::lemma_ "lemma:bound-J2-J4-J6" (uses := "def:b-definition, lemma:psi-bound, lemma:psi-slash-relations")
There exist $`C_1, C_2 > 0` such that for all $`r \geq 0`,
$$`\begin{aligned} |J_2(r)|, |J_4(r)| &\le C_1 e^{-\pi r}, \\ |J_6(r)| &\le C_2 \frac{e^{-\pi (r + 1)}}{r + 1}. \end{aligned}`
:::

:::proof "lemma:bound-J2-J4-J6"
For $`J_2` and $`J_4`, argue as for $`I_2` and $`I_4` in {bpref "lem:bound-I2-I4-I6"}[]: the
integrands are continuous, hence bounded, on the compact horizontal contours at height $`1`, and
$`|e^{\pi i r z}| = e^{-\pi r}` there. For $`J_6`, parametrise $`z = it`, $`t \in [1, \infty)`, and
use (7.53):
$$`|J_6(r)| \le 2 \int_1^\infty |\psi_S(it)|\, e^{-\pi r t}\, \dd t \le 2 C_S \int_1^\infty e^{-\pi(r+1)t}\, \dd t = \frac{2C_S}{\pi} \frac{e^{-\pi(r+1)}}{r+1}.`
:::

Note the asymmetry with the $`a`-side: since $`\psi_S` decays like $`e^{-\pi \Im z}` rather than
$`e^{-2\pi \Im z}`, the integral defining $`J_6` converges (and defines a smooth function) only for
$`r > -1`, whereas $`I_6` converged for $`r > -2`. Arguing exactly as in
{bpref "lem:Ij-smooth"}[], the functions $`J_1, \ldots, J_5` are smooth on $`\R` and $`J_6` is
smooth on $`(-1, \infty)`, with all derivatives of all $`J_j` decaying rapidly on $`[0, \infty)` by
{bpref "lemma:bound-J1-J3-J5"}[], {bpref "lemma:bound-J2-J4-J6"}[] and
{bpref "lem:integral-bound"}[] (the latter applied with $`\alpha = \pi`).
{bpref "cor:schwartz-of-nonneg-decay"}[] then applies with $`\theta = -1`, the cutoff transitioning
on $`[-1/2, 0]`.

:::proposition "prop:b-schwartz" (lean := "MagicFunction.FourierEigenfunctions.b") (uses := "lemma:psi-bound")
$`b(x)` is a Schwartz function.
:::

:::proof "prop:b-schwartz" (uses := "lemma:bound-J1-J3-J5, lemma:bound-J2-J4-J6, lem:integral-bound, cor:schwartz-of-nonneg-decay")
As for {bpref "prop:a-schwartz"}[]: $`b_\rad` is smooth on $`(-1, \infty)` with all derivatives
decaying rapidly on $`[0, \infty)`, so {bpref "cor:schwartz-of-nonneg-decay"}[] with
$`\theta = -1` shows that $`b = b_\rad(\|\cdot\|^2)` is Schwartz.
:::

# The Eigenfunction Property of $`b`

The Fourier transform also permutes the summands of $`b`, but with a sign change:
$$`\mathcal{F}(J_1 + J_2) = -(J_3 + J_4), \tag{7.54}`
$$`\mathcal{F}(J_5) = -J_6. \tag{7.55}`

:::lemma_ "lemma:perm-J12" (lean := "MagicFunction.b.Fourier.perm_J₁_J₂") (uses := "def:b-definition, lemma:Gaussian-Fourier, lemma:psi-slash-relations, prop:b-schwartz")
(7.54) holds: $`\mathcal{F}(J_1 + J_2) = -(J_3 + J_4)`.
:::

:::proof "lemma:perm-J12"
As in {bpref "lemma:perm-I12"}[], we exchange the Fourier integral with the contour integral
(absolute convergence follows from the bounds above), apply {bpref "lemma:Gaussian-Fourier"}[], and
substitute $`w = -1/z`. Here the relevant transformation law is (7.34):
$`\psi_T(-1/w)\, w^2 = -\psi_T(w)`, so the integrand becomes
$`-\psi_T(w)\, e^{\pi i \|\xi\|^2 w}`, and the same contour deformation as in
{bpref "lemma:perm-I12"}[] identifies the result with $`-(J_3 + J_4)`.
:::

:::lemma_ "lemma:perm-J56" (lean := "MagicFunction.b.Fourier.perm_J₅") (uses := "def:b-definition, lemma:Gaussian-Fourier, lemma:psi-slash-relations, prop:b-schwartz")
(7.55) holds: $`\mathcal{F}(J_5) = -J_6`.
:::

:::proof "lemma:perm-J56"
As in {bpref "lemma:perm-I56"}[], using the definition (7.28) in the form
$`\psi_I(-1/w)\, w^2 = \psi_S(w)`. The substitution $`w = -1/z` maps the contour of $`J_5` onto
that of $`J_6` with reversed orientation, whence the sign.
:::

:::lemma_ "lemma:perm-J-reverse" (lean := "MagicFunction.b.Fourier.perm_₃_J₄, MagicFunction.b.Fourier.perm_J₆") (uses := "lemma:perm-J12, lemma:perm-J56, lemma:radial-fourier-inversion")
$`\mathcal{F}(J_3 + J_4) = -(J_1 + J_2)` and $`\mathcal{F}(J_6) = -J_5`.
:::

:::proof "lemma:perm-J-reverse"
Apply $`\mathcal{F}` to (7.54) and (7.55) and use $`\mathcal{F}^2 = \mathrm{id}` on radial
Schwartz functions ({bpref "lemma:radial-fourier-inversion"}[]).
:::

:::proposition "prop:b-fourier" (lean := "MagicFunction.b.Fourier.eig_b") (uses := "def:b-definition, prop:b-schwartz, lemma:perm-J12, lemma:perm-J56, lemma:perm-J-reverse")
$`b(x)` satisfies (7.2).
:::

:::proof "prop:b-fourier"
By linearity, {bpref "lemma:perm-J12"}[], {bpref "lemma:perm-J56"}[] and
{bpref "lemma:perm-J-reverse"}[] give
$$`\mathcal{F}(b) = -(J_3 + J_4) - (J_1 + J_2) - J_6 - J_5 = -b.`
:::

# Double Zeroes and Special Values of $`b`

Now we regard the radial function $`b` as a function on $`\R_{\geq0}` and check that $`b` has
double roots at $`\Lambda_8`-points.

:::corollary "cor:psiI-near-0-infty" (uses := "lemma:psi-bound, lemma:psi-slash-relations")
We have
$$`\psi_I(it) = O(t^2 e^{-\pi/t}) \quad \text{as } t \to 0 \tag{7.56}`
$$`\psi_I(it) = O(e^{2 \pi t}) \quad \text{as } t \to \infty. \tag{7.57}`
:::

:::proof "cor:psiI-near-0-infty"
By (7.33), we have
$$`\psi_I(it) = (it)^{2} \psi_S\left(\frac{-1}{it}\right) = -t^{2} \psi_S\left(\frac{i}{t}\right),`
and combined with (7.53) we get (7.56).
(7.57) follows from {bpref "lemma:psi-bound"}[].
:::

We will also need the following identity.

:::lemma_ "lemma:psi-sum" (uses := "def:psiI-psiT-psiS")
$`\psi_T+\psi_S=\psi_I`.
:::

:::proof "lemma:psi-sum"
From definitions (7.26)–(7.28) we get
$$`\begin{aligned}\psi_T+\psi_S=&(h-h|_{-2}ST)|_{-2}T+(h-h|_{-2}ST)|_{-2}S\\ =&h|_{-2}T-h|_{-2}ST^2+h|_{-2}S-h|_{-2}STS.\end{aligned}`
Note that $`ST^2S` belongs to $`\Gamma_0(2)`. Thus, since $`h\in M^!_{-2}(\Gamma_0(2))` we get
$$`\psi_T+\psi_S=h|_{-2}T-h|_{-2}STS.`
Now we observe that $`T` and $`STS(ST)^{-1}` are also in $`\Gamma_0(2)`. Therefore,
$$`\psi_T+\psi_S=h|_{-2}T-h|_{-2}STS=h-h|_{-2}ST=\psi_I.`
:::

:::proposition "prop:b-double-zeros" (uses := "lemma:psiI-psiT-psiS-fourier, def:psiI-psiT-psiS, cor:psiI-near-0-infty, cor:disc-nonvanishing, lem:CG-unbounded, lemma:psi-sum, lemma:psi-slash-relations")
For $`r>\sqrt{2}` function $`b(r)` can be expressed as
$$`b(r)=-4\sin(\pi r^2/2)^2\,\int\limits_{0}^{i\infty}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz. \tag{7.58}`
:::

:::proof "prop:b-double-zeros"
We denote the right hand side of (7.58) by $`c(r)`.
By {bpref "cor:psiI-near-0-infty"}[], the integral in (7.58) converges for $`r>\sqrt{2}`.
As in {bpref "prop:a-double-zeros"}[], we write $`-4\sin(\pi r^2/2)^2 = e^{\pi i r^2} - 2 + e^{-\pi i r^2}`
and shift variables:
$$`c(r)=\int\limits_{-1}^{i\infty-1}\psi_I(z+1)\,e^{\pi i r^2 \,z}\,dz-2\int\limits_{0}^{i\infty}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz+ \int\limits_{1}^{i\infty+1}\psi_I(z-1)\,e^{\pi i r^2 \,z}\,dz.`
By (7.27) and (7.32), $`\psi_I(z+1) = \psi_I(z - 1) = \psi_T(z)`.
From the Fourier expansion (7.41) we know that $`\psi_I(z)=e^{-2\pi i z}+O(1)` as
$`\Im(z)\to\infty`.
By assumption $`r^2>2`, hence the integrands tend to $`0` as $`\Im(z) \to \infty` and we can deform
the paths of integration by {bpref "lem:CG-unbounded"}[]:
$$`\begin{aligned} \int\limits_{-1}^{i\infty-1}\psi_I(z+1)\,e^{\pi i r^2 \,z}\,dz=& \int\limits_{-1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{i}^{i\infty}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz\\ \int\limits_{1}^{i\infty+1}\psi_I(z-1)\,e^{\pi i r^2 \,z}\,dz=& \int\limits_{1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{i}^{i\infty}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz, \end{aligned} \tag{7.59}`
where the first integrals on the right run along the rectangular contours through $`-1 + i` resp.
$`1 + i`. We obtain
$$`\begin{aligned}c(r)=&\int\limits_{-1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz -2\int\limits_{0}^{i}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz\\ &+2\int\limits_{i}^{i\infty}(\psi_T(z)-\psi_I(z))\,e^{\pi i r^2 \,z}\,dz.\end{aligned} \tag{7.60}`
By {bpref "lemma:psi-sum"}[], $`\psi_T - \psi_I = -\psi_S`, so the last integral is $`J_6(r^2)`, and
$$`\begin{aligned}c(r)=&\int\limits_{-1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz+\int\limits_{1}^{i}\psi_T(z)\,e^{\pi i r^2 \,z}\,dz -2\int\limits_{0}^{i}\psi_I(z)\,e^{\pi i r^2 \,z}\,dz\\ &-2\int\limits_{i}^{i\infty}\psi_S(z)\,e^{\pi i r^2 \,z}\,dz\\ =&b(r).\end{aligned}`
:::

At the end of this section we find another integral representation of $`b(r)` for
$`r\in\R_{\geq0}` and compute special values of $`b`.

:::proposition "prop:b-another-integral" (uses := "prop:b-double-zeros, lemma:psiI-psiT-psiS-fourier, def:b-definition")
For $`r\geq0` we have
$$`b(r)=-4i\,\sin(\pi r^2/2)^2\,\left(\frac{144}{\pi\,r^2}+\frac{1}{\pi\,(r^2-2)}+\int\limits_0^\infty\,\left(\psi_I(it)-144-e^{2\pi t}\right)\,e^{-\pi r^2 t}\,dt\right). \tag{7.61}`
The integral converges absolutely for all $`r\in\R_{\geq 0}`.
:::

:::proof "prop:b-another-integral"
The proof is analogous to the proof of {bpref "prop:a-another-integral"}[].
First, suppose that $`r>\sqrt{2}`. Then by {bpref "prop:b-double-zeros"}[], parametrising
$`z = it` (so that $`\dd z = i\,\dd t`),
$$`b(r)=-4i\,\sin(\pi r^2/2)^2\,\int\limits_{0}^{\infty}\psi_I(it)\,e^{-\pi r^2 t}\,dt.`
(Note the sign: unlike in {bpref "prop:a-another-integral"}[], there is no factor $`z^2 = -t^2` in
the integrand to absorb the $`i` coming from $`\dd z`.)
From (7.41) we obtain
$$`\psi_I(it)=e^{2\pi t}+144+O(e^{-\pi t})\quad\text{as}\;t\to\infty. \tag{7.62}`
For $`r>\sqrt{2}` we have
$$`\int\limits_0^\infty \left(e^{2\pi t}+144\right)\,e^{-\pi r^2 t}\,dt =\frac{1}{\pi\,(r^2-2)}+\frac{144}{\pi\,r^2}.`
Therefore, the identity (7.61) holds for $`r>\sqrt{2}`.

On the other hand, from the definition (7.43) we see that $`b(r)` is analytic in some neighborhood
of $`[0,\infty)`. The asymptotic expansion (7.62) implies that the right hand side of (7.61) is
also analytic in some neighborhood of $`[0,\infty)`. Hence, by the identity principle for analytic
functions, the identity (7.61) holds on the whole interval $`[0,\infty)`. This finishes the proof
of the proposition.
:::

We see from (7.61) that $`b(r)\in i\R` for all $`r\in\R_{\geq0}`.
Another immediate corollary of this proposition is

:::proposition "prop:b0" (lean := "MagicFunction.b.SpecialValues.b_zero") (uses := "prop:b-another-integral")
We have $`b(0) = 0`.
:::

:::proof "prop:b0"
As $`r \to 0`, the factor $`\sin(\pi r^2/2)^2` vanishes to order $`r^4`, while the expression in
parentheses in (7.61) has only a simple pole in $`r^2` (the term $`\frac{144}{\pi r^2}`). Hence the
product tends to $`0`.
:::
