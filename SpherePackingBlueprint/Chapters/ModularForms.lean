import Verso
import VersoManual
import VersoBlueprint
import SpherePacking
import SpherePackingBlueprint.Macros

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Modular forms" =>

In this section, we recall and develop some theory of (quasi)modular forms.

# Modular forms and examples

Let $`\h` be the upper half-plane $`\{z\in\C\mid\Im(z)>0\}`.

:::lemma_ "def:Gamma-1-Action"
The modular group $`\Gamma_1:=\mathrm{SL}_2(\Z)` acts on $`\h` by linear fractional
transformations
$$`\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)z:=\frac{az+b}{cz+d}.`
:::

Let $`N` be a positive integer.

:::definition "def:level-N-princ-cong-subgp"
The *level $`N` principal congruence subgroup* of $`\Gamma_1` is
$$`\Gamma(N):=\left\{\left.\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\in\Gamma_1\right|\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\equiv\left(\begin{smallmatrix}1&0\\0&1\end{smallmatrix}\right)\;\mathrm{mod}\;N\right\}.`
:::

:::definition "def:congruence-subgroup" (uses := "def:level-N-princ-cong-subgp")
A subgroup $`\Gamma\subset\Gamma_1` is called a *congruence subgroup* if $`\Gamma(N)\subset\Gamma`
for some $`N\in\N`.
:::

:::definition "def:Gamma-generators" (lean := "ModularGroup.S,ModularGroup.T,α,β") (uses := "def:level-N-princ-cong-subgp")
Define the matrices

$$`S = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix} \in \Gamma_1, T = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix} \in \Gamma_1, \alpha = \begin{pmatrix} 1 & 2 \\ 0 & 1 \end{pmatrix} \in \Gamma_2 \subset \Gamma_1, \beta = \begin{pmatrix} 1 & 0 \\ 2 & 1 \end{pmatrix} \in \Gamma_2 \subset \Gamma_1.`

It is easily verifiable that $`\alpha = T^2` and $`\beta = -S\alpha^{-1}S = -ST^{-2}S`.
:::

The following two lemmas tell us the group structure of $`\Gamma(1) = \Gamma_1` and $`\Gamma(2)`,
which we will use later on to define the theta forms.

:::lemma_ "lemma:Gamma-1-generators" (lean := "SL2Z_generate") (uses := "def:Gamma-generators")
We have $`\Gamma(1) = \langle S, T, -I \rangle`.
:::

:::proof "lemma:Gamma-1-generators"
See \[first course, Exercise 1.1.1\].
:::

:::lemma_ "lemma:Gamma-2-generators" (lean := "Γ2_generate") (uses := "def:Gamma-generators")
We have $`\Gamma(2) = \langle \alpha, \beta, -I \rangle`.
:::

:::proof "lemma:Gamma-2-generators"
See \[first course, Exercise 1.2.4\].
:::

Let $`z\in\h`, $`k\in\Z`, and
$`\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\in\mathrm{SL}_2(\Z)`. We omit many of
the proofs below when they exist in Mathlib already.

:::definition "def:automorphy-factor" (lean := "UpperHalfPlane.denom")
The *automorphy factor* of weight $`k` is defined as
$$`j_k(z,\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)):=(cz+d)^{-k}.`
:::

:::lemma_ "lemma:automorphy-factor-chain-rule" (lean := "UpperHalfPlane.denom_cocycle") (uses := "def:automorphy-factor")
The automorphy factor satisfies the *chain rule*
$$`j_k(z,\gamma_1\gamma_2)=j_k(z,\gamma_1)\,j_k(\gamma_2z,\gamma_1).`
:::

:::definition "def:slash-operator" (uses := "def:automorphy-factor, def:Gamma-1-Action")
Let $`F` be a function on $`\h` and $`\gamma\in\mathrm{SL}_2(\Z)`. Then the *slash operator* acts
on $`F` by
$$`(F|_k\gamma)(z):=j_k(z,\gamma)\,F(\gamma z).`
:::

:::lemma_ "lemma:slash-operator-chain-rule" (lean := "SlashAction.slash_mul") (uses := "lemma:automorphy-factor-chain-rule")
The chain rule implies $$`F|_k\gamma_1\gamma_2=(F|_k\gamma_1)|_k\gamma_2.`
:::

In particular, this lemma implies that if
$`\Gamma = \langle M_i \rangle_{i \in \mathcal{I}} \rangle`, then the slash action $`F|\gamma` is
uniquely determined by the action of generators, i.e. $`F|M_i` and $`F|M_i^{-1}`.

:::lemma_ "lemma:slash-negI-even-weight" (lean := "modular_slash_negI_of_even") (uses := "def:slash-operator")
For even $`k`, $`F|_{k}(-I) = F`.
:::

:::proof "lemma:slash-negI-even-weight"
Follows from the definition of the slash operator:
$`(F|_{k}(-I))(z) = (-1)^{-k}F((-I)z) = F(z)`.
:::

:::definition "def:Mk" (lean := "ModularForm") (uses := "def:congruence-subgroup")
Let $`\Gamma` denote a subgroup of $`\mathrm{SL}_2(\mathbb{Z})`, then a modular form of level
$`\Gamma` and weight $`k \in \mathbb{Z}` is a function $`f : \mathbb{H} \to \mathbb{C}` such that:

1. For all $`\gamma \in \Gamma` we have $`f\mid_k \gamma = f` (such functions are called slash
   invariant).
2. $`f` is holomorphic on $`\mathbb{H}`.
3. For all $`\gamma \in \mathrm{SL}_2(\mathbb{Z})`, there exist $`A, B \in \mathbb{R}` such that for
   all $`z \in \mathbb{H}`, with $` A \le \mathrm{Im}(z)`, we have
   $`|(f \mid_k \gamma) (z) |\le B`. Here $`| - |` denotes the standard complex absolute value.

This defines a complex vector space which we denote by $`M_{k}(\Gamma)`.
:::

By replacing condition $`(3)` above with (4) below defines the subspace of cusp forms, which we
denote by $`S_k(\Gamma)`.

4. For all $`\gamma \in \mathrm{SL}_2(\mathbb{Z})`, and all $`0 < \epsilon`, there exists
   $`A \in \mathbb{R}` such that for all $`z \in \mathbb{H}`, with $` A \le \mathrm{Im}(z)`, we
   have $`|(f \mid_k \gamma) (z) |\le \epsilon`.

Let us consider several examples of modular forms.

:::definition "def:Ek" (lean := "E")
For an even integer $`k\geq 4` we define the *weight $`k` Eisenstein series* as
$$`E_k(z):=\frac{1}{2}\sum_{(c,d)\in\Z^2, (c,d)=1}(cz+d)^{-k}. \tag{6.1}`
:::

:::lemma_ "lemma:Ek-is-modular-form" (lean := "EisensteinSeries.eisensteinSeriesSIF") (uses := "def:Mk, def:Ek")
For all $`k`, $`E_k\in M_k(\Gamma_1)`. Especially, we have
$$`E_k \left(-\frac{1}{z}\right) = z^k E_k(z). \tag{6.2}`
:::

:::proof "lemma:Ek-is-modular-form"
This follows from the fact that the sum converges absolutely. Now apply slash operator with
$`\gamma = \left(\begin{smallmatrix} 0 & -1 \\ 1 & 0 \end{smallmatrix}\right)` gives (6.2).
:::

Since modular forms are holomorphic and periodic they have a Fourier expansions. One thing that we
will need is the growth of the Fourier coefficients, which is given by the following lemma.

:::lemma_ "lemma:mod_form_poly_growth"
Let $`\Gamma` be a finite index subgroup of $`\mathrm{SL}_2(\Z)` and $`f \in \mathcal{M}_k(\Gamma)`
be a modular form of weight $`k`. Then the Fourier coefficients $`a_n(f)` has a polynomial growth,
i.e. $`|a_n(f)| = O(n^k)`.
:::

:::proof "lemma:mod_form_poly_growth"
Note that the assumption on the polynomial growth holds when $`f` is a holomorphic modular form,
where the proof can be found in \[Serre73, p. 94\] for the case of level 1 modular forms. This has
been done in Lean 4 by David Loeffler.
:::

For Eisenstein series, we can see this directly from the following:

:::lemma_ "lemma:Ek-Fourier" (lean := "EisensteinSeries.q_expansion_bernoulli") (uses := "def:Ek")
The Eisenstein series possesses the Fourier expansion
$$`E_k(z)=1+\frac{2}{\zeta(1-k)}\sum_{n=1}^\infty \sigma_{k-1}(n)\,e^{2\pi i z}, \tag{6.3}`
where $`\sigma_{k-1}(n)\,=\,\sum_{d|n} d^{k-1}`. In particular, we have
$$`\begin{aligned} E_4(z)\,=\,& 1+240\sum_{n=1}^\infty \sigma_3(n)\,e^{2\pi i n z} \\ E_6(z)\,=\,& 1-504\sum_{n=1}^\infty \sigma_5(n)\,e^{2\pi i n z}. \end{aligned}`
:::

The infinite sum (6.1) does not converge absolutely for $`k=2`. On the other hand, the expression
(6.3) converges to a holomorphic function on the upper half-plane and we will take it as a
definition of $`E_2` (See {bpref "def:E2"}[] below).

The discriminant form is a unique normalized cusp form of weight 12, which can be defined as:

:::definition "def:disc-definition" (lean := "ModularForm.discriminant, Δ_eq_cexp_prod") (uses := "def:dedekind_eta")
The *discriminant form* $`\Delta(z)` is given by
$$`\Delta(z) = e^{2 \pi i z} \prod_{n \ge 1} (1 - e^{2 \pi i n z})^{24}. \tag{6.4}`
:::

This product formula allows us to prove positivity of $`\Delta(it)` for $`t > 0` later. But we
need to first check its a modular form. For this we first need some definitions/ results.

We define it as a $`q`-series, which gives a holomorphic function on $`\mathfrak{H}`.

:::definition "def:E2" (lean := "E₂_eq")
We set
$$`E_2(z):= 1-24\sum_{n=1}^\infty \sigma_1(n)\,e^{2\pi i n z}. \tag{6.5}`
:::

:::lemma_ "lemma:E2-transform-S" (lean := "E₂_transform") (uses := "def:E2")
This function is not modular, however it satisfies
$$`z^{-2}\,E_2\left(-\frac{1}{z}\right) = E_2(z) -\frac{6i}{\pi}\, \frac{1}{z}. \tag{6.6}`
:::

:::proof "lemma:E2-transform-S"
This is exercise 1.2.8 of \[first course\].
:::

More generally, we have

:::lemma_ "lemma:E2-transform-general" (lean := "E₂_slash_transform") (uses := "lemma:E2-transform-S, def:E2")
$$`(cz + d)^{-2} E_2\left(\frac{az + b}{cx + d}\right) = E_2(z) - \frac{6ic}{\pi (cz + d)}, \quad \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \mathrm{SL}_{2}(\mathbb{Z}). \tag{6.7}`
:::

:::proof "lemma:E2-transform-general"
Use the fact that $`\mathrm{SL}_2(\mathbb{Z})` is generated by $`S` and $`T`. Then (6.7) follows
from (6.6) and $`E_2|_T = E_2`.
:::

:::definition "def:dedekind_eta" (lean := "ModularForm.eta")
The Dedekind eta function is defined as
$$`\eta(z) = q^{1/24} \prod_{n \ge 1} (1 - q^n)`
where $`q = e^{2\pi i z}`.
:::

:::lemma_ "lemma:dedekind_eta_transformation" (lean := "ModularForm.eta_comp_eq_csqrt_I_inv") (uses := "def:dedekind_eta")
The Dedekind eta function transforms as
$$`\eta\left(-\frac{1}{z}\right) = \sqrt{-iz} \eta(z).`
:::

:::proof "lemma:dedekind_eta_transformation"
Consider the logarithmic derivative of $`\eta`, which one can easily see is equal to
$`\frac{\pi i}{12} E_2`. The result then follows from the transformation of $`E_2`.

See \[first course, proposition 1.2.5\].
:::

:::lemma_ "lemma:disc-cuspform" (lean := "CuspForm.discriminant") (uses := "def:disc-definition, lemma:dedekind_eta_transformation")
$`\Delta(z) \in M_{12}(\Gamma_1)`. Especially, we have
$$`\Delta\left(-\frac{1}{z}\right) = z^{12} \Delta(z). \tag{6.8}`
Also, it vanishes at the unique cusp, i.e. it is a cusp form of level $`\Gamma_1` and weight
$`12`.
:::

:::proof "lemma:disc-cuspform"
The fact that it is invariant under translation is clear from the definition, so we only need to
check transformation under $`S`. Now, note that $`\eta^{24} = \Delta`, and from
{bpref "lemma:dedekind_eta_transformation"}[] we have $`\eta(-1/z) = \sqrt{-iz} \eta(z)`, so
$`\Delta(-1/z) = z^{12} \Delta(z)` as required.
:::

:::lemma_ "lemma:disc-E4E6" (lean := "ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq") (uses := "def:disc-definition")
We have
$$`\Delta(z) = (E_4^3-E_6^2)/1728.`
:::

:::proof "lemma:disc-E4E6"
We only need to show its a cuspform, since once we have this, dividing the rhs by $`\Delta` would
give a modular form of weight $`0` which is a constant, and so we can determine the constant
easily.

To check its a cuspform, we just look at the $`q`-expansions of $`E_4` and $`E_6` and prove
directly that the first term vanishes.
:::

:::corollary "cor:disc-pos" (lean := "Δ_imag_axis_pos") (uses := "def:disc-definition")
$`\Delta(it) > 0` for all $`t > 0`.
:::

:::proof "cor:disc-pos"
By {bpref "def:disc-definition"}[], we have
$$`\Delta(it) = e^{-2 \pi t} \prod_{n \ge 1} (1 - e^{-2 \pi n t})^{24} > 0.`
:::

The following nonvanishing result, which directly follows from {bpref "def:disc-definition"}[],
will be used in the construction of the magic function.

:::corollary "cor:disc-nonvanishing" (lean := "ModularForm.discriminant_ne_zero") (uses := "def:disc-definition")
$`\Delta(z) \neq 0` for all $`z \in \h`.
:::

:::proof "cor:disc-nonvanishing"
This follows from the product formula.
:::

A key fact in the theory of modular forms is that the spaces $`M_k(\Gamma)` are
finite-dimensional. To prove this we will do use the following non-standard proof. First we have
the following result.

:::theorem "thm:nonpos_wt" (lean := "ModularFormClass.levelOne_neg_weight_eq_zero, ModularForm.levelOne_weight_zero_rank_one") (uses := "def:Mk")
Let $`k \in \Z` with $`k < 0`. Then $`M_k(\Gamma_1) = \{0\}` and moreover
$`\dim M_0(\Gamma(1)) = 1`.
:::

:::proof "thm:nonpos_wt"
The proof makes use of the maximum modulus principle, as its already been formalised we skip the
details here but see the lean proof for details.
:::

:::theorem "thm:lvl1_dims" (lean := "ModularForm.dimension_level_one") (uses := "def:Mk, lemma:disc-E4E6, def:disc-definition")
Let $`k \in \Z` with $`k \ge 0` and even. Then $`\dim M_k(\Gamma_1) = \lfloor k / 12 \rfloor ` if
$`k \equiv 2 \mod 12` and $`\dim M_k(\Gamma_1) = \lfloor k / 12 \rfloor + 1` if
$`k \not\equiv 2 \mod 12`.
:::

:::proof "thm:lvl1_dims"
First we note that for $`2 < k` we have $`\dim(M_k(\Gamma_1)) = 1 + \dim S_k(\Gamma_1)`. This
follows since we know the $`E_k` are in $`M_k` so by scaling appropriately, any non-cuspform
$`f \in M_k` we would have $`f - a E_k \in S_k` for some $`a`.

Next, note that $`S_k(\Gamma_1)` is isomorphic to $`M_{k-12}(\Gamma_1)`, since if $`f \in S_k`
then $`f/ \Delta` is now a modular form (using the product expansion of $`\Delta` and its
non-vanishing on $`\mathfrak{H}`) of weight $`k-12`. Note its important that $`f` is a cuspform so
that the quotient by $`\Delta` is a modular form.

So we only need to know the dimensions of $`M_k(\Gamma_1)` for $`0 \le k \le 12`. For $`k = 0` we
have $`\dim M_0(\Gamma_1) = 1` by {bpref "thm:nonpos_wt"}[]. For $`k = 4` we have
$`\dim M_4(\Gamma_1) = 1` since if there was a cuspform $`f` of weight $`4` then $`f/ \Delta`
would be a modular form of negative weight, i.e. zero, so $`f=0`. Similarly for $`k=6,8,10`. For
$`k=12` we have $`\dim S_{12}(\Gamma_1) = 1` since the discriminant form is a cusp form of weight
$`12` and any other cusp form of weight $`12` would be a scalar multiple of $`\Delta` (since their
ratio would be a modular form of weight $`0`). So we have $`\dim M_{12}(\Gamma_1) = 2`.

Finally we need to check that $`\dim M_2(\Gamma_1) = 0`. Firstly, there can't be any cuspforms
here by the same argument as above. So we need to check that there are no modular forms of weight
$`2`. If we did have one, call it $`f` then $`f^2` would be a non-cuspform of weight $`4` and so
$`f^2 = a E_4`, where in fact $`a=a_0(f)^2` (since $`(f^2-a_0(f)E_4)` is now a cuspform of weight
$`4` which means its zero). Similarly, $`f^3 = a_0(f)^3 E_6`. But now taking powers to make them
weight $`12` forms we see that $`a_0(f)^6(E_4^3 - E_6^2) = 0 = 1728 a_0(f)^6 \Delta` but
$`a_0(f) \ne 0` (since its assumed to not be a cuspform), this would mean $`\Delta =0` which we
know can't happen.
:::

:::theorem "thm:dim-mf-general-level" (lean := "dim_gen_cong_levels") (uses := "def:Mk, thm:lvl1_dims")
Let $`\Gamma` be a congruence subgroup. Then $`M_k(\Gamma)` is finite-dimensional.
:::

:::proof "thm:dim-mf-general-level"
We know that $`\dim(M_k(\Gamma_1))` is finite dimensional from the above, now this means that
there is some $`r_k` such that any element of $`M_k(\Gamma_1)` vanishing at infinity to degree
$`> r_k` must be zero. Now take $`f \in M_k(\Gamma)` and vanishes to degree $`n` at infinity, then
consider $`F = \prod_\gamma f\mid_k \gamma` where the product is over a set of representatives of
$`\Gamma_1 \backslash \Gamma`. Then $`F` is a modular form of weight $`k d` where
$`d = [\Gamma_1: \Gamma]` and vanishes at infinity to degree at least $`n`. So if $`n > r_{kd}`
then $`F=0` meaning the $`f=0`.
:::

:::corollary "cor:dim-mf" (uses := "def:Mk, thm:lvl1_dims")
We have
$$`\dim M_2(\mathrm{SL}_{2}(\mathbb{Z})) = 0, \tag{6.9}`
$$`\dim M_4(\mathrm{SL}_{2}(\mathbb{Z})) = 1, \tag{6.10}`
$$`\dim M_6(\mathrm{SL}_{2}(\mathbb{Z})) = 1, \tag{6.11}`
$$`\dim M_8(\mathrm{SL}_{2}(\mathbb{Z})) = 1, \tag{6.12}`
$$`\dim S_4(\mathrm{SL}_{2}(\mathbb{Z})) = 0, \tag{6.13}`
$$`\dim S_6(\mathrm{SL}_{2}(\mathbb{Z})) = 0, \tag{6.14}`
$$`\dim S_8(\mathrm{SL}_{2}(\mathbb{Z})) = 0. \tag{6.15}`
:::

Another examples of modular forms we would like to consider are *theta functions*
\[1-2-3, Section 3.1\].

:::definition "def:th00-th01-th10" (lean := "Θ₂, Θ₃, Θ₄")
We define three different theta functions (so called “Thetanullwerte”) as
$$`\begin{aligned} \Theta_{2}(z) = \theta_{10}(z)\,=\, & \sum_{n\in\Z}e^{\pi i (n+\frac12)^2 z}. \\ \Theta_{3}(z) = \theta_{00}(z)\,=\, & \sum_{n\in\Z}e^{\pi i n^2 z} \\ \Theta_{4}(z) = \theta_{01}(z)\,=\, & \sum_{n\in\Z}(-1)^n\,e^{\pi i n^2 z} \end{aligned}`
:::

For convenience, we use the following notations for the fourth powers of the theta functions.

:::definition "def:H2-H3-H4" (lean := "H₂, H₃, H₄") (uses := "def:th00-th01-th10")
Define
$$`H_2 = \Theta_2^4, \quad H_3 = \Theta_3^4, \quad H_4 = \Theta_4^4. \tag{6.16}`
:::

Note that we only need these fourth powers to define {bpref "def:b-definition"}[].

The group $`\Gamma_1` is generated by the elements
$`T=\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)`,
$`S=\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)`, and
$`-I = \left(\begin{smallmatrix}-1&0\\0&-1\end{smallmatrix}\right)`
({bpref "lemma:Gamma-1-generators"}[]), and the transformation of functions under $`\Gamma(2)` is
determined by that under $`\Gamma_1` (by {bpref "lemma:slash-operator-chain-rule"}[]). The
following lemma shows how the theta functions (and their powers) transform under the slash action
of these matrices.

:::lemma_ "lemma:theta-transform-S-T" (lean := "H₂_T_action,H₃_T_action,H₄_T_action,H₂_S_action,H₃_S_action,H₄_S_action") (uses := "def:th00-th01-th10, def:H2-H3-H4")
These elements act on the theta functions in the following way
$$`\begin{align} H_2 | S &= -H_4 \tag{6.17} \\ H_3 | S &= -H_3 \tag{6.18} \\ H_4 | S &= -H_2 \tag{6.19} \end{align}`
and
$$`\begin{align} H_2 | T &= -H_2 \tag{6.20} \\ H_3 | T &= H_4 \tag{6.21} \\ H_4 | T &= H_3 \tag{6.22} \end{align}`
:::

:::proof "lemma:theta-transform-S-T"
The last three identities easily follow from the definition. For example, (6.20) follows from
$$`\begin{aligned} \Theta_{2}(z + 1) &= \sum_{n\in\Z}e^{\pi i (n+\frac12)^2 (z + 1)} = \sum_{n \in \Z} e^{\pi i (n + \frac{1}{2})^{2}} e^{\pi i (n + \frac{1}{2})^{2} z} \\ &= \sum_{n \in \Z} e^{\pi i (n^2 + n + \frac{1}{4})} e^{\pi i (n + \frac{1}{2})^{2} z} = \sum_{n \in \Z} (-1)^{n^2 + n}e^{\pi i / 4} e^{\pi i (n + \frac{1}{2})^{2} z} \\ &= e^{\pi i / 4} \Theta_{2}(z) \end{aligned}`
and taking 4th power. (6.17) and (6.19) are equivalent under $`z \leftrightarrow -1/z`, so it is
enough to show (6.17) and (6.18). These identities follow from the identities of the
*two-variable* Jacobi theta function, which is defined as (be careful for the variables, where we
use $`\tau` instead of $`z`)
$$`\theta(z, \tau) = \sum_{n \in \mathbb{Z}} e^{2 \pi i n z + \pi i n^2 \tau} \tag{6.23}`
and already formalized by David Loeffler. This function specialize to the theta functions as
$$`\begin{align} \Theta_{2}(\tau) &= e^{\pi i \tau / 4} \theta(-\tau / 2, \tau) \tag{6.24} \\ \Theta_{3}(\tau) &= \theta(0, \tau) \tag{6.25} \\ \Theta_{4}(\tau) &= \theta(1/2, \tau) \tag{6.26} \end{align}`

Poisson summation formula gives
$$`\theta(z, \tau) = \frac{1}{\sqrt{-i \tau}} e^{-\frac{\pi i z^2}{\tau}} \theta\left(\frac{z}{\tau}, -\frac{1}{\tau}\right) \tag{6.27}`
and applying the specializations above yield the identities. For example, (6.19) follows from
$$`\Theta_{4}(\tau) = \theta\left(\frac{1}{2}, \tau\right) = \frac{1}{\sqrt{-i\tau}} e^{- \frac{\pi i }{4 \tau}} \theta\left(\frac{1}{2 \tau}, -\frac{1}{\tau}\right) = \frac{1}{\sqrt{-i\tau}} \Theta_{2}\left(-\frac{1}{\tau}\right)`
and taking 4th power.
:::

Using the above identities, we can prove that these are modular forms.

:::lemma_ "lemma:theta-slash-invariant" (lean := "H₂_SIF,H₃_SIF,H₄_SIF") (uses := "lemma:slash-operator-chain-rule,lemma:slash-negI-even-weight,lemma:theta-transform-S-T,lemma:Gamma-2-generators")
$`H_{2}`, $`H_{3}`, and $`H_{4}` are slash invariant under $`\Gamma(2)`, i.e. for all
$`\gamma \in \Gamma(2)` and $`i \in \{2, 3, 4\}`, we have $`H_i|\gamma = H_i|\gamma^{-1} = H_i`.
:::

:::proof "lemma:theta-slash-invariant"
By {bpref "lemma:Gamma-2-generators"}[] and {bpref "lemma:slash-operator-chain-rule"}[], it
suffices to show that the $`H_i` are invariant under slash actions with respect to $`\alpha`,
$`\beta`, and $`-I`. Invariance under $`-I` follows from
{bpref "lemma:slash-negI-even-weight"}[]. The rest follows from
{bpref "lemma:slash-operator-chain-rule"}[], {bpref "lemma:theta-transform-S-T"}[], and the matrix
identities
$$`\alpha = T^2, \quad \beta = -S\alpha^{-1}S = -ST^{-2}S. \tag{6.28}`
For example, invariance for $`H_2` can be proved by
$$`\begin{aligned} H_2|\alpha &= H_2 |T^{2} = -H_2 |T = H_2 \\ H_2|\beta &= H_2 |(-S\alpha^{-1}S) = H_2 | (S\alpha^{-1}S) =-H_4 |(\alpha^{-1}S) = -H_4 |S = H_2. \end{aligned}`
:::

:::lemma_ "lemma:theta-bounded-im-infty" (lean := "isBoundedAtImInfty_H_slash") (uses := "lemma:theta-slash-invariant, lemma:Gamma-1-generators")
For all $`\gamma \in \Gamma_1`, $`H_{2}|_2 \gamma`, $`H_{3}|_2 \gamma`, and $`H_{4}|_2 \gamma`
are holomorphic at $`i\infty`.
:::

:::proof "lemma:theta-bounded-im-infty"
We want to show that for $`\gamma \in \Gamma_1`, $`\|H_2|_2\gamma(z)\|` is bounded as
$`z \in \mathbb{H} \to i\infty`. Firstly, by {bpref "lemma:theta-transform-S-T"}[],
{bpref "lemma:Gamma-2-generators"}[] and induction on group elements, we notice that
$`\{\pm H_2, \pm H_3, \pm H_4\}` is closed under action by $`\Gamma_1`. Hence, it suffices to
prove that $`H_2`, $`H_3` and $`H_4` are bounded at $`i\infty`. Consider $`z \in \mathbb{H}` with
$`\Im(z) \geq A`. We proceed by direct algebraic manipulation:
$$`\begin{aligned} \|H_2(z)\| &= \left\|\sum_{n \in \Z} \exp\left(\pi i \left(n + \frac{1}{2}\right)^2 z\right)\right\|^4 \leq \left(\sum_{n \in \Z} \left\|\exp\left(\pi i \left(n + \frac{1}{2}\right)^2 z\right)\right)\right\|^4 \\ &= \left(\sum_{n \in \Z} \left\|\exp\left(-\pi \left(n + \frac{1}{2}\right)^2 \Im(z)\right)\right)\right\|^4 \leq \left(\sum_{n \in \Z} \left\|\exp\left(-\pi \left(n + \frac{1}{2}\right)^2 A\right)\right)\right\|^4 \end{aligned}`

Where we prove the final term is convergent by noticing that it equals
$`\exp(-\pi A / 4)\theta(iA / 2, iA)`, which has been shown to converge in `Mathlib`. The proofs
for $`H_3` and $`H_4` are similar (actually easier) and have been omitted.

*TODO: It seems the `MDifferentiable` requirement is missing.*
:::

:::lemma_ "lemma:theta-modular" (lean := "H₂_MF,H₃_MF,H₄_MF") (uses := "lemma:theta-slash-invariant,lemma:theta-bounded-im-infty")
$`H_{2}`, $`H_{3}`, and $`H_{4}` belong to $`M_2(\Gamma(2))`.
:::

:::proof "lemma:theta-modular"
From {bpref "lemma:theta-slash-invariant"}[] and {bpref "lemma:theta-bounded-im-infty"}[], it
remains ot prove that $`H_2`, $`H_3` and $`H_4` are holomorphic on $`\mathbb{H}`.
*TODO: fill in proof.*
:::

They have Fourier expansions as follows.

:::proposition "prop:H2-fourier" (uses := "def:H2-H3-H4")
$`H_2` admits a Fourier series of the form
$$`H_2(z) = \sum_{n \ge 1} c_{H_2}(n) e^{\pi i n z}`
for some $`c_{H_2}(n) \in \R_{\ge 0}`, with $`c_{H_2}(1) = 16` and $`c_{H_2}(n) = O(n^k)` for some
$`k \in \N`.
:::

:::proof "prop:H2-fourier"
We have
$$`\begin{aligned} H_2(z) &= \Theta_2(z)^4 \\ &= \left(\sum_{n \in \Z} e^{\pi i (n + \frac{1}{2})^{2} z}\right)^{4} \\ &= \left(2\sum_{n \ge 0} e^{\pi i (n + \frac{1}{2})^{2} z}\right)^{4} \\ &= \left(2 e^{\pi i z / 4} + 2 \sum_{n \ge 1} e^{\pi i (n^2 + n + \frac{1}{4}) z}\right)^{4} \\ &= 16 e^{\pi i z}\left(1 + \sum_{n \ge 1} e^{\pi i (n^2 + n)z}\right)^{4} \\ &= 16 e^{\pi i z} + \sum_{n \ge 2} c_{H_2}(n) e^{\pi i n z} \\ &= \sum_{n \ge 1} c_{H_2}(n) e^{\pi i n z}. \end{aligned}`
:::

:::proposition "prop:H3-fourier" (uses := "def:H2-H3-H4")
$`H_3` admits a Fourier series of the form
$$`H_3(z) = \sum_{n \ge 0} c_{H_3}(n) e^{\pi i n z}`
for some $`c_{H_3}(n) \in \R_{\ge 0}` with $`c_{H_3}(0) = 1` and $`c_{H_3}(n) = O(n^k)` for some
$`k \in \N`. Especially, $`H_3` is not cuspidal.
:::

:::proof "prop:H3-fourier"
We have
$$`H_3(z) = \Theta_3(z)^{4} = \left(\sum_{n \in \Z} e^{\pi i n^2 z}\right)^{4} = \left(1 + 2 \sum_{n \ge 1} e^{\pi i n^2 z}\right)^{4} = 1 + O(e^{\pi i z}).`
:::

:::proposition "prop:H4-fourier" (uses := "def:H2-H3-H4")
$`H_4` admits a Fourier series of the form
$$`H_4(z) = \sum_{n \ge 0} c_{H_4}(n) e^{\pi i n z}`
for some $`c_{H_4}(n) \in \R` with $`c_{H_4}(0) = 1` and $`c_{H_4}(n) = O(n^k)` for some
$`k \in \N`. Especially, $`H_4` is not cuspidal.
:::

We also have a nontrivial relation between these theta functions.

:::lemma_ "lemma:jacobi-identity" (lean := "jacobi_identity") (uses := "lemma:theta-modular, cor:dim-mf")
These three theta functions satisfy the *Jacobi identity*
$$`H_{2} + H_{4} = H_{3} \Leftrightarrow \Theta_{2}^4 + \Theta_{4}^4 = \Theta_{3}^4. \tag{6.29}`
:::

:::proof "lemma:jacobi-identity"
Let $`f = (H_2 + H_4 - H_3)^{2}`. Obviously, $`f` is a modular form of weight $`4` and level
$`\Gamma(2)`. However, by using the transformation rules of $`H_2, H_3, H_4`, one have
$$`\begin{aligned} f|_{S} &= (-H_4 - H_2 + H_3)^{2} = f \\ f|_{T} &= (-H_2 + H_3 - H_4)^{2} = f \end{aligned}`
so $`f` is actually a modular form of level $`1`. By considering the limit as $`z \to i\infty`,
$`f` is a cusp form, so we get $`f = 0` from (6.13).
:::

These are also related to $`E_4`, $`E_6`, and $`\Delta` as follows.

:::lemma_ "lemma:lv1-lv2-identities" (uses := "lemma:theta-transform-S-T, lemma:theta-modular, lemma:disc-cuspform")
We have
$$`\begin{align} E_4 &= \frac{1}{2}(H_{2}^{2} + H_{3}^{2} + H_{4}^{2}) = H_{2}^{2} + H_{2}H_{4} + H_{4}^{2} \tag{6.30} \\ E_6 &= \frac{1}{2} (H_{2} + H_{3})(H_{3} + H_{4}) (H_{4} - H_{2}) = \frac{1}{2}(H_2 + 2H_4)(2H_2 + H_4)(H_4 - H_2) \tag{6.31} \\ \Delta &= \frac{1}{256} (H_{2}H_{3}H_{4})^2. \tag{6.32} \end{align}`
:::

:::proof "lemma:lv1-lv2-identities"
We can prove these similarly as {bpref "lemma:jacobi-identity"}[]. Right hand sides of (6.30),
(6.31), and (6.32) are all modular forms of level $`\Gamma_1` and desired weights, where (6.32) is
a cusp form since $`H_2` is. Now the identities follow from the dimension calculations
$`\dim M_4(\Gamma_1) = \dim M_6(\Gamma_1) = \dim S_{12}(\Gamma_1) = 1` and comparing the first
nonzero $`q`-coefficients.
:::

The *strict* positivity of Jacobi theta functions might needed later.

:::corollary "cor:theta-pos" (lean := "H₂_imag_axis_pos, H₄_imag_axis_pos") (uses := "lemma:theta-transform-S-T")
$`H_2(it)` and $`H_4(it)` are positive for $`t > 0`.
:::

:::proof "cor:theta-pos"
By the transformation law (6.17), it is enough to prove the positivity for $`\Theta_2(it)`, which
is clear from its definition:
$$`\Theta_{2}(it) = \sum_{n \in \Z} e^{- \pi (n + \frac{1}{2})^{2} t} > 0.`
:::

# Quasimodular forms and derivatives

Morally, quasimodular forms can be thought as *modular forms with differentiations*. It can be
defined formally as follows: Let $`f: \mathfrak{H} \to \C` be a holomorphic function, and let
$`k` and $`s \ge 0` be integers. The function $`f` is a *quasimodular form of weight $`k`, level
$`\Gamma`, and depth $`s`* if there exist holomorphic functions
$`f_0, \dots, f_s : \mathfrak{H} \to \C` such that
$$`(f|_{k}\gamma)(z) = (cz + d)^{-k} f\left(\frac{az + b}{cz + d}\right) = \sum_{j=0}^{s} f_j(z) \left(\frac{c}{cz + d}\right)^j \tag{6.33}`
for all $`z \in \mathfrak{H}` and
$`\gamma = \left(\begin{smallmatrix} a&b\\c&d \end{smallmatrix}\right) \in \Gamma`.

By taking $`\gamma = \left(\begin{smallmatrix} 1 & 0 \\ 0 & 1 \end{smallmatrix}\right)`, one can
check that we should have $`f_0 = f`. Thus, a quasimodular form of depth $`0` is just a modular
form of same weight and level. Also, it is easy to see that the space of quasimodular forms is
closed under the normalized derivative.

In this project, we are *not* going to formalize the above definition of quasimodular forms.
Instead, we only use $`E_2` (defined in {bpref "def:E2"}[]) and define the normalized derivative
operator $`D` ({bpref "def:derivative"}[]) and the Serre derivative $`\partial_k`
({bpref "def:serre-der"}[]) as the main tools to work with quasimodular forms.

:::definition "def:derivative" (lean := "D")
Let $`F` be a quasimodular form. We define the (normalized) derivative of $`F` as
$$`F' = DF := \frac{1}{2\pi i} \frac{\dd}{\dd z} F. \tag{6.34}`
:::

Normalizing the derivative by $`1/(2 \pi i)` as in (6.34) is standard in the theory of modular
forms, since it makes the $`q`-expansion coefficients nicer.

:::lemma_ "lemma:der-q-series" (lean := "D_qexp_tsum_pnat") (uses := "def:derivative")
We have an equality of operators $`D = q \frac{\dd}{\dd q}`. In particular, the $`q`-series of the
derivative of a quasimodular form $`F(z) = \sum_{n \ge n_0} a_n q^n` is
$`F'(z) = \sum_{n \ge n_0} n a_n q^n`.
:::

:::proof "lemma:der-q-series"
Directly follows from the definition {bpref "def:derivative"}[], where
$`\frac{1}{2 \pi i}\frac{\dd}{\dd z}e^{2\pi i n z} = n e^{2\pi i n z}`.
:::

The most important example of quasimodular form is the weight 2 Eisenstein series $`E_2`
({bpref "def:E2"}[]). Using it, we can define the *Serre derivative* of a quasimodular form.

:::definition "def:serre-der" (lean := "serre_D") (uses := "def:derivative, def:E2")
For $`k \in \mathbb{R}`, define the weight $`k` Serre derivative $`\partial_{k}` of a modular form
$`F` as
$$`\partial_{k}F := F' - \frac{k}{12} E_2 F. \tag{6.35}`
:::

:::theorem "thm:serre-der-equiv-action" (lean := "serre_D_slash_equivariant") (uses := "def:serre-der, def:E2, lemma:E2-transform-general")
Serre derivative $`\partial_{k}` is equivariant with the slash action of
$`\mathrm{SL}_{2}(\mathbb{Z})` in the following sense:
$$`\partial_{k} (F|_{k}\gamma) = (\partial_{k} F)|_{k+2}\gamma, \quad \forall \gamma \in \mathrm{SL}_{2}(\mathbb{Z}).`
:::

:::proof "thm:serre-der-equiv-action"
Let $`G = \partial_{k}F = F' - \frac{k}{12}E_2 F`. From $`F \in M_k(\Gamma)`, we have
$$`(F|_{k}\gamma)(z) := (cz + d)^{-k} F\left(\frac{az + b}{cz + d}\right), \quad \gamma = \begin{pmatrix}a & b \\ c & d\end{pmatrix} \in \Gamma.`
By taking the derivative of the above equation, we get
$$`\begin{aligned} \frac{\dd}{\dd z}(F|_{k} \gamma)(z) &= -kc (cz + d)^{-k - 1} F\left(\frac{az + b}{cz + d}\right) + (cz + d)^{-k} (cz + d)^{-2} \frac{\dd F}{\dd z}\left(\frac{az + b}{cz + d}\right) \\ &= -kc (cz + d)^{-k - 1} F\left(\frac{az + b}{cz + d}\right) + (cz + d)^{-k - 2} \frac{\dd F}{\dd z}\left(\frac{az + b}{cz + d}\right) \\ &= -kc (cz + d)^{-k - 1} F\left(\frac{az + b}{cz + d}\right) + 2 \pi i (cz + d)^{-k - 2} F'\left(\frac{az + b}{cz + d}\right) \\ \Leftrightarrow (F|_{k} \gamma)'(z) &= -\frac{kc}{2 \pi i} (cz + d)^{-k - 1} F\left(\frac{az + b}{cz + d}\right) + (cz + d)^{-k - 2} F'\left(\frac{az + b}{cz + d}\right). \end{aligned}`
Combined with (6.7), we get
$$`\begin{aligned} ((\partial_k F)|_{k+2}\gamma)(z) &= (cz + d)^{-k-2} \left(F'\left(\frac{az + b}{cz + d}\right) - \frac{k}{12}E_2\left(\frac{az + b}{cz + d}\right)F\left(\frac{az + b}{cz + d}\right)\right) \\ &= (cz + d)^{-k-2} F'\left(\frac{az + b}{cz + d}\right) - \frac{k}{12} \left(E_2(z) - \frac{6ic}{\pi(cz + d)}\right) \cdot (cz + d)^{-k} F\left(\frac{az + b}{cz + d}\right) \\ &= (F|_{k}\gamma)'(z) - \frac{k}{12} E_2(z) (F|_{k}\gamma)(z) \\ &= \partial_{k} (F|_{k}\gamma)(z). \end{aligned}`
:::

As a direct consequence of {bpref "thm:serre-der-equiv-action"}[], we can check that the Serre
derivative preserves the modularity of a modular form.

:::theorem "thm:serre-der-modularity" (lean := "serre_D_slash_invariant") (uses := "def:serre-der, def:Mk, thm:serre-der-equiv-action")
Let $`F` be a modular form of weight $`k` and level $`\Gamma`. Then, $`\partial_{k}F` is a modular
form of weight $`k + 2` of the same level.
:::

:::proof "thm:serre-der-modularity"
Immediate from {bpref "thm:serre-der-equiv-action"}[] since $`F|_k\gamma = F` for all
$`\gamma \in \Gamma`.
:::

*Remark.* More generally, the following theorem holds: if $`F` is a quasimodular form of weight
$`k` and depth $`s`, then $`\partial_{k-s}F` is a quasimodular form of weight $`k + 2` *and depth
$`\le s`* of the same level. We will not prove this here.

:::theorem "thm:ramanujan-formula" (lean := "ramanujan_E₂, ramanujan_E₄, ramanujan_E₆, ramanujan_E₂', ramanujan_E₄', ramanujan_E₆'") (uses := "thm:serre-der-modularity, def:serre-der, lemma:E2-transform-general, cor:dim-mf")
We have
$$`\begin{align} E_2' &= \frac{E_2^2 - E_4}{12} \tag{6.36} \\ E_4' &= \frac{E_2 E_4 - E_6}{3} \tag{6.37} \\ E_6' &= \frac{E_2 E_6 - E_4^2}{2} \tag{6.38} \end{align}`
:::

:::proof "thm:ramanujan-formula"
In terms of Serre derivatives, these are equivalent to
$$`\begin{align} \partial_{1}E_2 &= -\frac{1}{12} E_4 \tag{6.39} \\ \partial_{4}E_4 &= -\frac{1}{3} E_6 \tag{6.40} \\ \partial_{6}E_6 &= -\frac{1}{2} E_4^2 \tag{6.41} \end{align}`
By {bpref "thm:serre-der-modularity"}[], all the Serre derivatives are, in fact, modular. To be
precise, the modularity of $`\partial_{4} E_4` and $`\partial_6 E_6` directly follows from
{bpref "thm:serre-der-modularity"}[], and that of $`\partial_{1}E_2` follows from (6.7).
Differentiating and squaring then gives us the following:
$$`\begin{align} E_2'|_{4}\gamma &= E_2' - \frac{ic}{\pi(cz + d)} E_2 - \frac{3c^2}{\pi^2 (cz + d)^2} \tag{6.42} \\ E_2^2|_{4}\gamma &= E_2^2 - \frac{12ic}{\pi(cz + d)} E_2 - \frac{36c^2}{\pi^2 (cz + d)^2} \tag{6.43} \end{align}`
Hence, (6.36)$`-\frac{1}{12}`(6.43) is a modular form of weight 4. By {bpref "cor:dim-mf"}[], they
should be multiples of $`E_4, E_6, E_4^2`, and the proportionality constants can be determined by
observing the constant terms of $`q`-expansions.
:::

:::corollary "cor:logder-disc-E2" (uses := "thm:ramanujan-formula, def:disc-definition")
$$`\Delta' = E_2 \Delta. \tag{6.44}`
:::

:::proof "cor:logder-disc-E2"
By Ramanujan's formula (6.37) and (6.38),
$$`\Delta' = \frac{3 E_4^2 E_4' - 2 E_6 E_6'}{1728} = \frac{1}{1728} \left(3 E_4^2 \cdot \frac{E_2 E_4 - E_6}{3} - 2 E_6 \cdot \frac{E_2 E_6 - E_4^2}{2}\right) = \frac{E_2(E_4^3 - E_6^2)}{1728} = E_2\Delta.`
:::

Similar argument allow us to compute (Serre) derivatives of $`H_2, H_3, H_4`.

:::proposition "prop:theta-der" (uses := "def:serre-der, lemma:theta-transform-S-T, lemma:jacobi-identity")
We have
$$`\begin{align} H_2' &= \frac{1}{6} (H_{2}^{2} + 2 H_{2} H_{4} + E_2 H_2) \tag{6.45} \\ H_3' &= \frac{1}{6} (H_{2}^{2} - H_{4}^{2} + E_2 H_3) \tag{6.46} \\ H_4' &= -\frac{1}{6} (2H_{2} H_{4} + H_{4}^{2} - E_2 H_4) \tag{6.47} \end{align}`
or equivalently,
$$`\begin{align} \partial_{2} H_{2} &= \frac{1}{6} (H_{2}^{2} + 2 H_{2} H_{4}) \tag{6.48} \\ \partial_{2} H_{3} &= \frac{1}{6} (H_{2}^{2} - H_{4}^{2}) \tag{6.49} \\ \partial_{2} H_{4} &= -\frac{1}{6} (2H_{2} H_{4} + H_{4}^{2}) \tag{6.50} \end{align}`
:::

:::proof "prop:theta-der"
Equivalences are obvious from the definition of the Serre derivative. Define $`f_{2}, f_{3}, f_{4}`
be the differences of the left and right hand sides of (6.48), (6.49), (6.50).
$$`\begin{aligned} f_{2} &:= \partial_{2} H_{2} - \frac{1}{6} H_{2}(H_{2} + 2H_{4}) \\ f_{3} &:= \partial_{2} H_{3} - \frac{1}{6} (H_{2}^2 - H_{4}^2) \\ f_{4} &:= \partial_{2} H_{4} + \frac{1}{6} H_{4}(2H_{2} + H_{4}). \end{aligned}`
Then these are a priori modular forms of weight $`4` and level $`\Gamma(2)`, and our goal is to
prove that they are actually zeros. By Jacobi's identity (6.29), we have $`f_{2} + f_{4} = f_{3}`.
Also, the transformation rules of $`H_2, H_3, H_4` give
$$`\begin{aligned} f_{2}|_{S} &= -f_{4} \\ f_{2}|_{T} &= -f_{2} \\ f_{4}|_{S} &= -f_{2} \\ f_{4}|_{T} &= f_{3} = f_{2} + f_{4}. \end{aligned}`
Now, define
$$`\begin{aligned} g &:= (2 H_2 + H_4) f_2 + (H_2 + 2 H_4) f_4 \\ h &:= f_{2}^{2} + f_{2}f_{4} + f_{4}^{2}. \end{aligned}`
Then one can check that both $`g` and $`h` are invariant under the actions of $`S` and $`T`, hence
they are modular forms of level $`1`. Also, by analyzing the limit of $`g` and $`h` as
$`z \to i \infty`, one can see that $`g` and $`h` are cusp forms, hence $`g = h = 0` by (6.14) and
(6.15). This implies
$$`\begin{aligned} 3 E_4 f_2^{2} &= 3 (H_2^2 + H_2 H_4 + H_4^2) f_2^{2} = ((2 H_2 + H_4)^{2} - (2H_2 + H_4)(H_2 + 2H_4) + (H_2 + 2H_4)^{2}) f_2^{2} \\ &= (2 H_2 + H_4)^{2} (f_2^2 + f_2 f_4 + f_4^2) = 0 \end{aligned}`
and by considering $`q`-series ($`E_4` has an invertible $`q`-series), we get $`f_2 = 0`.
:::

:::theorem "thm:serre-der-prod-rule" (lean := "serre_D_mul") (uses := "def:serre-der")
The Serre derivative satisfies the following product rule: for any quasimodular forms $`F` and
$`G`,
$$`\partial_{w_1 + w_2} (FG) = (\partial_{w_1}F)G + F (\partial_{w_2}G).`
:::

:::proof "thm:serre-der-prod-rule"
It follows from the definition:
$$`\begin{aligned} \partial_{w_1 + w_2} (FG) &= (FG)' - \frac{w_1 + w_2}{12} E_2 (FG) \\ &= F'G + FG' - \frac{w_1 + w_2}{12} E_2(FG) \\ &= \left(F' - \frac{w_1}{12}E_2 F\right)G + F \left(G' - \frac{w_2}{12}E_2 G\right) \\ &= (\partial_{w_1}F)G + F(\partial_{w_2}G). \end{aligned}`
:::

We also have the following useful theorem for proving positivity of quasimodular forms on the
imaginary axis, which is \[Lee, Proposition 3.5, Corollary 3.6\].

:::theorem "thm:anti-serre-der-pos" (uses := "def:serre-der, cor:logder-disc-E2")
Let $`F` be a holomorphic quasimodular cusp form with real Fourier coefficients. Assume that there
exists $`k` such that $`(\partial_{k}F)(it) > 0` for all $`t > 0`. If the first Fourier
coefficient of $`F` is positive, then $`F(it) > 0` for all $`t > 0`.
:::

:::proof "thm:anti-serre-der-pos"
By (6.44), we have
$$`\begin{aligned} \frac{\dd}{\dd t} \left( \frac{F(it)}{\Delta(it)^{\frac{k}{12}}}\right) &= (-2 \pi) \frac{F'(it) \Delta(it)^{\frac{k}{12}} - F(it) \frac{k}{12} E_{2}(it) \Delta(it)^{\frac{k}{12}}}{\Delta(it)^{\frac{k}{6}}} \\ &= (-2 \pi) \frac{(\partial_{k} F)(it)}{\Delta(it)^{\frac{k}{12}}} < 0, \end{aligned}`
hence
$$`t \mapsto \frac{F(it)}{\Delta(it)^{\frac{k}{12}}}`
is monotone decreasing. Because of the assumption on the positivity of the first nonzero Fourier
coefficient of $`F`, $`F(it) > 0` for sufficiently large $`t` since
$$`F = \sum_{n \geq n_{0}} a_{n} q^{n} \Rightarrow e^{2 \pi n_{0} t} F(it) = a_{n_{0}} + e^{-2 \pi t}\sum_{n\geq n_{0} + 1} a_{n} e^{-2 \pi (n - n_{0} - 1)t}`
and $`\lim_{t \to \infty} e^{2 \pi n_{0}t} F(it) = a_{n_0} > 0`, hence the result follows.
:::
