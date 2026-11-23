import Verso
import VersoManual
import VersoBlueprint
import SpherePacking
import SpherePackingBlueprint.Macros

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Proof of the existence of the magic function g" =>

Our proof of the {bpref "thm:g"}[] relies on the following two inequalities for modular objects.

:::proposition "prop:ineqA" (lean := "A, A_neg") (uses := "lemma:ineqABnew-equiv, lemma:F-G-phi-psi-identities, lemma:F-G-pos, cor:ineqAnew")
Consider the function $`A:(0,\infty)\to\C` defined as
$$`A(t):=-t^2\phi_0(i/t)-\frac{36}{\pi^2}\,\psi_I(it). \tag{8.1}`
Then
$$`A(t) < 0 \tag{8.2}`
for all $`t > 0`.
:::

:::proposition "prop:ineqB" (lean := "B, B_pos") (uses := "lemma:ineqABnew-equiv, lemma:F-G-phi-psi-identities, cor:ineqBnew")
Consider the function $`B:(0,\infty)\to\C` defined as
$$`B(t) := -t^2\phi_0(i/t)+\frac{36}{\pi^2}\,\psi_I(it) \tag{8.3}`
Then
$$`B(t) > 0 \tag{8.4}`
for all $`t > 0`.
:::

Here we formalize the proof of the inequalities by Lee \[Lee\].
First, we can rewrite the inequality in {bpref "prop:ineqA"}[] as follows.

:::definition "def:FG-definition" (lean := "F, G") (uses := "def:E2, def:Ek, def:H2-H3-H4")
Define two (quasi) modular forms as
$$`F(z) = (E_2(z) E_4(z) - E_6(z))^2 \tag{8.5}`
$$`G(z) = H_2(z)^{3} (2 H_{2}(z)^{2} + 5 H_{2}(z) H_{4}(z) + 5 H_{4}(z)^{2}). \tag{8.6}`
:::

:::lemma_ "lemma:F-G-phi-psi-identities" (lean := "φ₀_eq_F_div_disc, ψS_eq_neg_one_half_smul_G_div_disc") (uses := "def:FG-definition, def:phi4-phi2-phi0, lemma:psi-new")
We have
$$`\phi_0 = \frac{F}{\Delta} \tag{8.7}`
$$`\psi_S = -\frac{1}{2} \frac{G}{\Delta} \tag{8.8}`
:::

:::proof "lemma:F-G-phi-psi-identities"
(8.7) is clear from the definitions.
(8.8) is already shown in {bpref "lemma:psi-new"}[].
:::

:::lemma_ "lemma:ineqABnew-equiv" (uses := "lemma:F-G-phi-psi-identities, def:psiI-psiT-psiS, cor:disc-pos")
Inequality (8.2) and (8.4) are equivalent to
$$`F(it) + \frac{18}{\pi^2} G(it) > 0 \tag{8.9}`
$$`F(it) - \frac{18}{\pi^2} G(it) < 0 \tag{8.10}`
respectively.
:::

:::proof "lemma:ineqABnew-equiv"
By (7.28),
$$`\psi_I(it) = (\psi_S|_{-2}S)(it) = (it)^{2}\psi_S\left(-\frac{1}{it}\right) = -t^2 \psi_S\left(\frac{i}{t}\right).`
Combined with {bpref "lemma:F-G-phi-psi-identities"}[] we can rewrite (8.2) as
$$`A(t) = -t^2 \left(\phi_0\left(\frac{i}{t}\right) - \frac{36}{\pi^2} \psi_S\left(\frac{i}{t}\right)\right) < 0 \Leftrightarrow \frac{F(i/t)}{\Delta(i/t)} + \frac{18}{\pi^2} \frac{G(i/t)}{\Delta(i/t)} > 0`
for $`t > 0`; since $`\Delta` is positive on the imaginary axis ({bpref "cor:disc-pos"}[]) and
$`t \mapsto 1/t` is a bijection of $`(0, \infty)`, this is equivalent to (8.9).
The equivalence of (8.4) and (8.10) follows similarly; just change the sign.
:::

Now, the first inequality (8.9) follows from the positivity of each $`F(it)` and $`G(it)`.

:::lemma_ "lemma:F-G-pos" (lean := "F_imag_axis_pos, G_imag_axis_pos") (uses := "thm:ramanujan-formula, cor:theta-pos")
For all $`t > 0`, we have $`F(it) > 0` and $`G(it) > 0`.
:::

:::proof "lemma:F-G-pos"
By Ramanujan's identity (6.37), we have $`F(z) = 9 E_4'(z)^2` and
$$`F(it) = 9E_4'(it)^2 = 9 \left(240\sum_{n \geq 1} n \sigma_3(n) e^{-2 \pi n t} \right)^{2} > 0.`
$`G(it) > 0` follows from positivity of $`H_2(it)` and $`H_4(it)` ({bpref "cor:theta-pos"}[]).
:::

:::corollary "cor:ineqAnew" (lean := "FG_inequality_1") (uses := "lemma:F-G-pos")
(8.9) holds.
:::

:::proof "cor:ineqAnew"
This directly follows from {bpref "lemma:F-G-pos"}[].
:::

To prove the second inequality (8.10), we need some identities satisfied by $`F` and $`G`.

:::lemma_ "lemma:FG-de" (lean := "MLDE_F, MLDE_G") (uses := "thm:ramanujan-formula, thm:serre-der-prod-rule, prop:theta-der, lemma:lv1-lv2-identities")
$`F` and $`G` satisfy the following differential equations:
$$`\partial_{12}\partial_{10} F - \frac{5}{6} E_{4} F = 7200 \Delta (-E_{2}') \tag{8.11}`
$$`\partial_{12}\partial_{10} G - \frac{5}{6} E_{4} G = -640 \Delta H_{2} \tag{8.12}`
:::

:::proof "lemma:FG-de"
Both can be shown by direct computations.
By Ramanujan's identities ({bpref "thm:ramanujan-formula"}[]) and the product rule of Serre
derivatives ({bpref "thm:serre-der-prod-rule"}[]), we have
$$`\begin{aligned} \partial_{5} (E_2 E_4 - E_6) &= (E_2 E_4 - E_6)' - \frac{5}{12} E_2 (E_2 E_4 - E_6) \\ &= \frac{E_2^2 - E_4}{12} \cdot E_4 + E_2 \cdot \frac{E_2 E_4 - E_6}{3} - \frac{E_2 E_6 - E_4^2}{2} - \frac{5}{12}E_2 (E_2 E_4 - E_6) \\ &= -\frac{5}{12} (E_2 E_6 - E_4^2) \end{aligned} \tag{8.13}`
$$`\begin{aligned} \partial_{7} (E_2 E_6 - E_4^2) &= (E_2 E_6 - E_4^2)' - \frac{7}{12} E_2 (E_2 E_6 - E_4^2) \\ &= \frac{E_2^2 - E_4}{12} \cdot E_6 + E_2 \cdot \frac{E_2 E_6 - E_4^2}{2} - 2 E_4 \cdot \frac{E_2 E_4 - E_6}{3} - \frac{7}{12} E_2 (E_2 E_6 - E_4^2) \\ &= -\frac{7}{12} E_4 (E_2 E_4 - E_6) \end{aligned} \tag{8.14}`
and using these we can compute
$$`\begin{aligned} \partial_{10} F &= \partial_{10} (E_2 E_4 - E_6)^2 \\ &= 2 (E_2 E_4 - E_6) \partial_{5} (E_2 E_4 - E_6) \\ &= -\frac{5}{6} (E_2 E_4 - E_6) (E_2 E_6 - E_4^2), \\ \partial_{12}\partial_{10} F &= -\frac{5}{6} \partial_{12} ((E_2 E_4 - E_6) (E_2 E_6 - E_4^2)) \\ &= -\frac{5}{6} (\partial_{5}(E_2 E_4 - E_6)) (E_2 E_6 - E_4^2) - \frac{5}{6} (E_2 E_4 - E_6) (\partial_{7} (E_2 E_6 - E_4^2)) \\ &= \frac{25}{72} (E_2 E_6 - E_4^2)^2 + \frac{35}{72} E_4 (E_2 E_4 - E_6)^2, \\ \partial_{12}\partial_{10}F - \frac{5}{6} E_4 F &= \frac{25}{72}(E_2 E_6 - E_4^2)^2 + \frac{35}{72} E_4 (E_2 E_4 - E_6)^2 - \frac{5}{6} E_4 (E_2 E_4 - E_6)^2 \\ &= \frac{25}{72} ((E_2 E_6 - E_4^2)^2 - E_4 (E_2 E_4 - E_6)^2) \\ &= \frac{25}{72} (- E_2^2 E_4^3 + E_2^2 E_6^2 + E_4^4 - E_4 E_6^2) \\ &= -\frac{25}{72} (E_4^3 - E_6^2) (E_2^2 - E_4) \\ &= 7200 \cdot \frac{E_4^3 - E_6^2}{1728} \cdot \frac{-E_2^2 + E_4}{12}\\ &= 7200 \Delta (-E_2') \end{aligned}`
which proves (8.11).
Similarly, (8.12) can be proved using {bpref "prop:theta-der"}[] and
{bpref "lemma:lv1-lv2-identities"}[].
:::

:::corollary "cor:MLDE-pos" (lean := "MLDE_F_imag_axis_pos, MLDE_G_imag_axis_neg") (uses := "lemma:FG-de, cor:disc-pos, cor:theta-pos, def:E2")
(8.11) (resp. (8.12)) is positive (resp. negative) on the (positive) imaginary axis.
:::

:::proof "cor:MLDE-pos"
From (6.5) and {bpref "cor:disc-pos"}[],
$$`7200 (-E_2'(it)) \Delta(it) = 7200 \cdot 24 \left(\sum_{n \ge 1} n \sigma_1(n) e^{-2 \pi n t}\right) \cdot \Delta(it) > 0.`
Negativity of (8.12), i.e. $`-640 \Delta(it) H_2(it) < 0` follows from {bpref "cor:theta-pos"}[]
and {bpref "cor:disc-pos"}[].
:::

The second inequality (8.10) follows from the following two observations.
Since $`G(it) > 0` for all $`t > 0`, we can define the quotient
$$`Q(t) := \frac{F(it)}{G(it)} \tag{8.15}`
as a function on $`(0, \infty)`.

:::lemma_ "lemma:Qlim" (lean := "FmodG_rightLimitAt_zero") (uses := "lemma:E2-transform-S, lemma:Ek-is-modular-form, lemma:theta-transform-S-T")
We have
$$`\lim_{t \to 0^+} Q(t) = \frac{18}{\pi^2}.`
:::

:::proof "lemma:Qlim"
We have
$$`\lim_{t \to 0^+} Q(t) = \lim_{t \to 0^+} \frac{F(it)}{G(it)} = \lim_{t \to \infty} \frac{F(i/t)}{G(i/t)}.`
By using the transformation laws of Eisenstein series (6.6), (6.2) (for $`k = 4, 6`) and the
thetanull functions, (6.17), (6.19), we get
$$`\begin{aligned} F\left(\frac{i}{t}\right) &= t^{12} F(it) - \frac{12t^{11}}{\pi} (E_2(it)E_4(it) - E_6(it))E_4(it) + \frac{36t^{10}}{\pi^2}E_4(it)^2, \\ G\left(\frac{i}{t}\right) &= t^{10} H_{4}(it)^{3}(2H_{4}(it)^{2} + 5 H_{4}(it)H_{2}(it) + 5 H_{2}(it)^{2}). \end{aligned}`
Since $`F`, $`E_2 E_4 - E_6` and $`H_2` are cusp forms, we have $`\lim_{t \to \infty}t^k A(it) = 0`
when $`A(z)` is one of these forms and $`k \geq 0`.
From $`\lim_{t \to \infty} E_4(it) = 1 = \lim_{t \to \infty}H_{4}(it)`, we get
$$`\begin{aligned} \lim_{t \to \infty} \frac{F(i/t)}{G(i/t)} &= \lim_{t \to \infty} \frac{t^{12} F(it) - \frac{12t^{11}}{\pi} (E_2(it)E_4(it) - E_6(it))E_4(it) + \frac{36t^{10}}{\pi^2}E_4(it)^2}{t^{10} H_{4}(it)^{3}(2H_{4}(it)^{2} + 5 H_{4}(it)H_{2}(it) + 5 H_{2}(it)^{2})} \\ &= \lim_{t \to \infty} \frac{t^{2} F(it) - \frac{12t}{\pi} (E_2(it)E_4(it) - E_6(it))E_4(it) + \frac{36}{\pi^2}E_4(it)^2}{H_{4}(it)^{3}(2H_{4}(it)^{2} + 5 H_{4}(it)H_{2}(it) + 5 H_{2}(it)^{2})} \\ &= \frac{18}{\pi^2}. \end{aligned}`
:::

:::lemma_ "lemma:log-der-inf" (lean := "logderiv_tendsto_of_div_exp_tendsto, D_F_div_F_tendsto, D_G_div_G_tendsto") (uses := "lemma:der-q-series")
Let $`F` be a quasimodular form where the vanishing order of $`F` at infinity is $`n_0 > 0`, i.e.
$`F(z) = \sum_{n \geq n_0} a_n q^{n}` with $`a_{n_0} \ne 0`. Then
$$`\lim_{t \to \infty} \frac{F'(it)}{F(it)} = n_0.`
:::

:::proof "lemma:log-der-inf"
By {bpref "lemma:der-q-series"}[],
$$`\lim_{t \to \infty} \frac{F'(it)}{F(it)} = \lim_{t \to \infty} \frac{\sum_{n \ge n_0} n a_n e^{-2 \pi n t}}{\sum_{n \ge n_0} a_n e^{-2 \pi n t}} = \lim_{t \to \infty} \frac{n_0 a_{n_0} e^{-2 \pi n_0 t} + O(e^{-2 \pi (n_0 + 1) t})}{a_{n_0} e^{-2 \pi n_0 t} + O(e^{-2 \pi (n_0 + 1) t})} = n_0.`
:::

:::proposition "prop:Qdec" (lean := "FmodG_strictAntiOn") (uses := "thm:ramanujan-formula, thm:serre-der-prod-rule, cor:MLDE-pos, thm:anti-serre-der-pos, lemma:log-der-inf")
The function $`t \mapsto Q(t)` is strictly decreasing.
:::

:::proof "prop:Qdec"
It is enough to show that
$$`\begin{aligned} \frac{\dd}{\dd t} \left(\frac{F(it)}{G(it)}\right) < 0 &\Leftrightarrow (- 2\pi) \frac{F'(it)G(it) - F(it) G'(it)}{G(it)^{2}} < 0 \\ &\Leftrightarrow F'(it) G(it) - F(it) G'(it) > 0 \\ &\Leftrightarrow (\partial_{10}F)(it) G(it) - F(it) (\partial_{10}G)(it) > 0. \end{aligned}`
Let $`\mathcal{L}_{1, 0} := (\partial_{10}F) G - F (\partial_{10} G) = F'G - FG'`.
Then
$$`\frac{\mathcal{L}_{1, 0}}{FG} = \frac{F'G - FG'}{FG} = \frac{F'}{F} - \frac{G'}{G}`
The vanishing order of $`F` and $`G` at the infinity are $`2` and $`\frac{3}{2}` respectively, so
by {bpref "lemma:log-der-inf"}[], we have
$$`\lim_{t \to \infty} \frac{\mathcal{L}_{1, 0}(it)}{F(it) G(it)} = \lim_{t \to \infty} \left(\frac{F'(it)}{F(it)} - \frac{G'(it)}{G(it)}\right) = 2 - \frac{3}{2} = \frac{1}{2} > 0`
so $`\mathcal{L}_{1, 0}(it) > 0` for sufficiently large $`t`.
Its Serre derivative $`\partial_{22} \mathcal{L}_{1, 0}` is positive by {bpref "cor:MLDE-pos"}[]:
$$`\partial_{22} \mathcal{L}_{1, 0} = (\partial_{12} \partial_{10} F) G - F (\partial_{12}\partial_{10} G) = \Delta (7200 (-E_{2}') G + 640 H_2 F) > 0.`
Hence $`\mathcal{L}_{1, 0}(it) > 0` by {bpref "thm:anti-serre-der-pos"}[], and the monotonicity
follows.
:::

:::corollary "cor:ineqBnew" (lean := "FG_inequality_2") (uses := "lemma:Qlim, prop:Qdec, lemma:F-G-pos")
(8.10) holds.
:::

:::proof "cor:ineqBnew"
$$`\frac{F(it)}{G(it)} = Q(t) < \lim_{u \to 0^+} Q(u) = \frac{18}{\pi^2}`
and multiplying by $`G(it) > 0` ({bpref "lemma:F-G-pos"}[]), (8.10) follows.
:::

Finally, we are ready to prove {bpref "thm:g"}[].

*TODO (audit note): with the definitions of $`a` and $`b` used in this blueprint (and in the Lean
code), the magic function is $`(\pi i/8640)a - (i/(240\pi))b`: for $`r > \sqrt{2}` one has
$`a(r) = 4i \sin^2(\pi r^2/2)\int_0^\infty t^2\phi_0(i/t)e^{-\pi r^2 t}\,dt` and
$`b(r) = -4i \sin^2(\pi r^2/2)\int_0^\infty \psi_I(it)e^{-\pi r^2 t}\,dt`
({bpref "prop:a-double-zeros"}[] and {bpref "prop:b-double-zeros"}[]), so only the minus
combination produces the integrand $`A(t) < 0`. The Lean declaration `g` currently uses the plus
sign and must be corrected accordingly.*

:::theorem "thm:g1" (lean := "g, g_nonpos, g_Fourier_nonneg, g_zero, fourier_g_zero") (uses := "prop:a-fourier, prop:b-fourier, prop:a-double-zeros, prop:b-double-zeros, prop:ineqA, prop:ineqB, prop:a0, prop:b0")
The function
$$`g(x):=\frac{\pi\,i}{8640}a(x)-\frac{i}{240\pi}\,b(x)`
satisfies conditions (5.5)–(5.7).
:::

:::proof "thm:g1"
Note first that, by {bpref "prop:a-fourier"}[] and {bpref "prop:b-fourier"}[],
$$`\widehat{g}=\frac{\pi\,i}{8640}\,a+\frac{i}{240\pi}\,b.`

We prove that (5.5) holds. By {bpref "prop:a-double-zeros"}[] and {bpref "prop:b-double-zeros"}[],
parametrising the contours by $`z = it`, we know that for $`r>\sqrt{2}`
$$`a(r) = 4i\,\sin(\pi r^2/2)^2\int\limits_0^\infty t^2\,\phi_0(i/t)\,e^{-\pi r^2 t}\,dt, \qquad b(r) = -4i\,\sin(\pi r^2/2)^2\int\limits_0^\infty \psi_I(it)\,e^{-\pi r^2 t}\,dt,`
and hence, since $`\frac{\pi i}{8640}\cdot 4i = -\frac{\pi}{2160}` and
$`\frac{i}{240\pi}\cdot 4i = -\frac{\pi}{2160}\cdot\frac{36}{\pi^2}`,
$$`g(r)=\frac{\pi}{2160}\,\sin(\pi r^2/2)^2\,\int\limits_0^\infty A(t)\,e^{-\pi r^2 t}\,dt \tag{8.16}`
where $`A` is as in (8.1).
From {bpref "prop:ineqA"}[] we know that $`A(t)<0` for $`t\in(0,\infty)`.
Therefore identity (8.16) implies (5.5).

Next, we prove (5.6). By {bpref "prop:a-another-integral"}[] and
{bpref "prop:b-another-integral"}[] (which are valid on all of $`[0, \infty)`), the same
bookkeeping gives, for $`r>0`,
$$`\widehat{g}(r)=\frac{\pi}{2160}\,\sin(\pi r^2/2)^2\,\int\limits_0^\infty B(t)\,e^{-\pi r^2 t}\,dt \tag{8.17}`
where $`B` is as in (8.3), and $`B(t) > 0` for $`t \in (0, \infty)` by {bpref "prop:ineqB"}[].
Hence $`\widehat{g}(r) \geq 0` for $`r > 0`, and $`\widehat{g}(0) = 1 > 0` by the computation
below.

Finally, the property (5.7) readily follows from {bpref "prop:a0"}[] and {bpref "prop:b0"}[]:
$$`g(0) = \widehat{g}(0) = \frac{\pi i}{8640}\cdot\frac{-8640\,i}{\pi} = 1.`
This finishes the proof of {bpref "thm:g1"}[] and {bpref "thm:g"}[].
:::
