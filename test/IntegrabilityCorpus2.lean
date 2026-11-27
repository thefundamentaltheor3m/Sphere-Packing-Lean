import Mathlib
import SpherePacking.Tactic.EndpointIntegrability.Tactic

/-!
# Integrability corpus, second sample (held-out check)

Purpose: a second, independent sample of real integrability goals taken from other Lean 4
projects, drawn by the same procedure as `test/IntegrabilityCorpus.lean` (the first sample) with a
new seed and with every goal of the first sample excluded, to be used as a held-out check for
integrability automation. Each `example` restates one goal from a source project as faithfully as
possible (same domain, same measure, same integrand shape; not simplified or normalised). Proofs
are intentionally omitted (`sorry`): this file only records the goals. It is deliberately outside
the Lake library so that it can `import Mathlib`; check it with
`lake env lean test/IntegrabilityCorpus2.lean` (only `declaration uses 'sorry'` and
unused-variable warnings are expected).

## Status

This sample was drawn after `endpoint_integrability` existed, but blind to it: no tactic was run
on these goals while they were collected, the tactic's code was not consulted, and nothing about
it influenced which candidates were kept or how they were restated. The only reasons for skipping
a drawn candidate are the skip rules below. The tags `kind`, `domain` and `integrand` of the
entries were assigned at that time.

The sample was then scored once, on 2026-11-24, with the tactic at commit 4876790, and never used
to choose a feature before that: **13 of the 100 goals were proved** (plain `fun_prop` proves
none), 12 of the 49 whose tags describe an explicit integrand over an interval of `ℝ`. That is
the held-out result. Since then this sample is development data like the first one: its open
entries were triaged by cause, and features were chosen from the triage (three fixes, then
integrable factors as comparison functions).

Each entry carries a `status:` line written by the scorer, `test/scripts/run.sh
test/IntegrabilityCorpus2.lean <work dir> endpoint_integrability
SpherePacking.Tactic.EndpointIntegrability.Tactic mark` (last run on 2026-11-26, with the tactic
at commit 877d268, after those changes and after the tactic was simplified and features which a
`have` replaces were removed; it stood at 21 before):

* `proved by endpoint_integrability` (15 entries);
* `out of scope: …` (50 entries), assigned only to goals which are not proved, from their tags:
  not an integral over an interval of `ℝ` (27), an abstract integrand (13), a domination
  hypothesis (10);
* `open: …` (35 entries): not proved and not excluded by its tags, with the goals left or the
  error.

Two caveats. The collectors read the first sample, including its `status:` lines, to learn the
format. And the documented shuffle, applied to the saved candidate lists with the seed of the
first sample, reproduces the order of the first sample only for the PhysLean records and for the
PrimeNumberTheoremAnd and PhysLean domination sites; for the other groups the first sample was
not drawn in the documented order, for a reason which was not found. This sample follows the
documented procedure literally; the frozen orders were fixed before any candidate was read.

## Sources and licence

All source projects are Apache-2.0 licensed; the statements below are taken (restated) from them
with attribution. Every entry names its repository, commit and `file:line`. The projects and
commits are those of the first sample.

* AlexKontorovich/PrimeNumberTheoremAnd @ a4fb6989b07e9c76b511807ae93e33e25b820e9b
* AlexKontorovich/quasi-rh              @ d26d846d6f3129017f06b6fd3f78dd72d361d60b
* PhysLean (HEPLean/PhysLean)            @ 44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc
* TauCetiProject/TauCeti                 @ fb3fbc9f05780f456267a29168dfae7a98c2d8d0
* fpvandoorn/carleson                    @ f7487cc9da4d1e73f009dc0280cd5b958f3e2c78
* RemyDegenne/brownian-motion            @ 8fd8dc52830cdd07cf9cc8eadd533e284425fa6f

## Sampling

Candidates: the candidate lists of the first sample, unchanged (the same regex survey for
top-level `theorem`/`lemma` statements whose conclusion, and in-proof `have`s whose type, mentions
`Integrable`, `IntegrableOn`, `IntervalIntegrable` or `HasFiniteIntegral`; domination candidates
are the call sites of the dominated-convergence / parametric-integral lemmas
`tendsto_integral_(filter_)of_dominated_convergence`, `hasSum_integral_of_dominated_convergence`,
`hasDerivAt_integral_of_dominated_loc_of_(deriv_le|lip)`, `hasFDerivAt_integral_of_dominated_*`,
`continuous(On|At|WithinAt)_of_dominated(_interval)`). Per project (carleson and brownian-motion
pooled), the records were sorted by (project, file, line) and shuffled with Python
`random.Random(20261124).shuffle` (seed 20261124; a fresh generator per project, records shuffled
first, then the domination sites by the same generator). Records: 434 PrimeNumberTheoremAnd,
206 quasi-rh, 338 PhysLean, 4638 TauCeti, 125 carleson + brownian-motion; domination sites:
21, 13, 42, 223, 7.

Exclusion of the first sample: every candidate whose repository, file and line is those of a
first-sample entry was removed from the shuffled lists (all 100 first-sample entries matched a
candidate: 90 records and 10 domination sites). In addition, a drawn candidate which is the same
statement as a first-sample entry (for instance a verbatim copy of the same `have` elsewhere in
the file, or the same lemma instantiated) was skipped, as rule (x) below.

The shuffled lists were walked in order until the quotas of the first sample were met, separately
for records and for domination sites. A drawn candidate was skipped only for:
(a) it cannot be made self-contained without more than ~15 lines of supporting definitions,
(b) it duplicates an already collected goal of this sample up to renaming, (c) the hit is not
actually an integrability goal (hypothesis-only occurrence, iff used as a rewrite, a different
notion such as `VectorMeasure.Integrable`), (x) it is the same statement as a first-sample entry.
The judgement calls of the first sample were applied in the same way: (a) covers a project object
whose only usable property is a project lemma that is, up to algebra, the goal itself, a
domination site inside a wrapper lemma that passes its own integrability and bound hypotheses
straight through (the entry would be two of its own binders; a site whose bound is a parameter
but whose a.e. bound still needs an argument is kept), and existential
"there is ... such that ... Integrable ..." statements; (c) covers PhysLean's
`VectorMeasure.Integrable` hits; (b) and (x) treat goals with the same integrand but different
hypotheses in context as different.

Every project's remaining candidates sufficed for its quota.

| project               | entries | of which domination | records drawn | sites drawn | skips (a / b / c / x) |
|-----------------------|---------|---------------------|---------------|-------------|-----------------------|
| PrimeNumberTheoremAnd | 45      | 4                   | 47            | 5           | 1 / 1 / 0 / 5         |
| quasi-rh              | 20      | 2                   | 20            | 2           | 1 / 0 / 0 / 1         |
| PhysLean              | 15      | 2                   | 16            | 2           | 1 / 0 / 2 / 0         |
| TauCeti               | 15      | 2                   | 17            | 2           | 1 / 0 / 3 / 0         |
| carleson + brownian   | 5       | 0                   | 5             | 0           | 0 / 0 / 0 / 0         |
| total                 | 100     | 10                  | 105           | 11          | 4 / 1 / 5 / 6         |

By kind: 55 `have`, 35 `statement`, 10 `domination`.
By domain: 24 whole line, 13 bounded interval, 15 interval integral, 16 half-line,
17 ℝⁿ/product, 15 abstract measure.
By integrand: 26 explicit, 39 explicit with opaque factor, 35 abstract.

## Conventions

Those of the first sample:

* Variables and hypotheses the goal depends on are binders. For a `have`, the binders are the
  relevant part of its local context (enclosing hypotheses and preceding `have`s it relies on).
* A project definition is inlined when it unfolds in a few lines to Mathlib terms; otherwise it is a
  variable function together with exactly the hypotheses the original proof used about it. Each
  entry's `notes:` says what was inlined or abstracted.
* `domination` entries state the integrability-plus-a.e.-bound hypotheses of the dominated
  convergence lemma that the project called, with the project's *concrete* bound, as a conjunction
  `Integrable bound μ ∧ ∀ᵐ …` (in the shape that lemma expects; for the interval versions,
  `IntervalIntegrable bound volume a b ∧ ∀ᵐ t, t ∈ Set.uIoc a b → …`).
* `original proof:` records how the project proved the goal, in one phrase.
* TauCeti paths are written from the repository root (`TauCeti/…`).
-/

set_option autoImplicit false

section PrimeNumberTheoremAnd

open MeasureTheory Set Filter Topology Real FourierTransform
open Complex (I)
open scoped ContDiff

/- [PNTB-001] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/LaplaceInversion.lean:415
   kind: statement
   domain: whole line
   integrand: explicit with opaque factor
   original proof: `hf.mono` with the unit-modulus bound `‖exp (i θ)‖ = 1`
   notes: the file-level variable `E` (complex normed space) is a binder.
   status: proved by `endpoint_integrability` -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℝ → E} (hf : Integrable f)
    (T : ℝ) :
    Integrable (fun v : ℝ => Complex.exp (-(((T * v : ℝ) : ℂ) * I)) • f v) := by
  endpoint_integrability

/- [PNTB-002] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/MellinCalculus.lean:245
   kind: have
   domain: half-line
   integrand: abstract
   original proof: support in `Icc a b` (`integrableOn_iff_integrable_of_support_subset`), then continuity on compact
   notes: enclosing hypotheses kept; the preceding `have Icc_sub` is a hypothesis.
   status: out of scope: abstract integrand; needs closure rules (`fun_prop`), not a leaf solver -/
example {a b : ℝ} (f g : ℝ → ℂ) (ha : 0 < a) (h : a ≤ b) (fSupp : f.support ⊆ Set.Icc a b)
    (fDiff : DifferentiableOn ℝ f (Ioi 0)) (gDiff : DifferentiableOn ℝ g (Ioi 0))
    (fderivCont : ContinuousOn (deriv f) (Ioi 0)) (gderivCont : ContinuousOn (deriv g) (Ioi 0))
    (Icc_sub : Icc a b ⊆ Ioi 0) :
    IntegrableOn (f * deriv g) (Ioi 0) := by
  sorry

/- [PNTB-003] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/Unused/Fejer_I_know_this_is_dirty_but_it_typechecks.lean:1217
   kind: have
   domain: bounded interval
   integrand: abstract
   original proof: `IntegrableOn.union` of two consecutive period intervals up to set equality
   notes: local hypotheses (integrability on every period interval, choice of `m`) kept.
   status: out of scope: abstract integrand; needs closure rules (`fun_prop`), not a leaf solver -/
example {f : ℝ → ℝ} {x₀ : ℝ}
    (h_integrable : ∀ m : ℤ,
      IntegrableOn f (Set.Icc (-Real.pi + m * 2 * Real.pi) (Real.pi + m * 2 * Real.pi)))
    (m : ℤ)
    (hm : x₀ - Real.pi ∈ Set.Icc (-Real.pi + m * 2 * Real.pi) (Real.pi + m * 2 * Real.pi)) :
    IntegrableOn f
      (Set.Icc (-Real.pi + m * 2 * Real.pi) (Real.pi + m * 2 * Real.pi + 2 * Real.pi)) := by
  sorry

/- [PNTB-004] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/LiSeries.lean:219
   kind: statement
   domain: half-line
   integrand: explicit
   original proof: comparison (`mono`) with `exp (-t)`, itself from the Gamma integral at `s = 1`
   notes:
   status: proved by `endpoint_integrability` -/
example : IntegrableOn (fun t => exp (-t) / t) (Set.Ioi 1) := by
  endpoint_integrability

/- [PNTB-005] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/CH2/CH2_part1.lean:4198
   kind: have
   domain: bounded interval
   integrand: explicit with opaque factor
   original proof: closure lemmas (`(hci a b).add (hsi a b)` up to congruence)
   notes: `Phi_circ ν ε`, `Phi_star ν ε` (project functions) are variable functions `Pc`, `Ps` with
     the preceding `hci`, `hsi` (the facts the proof used) as hypotheses; the local `fR` and
     `E z = Complex.exp (2 * π * I * z)` inlined.
   status: open: goals left: locallyIntegrableOn, nhdsGT, nhdsLT -/
example (x : ℝ) (Pc Ps : ℂ → ℂ)
    (hci : ∀ (a b : ℝ), IntegrableOn
      (fun t : ℝ ↦ Pc (↑t : ℂ) * Complex.exp (2 * π * I * (-(↑t : ℂ) * ↑x))) (Set.Ioc a b))
    (hsi : ∀ (a b : ℝ), IntegrableOn
      (fun t : ℝ ↦ Ps (↑t : ℂ) * Complex.exp (2 * π * I * (-(↑t : ℂ) * ↑x))) (Set.Ioc a b))
    (a b : ℝ) :
    IntegrableOn
      (fun t : ℝ ↦ (Pc (t : ℂ) + Ps (t : ℂ)) * Complex.exp (2 * π * I * (-(t : ℂ) * x)))
      (Set.Ioc a b) := by
  sorry

/- [PNTB-006] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/Unused/Fejer_I_know_this_is_dirty_but_it_typechecks.lean:540
   kind: have
   domain: bounded interval
   integrand: abstract
   original proof: periodicity: indicator rewrite + `comp_sub_right`, then congruence by `Periodic.int_mul`
   notes: `hg_int` in the form it has at this point (rewritten to `IntegrableOn` on `Icc (-π) π`).
   status: out of scope: abstract integrand; needs closure rules (`fun_prop`), not a leaf solver -/
example (g : ℝ → ℝ) (hg_per : Function.Periodic g (2 * Real.pi))
    (hg_int : IntegrableOn g (Set.Icc (-Real.pi) Real.pi) volume) :
    ∀ n : ℤ,
      IntegrableOn g (Set.Icc (-Real.pi + 2 * Real.pi * n) (Real.pi + 2 * Real.pi * n)) := by
  sorry

/- [PNTB-007] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/LaplaceInversion.lean:2272
   kind: have
   domain: interval integral
   integrand: explicit with opaque factor
   original proof: project lemma `intervalIntegrable_sin_div_kernel_error_of_intervalIntegrable_quotient`
     applied to `hq`, for every `T`
   notes: the file-level variable `E` is a binder; only the enclosing hypotheses the goal depends on
     are kept (`htail` dropped).
   status: open: unsupported goal -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℝ → E} {x R : ℝ} (hR : 0 < R)
    (hq : IntervalIntegrable
      (fun u : ℝ => if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x))
      volume (-R) R) :
    ∀ᶠ T in Filter.atTop,
      IntervalIntegrable
        (fun u : ℝ =>
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • (f (x - u) - f x))
        volume (-R) R := by
  sorry

/- [PNTB-008] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/Unused/Fejer_I_know_this_is_dirty_but_it_typechecks.lean:534
   kind: have
   domain: bounded interval
   integrand: abstract
   original proof: instance of the preceding `h_integrable` (`h_integrable _`)
   notes: the preceding `have h_integrable` (integrability on every period interval) is a hypothesis.
   status: out of scope: abstract integrand; needs closure rules (`fun_prop`), not a leaf solver -/
example (g : ℝ → ℝ) (a : ℝ)
    (h_integrable : ∀ n : ℤ,
      IntegrableOn g (Set.Icc (-Real.pi + 2 * Real.pi * n) (Real.pi + 2 * Real.pi * n))) :
    IntegrableOn g (Set.Icc (-Real.pi + 2 * Real.pi * ⌊(a + Real.pi) / (2 * Real.pi)⌋)
      (Real.pi + 2 * Real.pi * ⌊(a + Real.pi) / (2 * Real.pi)⌋)) := by
  sorry

/- [PNTB-009] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/ZetaAppendix.lean:303
   kind: have
   domain: interval integral
   integrand: explicit with opaque factor
   original proof: project lemma `intervalIntegrable_term1` (continuity on compact, `deriv φ ≠ 0`)
   notes: `e α = Complex.exp (2 * π * I * α)` inlined; hypotheses are those of the project lemma.
   status: open: goals left: locallyIntegrableOn, nhdsGT, nhdsLT -/
example (σ : ℝ) (φ : ℝ → ℝ) (a b : ℝ) (hab_le : a ≤ b) (ha_pos : 0 < a)
    (h_phi_cont : ContinuousOn φ (Set.Icc a b))
    (h_deriv_cont : ContinuousOn (fun t ↦ deriv φ t) (Set.Icc a b))
    (h_phi_ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) :
    IntervalIntegrable
      (fun x ↦ ((x ^ (-σ - 1) : ℝ) : ℂ) / (2 * π * I * ↑(deriv φ x)) *
        Complex.exp (2 * π * I * (φ x : ℂ))) volume a b := by
  sorry

/- [PNTB-010] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/Ramanujan/RamanujanCalculations.lean:184
   kind: have
   domain: bounded interval
   integrand: abstract
   original proof: `hInt.mono_set`
   notes:
   status: out of scope: abstract integrand; needs closure rules (`fun_prop`), not a leaf solver -/
example (f : ℝ → ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hInt : IntegrableOn f (Set.Icc a c) volume) :
    IntegrableOn f (Set.Icc a b) volume := by
  sorry

/- [PNTB-011] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/LaplaceInversion.lean:1005
   kind: statement
   domain: interval integral
   integrand: explicit
   original proof: congr_ae with the continuous `sinc` reformulation
   notes: removable singularity at 0 handled by an `if`.
   status: open: failed to prove -/
example (a b : ℝ) :
    IntervalIntegrable
      (fun v : ℝ => if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ))
      volume a b := by
  sorry

/- [PNTB-012] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/CH2/CH2_part1.lean:5090
   kind: have
   domain: bounded interval
   integrand: explicit
   original proof: continuity on compact (project lemma `B.continuous_ofReal`)
   notes: `B ε s = if s = 0 then 1 else s * (coth (s / 2) + ε) / 2` and `coth z = 1 / tanh z`
     (project definitions) inlined; the local `φ` inlined.
   status: open: goals left: locallyIntegrableOn, nhdsGT, nhdsLT -/
example (ν T ε u : ℝ) :
    IntegrableOn
      (fun t : ℝ ↦
        ((if ((ν : ℂ) - (t : ℂ)) = 0 then 1 else
            ((ν : ℂ) - (t : ℂ)) * (1 / Complex.tanh (((ν : ℂ) - (t : ℂ)) / 2) + ε) / 2) -
          (if (ν : ℂ) = 0 then 1 else (ν : ℂ) * (1 / Complex.tanh ((ν : ℂ) / 2) + ε) / 2)) *
          (Real.exp (u * t) : ℂ))
      (Set.Icc 0 T) := by
  sorry

/- [PNTB-013] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/Wiener.lean:3195
   kind: have
   domain: whole line
   integrand: abstract
   original proof: `hnorm.indicator measurableSet_Ici`
   notes: the enclosing scalar `A` (unused by the goal) dropped.
   status: out of scope: abstract integrand; needs closure rules (`fun_prop`), not a leaf solver -/
example (F : ℝ → ℂ) (a : ℝ) (hF : IntegrableOn F (Set.Ici a))
    (hnorm : Integrable (fun u : ℝ => ‖F u‖)) :
    Integrable (Set.indicator (Set.Ici a) (fun u => ‖F u‖)) := by
  sorry

/- [PNTB-014] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/LaplaceInversion.lean:1766
   kind: have
   domain: half-line
   integrand: explicit
   original proof: project lemma `integrableOn_exp_neg_mul_sinc` (domination by `exp (-a x)`) + `mono_set`
   notes: the preceding `hR_pos` is a hypothesis.
   status: open: goals left: atTop -/
example {a R : ℝ} (ha : 0 < a) (hR : 1 ≤ R) (hR_pos : 0 < R) :
    IntegrableOn (fun x : ℝ => Real.exp (-a * x) * Real.sinc x) (Set.Ioi R) := by
  sorry

/- [PNTB-015] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/Unused/Fejer_I_know_this_is_dirty_but_it_typechecks.lean:1603
   kind: have
   domain: bounded interval
   integrand: abstract
   original proof: rewrite `intervalIntegrable_iff_integrableOn_Icc_of_le` at `hg_int`
   notes: the other enclosing hypothesis (`hg_lim`, a limit at `0⁺`) dropped.
   status: out of scope: abstract integrand; needs closure rules (`fun_prop`), not a leaf solver -/
example {g : ℝ → ℝ} (hg_int : IntervalIntegrable g MeasureTheory.volume 0 Real.pi) :
    IntegrableOn g (Set.Icc 0 Real.pi) := by
  sorry

/- [PNTB-016] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/EulerMaclaurin.lean:42
   kind: statement
   domain: interval integral
   integrand: explicit with opaque factor
   original proof: `continuousOn_mul` with a bounded measurable factor (`|B1 x| ≤ 1 / 2`)
   notes: `B1 x = x - ⌊x⌋₊ - 1 / 2` (first Bernoulli function) inlined; `[[a, b]]` written `Set.uIcc a b`.
   status: open: goals left: locallyIntegrableOn, nhdsGT, nhdsLT -/
example {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h_cont : ContinuousOn (deriv f) (Set.uIcc a b)) :
    IntervalIntegrable (fun t ↦ deriv f t * ((t - ⌊t⌋₊ - 1 / 2 : ℝ) : 𝕜)) volume a b := by
  sorry

/- [PNTB-017] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/Li2Bounds.lean:100
   kind: statement
   domain: interval integral
   integrand: explicit
   original proof: `mono_set` from integrability on `[0, 1]` (bounded by 2, certified LeanCert bound)
   notes: `g = LeanCert.CertifiedBounds.Li2.integrand` inlined as `1 / log (1 + t) + 1 / log (1 - t)`
     (checked against LeanCert at the revision pinned by the project, d3e7f686eb6b: `integrand` is
     `Li2.g = symmetricLogCombination`, defined as this sum).
   status: open: goals left: continuity, nhdsGT, nhdsLT -/
example (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / log (1 + t) + 1 / log (1 - t)) volume a b := by
  sorry

/- [PNTB-018] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/Wiener.lean:3379
   kind: have
   domain: whole line
   integrand: explicit with opaque factor
   original proof: `hR.mono'` (domination by `K * ‖ψ t‖`)
   notes: enclosing hypotheses kept; the preceding `hmeas_main`, `hpt`, `hR` are hypotheses.
   status: open: goals left: locallyIntegrableOn, atBot, atTop -/
example (G : ℂ → ℂ) (ψ : ℝ → ℂ) (x K : ℝ)
    (hGline_meas : Measurable (fun t : ℝ => G (1 + t * I)))
    (hψ_meas : AEStronglyMeasurable ψ) (hx : 0 < x)
    (hK : ∀ t : ℝ, t ∈ Function.support ψ → ‖G (1 + t * Complex.I)‖ ≤ K)
    (hψ : Integrable (fun t : ℝ => ‖ψ t‖))
    (hmeas_main : AEStronglyMeasurable
      (fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))))
    (hpt : (fun t : ℝ => ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖)
      ≤ᵐ[volume] (fun t : ℝ => K * ‖ψ t‖))
    (hR : Integrable (fun t : ℝ => K * ‖ψ t‖)) :
    Integrable (fun t : ℝ =>
      ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖) := by
  sorry

/- [PNTB-019] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/CartanBound.lean:406
   kind: statement
   domain: interval integral
   integrand: explicit
   original proof: the integrand vanishes on `[A, 2A]` (congruence with `0`)
   notes: `φ t = log⁺ (1 / |1 - t|)` inlined (`Real.posLog`).
   status: proved by `endpoint_integrability` -/
example {A : ℝ} (hA : (2 : ℝ) ≤ A) :
    IntervalIntegrable (fun t : ℝ => Real.posLog (1 / |1 - t|)) volume A (2 * A) := by
  endpoint_integrability

/- [PNTB-020] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/Mertens.lean:245
   kind: have
   domain: half-line
   integrand: explicit
   original proof: library lemma `(integrableOn_exp_neg_Ioi 0).const_mul _`
   notes:
   status: proved by `endpoint_integrability` -/
example (s : ℝ) (hs : 1 < s) :
    IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) := by
  endpoint_integrability

/- [PNTB-021] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/KadiriEq12Helpers.lean:180
   kind: statement
   domain: whole line
   integrand: explicit with opaque factor
   original proof: big-O lemmas (local integrability + `=O` at `atTop`/`atBot` against exponentials)
   notes:
   status: open: goals left: atBot, atTop -/
open Asymptotics in
example {φ : ℝ → ℂ} {b σ : ℝ} (hφ : Continuous φ)
    (hφ_decay : (fun x : ℝ ↦ φ x * Complex.exp ((x:ℂ)/2)) =O[cocompact ℝ]
      fun x ↦ Real.exp (-(1/2+b)*|x|))
    (hσ_top : -(1+b) < σ) (hσ_bot : σ < b) :
    Integrable (fun y : ℝ ↦ φ y * Complex.exp (-(σ:ℂ)*y)) := by
  sorry

/- [PNTB-022] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/LaplaceInversion.lean:1712
   kind: have
   domain: half-line
   integrand: explicit
   original proof: library lemma `integrableOn_exp_mul_complex_Ioi`
   notes: local `z = -a + I` inlined; the preceding `hzre` is a hypothesis.
   status: proved by `endpoint_integrability` -/
example (a : ℝ) (ha : 0 < a) (hzre : ((-(a : ℂ)) + Complex.I).re < 0) :
    Integrable (fun x : ℝ => Complex.exp (((-(a : ℂ)) + Complex.I) * x))
      (volume.restrict (Set.Ioi 0)) := by
  endpoint_integrability

/- [PNTB-023] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/KadiriEq14.lean:643
   kind: have
   domain: whole line
   integrand: explicit with opaque factor
   original proof: project lemma `kadiri_laplace_positive_line_weight_integrable`, then `smul_eq_mul`
   notes: local `F` inlined; only the enclosing hypotheses the goal depends on are kept.
   status: open: goals left: locallyIntegrableOn, atBot, atTop -/
open Asymptotics in
example {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * Complex.exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    Integrable (fun y : ℝ => Complex.exp (-((a : ℂ) * (y : ℂ))) • φ y) := by
  sorry

/- [PNTB-024] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/LaplaceInversion.lean:1041
   kind: statement
   domain: interval integral
   integrand: explicit
   original proof: project lemma `intervalIntegrable_scaled_sin_div_kernel`, then `smul_const`
   notes: the file-level variable `E` is a binder; removable singularity at 0 handled by an `if`.
   status: open: failed to prove -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z : E) (T a b : ℝ) :
    IntervalIntegrable
      (fun u : ℝ =>
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • z)
      volume a b := by
  sorry

/- [PNTB-025] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/Fourier.lean:68
   kind: have
   domain: whole line
   integrand: explicit with opaque factor
   original proof: `Integrable.const_mul` of the structure field (`f.integrable le_rfl`)
   notes: `f : W21` unpacked into its fields (`smooth`, `integrable`).
   status: open: goals left: locallyIntegrableOn, atBot, atTop -/
example (f : ℝ → ℂ) (smooth : ContDiff ℝ 2 f)
    (integrable : ∀ ⦃k : ℕ⦄, k ≤ 2 → Integrable (iteratedDeriv k f)) :
    Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
  sorry

/- [PNTB-026] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/CH2/CH2_part1.lean:3553
   kind: have
   domain: bounded interval
   integrand: explicit with opaque factor
   original proof: continuity on compact (`ContinuousOn.integrableOn_compact`)
   notes: `E z = Complex.exp (2 * π * I * z)` inlined; the `have`'s own arguments `T`, `F`, `hF` are
     binders.
   status: open: goals left: locallyIntegrableOn, nhdsGT, nhdsLT -/
example (x : ℝ) (T : ℝ) (F : ℂ → ℂ)
    (hF : ∀ t ∈ Set.Icc (0 : ℝ) T, ContinuousAt (fun y : ℝ ↦ F (I * ↑y)) t) :
    Integrable (fun t : ℝ ↦ F (I * ↑t) * Complex.exp (2 * π * I * (-(I * ↑t) * ↑x)))
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  sorry

/- [PNTB-027] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/Mertens.lean:1504
   kind: statement
   domain: half-line
   integrand: explicit with opaque factor
   original proof: `Integrable.mono'` with explicit bound `B * x ^ (a - s)` (`integrableOn_Ioi_rpow_of_lt`)
   notes:
   status: proved by `endpoint_integrability` -/
example {c B a s : ℝ} (hc : 0 < c) (has : a + 1 < s) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x ∈ Set.Ioi c, |f x| ≤ B * x ^ a) :
    MeasureTheory.IntegrableOn (fun x => f x * x ^ (-s)) (Set.Ioi c) := by
  endpoint_integrability

/- [PNTB-028] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/CartanBound.lean:717
   kind: have
   domain: interval integral
   integrand: explicit
   original proof: library lemma `intervalIntegrable_const`
   notes: `Cφ` (project constant `Real.log 2 + 4 * K + 1`, `K` another project constant) kept as a
     real variable.
   status: proved by `endpoint_integrability` -/
example {ι : Type} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (Cφ : ℝ) {R : ℝ}
    (hR : 0 < R) :
    IntervalIntegrable (fun _r : ℝ => Cφ * (∑ i ∈ s, w i)) volume R (2 * R) := by
  endpoint_integrability

/- [PNTB-029] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/Wiener.lean:3448
   kind: have
   domain: whole line
   integrand: abstract
   original proof: project lemma `integrable_norm_fourier_scaled_of_CS2`
   notes: `ψ : CS 2 ℂ` (structure: `ContDiff ℝ 2` + `HasCompactSupport`) unpacked into its fields.
   status: out of scope: abstract integrand; needs closure rules (`fun_prop`), not a leaf solver -/
example (ψ : ℝ → ℂ) (h1 : ContDiff ℝ 2 ψ) (h2 : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
  sorry

/- [PNTB-030] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/LaplaceInversion.lean:841
   kind: have
   domain: whole line
   integrand: abstract
   original proof: library lemma `Integrable.comp_sub_left`
   notes:
   status: out of scope: abstract integrand; needs closure rules (`fun_prop`), not a leaf solver -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℝ → E} (hf : Integrable f)
    (x : ℝ) :
    Integrable (fun u : ℝ => f (x - u)) := by
  sorry

/- [PNTB-031] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/Mertens.lean:709
   kind: statement
   domain: half-line
   integrand: explicit
   original proof: `integrableOn_Ioi_deriv_of_nonneg'` (explicit antiderivative)
   notes:
   status: open: goals left: atTop -/
example : MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  sorry

/- [PNTB-032] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/CH2/CH2_part1.lean:3396
   kind: statement
   domain: bounded interval
   integrand: explicit with opaque factor
   original proof: continuity on compact (`ContinuousOn.integrableOn_compact`, `fun_prop`)
   notes: `E z = Complex.exp (2 * π * I * z)` inlined.
   status: proved by `endpoint_integrability` -/
example (a b x : ℝ) (f : ℝ → ℂ) (p : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc a b))
    (hp : ContinuousOn p (Set.Icc a b)) :
    Integrable (fun t ↦ f t * Complex.exp (2 * π * I * (-p t * x)))
      (volume.restrict (Set.Icc a b)) := by
  endpoint_integrability

/- [PNTB-033] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/KadiriEq15.lean:327
   kind: have
   domain: whole line
   integrand: explicit with opaque factor
   original proof: project lemma `kadiri_laplace_strip_weight_deriv_integrable`
   notes: local `g y = exp (σ * y) * φ y` inlined; hypotheses are those of the project lemma.
   status: open: goals left: locallyIntegrableOn, atBot, atTop -/
example {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * Complex.exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * Complex.exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a σ : ℝ} (ha : 0 < a) (hab : a < b) (hσlo : -a ≤ σ) (hσhi : σ ≤ 1 / 2) :
    Integrable (deriv (fun y : ℝ => Complex.exp ((σ : ℂ) * (y : ℂ)) * φ y)) := by
  sorry

/- [PNTB-034] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/LaplaceInversion.lean:707
   kind: statement
   domain: whole line
   integrand: explicit with opaque factor
   original proof: `Integrable.mono` against `C • f (x - u)` with `C = 1 / (π * R)`
   notes:
   status: open: goals left: locallyIntegrableOn, atBot, atTop -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℝ → E} (hf : Integrable f)
    (x : ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable ((Set.Ioc (-R) R)ᶜ.indicator
      (fun u : ℝ => (if u = 0 then (0 : ℂ) else (1 / (π * u) : ℂ)) • f (x - u))) := by
  sorry

/- [PNTB-035] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/Unused/Fejer_I_know_this_is_dirty_but_it_typechecks.lean:750
   kind: have
   domain: bounded interval
   integrand: abstract
   original proof: periodicity: integrable on every period interval, union of two, `mono_set`, then
     indicator rewrite + `comp_sub_left`
   notes: the preceding `h_integrable` (for `|f t|` on `[-π, π]`) is a hypothesis; unused binders of
     the enclosing theorem omitted.
   status: out of scope: abstract integrand; needs closure rules (`fun_prop`), not a leaf solver -/
example (f : ℝ → ℝ) (hf_int : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (hf_per : Function.Periodic f (2 * Real.pi)) (x : ℝ)
    (h_integrable : MeasureTheory.IntegrableOn (fun t => |f t|) (Set.Icc (-Real.pi) Real.pi)) :
    MeasureTheory.IntegrableOn (fun t => |f (x - t)|) (Set.Icc (-Real.pi) Real.pi) := by
  sorry

/- [PNTB-036] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/GammaBounds.lean:82
   kind: have
   domain: half-line
   integrand: explicit
   original proof: library lemma `Real.GammaIntegral_convergent` + `mono_set`
   notes:
   status: proved by `endpoint_integrability` -/
example {a : ℝ} (ha_low : (1 / 2 : ℝ) ≤ a) (ha_high : a ≤ 1) :
    IntegrableOn (fun t ↦ Real.exp (-t) * t ^ (a - 1)) (Ioi 1) := by
  endpoint_integrability

/- [PNTB-037] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/Unused/Fejer_I_know_this_is_dirty_but_it_typechecks.lean:1183
   kind: have
   domain: interval integral
   integrand: explicit with opaque factor
   original proof: `mul_continuousOn` (continuity of the kernel) on the preceding `h_integrable`, minus a
     continuous term
   notes: `fejer_kernel n t = 1 / (n + 1) * ∑ j ∈ range (n + 1), dirichlet_kernel j t` and
     `dirichlet_kernel j t = 1 / 2 + ∑ k ∈ Icc 1 j, cos (k * t)` inlined; the preceding
     `h_integrable` is a hypothesis.
   status: open: failed to prove -/
example {f : ℝ → ℝ} {n : ℕ} {x₀ L_plus L_minus : ℝ}
    (hf_int : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (hf_per : Function.Periodic f (2 * Real.pi))
    (h_integrable : IntervalIntegrable (fun t => f (x₀ - t)) MeasureTheory.volume (-Real.pi) Real.pi) :
    IntervalIntegrable (fun t => (1 / (n + 1 : ℝ) * ∑ j ∈ Finset.range (n + 1),
        (1 / 2 + ∑ k ∈ Finset.Icc 1 j, Real.cos (k * t))) * (f (x₀ - t) - (L_plus + L_minus) / 2))
      MeasureTheory.volume (-Real.pi) Real.pi := by
  sorry

/- [PNTB-038] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/Ramanujan/RamanujanCalculations.lean:190
   kind: have
   domain: bounded interval
   integrand: abstract
   original proof: `simpa [Set.uIcc_of_le hbc]` from the preceding `h_int_right`
   notes: the preceding `h_int_right` is a hypothesis.
   status: out of scope: abstract integrand; needs closure rules (`fun_prop`), not a leaf solver -/
example (f : ℝ → ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hInt : IntegrableOn f (Set.Icc a c) volume)
    (h_int_right : IntegrableOn f (Set.Icc b c) volume) :
    IntegrableOn f (Set.uIcc b c) volume := by
  sorry

/- [PNTB-039] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/CH2/CH2_part1.lean:5228
   kind: statement
   domain: whole line
   integrand: abstract
   original proof: split into `[-1, 1]` and its complement; `contDiffOn_Icc_deriv_integrableOn` on
     `[-1, 0]` and `[0, 1]`, derivative zero outside
   notes: `ϕ_pm ν ε` (piecewise project definition) is a variable function `ϕ` with the facts the proof
     used: `ϕ_c2_left`, `ϕ_c2_right` (`C²` on `[-1, 0]` and `[0, 1]`) and the `else 0` branch of its
     definition (zero outside `[-1, 1]`).
   status: out of scope: abstract integrand; needs closure rules (`fun_prop`), not a leaf solver -/
example (ϕ : ℝ → ℂ) (h_left : ContDiffOn ℝ 2 ϕ (Set.Icc (-1) 0))
    (h_right : ContDiffOn ℝ 2 ϕ (Set.Icc 0 1)) (h_out : ∀ t : ℝ, ¬(-1 ≤ t ∧ t ≤ 1) → ϕ t = 0) :
    Integrable (deriv ϕ) := by
  sorry

/- [PNTB-040] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/CH2/CH2.lean:2158
   kind: have
   domain: interval integral
   integrand: explicit with opaque factor
   original proof: project lemma `integrable_vseg_L` (meromorphic + bounded with no poles on `L`)
   notes: `LadderParams` fields are binders; `l.R`, `l.L`, `IsBoundedNoPolesOn` inlined. Same context
     as PNT-022, on the interval `[-δ, δ]`.
   status: open: goals left: locallyIntegrableOn, nhdsGT, nhdsLT -/
example (σ : ℕ → ℝ) (T δ : ℝ) (hσ : ∀ n, σ n ≤ 1) (hδ : δ ∈ Set.Ioo 0 (T / 4))
    (n : ℕ) (hn : 1 ≤ n) {F G_circ : ℂ → ℂ} {x₀ x : ℝ}
    (hF : F = fun s ↦ G_circ s * (x : ℂ) ^ s) (hx₀ : 1 ≤ x₀) (hx : x₀ < x)
    (hG_circ_mero : MeromorphicOn G_circ {z : ℂ | z.re ≤ 1 ∧ |z.im| ≤ T})
    (hGc_L : ∃ M, ∀ z ∈ {z : ℂ | ∃ n, 1 ≤ n ∧ z.re = σ n ∧ |z.im| ≤ T},
      ‖G_circ z * (x₀ : ℂ) ^ z‖ ≤ M ∧ 0 ≤ meromorphicOrderAt (fun s ↦ G_circ s * (x₀ : ℂ) ^ s) z) :
    IntervalIntegrable (fun t : ℝ ↦ F ((σ n : ℂ) + t * Complex.I) * Complex.I) volume (-δ) δ := by
  sorry

/- [PNTB-041] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/Wiener.lean:3179
   kind: have
   domain: half-line
   integrand: abstract
   original proof: `hF` (definitional unfolding of `IntegrableOn`)
   notes:
   status: proved by `endpoint_integrability` -/
example (A : ℂ) (F : ℝ → ℂ) (a : ℝ) (hF : IntegrableOn F (Set.Ici a))
    (hnorm : Integrable (fun u : ℝ => ‖F u‖)) :
    Integrable F (Measure.restrict volume (Set.Ici a)) := by
  endpoint_integrability

/- [PNTB-042] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/KadiriEq12Helpers.lean:280
   kind: domination
   domain: whole line
   integrand: explicit with opaque factor
   original proof: project lemma `laplace_deriv_integrand_integrable` (twice, `.norm.add`) for the bound;
     `‖exp (-s y)‖ = exp (-(s.re y))` and a case split on the sign of `y` for the a.e. bound
   notes: hypotheses of `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the project's concrete
     bound `‖(-y φ y) exp (-(σ₀ - ε) y)‖ + ‖(-y φ y) exp (-(σ₀ + ε) y)‖`; the `set`s `σ₀ = x₀.re` and
     `ε = min (b - σ₀) (σ₀ + 1 + b) / 4` inlined.
   status: out of scope: a domination hypothesis, not an integrability goal -/
open Asymptotics in
example {φ : ℝ → ℂ} {b : ℝ} (hφc : Continuous φ)
    (hφ_decay : (fun x : ℝ ↦ φ x * Complex.exp ((x : ℂ) / 2)) =O[cocompact ℝ]
      fun x ↦ Real.exp (-(1 / 2 + b) * |x|))
    {x₀ : ℂ} (h_top : -(1 + b) < x₀.re) (h_bot : x₀.re < b) :
    Integrable (fun y : ℝ ↦
      ‖(-(y : ℂ) * φ y) *
          Complex.exp (-((x₀.re - min (b - x₀.re) (x₀.re + 1 + b) / 4 : ℝ) : ℂ) * y)‖ +
        ‖(-(y : ℂ) * φ y) *
          Complex.exp (-((x₀.re + min (b - x₀.re) (x₀.re + 1 + b) / 4 : ℝ) : ℂ) * y)‖) ∧
      ∀ᵐ (y : ℝ) ∂volume, ∀ s ∈ Metric.ball x₀ (min (b - x₀.re) (x₀.re + 1 + b) / 4),
        ‖-(y : ℂ) * φ y * Complex.exp (-s * (y : ℂ))‖ ≤
          ‖(-(y : ℂ) * φ y) *
              Complex.exp (-((x₀.re - min (b - x₀.re) (x₀.re + 1 + b) / 4 : ℝ) : ℂ) * y)‖ +
            ‖(-(y : ℂ) * φ y) *
              Complex.exp (-((x₀.re + min (b - x₀.re) (x₀.re + 1 + b) / 4 : ℝ) : ℂ) * y)‖ := by
  sorry

/- [PNTB-043] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/Wiener.lean:2518
   kind: domination
   domain: half-line
   integrand: explicit with opaque factor
   original proof: project lemma `limiting_fourier_lim2_aux` (`integrable_inv_one_add_sq.comp_div`) for
     the bound; `exp (-(t (σ' - 1))) ≤ max |x| 1` on `Ioo 1 2` and the decay bound `hC` for the a.e. bound
   notes: hypotheses of `tendsto_integral_filter_of_dominated_convergence` with the project's concrete
     bound `max |x| 1 * (C / (1 + (t / (2 π)) ^ 2))` on `volume.restrict (Ici (-log x))`; `ψ : W21`
     replaced by `ψ : ℝ → ℂ`, and the obtained `C` with its decay bound `hC` (`decay_bounds_cor ψ`) is a
     hypothesis.
   status: out of scope: a domination hypothesis, not an integrability goal -/
example (x : ℝ) (hx : 0 < x) (ψ : ℝ → ℂ) (C : ℝ) (hC : ∀ u, ‖𝓕 ψ u‖ ≤ C / (1 + u ^ 2)) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
        (volume.restrict (Ici (-Real.log x))) ∧
      ∀ᶠ (σ' : ℝ) in 𝓝[>] 1, ∀ᵐ u ∂(volume.restrict (Ici (-Real.log x))),
        ‖(Real.exp (-u * (σ' - 1)) : ℂ) * 𝓕 ψ (u / (2 * π))‖ ≤
          max |x| 1 * (C / (1 + (u / (2 * π)) ^ 2)) := by
  sorry

/- [PNTB-044] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/IEANTN/FioriKadiriSwidinsky/FioriKadiriSwidinsky.lean:321
   kind: domination
   domain: half-line
   integrand: explicit
   original proof: comparison with `exp (-u) * (2 u) ^ (s - 1)` (Gamma integral) on `Ioi 1` and
     continuity on `Icc 0 1`, glued by `IntegrableOn.union`, for the bound; `rpow_le_rpow` for the a.e. bound
   notes: hypotheses of `tendsto_integral_filter_of_dominated_convergence` with the project's concrete
     bound `exp (-u) * (1 + u) ^ (s - 1)` on `volume.restrict (Ioi 0)`.
   status: out of scope: a domination hypothesis, not an integrability goal -/
example (s : ℝ) (h : s > 1) :
    Integrable (fun u : ℝ ↦ Real.exp (-u) * (1 + u) ^ (s - 1)) (volume.restrict (Ioi 0)) ∧
      ∀ᶠ (x : ℝ) in atTop, ∀ᵐ u ∂(volume.restrict (Ioi 0)),
        ‖Real.exp (-u) * (1 + u / x) ^ (s - 1)‖ ≤ Real.exp (-u) * (1 + u) ^ (s - 1) := by
  sorry

/- [PNTB-045] AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b PrimeNumberTheoremAnd/LaplaceInversion.lean:71
   kind: domination
   domain: whole line
   integrand: explicit with opaque factor
   original proof: `hf_int.norm` for the bound; pointwise `‖exp‖` computation for the a.e. bound
   notes: hypotheses of `tendsto_integral_filter_of_dominated_convergence`, stated with the project's
     concrete bound `fun y => ‖exp (-(σ * y)) * f y‖`.
   status: out of scope: a domination hypothesis, not an integrability goal -/
example {f : ℝ → ℂ} {sigma : ℝ} (hf_cont : Continuous f)
    (hf_int : Integrable (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y)) (t0 : ℝ) :
    Integrable (fun y : ℝ => ‖Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y‖) ∧
      ∀ᶠ t in 𝓝 t0, ∀ᵐ y ∂volume,
        ‖f y * Complex.exp ((((t : ℂ) * I - (sigma : ℂ)) * (y : ℂ)))‖ ≤
          ‖Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y‖ := by
  sorry

end PrimeNumberTheoremAnd

section QuasiRH

open MeasureTheory Set Filter Topology Real
open scoped FourierTransform SchwartzMap ContDiff

/- [QRHB-001] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/CubicSieve/LogSeparation.lean:217
   kind: have
   domain: whole line
   integrand: explicit with opaque factor
   original proof: project lemma `reopening_integrable` (`Integrable.mul_bdd` of a Schwartz function), `.const_mul`
   notes: `reopeningCoefficient …` (a Schwartz map) is a Schwartz binder `b`; the local `G`,
     `cubeFrequencyFactor t ξ = exp (t/2) * logPhase ξ (3t)`, `frequencyTwist V ξ u = logPhase ξ u * V u`
     and `logPhase t y = exp (((2π t y : ℝ) : ℂ) * I)` inlined.
   status: open: goals left: atBot, atTop -/
example {κ τ : Type*} (β : κ → ℂ) (A : κ → τ → ℂ) (n : κ → ℝ) (q : τ → ℝ) (B ell : ℝ)
    (b V : 𝓢(ℝ, ℂ)) (v : κ) (j : τ) :
    Integrable (fun ξ : ℝ => (β v * A v j) *
      (b ξ * ((Real.exp (Real.log (n v / B) / 2) : ℂ) *
          Complex.exp (((2 * Real.pi * ξ * (3 * Real.log (n v / B)) : ℝ) : ℂ) * Complex.I)) *
        (Complex.exp (((2 * Real.pi * ξ * Real.log (q j / ell) : ℝ) : ℂ) * Complex.I) *
          V (Real.log (q j / ell))))) := by
  sorry

/- [QRHB-002] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/Eisenstein/SourceMellinInversion.lean:186
   kind: statement
   domain: whole line
   integrand: explicit with opaque factor
   original proof: `Integrable.mono'` with bound `r ^ σ * ‖M t‖` (norm of the vertical power)
   notes:
   status: open: goals left: locallyIntegrableOn, atBot, atTop -/
example (M : ℝ → ℂ) (hM : Integrable M) (r σ : ℝ) (hr : 0 < r) :
    Integrable (fun t : ℝ => (r : ℂ) ^ ((σ : ℂ) + t * Complex.I) * M t) := by
  sorry

/- [QRHB-003] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/Eisenstein/DirichletForm.lean:334
   kind: have
   domain: whole line
   integrand: explicit with opaque factor
   original proof: `Integrable.mul_bdd` (Schwartz function times a bounded continuous factor)
   notes: the local `φ k` (a row phase times a finite sum of project coefficients) is a variable family
     with the preceding `hφc` (continuity) and `hpoint` (bound by `√E`); `idealRange K` is a type `ι`.
   status: open: goals left: atBot, atTop -/
example {ι : Type*} (b : 𝓢(ℝ, ℂ)) (φ : ι → ℝ → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hφc : ∀ k, Continuous (φ k)) (hpoint : ∀ k t, ‖φ k t‖ ≤ Real.sqrt E) (k : ι) :
    Integrable (fun t : ℝ => b t * φ k t) := by
  sorry

/- [QRHB-004] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/Eisenstein/CompactEnergyFamilies.lean:184
   kind: have
   domain: ℝⁿ/product
   integrand: abstract
   original proof: `IntegrableOn.smul_measure` then `mono_measure` (density bound of the measure)
   notes: `EuclideanSpatial = EuclideanSpace ℝ (Fin 3)`; `hyperbolicEuclideanVolume` (Lebesgue restricted to
     `{p | 0 < p 2}` with density `ofReal ((p 2)^3)⁻¹`) inlined; `kernelLocalizedField χ f` is a variable
     function `F` with the preceding `hloc`; the preceding `hm` (measure comparison) is a hypothesis.
   status: out of scope: not an integral over an interval of `ℝ` -/
example (F : EuclideanSpace ℝ (Fin 3) → ℂ) (S : Set (EuclideanSpace ℝ (Fin 3)))
    (hS : MeasurableSet S) (hpos : S ⊆ {p : EuclideanSpace ℝ (Fin 3) | 0 < p 2}) (H : ℝ)
    (hm : ((volume.restrict {p : EuclideanSpace ℝ (Fin 3) | 0 < p 2}).withDensity
        (fun p => ENNReal.ofReal ((p 2) ^ 3)⁻¹)).restrict S ≤ ENNReal.ofReal H • volume.restrict S)
    (hloc : Integrable (fun p => ‖F p‖ ^ 2) volume) :
    IntegrableOn (fun p => ‖F p‖ ^ 2) S
      ((volume.restrict {p : EuclideanSpace ℝ (Fin 3) | 0 < p 2}).withDensity
        (fun p => ENNReal.ofReal ((p 2) ^ 3)⁻¹)) := by
  sorry

/- [QRHB-005] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/Eisenstein/GreenIdentity.lean:113
   kind: have
   domain: interval integral
   integrand: explicit with opaque factor
   original proof: closure lemmas (`mul_continuousOn`, `continuousOn_mul`, `.sub`) from `hif` and `hstar`
   notes: `greenSecondTerm f g x = deriv (deriv f) x * star (g x) - f x * star (deriv (deriv g) x)`
     inlined; the preceding `hstar` is a hypothesis.
   status: open: failed to prove -/
example (f g : ℝ → ℂ) (a b : ℝ)
    (hf : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ g x)
    (hif : IntervalIntegrable (deriv (deriv f)) volume a b)
    (hig : IntervalIntegrable (deriv (deriv g)) volume a b)
    (hstar : IntervalIntegrable (fun x => star (deriv (deriv g) x)) volume a b) :
    IntervalIntegrable
      (fun x : ℝ => deriv (deriv f) x * star (g x) - f x * star (deriv (deriv g) x)) volume a b := by
  sorry

/- [QRHB-006] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/QuadraticSieve/CuspCoercivity.lean:445
   kind: have
   domain: half-line
   integrand: explicit
   original proof: library lemma `integrableOn_Ioi_rpow_of_lt`
   notes:
   status: open: goals left: continuity -/
example (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun v : ℝ => (v ^ 3)⁻¹) (Set.Ioi a) volume := by
  sorry

/- [QRHB-007] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/CubicSieve/DensityBudgets.lean:463
   kind: have
   domain: whole line
   integrand: explicit with opaque factor
   original proof: project lemma `separated_canonical_integrable` (closure lemmas over `reopening_integrable`)
   notes: `reopenedCanonicalRow` unfolded with its `ξ`-independent factors as constants: `c S` for the
     `canonicalSourceCoefficient` factors other than `H S`, `d v S` for the multiplicity and squarefree
     rows; `separatedCubeCoefficient`, `cubeFrequencyFactor`, `frequencyTwist`, `logPhase` inlined;
     `primeProductNorm p` is a variable function `q`; `β I` is `β`.
   status: open: goals left: atBot, atTop -/
example {ι : Type*} (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (c : Finset ι → ℂ) (d : (ι →₀ ℕ) → Finset ι → ℂ) (q : Finset ι → ℝ)
    (b V : 𝓢(ℝ, ℂ)) (B ell : ℝ) :
    Integrable (fun ξ : ℝ => b ξ * ∑ v ∈ Q, ∑ S ∈ pool.powerset,
      ((β v * ((Real.exp (Real.log (n v / B) / 2) : ℂ) *
          Complex.exp (((2 * Real.pi * ξ * (3 * Real.log (n v / B)) : ℝ) : ℂ) * Complex.I))) *
        (c S * (Complex.exp (((2 * Real.pi * ξ * Real.log (q S / ell) : ℝ) : ℂ) * Complex.I) *
          V (Real.log (q S / ell))))) * d v S) := by
  sorry

/- [QRHB-008] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/Eisenstein/CuspIntegration.lean:314
   kind: statement
   domain: ℝⁿ/product
   integrand: abstract
   original proof: a.e. congruence with a continuous extension (`extendAboveHeight`), continuity on a
     compact box
   notes: `SpatialCoordinates = Fin 3 → ℝ`, `spatialTriple x y v = ![x, y, v]` and `cuspCylinderMeasure`
     inlined.
   status: out of scope: not an integral over an interval of `ℝ` -/
example (f : (Fin 3 → ℝ) → ℂ) (hf : ∀ p : Fin 3 → ℝ, 0 < p 2 → ContinuousAt f p) (a b : ℝ)
    (ha : 0 < a) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => f ![q.2.2, q.2.1, q.1])
      ((volume.restrict (Set.Icc a b)).prod
        ((volume.restrict (Set.Icc 0 (3 * Real.sqrt 3))).prod (volume.restrict (Set.Icc 0 3)))) := by
  sorry

/- [QRHB-009] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/Eisenstein/CuspIntegration.lean:153
   kind: have
   domain: ℝⁿ/product
   integrand: abstract
   original proof: rewriting the measure in the preceding `hi` (`Measure.prod_restrict`)
   notes: `spatialTriple x y v = ![x, y, v]` inlined; the integrand is a parametric integral; the
     preceding `hi` is a hypothesis.
   status: out of scope: not an integral over an interval of `ℝ` -/
example (f : (Fin 3 → ℝ) → ℂ) (hf : Continuous f) (a b : ℝ) (hab : a ≤ b)
    (hi : IntegrableOn (fun q : ℝ × ℝ => ∫ v in Set.Icc a b, f ![q.2, q.1, v])
      (Set.Icc 0 (3 * Real.sqrt 3) ×ˢ Set.Icc 0 3) volume) :
    Integrable (fun q : ℝ × ℝ => ∫ v in Set.Icc a b, f ![q.2, q.1, v])
      ((volume.restrict (Set.Icc 0 (3 * Real.sqrt 3))).prod (volume.restrict (Set.Icc 0 3))) := by
  sorry

/- [QRHB-010] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/MeanSquare/DiagonalDensity.lean:579
   kind: have
   domain: ℝⁿ/product
   integrand: explicit with opaque factor
   original proof: project lemma `tripleLogDensity_slice_integrable` (`mul_prod` then `mul_bdd`), `.const_mul`
   notes: `Frequency = ℝ × ℝ × ℝ`; the local `u`, `tripleLogDensity` and
     `firstLogDensity J t = ((1 + ‖t‖)^(J+2))⁻¹` inlined.
   status: out of scope: not an integral over an interval of `ℝ` -/
example (G : ℝ × ℝ × ℝ → ℝ) (J : ℕ) (hG : Continuous G) (M : ℝ) (hGM : ∀ q, ‖G q‖ ≤ M) (C : ℝ)
    (x : ℝ) :
    Integrable (fun yz : ℝ × ℝ => C * ((((1 + ‖x‖) ^ (J + 2))⁻¹ *
      (((1 + ‖yz.1‖) ^ (J + 2))⁻¹ * ((1 + ‖yz.2‖) ^ (J + 2))⁻¹)) * G (x, yz))) := by
  sorry

/- [QRHB-011] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/Eisenstein/ResidualFourierExpansion.lean:87
   kind: statement
   domain: bounded interval
   integrand: explicit
   original proof: case split on `h = 0`; continuity on `Icc` (constant mode), project lemma
     `cubicBesselHeight_integrable` (nonzero modes), a.e. congruence
   notes: `cubicResidualFullModeAmplitude` inlined; `schlafliBesselK ν x = 1/2 * (x/2)^(-ν) * schlafliIntegral ν x`
     with `schlafliIntegral ν x = ∫ t in Ioi 0, t^(ν-1) * exp (-t - x^2/(4t))` inlined at `ν = 1/3`;
     the Eisenstein integers are a type `O`; `constantArithmeticResidue`,
     `cubicResidualFourierCoefficient h` and `cuspFrequency h` are constants `K₀`, `c`, `freq`, with
     the fact `cuspFrequency_ne_zero` used by the project lemma.
   status: open: goals left: locallyIntegrableOn, nhdsGT, nhdsLT -/
example {O : Type*} [Zero O] [DecidableEq O] (h : O) (K₀ c freq : ℂ) (hfreq : h ≠ 0 → freq ≠ 0)
    (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (fun v : ℝ =>
      (if h = 0 then (3 * (Real.pi : ℂ)) * K₀ * (v : ℂ) ^ (2/3 : ℂ)
        else c * (v : ℂ) *
          ((1/2 : ℂ) * (((4 * Real.pi * ‖freq‖ * v : ℝ) : ℂ) / 2) ^ (-(1/3 : ℂ)) *
            ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ ((1/3 : ℂ) - 1) *
              Complex.exp (-(t : ℂ) - ((4 * Real.pi * ‖freq‖ * v : ℝ) : ℂ) ^ 2 / (4 * t)))) /
        (v : ℂ) ^ 3)
      (Set.Icc a b) volume := by
  sorry

/- [QRHB-012] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/CubicSieve/IntegratedTransfer.lean:279
   kind: have
   domain: whole line
   integrand: abstract
   original proof: `Finset.mul_sum`, closure lemma `integrable_finsetSum` over a project integrability lemma
   notes: `firstCoreInputRow … r t z` (deep project definition) is a variable family `Q r t z` with the fact
     the proof used (`firstCoreInputRow_integrable`: each `k t * ‖Q r t z‖ ^ 2` is integrable);
     `FirstCoreIndex` and `O` are types `ρ`, `Z`.
   status: out of scope: abstract integrand; needs closure rules (`fun_prop`), not a leaf solver -/
example {Z ρ : Type*} (T : Finset Z) (k : ℝ → ℝ) (hk : Integrable k volume) (hk0 : ∀ t, 0 ≤ k t)
    (Q : ρ → ℝ → Z → ℂ) (hQ : ∀ r z, Integrable (fun t : ℝ => k t * ‖Q r t z‖ ^ 2) volume) (r : ρ) :
    Integrable (fun t : ℝ => k t * ∑ z ∈ T, ‖Q r t z‖ ^ 2) volume := by
  sorry

/- [QRHB-013] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/Eisenstein/CuspIntegration.lean:381
   kind: statement
   domain: ℝⁿ/product
   integrand: explicit with opaque factor
   original proof: project lemma `integrable_cuspBox_of_positive_continuity` (QRHB-008) and continuity of
     the fields on the upper half
   notes: `eisensteinHermitianDensity`, `spatialTriple`, `cuspCylinderMeasure` inlined;
     `upperEisensteinField` is a variable function `E` with the fact the proof used
     (`actual_spatial_continuousAt`: continuity at points with `0 < p 2`, for `s` and `t`).
   status: out of scope: not an integral over an interval of `ℝ` -/
example (E : ℂ → (Fin 3 → ℝ) → ℂ) (s t : ℂ) (hs : 2 < s.re) (ht : 2 < t.re)
    (hEs : ∀ p : Fin 3 → ℝ, 0 < p 2 → ContinuousAt (E s) p)
    (hEt : ∀ p : Fin 3 → ℝ, 0 < p 2 → ContinuousAt (E t) p) (a b : ℝ) (ha : 0 < a) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => E s ![q.2.2, q.2.1, q.1] * star (E t ![q.2.2, q.2.1, q.1]) /
        ((((![q.2.2, q.2.1, q.1] : Fin 3 → ℝ) 2 : ℝ)) : ℂ) ^ 3)
      ((volume.restrict (Set.Icc a b)).prod
        ((volume.restrict (Set.Icc 0 (3 * Real.sqrt 3))).prod (volume.restrict (Set.Icc 0 3)))) := by
  sorry

/- [QRHB-014] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/Eisenstein/DirichletForm.lean:191
   kind: statement
   domain: abstract measure
   integrand: abstract
   original proof: closure lemmas (`.ofReal`, `.sub`, `.add`, `.mul_const`, `.div_const`) over a project
     integrability lemma
   notes: `kernelDirichletPairDensity` (polarisation of the energy density) inlined; the quotient space
     with `integralQuotientVolume globalKubotaKernel` is a measure space `(X, μ)`, `kernelSmoothTests` a
     complex vector space `V`, `kernelQuotientEnergyDensity` a variable function `e` with the fact the proof
     used (`kernelQuotientEnergyDensity_integrable`).
   status: out of scope: not an integral over an interval of `ℝ` -/
example {X V : Type*} [MeasurableSpace X] [AddCommGroup V] [Module ℂ V] (μ : Measure X)
    (e : V → X → ℝ) (he : ∀ h, Integrable (e h) μ) (f g : V) :
    Integrable (fun q : X => ((e (f + g) q : ℂ) - (e (f - g) q : ℂ) +
      ((e (f - Complex.I • g) q : ℂ) - (e (f + Complex.I • g) q : ℂ)) * Complex.I) / 4) μ := by
  sorry

/- [QRHB-015] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/CubicSieve/RayExpansion.lean:296
   kind: have
   domain: whole line
   integrand: explicit with opaque factor
   original proof: case split on `Disjoint N P`; rewrite with `threeGaussRowFactor_log_twist`, project lemma
     `integrable_log_pair` (`Integrable.mul_bdd`); `integrable_zero`
   notes: the local `G` inlined; `threeGaussRowFactor … (logTwistMinus …) (logTwistPlus …) d h` is a variable
     function `R N P t` with the equation the proof used (`threeGaussRowFactor_log_twist`), whose
     `t`-independent factor is a constant `K N P`; `logPhase` inlined.
   status: open: goals left: locallyIntegrableOn, atBot, atTop -/
example {ι : Type*} [DecidableEq ι] (b : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (y₁ y₂ : Finset ι → ℝ)
    (R : Finset ι → Finset ι → ℝ → ℂ) (K : Finset ι → Finset ι → ℂ)
    (hR : ∀ N P t, R N P t =
      (V₁ (y₁ N) * Complex.exp (((2 * Real.pi * t * (-(y₁ N)) : ℝ) : ℂ) * Complex.I)) *
        (V₂ (y₂ P) * Complex.exp (((2 * Real.pi * t * (-(y₂ P)) : ℝ) : ℂ) * Complex.I)) * K N P)
    (N P : Finset ι) :
    Integrable (fun t : ℝ => if Disjoint N P then b t * R N P t else 0) volume := by
  sorry

/- [QRHB-016] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/Eisenstein/OppositeCusp.lean:427
   kind: statement
   domain: ℝⁿ/product
   integrand: explicit
   original proof: rewrite as a constant times a shifted height kernel, project lemma
     `shiftedHeightKernel_integrable`, `.const_mul`
   notes: `oppositeTerm` inlined; `eisEmbedding (symbol (3x) c)`, `eisEmbedding c`, `eisEmbedding (3x)` are
     constants `K`, `C`, `D`, with `C ≠ 0` from `hc` (injectivity of `eisEmbedding`).
   status: out of scope: not an integral over an interval of `ℝ` -/
example (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re) (K C D : ℂ) (hC : C ≠ 0) :
    Integrable (fun z : ℂ =>
      K * ((v / (‖C * z + D‖ ^ 2 + ‖C‖ ^ 2 * v ^ 2) : ℝ) : ℂ) ^ s) := by
  sorry

/- [QRHB-017] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/CubicSieve/IntegratedTransfer.lean:462
   kind: statement
   domain: ℝⁿ/product
   integrand: explicit with opaque factor
   original proof: `Integrable.mul_prod` of two Schwartz functions, `.const_mul`, `.norm`, then `mul_bdd`
   notes: `Frequency = ℝ × ℝ × ℝ`; `tripleCoefficient b₁ b₂ b₃ t = b₁ t.1 * (b₂ t.2.1 * b₃ t.2.2)` inlined.
   status: out of scope: not an integral over an interval of `ℝ` -/
example (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (G : ℝ × ℝ × ℝ → ℝ) (hG : Continuous G) (M : ℝ)
    (hM : ∀ t, ‖G t‖ ≤ M) (x : ℝ) :
    Integrable (fun t : ℝ × ℝ =>
      ‖b₁ (x, t).1 * (b₂ (x, t).2.1 * b₃ (x, t).2.2)‖ * G (x, t)) := by
  sorry

/- [QRHB-018] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/Eisenstein/CuspAverage.lean:393
   kind: statement
   domain: half-line
   integrand: explicit
   original proof: Mellin convergence of the Gamma integrand, `MellinConvergent.comp_mul_left` and `comp_rpow`
   notes:
   status: proved by `endpoint_integrability` -/
example (s : ℂ) (r : ℝ) (hs : 0 < s.re) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * Complex.exp (-(r : ℂ) * (x : ℂ) ^ 2))
      (Set.Ioi 0) volume := by
  endpoint_integrability

/- [QRHB-019] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/Eisenstein/FourierCoefficients.lean:225
   kind: domination
   domain: ℝⁿ/product
   integrand: abstract
   original proof: `integrable_const` on a finite measure for the bound; `‖breveE‖ = 1` and the majorant
     for the a.e. bound; summability of the majorant
   notes: hypotheses of `hasSum_integral_of_dominated_convergence` with the project's concrete bound
     `fun x _ => M x` on `volume.restrict periodDomain`; `periodDomain` is a measurable set `P` of finite
     measure (the facts the proof used); `summand (upperSection z v hv) s x` is a variable family `F x z`;
     the obtained majorant `M` with `hM`, `hMnonneg`, `hbound` are hypotheses;
     `breveE w = exp (2π I (w + conj w))` inlined; `CuspCosets` is a countable type `ι`.
   status: out of scope: a domination hypothesis, not an integrability goal -/
example {ι : Type*} [Countable ι] (P : Set ℂ) (hP : MeasurableSet P)
    [IsFiniteMeasure (volume.restrict P)] (F : ι → ℂ → ℂ) (freq : ℂ) (M : ι → ℝ)
    (hM : Summable M) (hMnonneg : ∀ x, 0 ≤ M x) (hbound : ∀ z ∈ P, ∀ x, ‖F x z‖ ≤ M x) :
    Integrable (fun _ : ℂ => ∑' x, M x) (volume.restrict P) ∧
      (∀ x, ∀ᵐ z ∂(volume.restrict P),
        ‖F x z * Complex.exp (2 * Real.pi * Complex.I * ((-freq * z) + starRingEnd ℂ (-freq * z)))‖ ≤
          M x) ∧
      (∀ᵐ z ∂(volume.restrict P), Summable fun x => M x) := by
  sorry

/- [QRHB-020] AlexKontorovich/quasi-rh@d26d846d6f3129017f06b6fd3f78dd72d361d60b OAI/NumberTheory/DirichletL/Eisenstein/WhittakerContinuation.lean:411
   kind: domination
   domain: ℝⁿ/product
   integrand: explicit with opaque factor
   original proof: `hyperbolicKernel_integrable` (on ℂ) times a constant on the finite measure `μ`
     (`mul_prod`), `.const_mul` twice; `‖ρ p.1‖ ≤ ‖ρ‖` and the pointwise log/rpow estimate for the derivative
   notes: hypotheses of `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on `μ.prod volume` (`μ` a finite
     measure) with the project's concrete bound `‖ρ‖ * (ε⁻¹ * (1 + ‖p.2‖^2)^(-b))`, `b = (s.re+1)/2`,
     `ε = (s.re-1)/4`, neighbourhood `{w | b + ε < w.re}`; `whittakerIntegrandDeriv`, `whittakerHeight`,
     `whittakerBase`, `breveE` inlined through the equation `hF'`, at the scaled point `(c * p.1, p.2)`.
   status: out of scope: a domination hypothesis, not an integrability goal -/
example (μ : Measure ℝ) [IsFiniteMeasure μ] (ρ : BoundedContinuousFunction ℝ ℂ) (c : ℝ)
    (freq s : ℂ) (hs : 1 < s.re) (F' : ℂ → ℝ × ℂ → ℂ)
    (hF' : F' = fun w p => ρ p.1 * (-(Real.log (max 5 (c * p.1) * (1 + ‖p.2‖ ^ 2)) : ℂ) *
      (((max 5 (c * p.1) : ℝ) : ℂ)⁻¹ * ((max 5 (c * p.1) * (1 + ‖p.2‖ ^ 2) : ℝ) : ℂ) ^ (-w) *
        Complex.exp (2 * Real.pi * Complex.I * ((-(freq * (max 5 (c * p.1) : ℝ)) * p.2) +
          starRingEnd ℂ (-(freq * (max 5 (c * p.1) : ℝ)) * p.2)))))) :
    Integrable (fun p : ℝ × ℂ => ‖ρ‖ * (((s.re - 1) / 4)⁻¹ * (1 + ‖p.2‖ ^ 2) ^ (-((s.re + 1) / 2))))
        (μ.prod volume) ∧
      ∀ᵐ p ∂(μ.prod volume),
        ∀ w ∈ {w : ℂ | (s.re + 1) / 2 + (s.re - 1) / 4 < w.re},
          ‖F' w p‖ ≤ ‖ρ‖ * (((s.re - 1) / 4)⁻¹ * (1 + ‖p.2‖ ^ 2) ^ (-((s.re + 1) / 2))) := by
  sorry

end QuasiRH

section PhysLean

/- PhysLean's `Space d` (a structure around `Fin d → ℝ` carrying the Euclidean structure) is
   replaced throughout by `EuclideanSpace ℝ (Fin d)` and `Time` (a structure around `ℝ`) by `ℝ`;
   `Space.basis i` becomes `EuclideanSpace.basisFun (Fin d) ℝ i` and `∂[i] u` becomes
   `fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin d) ℝ i)`. -/

open MeasureTheory Set Filter Topology Real
open scoped FourierTransform SchwartzMap ContDiff InnerProductSpace

/- [PHYSB-001] HEPLean/PhysLean@44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc PhyslibAlpha/ClassicalFieldTheory/KleinGordon/FourierRepresentation.lean:136
   kind: have
   domain: interval integral
   integrand: explicit with opaque factor
   original proof: continuous on a compact interval (`((hM T).smul hsh).intervalIntegrable`)
   notes: `sourceHat F f ξ` (Fourier transform of a time slice of the source) is a variable function
     `S` with the continuity the proof used (`hsh`); `multiplier τ μ ξ = sincPropagator τ ω` and
     `sincPropagator t ω = t * sinc (ω * t)` inlined; `ω = dispersion μ ξ` renamed `w`.
   status: proved by `endpoint_integrability` -/
example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (S : ℝ → F) (hS : Continuous S)
    (w T a : ℝ) :
    IntervalIntegrable (fun s => (((T - s) * Real.sinc (w * (T - s)) : ℝ) : ℂ) • S s)
      volume a T := by
  endpoint_integrability

/- [PHYSB-002] HEPLean/PhysLean@44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc PhyslibAlpha/Mathematics/Geometry/Sphere/Profile.lean:60
   kind: have
   domain: ℝⁿ/product
   integrand: explicit with opaque factor
   original proof: `Integrable.of_bound` with constant `R ^ 2 * M` (`M` a bound of `h` on `[-R, R]`)
   notes: `Sph` (unit sphere of `Space 3`) and `sphereMeasure = volume.toSphere` inlined.
   status: out of scope: not an integral over an interval of `ℝ` -/
example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (i : Fin 3) {h : ℝ → F}
    (hh : Continuous h) {R : ℝ} (hR : 0 < R) :
    Integrable (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ =>
        p.2 ^ 2 • h (p.2 * (p.1.1 i)))
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere).prod
        (volume.restrict (Set.Ioo 0 R))) := by
  sorry

/- [PHYSB-003] HEPLean/PhysLean@44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc PhyslibAlpha/ClassicalFieldTheory/KleinGordon/FinitePropagation.lean:372
   kind: have
   domain: ℝⁿ/product
   integrand: abstract
   original proof: continuous with compact support (`integrable_of_hasCompactSupport`)
   notes: the weight `W.w τ0` and the energy derivative `D.e' τ0` are variable functions `w`, `e'`
     with the facts the proof used (continuity, `w` vanishes outside the ball of radius `R`).
   status: out of scope: not an integral over an interval of `ℝ` -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (w e' : E → ℝ) (R : ℝ) (hw : Continuous w)
    (he' : Continuous e') (hR : ∀ x, R < ‖x‖ → w x = 0) :
    Integrable (fun x : E => w x * e' x) volume := by
  sorry

/- [PHYSB-004] HEPLean/PhysLean@44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Gaussians.lean:161
   kind: statement
   domain: whole line
   integrand: explicit with opaque factor
   original proof: completing the square, then project lemma `abs_mul_gaussian_integrable`
     (`f` times a shifted Gaussian is in `L¹` by Cauchy–Schwarz in `L²`)
   notes: `MemHS f = MemLp f 2 volume` inlined.
   status: open: goals left: locallyIntegrableOn, atBot, atTop -/
example (f : ℝ → ℂ) (hf : MemLp f 2 volume) (b c : ℝ) (hb : 0 < b) :
    Integrable (fun x => Real.exp (c * x) * norm (f x) * Real.exp (- b * x ^ 2)) := by
  sorry

/- [PHYSB-005] HEPLean/PhysLean@44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc PhyslibAlpha/ClassicalFieldTheory/KleinGordon/FourierRepresentation.lean:143
   kind: have
   domain: interval integral
   integrand: explicit with opaque factor
   original proof: closure lemmas (`h1.smul _`)
   notes: `sourceHat F f ξ` is a variable function `S`; the preceding `h1` is a hypothesis;
     `multiplier τ μ ξ = sincPropagator τ ω` and `sincPropagator t ω = t * sinc (ω * t)` inlined;
     `ω` renamed `w`.
   status: open: failed to prove -/
example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (S : ℝ → F) (w t T a : ℝ)
    (h1 : IntervalIntegrable (fun s => (((T - s) * Real.sinc (w * (T - s)) : ℝ) : ℂ) • S s)
      volume a T) :
    IntervalIntegrable (fun s => (Real.cos (w * (t - T)) : ℂ) •
      ((((T - s) * Real.sinc (w * (T - s)) : ℝ) : ℂ) • S s)) volume a T := by
  sorry

/- [PHYSB-006] HEPLean/PhysLean@44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Gaussians.lean:72
   kind: statement
   domain: whole line
   integrand: explicit
   original proof: completing the square, then library lemma `integrable_exp_neg_mul_sq` shifted
   notes:
   status: proved by `endpoint_integrability` -/
example (b c : ℝ) (hb : 0 < b) :
    Integrable (fun x => Real.exp (c * x) * Real.exp (- b * x ^ 2)) := by
  endpoint_integrability

/- [PHYSB-007] HEPLean/PhysLean@44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc PhyslibAlpha/Mathematics/Fourier/Marginal.lean:82
   kind: have
   domain: ℝⁿ/product
   integrand: explicit with opaque factor
   original proof: `Integrable.mono'` with bound `‖φ (toLp 2 p)‖` (the character has norm 1)
   notes: the preceding `hint` (integrability of `φ` transported to `E × F`) is a hypothesis.
   status: out of scope: not an integral over an interval of `ℝ` -/
example {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (φ : WithLp 2 (E × F) → ℂ) (ξ : E)
    (hint : Integrable (fun p : E × F => φ (WithLp.toLp 2 p))) :
    Integrable (fun p : E × F => (𝐞 (-inner ℝ p.1 ξ) : ℂ) • φ (WithLp.toLp 2 p)) := by
  sorry

/- [PHYSB-008] HEPLean/PhysLean@44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc PhyslibAlpha/ClassicalFieldTheory/KleinGordon/DimensionRaising/Retarded.lean:160
   kind: have
   domain: half-line
   integrand: explicit with opaque factor
   original proof: constant on a compact set (`integrableOn_const`, `integrable_indicator`), then restriction
   notes: the time support `Prod.fst '' tsupport ψb` of the source is a variable set `K` with the fact
     the proof used (compactness, `isCompact_timeSupport`).
   status: open: goals left: locallyIntegrableOn, atBot, nhdsLT -/
example (K : Set ℝ) (hK : IsCompact K) (B t : ℝ) :
    Integrable (K.indicator fun _ : ℝ => B) (volume.restrict (Set.Iic t)) := by
  sorry

/- [PHYSB-009] HEPLean/PhysLean@44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc QuantumInfo/ForMathlib/HermitianMat/LogExp.lean:552
   kind: statement
   domain: interval integral
   integrand: explicit with opaque factor
   original proof: continuity of the inverse on `[0, b]` (determinant nonzero, adjugate formula),
     then `ContinuousOn.intervalIntegrable_of_Icc`
   notes: `HermitianMat d 𝕜` (Hermitian matrices, with the inverse of the underlying matrix and the
     Frobenius norm) replaced by `Matrix d d 𝕜` with the Frobenius norm; `A.mat.PosDef` becomes
     `A.PosDef`; the source's `set_option backward.isDefEq.respectTransparency false in` kept.
   status: open: goals left: locallyIntegrableOn, nhdsGT, nhdsLT -/
open ComplexOrder in
open scoped Matrix.Norms.Frobenius in
set_option backward.isDefEq.respectTransparency false in
example {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜] {A : Matrix d d 𝕜}
    (hA : A.PosDef) (b : ℝ) (hb : 0 ≤ b) :
    IntervalIntegrable (fun t : ℝ => (A + t • (1 : Matrix d d 𝕜))⁻¹) volume 0 b := by
  sorry

/- [PHYSB-010] HEPLean/PhysLean@44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc PhyslibAlpha/ClassicalFieldTheory/KleinGordon/RetardedSolution.lean:450
   kind: have
   domain: ℝⁿ/product
   integrand: explicit with opaque factor
   original proof: `Integrable.mono'` with bound `‖ξ‖ ^ 0 * ‖freqSolution‖` (moment lemma with `n = 0`)
   notes: `freqSolution F f μ a ξ t` (`t` fixed) is a variable function `fs` with the facts the proof
     used (`integrable_norm_pow_mul_freqSolution` with `n = 0`, `continuous_freqSolution_xi`);
     `A ξ = 𝐞 ⟪ξ, x⟫ • fs ξ` inlined.
   status: out of scope: not an integral over an interval of `ℝ` -/
example {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (fs : E → F) (x : E) (hfs : Continuous fs)
    (hmom : Integrable (fun ξ : E => ‖ξ‖ ^ 0 * ‖fs ξ‖) volume) :
    Integrable (fun ξ : E => (𝐞 (inner ℝ ξ x) : ℂ) • fs ξ) volume := by
  sorry

/- [PHYSB-011] HEPLean/PhysLean@44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc PhyslibAlpha/ProbabilisticTheory/HilbertSpace/Unbounded/Existence/GaussianKernelGrowth.lean:253
   kind: have
   domain: whole line
   integrand: explicit
   original proof: by contradiction from the project's closed form of the integral
     (`hermite_gaussian_sq_integral`: a non-integrable function would have integral `0`)
   notes:
   status: open: goals left: atBot, atTop -/
open Polynomial in
example (n : ℕ) :
    Integrable (fun x : ℝ => (aeval x (hermite n)) ^ 2 * Real.exp (-(x ^ 2 / 2))) := by
  sorry

/- [PHYSB-012] HEPLean/PhysLean@44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc PhyslibAlpha/ProbabilisticTheory/HilbertSpace/Unbounded/Existence/GardingVectors.lean:313
   kind: statement
   domain: whole line
   integrand: explicit
   original proof: library lemmas `integrable_mul_exp_neg_mul_sq` (with `.abs`) and
     `integrable_exp_neg_mul_sq`, rewrite, `const_mul`
   notes:
   status: proved by `endpoint_integrability` -/
example {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    Integrable (fun u : ℝ => c * ((|u| + 1) * Real.exp (-(u ^ 2) / (2 * ε)))) := by
  endpoint_integrability

/- [PHYSB-013] HEPLean/PhysLean@44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc Physlib/QuantumMechanics/HarmonicOscillator/OneDimension/Eigenfunction.lean:128
   kind: statement
   domain: whole line
   integrand: explicit with opaque factor
   original proof: rewrite the squared norm, then `const_mul` and project lemma
     `guassian_integrable_polynomial_cons` (polynomial times Gaussian)
   notes: `Q.eigenfunction n` inlined; the physicists' Hermite polynomial `physHermite n` (a recursive
     definition, evaluated by `aeval`) is a variable polynomial `P : ℤ[X]` (the proof only used that it
     is a polynomial); `Q.ξ = √(ℏ / (m ω))` is a variable `ξ` with `0 < ξ`.
   status: open: goals left: atBot, atTop -/
example (n : ℕ) (P : Polynomial ℤ) (ξ : ℝ) (hξ : 0 < ξ) :
    Integrable (fun x : ℝ => ‖(1 / √(2 ^ n * n.factorial) * (1 / √(√Real.pi * ξ)) *
      ((Polynomial.aeval (x / ξ) P : ℝ) : ℂ) * (Real.exp (- x ^ 2 / (2 * ξ ^ 2)) : ℂ) : ℂ)‖ ^ 2) := by
  sorry

/- [PHYSB-014] HEPLean/PhysLean@44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc Physlib/Mathematics/Calculus/ParametricIntegration.lean:43
   kind: domination
   domain: interval integral
   integrand: abstract
   original proof: `intervalIntegrable_const`; the a.e. bound from the maximum of `‖F'‖` on the compact
     set `closedBall x₀ 1 ×ˢ Icc 0 1` (`IsCompact.exists_isMaxOn`)
   notes: hypotheses of `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le` with
     `s = closedBall x₀ 1` and the constant bound `‖F' a.1 a.2‖`; `F' x t = fderiv ℝ (F · t) x`
     inlined; the maximiser `a` is a binder with its `IsMaxOn` property.
   status: out of scope: a domination hypothesis, not an integrability goal -/
example {M N : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [ProperSpace M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] {F : M → ℝ → N} (hf : ContDiff ℝ 1 ↿F) (x₀ : M)
    (a : M × ℝ)
    (ha : a ∈ Metric.closedBall x₀ 1 ×ˢ Set.Icc (0 : ℝ) 1 ∧
      IsMaxOn (fun a : M × ℝ => ‖fderiv ℝ (F · a.2) a.1‖)
        (Metric.closedBall x₀ 1 ×ˢ Set.Icc (0 : ℝ) 1) a) :
    IntervalIntegrable (fun _ : ℝ => ‖fderiv ℝ (F · a.2) a.1‖) volume 0 1 ∧
      ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Metric.closedBall x₀ 1,
        ‖fderiv ℝ (F · t) x‖ ≤ ‖fderiv ℝ (F · a.2) a.1‖ := by
  sorry

/- [PHYSB-015] HEPLean/PhysLean@44adced7fc6cbf4e9da05f62fc3143b4d3cd97fc PhyslibAlpha/ProbabilisticTheory/Classical/NormalStates.lean:129
   kind: domination
   domain: abstract measure
   integrand: abstract
   original proof: `integrable_const` (probability measure); the pointwise bound `hle`
   notes: hypotheses of `tendsto_integral_of_dominated_convergence` with the constant bound `C + D`;
     the monotone sequence `f n` of bounded measurable functions is a variable sequence of functions
     with the preceding `hle` as a hypothesis.
   status: out of scope: a domination hypothesis, not an integrability goal -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ℕ → Ω → ℝ) (C D : ℝ) (hle : ∀ n x, |f n x| ≤ C + D) :
    Integrable (fun _ : Ω => C + D) μ ∧ ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ C + D := by
  sorry

end PhysLean

section TauCeti

open MeasureTheory Set Filter Topology Real
open scoped ContDiff ENNReal Interval

/- [TAUB-001] TauCetiProject/TauCeti@fb3fbc9f05780f456267a29168dfae7a98c2d8d0 TauCeti/Analysis/Bochner/Fourier/Nonneg.lean:652
   kind: statement
   domain: ℝⁿ/product
   integrand: explicit
   original proof: Mathlib `fourier_gaussian_innerProductSpace` rewrites the transform as a Gaussian,
     then `integrable_cexp_neg_mul_sq_norm`
   notes:
   status: out of scope: not an integral over an interval of `ℝ` -/
open scoped FourierTransform in
example {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {t : ℝ} (ht : 0 < t) :
    Integrable (𝓕 fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) := by
  sorry

/- [TAUB-002] TauCetiProject/TauCeti@fb3fbc9f05780f456267a29168dfae7a98c2d8d0 TauCeti/Analysis/Calculus/LineDeriv/IntegrationByParts.lean:268
   kind: statement
   domain: abstract measure
   integrand: abstract
   original proof: specialization of the project lemma `integrable_mul_sq_of_hasCompactSupport`
     (continuous with compact support)
   notes: the `omit` line drops `NormedSpace ℝ E`, `FiniteDimensional` and the Haar instance, so `μ`
     is any measure finite on compacts.
   status: out of scope: not an integral over an interval of `ℝ` -/
example {E V : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {u : E → V} (L : V →L[ℝ] ℝ) (hu : Continuous u) (hsupp : HasCompactSupport u) :
    Integrable (fun x ↦ L (u x) ^ 2) μ := by
  sorry

/- [TAUB-003] TauCetiProject/TauCeti@fb3fbc9f05780f456267a29168dfae7a98c2d8d0 TauCeti/Analysis/PDE/Vortex/Overlap.lean:151
   kind: statement
   domain: ℝⁿ/product
   integrand: abstract
   original proof: project lemma `integrable_mul_comp_add_of_forall_lt` (both factors measurable,
     nonnegative, with exponential decay at every rate below `1`)
   notes: `energyDensity x` and `energyDensity y` (curvature, covariant derivatives and section of a
     vortex, defined through several project definitions) are variable functions `ex`, `ey` with the
     facts the proof used: continuity (`continuous_energyDensity_of_equation_eq_zero`), nonnegativity,
     and the decay bound `exists_energyDensity_le_mul_exp`.
   status: out of scope: not an integral over an interval of `ℝ` -/
example (μ : Measure ℂ) [μ.IsAddHaarMeasure] (a : ℂ) {ex ey : ℂ → ℝ} (hcx : Continuous ex)
    (hcy : Continuous ey) (hx0 : ∀ z, 0 ≤ ex z) (hy0 : ∀ z, 0 ≤ ey z)
    (hxd : ∀ c < 1, ∃ K, ∀ z, ex z ≤ K * Real.exp (-(c * ‖z‖)))
    (hyd : ∀ c < 1, ∃ K, ∀ z, ey z ≤ K * Real.exp (-(c * ‖z‖))) :
    Integrable (fun z ↦ ex z * ey (z + a)) μ := by
  sorry

/- [TAUB-004] TauCetiProject/TauCeti@fb3fbc9f05780f456267a29168dfae7a98c2d8d0 TauCeti/Probability/Distributions/Stable/SmallJump/Basic.lean:54
   kind: statement
   domain: abstract measure
   integrand: explicit
   original proof: case split on the parameters; density computation, then `mono'` against the
     project's ball integrability `integrableOn_norm_rpow_ball` of `|x| ^ (q - α - 1)`
   notes: `stableLevyMeasure α β` (Lebesgue measure with density `stableLevyDensity α β`) inlined.
   status: out of scope: not an integral over an interval of `ℝ` -/
example {α β q : ℝ} (hq : α < q) (r : ℝ) :
    IntegrableOn (fun x : ℝ ↦ |x| ^ q) (Metric.ball 0 r)
      ((volume : Measure ℝ).withDensity fun x ↦ ENNReal.ofReal
        (if 0 < α ∧ α < 2 ∧ |β| ≤ 1 ∧ x ≠ 0 then
          Real.Gamma (1 + α) * Real.sin (π * α / 2) / π *
            (if 0 < x then 1 + β else 1 - β) * |x| ^ (-(α + 1))
        else 0)) := by
  sorry

/- [TAUB-005] TauCetiProject/TauCeti@fb3fbc9f05780f456267a29168dfae7a98c2d8d0 TauCeti/Analysis/LaplaceTransform/Truncated.lean:170
   kind: have
   domain: half-line
   integrand: explicit
   original proof: Mathlib `integrableOn_exp_mul_Iic`, then `const_mul`
   notes: the enclosing `hz`, `hT` and the preceding `hM` are hypotheses.
   status: proved by `endpoint_integrability` -/
example {M T : ℝ} {z : ℂ} (hz : z.re < 0) (hT : 0 ≤ T) (hM : 0 ≤ M) :
    IntegrableOn (fun t : ℝ ↦ M * Real.exp (-z.re * t)) (Iic T) := by
  endpoint_integrability

/- [TAUB-006] TauCetiProject/TauCeti@fb3fbc9f05780f456267a29168dfae7a98c2d8d0 TauCeti/MeasureTheory/Integral/Bochner/Basic.lean:941
   kind: have
   domain: abstract measure
   integrand: abstract
   original proof: `integrable_of_norm_sub_le` against `hfw` with the bound `ε / (I + 1) * ‖w‖`
   notes: the local `I` (set to `∫ x, ‖w x‖ ∂μ`) inlined; the index `i` of the uniformly convergent
     family is fixed, and its measurability `hmi` and the preceding pointwise bound `hbound` are
     hypotheses.
   status: out of scope: not an integral over an interval of `ℝ` -/
example {α ι 𝕜 G : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [PseudoMetricSpace 𝕜] [Zero 𝕜] [SMul 𝕜 G] [IsBoundedSMul 𝕜 G]
    {fs : ι → α → 𝕜} {f : α → 𝕜} {w : α → G} (hw : Integrable w μ)
    (hfw : Integrable (fun x => f x • w x) μ) {ε : ℝ} (hε : 0 < ε) (i : ι)
    (hmi : AEStronglyMeasurable (fun x => fs i x • w x) μ)
    (hbound : ∀ x, ‖f x • w x - fs i x • w x‖ ≤ ε / ((∫ x, ‖w x‖ ∂μ) + 1) * ‖w x‖) :
    Integrable (fun x => fs i x • w x) μ := by
  sorry

/- [TAUB-007] TauCetiProject/TauCeti@fb3fbc9f05780f456267a29168dfae7a98c2d8d0 TauCeti/Analysis/PDE/Yamabe/Quotient.lean:350
   kind: have
   domain: abstract measure
   integrand: abstract
   original proof: continuous on a compact space (`integrable_of_compactSpace`)
   notes: the closed Riemannian manifold with `riemannianVolume` is a compact topological measure space
     with a measure finite on compacts; `conformalLaplacian I u` is a variable function `L` with the
     fact the proof used (continuity, from `contMDiff_conformalLaplacian`); `v` is continuous (from
     `hv : ContMDiff I 𝓘(ℝ) 1 v`).
   status: out of scope: not an integral over an interval of `ℝ` -/
example {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M] [MeasurableSpace M]
    [BorelSpace M] (μ : Measure M) [IsFiniteMeasureOnCompacts μ] {v L : M → ℝ}
    (hv : Continuous v) (hL : Continuous L) :
    Integrable (fun x ↦ v x * L x) μ := by
  sorry

/- [TAUB-008] TauCetiProject/TauCeti@fb3fbc9f05780f456267a29168dfae7a98c2d8d0 TauCeti/MeasureTheory/Function/LocallyIntegrable.lean:745
   kind: statement
   domain: abstract measure
   integrand: abstract
   original proof: integrable on the compact `tsupport g` (`integrableOn_compact_subset`), then
     `continuousOn_clm_apply_of_ae_mem` with `innerSL`, and zero off `tsupport g`
   notes:
   status: out of scope: not an integral over an interval of `ℝ` -/
open scoped InnerProductSpace in
example {X 𝕜 E : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {μ : Measure X} {s : Set X}
    {f g : X → E} (hf : LocallyIntegrableOn f s μ) (hg : ContinuousOn g (tsupport g))
    (h'g : HasCompactSupport g) (hgs : tsupport g ⊆ s) :
    Integrable (fun x ↦ ⟪g x, f x⟫_𝕜) μ := by
  sorry

/- [TAUB-009] TauCetiProject/TauCeti@fb3fbc9f05780f456267a29168dfae7a98c2d8d0 TauCeti/Probability/Distributions/Stable/Approximation/Basic.lean:136
   kind: have
   domain: abstract measure
   integrand: explicit
   original proof: `integrableOn_const` from the finiteness of the cutoff mass
   notes: `ν = stableLevyMeasure α β` (Lebesgue measure with density `stableLevyDensity α β`) and the
     cutoff set `s = {x | ε < |x|}` inlined; the preceding `hm_top` (project lemma
     `stableLevyMeasure_abs_gt_ne_top`) is a hypothesis.
   status: out of scope: not an integral over an interval of `ℝ` -/
example {α β ε : ℝ} (hε : 0 < ε)
    (hm_top : (volume : Measure ℝ).withDensity (fun x ↦ ENNReal.ofReal
        (if 0 < α ∧ α < 2 ∧ |β| ≤ 1 ∧ x ≠ 0 then
          Real.Gamma (1 + α) * Real.sin (π * α / 2) / π *
            (if 0 < x then 1 + β else 1 - β) * |x| ^ (-(α + 1))
        else 0)) {x : ℝ | ε < |x|} ≠ (∞ : ℝ≥0∞)) :
    IntegrableOn (fun _ : ℝ ↦ (1 : ℂ)) {x : ℝ | ε < |x|}
      ((volume : Measure ℝ).withDensity fun x ↦ ENNReal.ofReal
        (if 0 < α ∧ α < 2 ∧ |β| ≤ 1 ∧ x ≠ 0 then
          Real.Gamma (1 + α) * Real.sin (π * α / 2) / π *
            (if 0 < x then 1 + β else 1 - β) * |x| ^ (-(α + 1))
        else 0)) := by
  sorry

/- [TAUB-010] TauCetiProject/TauCeti@fb3fbc9f05780f456267a29168dfae7a98c2d8d0 TauCeti/Statistics/MissingData/AugmentedIPW.lean:134
   kind: have
   domain: abstract measure
   integrand: abstract
   original proof: project lemma `integrable_div_mul` (`Integrable.bdd_mul`, the factor bounded by `δ⁻¹`)
   notes: the propensities `π₀`, `π` renamed `p₀`, `p` (`π` is notation under `open Real`);
     `IsMissingAtRandom Q π₀` replaced by the three facts the proof used (measurable, `0 ≤ p₀ ≤ 1`).
   status: out of scope: not an integral over an interval of `ℝ` -/
example {X : Type*} [MeasurableSpace X] (Q : Measure (Bool × X × ℝ)) [IsFiniteMeasure Q]
    (p₀ p : X → ℝ) (hp₀m : Measurable p₀) (hp₀0 : ∀ x, 0 ≤ p₀ x) (hp₀1 : ∀ x, p₀ x ≤ 1)
    (hpm : Measurable p) (δ : ℝ) (hδ : 0 < δ) (hp : ∀ x, δ ≤ p x) :
    ∀ {f : Bool × X × ℝ → ℝ}, Integrable f Q →
      Integrable (fun w ↦ p₀ w.2.1 / p w.2.1 * f w) Q := by
  sorry

/- [TAUB-011] TauCetiProject/TauCeti@fb3fbc9f05780f456267a29168dfae7a98c2d8d0 TauCeti/NumberTheory/ModularForms/ModularSymbols/Period/Integral.lean:384
   kind: have
   domain: half-line
   integrand: explicit with opaque factor
   original proof: project lemma `integrableOn_resToImagAxis_periodIntegrand_slash` (cusp-form decay at
     both ends of the imaginary axis) after identifying the period integrand of a monomial
   notes: `resToImagAxis F t = if 0 < t then F (I t) else 0` inlined; the local `c j` inlined; TauCeti's
     scoped slash action of `GL(2, ℚ)` is by definition the slash by the real image
     `Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g`, written so.
   status: open: goals left: locallyIntegrableOn, nhdsGT, atTop -/
open UpperHalfPlane in
open scoped ModularForm MatrixGroups in
example {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}
    [CuspFormClass F Γ k] (f : F) {w : ℕ} (hk : k = w + 2) (τ : ℂ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det) (j : ℕ) (hj : j ∈ Finset.range (w + 1)) :
    IntegrableOn (fun t : ℝ ↦ if ht : 0 < t then
        (((((w.choose j : ℂ) * (-τ) ^ (w - j)) • fun z : ℍ ↦ f z * (z : ℂ) ^ j) ∣[(2 : ℤ)]
          (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g)) ⟨Complex.I * t, by simpa using ht⟩)
      else 0) (Ioi 0) := by
  sorry

/- [TAUB-012] TauCetiProject/TauCeti@fb3fbc9f05780f456267a29168dfae7a98c2d8d0 TauCeti/Analysis/Complex/CauchyIntegralPolydisc.lean:505
   kind: statement
   domain: bounded interval
   integrand: explicit
   original proof: the derivative is continuous (`deriv_circleMap`), integrable on `Icc`, then
     restricted to `Ioc`
   notes:
   status: open: goals left: locallyIntegrableOn, nhdsGT, nhdsLT -/
example (c : ℂ) (R : ℝ) :
    Integrable (deriv (circleMap c R)) (volume.restrict (Ioc 0 (2 * π))) := by
  sorry

/- [TAUB-013] TauCetiProject/TauCeti@fb3fbc9f05780f456267a29168dfae7a98c2d8d0 TauCeti/Probability/Distributions/Skellam/Transforms.lean:96
   kind: statement
   domain: abstract measure
   integrand: explicit
   original proof: project lemma `integrable_pow_of_integrable_exp_mul` from the exponential moments
     at `1` and `-1`
   notes: `skellamMeasure r₁ r₂` (image of the product of two Poisson laws under `(a, b) ↦ a - b`)
     inlined.
   status: out of scope: not an integral over an interval of `ℝ` -/
open scoped NNReal in
example (r₁ r₂ : ℝ≥0) (n : ℕ) :
    Integrable (fun k : ℤ => (k : ℝ) ^ n)
      (((ProbabilityTheory.poissonMeasure r₁).prod (ProbabilityTheory.poissonMeasure r₂)).map
        (fun z : ℕ × ℕ => (z.1 : ℤ) - (z.2 : ℤ))) := by
  sorry

/- [TAUB-014] TauCetiProject/TauCeti@fb3fbc9f05780f456267a29168dfae7a98c2d8d0 TauCeti/Analysis/PDE/Vortex/FiniteKernel.lean:161
   kind: domination
   domain: ℝⁿ/product
   integrand: abstract
   original proof: `hn.const_mul _` for the bound; `|ψ n z * χ z| ≤ M` for the a.e. bound
   notes: hypotheses of `tendsto_integral_of_dominated_convergence`, concrete bound `M ^ 2 * ‖y z‖ ^ 2`
     on `volume` on `ℂ`; the cutoffs `ψ n` and the factor `χ` are variable functions with the facts
     the proof used (`hψ01`, `hχM`); the preceding `hn` is a hypothesis.
   status: out of scope: a domination hypothesis, not an integrability goal -/
example {M : ℝ} {ψ : ℕ → ℂ → ℝ} {χ : ℂ → ℝ} {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hχM : ∀ z, |χ z| ≤ M) (hψ01 : ∀ n z, 0 ≤ ψ n z ∧ ψ n z ≤ 1)
    (hn : Integrable fun z ↦ ‖y z‖ ^ 2) :
    Integrable (fun z ↦ M ^ 2 * ‖y z‖ ^ 2) ∧
      ∀ n : ℕ, ∀ᵐ z ∂volume, ‖‖(ψ n z * χ z) • y z‖ ^ 2‖ ≤ M ^ 2 * ‖y z‖ ^ 2 := by
  sorry

/- [TAUB-015] TauCetiProject/TauCeti@fb3fbc9f05780f456267a29168dfae7a98c2d8d0 TauCeti/Analysis/Fourier/Continuous.lean:170
   kind: domination
   domain: ℝⁿ/product
   integrand: abstract
   original proof: `hb` for the bound; `hbd` and `Circle.norm_smul` for the a.e. bound
   notes: hypotheses of `hasDerivAt_integral_of_dominated_loc_of_deriv_le` for the integrands
     `𝐞 ⟪ξ, x⟫ • G' s ξ`, with the hypothesised bound `b`; the enclosing `hbd`, `hb` are hypotheses.
   status: out of scope: a domination hypothesis, not an integrability goal -/
open scoped FourierTransform in
example {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E]
    {G' : ℝ → V → E} {b : V → ℝ} {S : Set ℝ} (hbd : ∀ᵐ ξ, ∀ s ∈ S, ‖G' s ξ‖ ≤ b ξ)
    (hb : Integrable b) (x : V) :
    Integrable b ∧ ∀ᵐ ξ ∂volume, ∀ s ∈ S, ‖𝐞 (inner ℝ ξ x) • G' s ξ‖ ≤ b ξ := by
  sorry

end TauCeti

section CarlesonBrownian

open MeasureTheory Set Filter Topology Metric

/- [CBB-001] fpvandoorn/carleson@f7487cc9da4d1e73f009dc0280cd5b958f3e2c78 Carleson/ForestOperator/PointwiseEstimate.lean:1139
   kind: have
   domain: abstract measure
   integrand: abstract
   original proof: `Integrable.bdd_mul` of `integrable_Ks_x` with the measurability of `approxOnCube` and
     the bound by the sum of the norms of the cube averages
   notes: `approxOnCube (𝓙 (t.𝔗 u)) f y = ∑ J with J ∈ 𝓙 (t.𝔗 u), (J : Set X).indicator (fun _ ↦ ⨍ y in J, f y) y`
     inlined, with the cubes as a finset `𝓙` of measurable sets; the kernel `Ks` is a variable function
     with the fact the proof used (`integrable_Ks_x`: `Integrable (Ks i x)`).
   status: out of scope: not an integral over an interval of `ℝ` -/
example {X : Type*} [MeasureSpace X] (f : X → ℂ) (𝓙 : Finset (Set X))
    (h𝓙 : ∀ J ∈ 𝓙, MeasurableSet J) (Ks : ℤ → X → X → ℂ)
    (hKs : ∀ (i : ℤ) (x : X), Integrable (Ks i x)) (x : X) {i : ℤ} :
    Integrable (fun y ↦ (∑ J ∈ 𝓙, J.indicator (fun _ ↦ ⨍ z in J, f z) y) * Ks i x y) := by
  sorry

/- [CBB-002] RemyDegenne/brownian-motion@8fd8dc52830cdd07cf9cc8eadd533e284425fa6f BrownianMotion/StochasticIntegral/DoobMeyer.lean:2535
   kind: have
   domain: abstract measure
   integrand: abstract
   original proof: `integrable_of_le_of_le` (a.e.-measurable `limsup` squeezed between integrable `W` and `Y`)
   notes: the preceding `have hae` (a.e. boundedness and coboundedness) is a hypothesis.
   status: out of scope: not an integral over an interval of `ℝ` -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ι : Type*} [Countable ι]
    {L : Filter ι} [L.NeBot] [L.IsCountablyGenerated] {X : ι → Ω → ℝ} {W Y : Ω → ℝ}
    (hX_meas : ∀ i, AEMeasurable (X i) P) (hW : Integrable W P) (hY : Integrable Y P)
    (hWX : ∀ i, W ≤ᵐ[P] X i) (hXY : ∀ i, X i ≤ᵐ[P] Y)
    (hae : ∀ᵐ ω ∂P, IsBoundedUnder (· ≤ ·) L (fun i ↦ X i ω) ∧
      IsCoboundedUnder (· ≤ ·) L (fun i ↦ X i ω)) :
    Integrable (fun ω ↦ limsup (fun i ↦ X i ω) L) P := by
  sorry

/- [CBB-003] fpvandoorn/carleson@f7487cc9da4d1e73f009dc0280cd5b958f3e2c78 Carleson/ForestOperator/L2Estimate.lean:17
   kind: statement
   domain: abstract measure
   integrand: abstract
   original proof: support in a closed ball, then `BoundedCompactSupport.integrable_mul` with the
     integrability of `K` on a bounded annulus (`integrableOn_K_Icc`)
   notes: `BoundedCompactSupport f volume` unpacked into its two fields (`MemLp f ⊤`, `HasCompactSupport f`);
     `EAnnulus.ci x' r = {y | edist x' y ∈ Ici r}` inlined; the kernel `K` is a variable function with the
     fact the proof used (`integrableOn_K_Icc`: integrable on every annulus `{y | dist x y ∈ Icc r R}`,
     `0 < r`); the project's `ProofData` space is replaced by a metric measure space with Borel σ-algebra.
   status: out of scope: not an integral over an interval of `ℝ` -/
example {X : Type*} [MetricSpace X] [MeasureSpace X] [BorelSpace X] {K : X → X → ℂ}
    (hK : ∀ (x : X) (r R : ℝ), 0 < r → IntegrableOn (K x) {y | dist x y ∈ Icc r R} volume)
    {f : X → ℂ} (hf₁ : MemLp f ⊤ volume) (hf₂ : HasCompactSupport f) {x' : X} {r : ENNReal}
    (hr : 0 < r) :
    IntegrableOn (fun y ↦ K x' y * f y) {y | edist x' y ∈ Ici r} volume := by
  sorry

/- [CBB-004] RemyDegenne/brownian-motion@8fd8dc52830cdd07cf9cc8eadd533e284425fa6f BrownianMotion/StochasticIntegral/Quasimartingale/MaximalInequality.lean:206
   kind: have
   domain: abstract measure
   integrand: abstract
   original proof: closure lemmas (`((integrable_const a).sub (hXint t)).pos_part`)
   notes:
   status: out of scope: not an integral over an interval of `ℝ` -/
example {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ι → Ω → ℝ} (hXint : ∀ s, Integrable (X s) μ) (a : ℝ) (t : ι) :
    Integrable (fun ω ↦ (a - X t ω)⁺) μ := by
  sorry

/- [CBB-005] fpvandoorn/carleson@f7487cc9da4d1e73f009dc0280cd5b958f3e2c78 Carleson/TwoSidedCarleson/WeakCalderonZygmund.lean:1318
   kind: statement
   domain: abstract measure
   integrand: abstract
   original proof: closure lemmas (`IntegrableOn.indicator` of the integrable remainder, minus a constant
     on a finite-measure ball)
   notes: `g r x hX j = g₀ r x hX j - d r x hX j` inlined, with `g₀ = (ball x r)ᶜ.indicator (czRemainder' hX j)`,
     `d = ⨍ y in czBall3 hX j, g₀ y` and `czBall3 hX j = ball (czCenter hX j) (3 * czRadius hX j)`;
     `czRemainder' hX j` is a variable function `R` with the fact the proof used (`Integrable R`, from
     `hf.czRemainder'`), centre and radius are variables `c`, `ρ`; the doubling metric measure space is
     replaced by the instances the proof used for `measure_ball_ne_top` (`ProperSpace`,
     `IsFiniteMeasureOnCompacts`).
   status: out of scope: not an integral over an interval of `ℝ` -/
example {X : Type*} [MetricSpace X] [MeasureSpace X] [ProperSpace X] [BorelSpace X]
    [IsFiniteMeasureOnCompacts (volume : Measure X)] (R : X → ℂ) (hR : Integrable R)
    (c : X) (ρ : ℝ) (x : X) (r : ℝ) :
    IntegrableOn (fun y ↦ (ball x r)ᶜ.indicator R y -
      ⨍ z in ball c (3 * ρ), (ball x r)ᶜ.indicator R z) (ball c (3 * ρ)) volume := by
  sorry

end CarlesonBrownian
