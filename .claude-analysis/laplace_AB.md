# LaplaceA / LaplaceB deduplication analysis

Target for deduplication: `SpherePacking/MagicFunction/g/CohnElkies/LaplaceA/` vs
`SpherePacking/MagicFunction/g/CohnElkies/LaplaceB/`.

Verified line counts (wc -l):

| File | Lines |
|---|---:|
| LaplaceA/Basic.lean | 484 |
| LaplaceA/StripBounds.lean | 786 |
| LaplaceA/TailDeformation.lean | 710 |
| LaplaceA/FiniteDifference.lean | 115 |
| LaplaceA/LaplaceRepresentation.lean | 141 |
| **LaplaceA total** | **2236** |
| LaplaceB/Basic.lean | 415 |
| LaplaceB/ContourIdentities.lean | 190 |
| LaplaceB/LaplaceRepresentation.lean | 918 |
| **LaplaceB total** | **1523** |
| LaplaceLemmas.lean (already shared) | 71 |
| DeltaBounds.lean (already shared) | 43 |
| IntegralPieces.lean (already shared, trig) | 59 |
| IntegralReductions.lean (already shared) | 75 |

Phase 6 commits were small: `adc68d3` created `AnotherIntegral/ContinuationGeneric.lean`
(70 lines, used by A/B of a different file-pair), `8e15f3d` and `f83c50d` together saved
~25 lines by factoring `exp_two_pi_mul_mul_exp_neg_pi_mul` into `LaplaceLemmas.lean`.
**Phase 6 touched only 3 tiny helpers**; the bulk of the LaplaceA/LaplaceB content was
untouched. There is no `LaplaceCommon.lean` — the only shared infrastructure for the
A/B Laplace pair is the 4 small files at the end of the table above.


## 1. Why is LaplaceA (2236) larger than LaplaceB (1523)?

The asymmetry is **mostly structural / legacy-duplication**, with a secondary
mathematical component. The math in both sides is the *same* rectangle-contour
deformation argument, differing only in which modular forms appear in the integrand.
The size difference breaks down as follows.

### 1a. Side A re-derives things side B encapsulated (~550 lines of overhead)

LaplaceB has a dedicated `ContourIdentities.lean` (190 lines) that introduces
first-class objects:

- `bContourWeight u z := cexp (π*I*u*z)` and multiplicativity
  `bContourWeight_add` (`LaplaceB/ContourIdentities.lean:32-38`)
- `bContourIntegrandI/T/S u z := ψI'/ψT'/ψS' z * bContourWeight u z`
  (`LaplaceB/ContourIdentities.lean:41-50`)
- pointwise shift identities `ψT'_eq_ψI'_add_one`,
  `ψT'_{neg_one,one,I}_add_I_mul` (`ContourIdentities.lean:77-112`)
- holomorphy/continuity of the integrand
  (`differentiableOn_bContourIntegrandT`, `ContourIdentities.lean:170-186`)

Side A has **no equivalent abstraction layer**. In A, every strip estimate inlines
the full `Φⱼ' u z = φ_{...} '' (...) * cexp (π*I*u*z)` expansion, computes
`‖cexp (π*I*u*(x+t*I))‖ = exp(-π*u*t)` from scratch, and rebuilds the exponential
weight at each call site. Grep counts:

- `LaplaceA/StripBounds.lean`: 40 lines containing `Real.exp`/`norm_exp`/`cexp`
- `LaplaceA/Basic.lean`: 44 such lines
- `LaplaceA/TailDeformation.lean`: 18 such lines
- `LaplaceB/LaplaceRepresentation.lean`: 40 such lines (but mostly on `bContourWeight`)

In A, the exponential-weight manipulation alone appears at least six times as a
hand-written `hExpNorm`/`hExpRew` block:
- `StripBounds.lean:508-521` (`norm_Φ₂'_imag_axis_le`)
- `StripBounds.lean:522-525` (`hExpRew`)
- `TailDeformation.lean:96-111` (`norm_Φ₂'_strip_le`)
- `TailDeformation.lean:204-219` (`norm_Φ₄'_strip_le`)
- `Basic.lean:428-435` (`hExpNorm`, `hExpRew` in `aLaplaceIntegral_convergent`)
- `StripBounds.lean:198-249` (`integrableOn_Φ₆'_imag_axis` contains a variant)

Each block is ~12-20 lines of `ring_nf; simp [Complex.ofReal_exp]`,
`Complex.norm_exp`, then using the shared `exp_two_pi_mul_mul_exp_neg_pi_mul`
from `LaplaceLemmas.lean`. **Total duplicated exponential-norm boilerplate in A:
~120 lines.**

### 1b. Side A's modular-form bounds are deeper but duplicate three times

Side A needs `φ₀` (weight-0 cusp form built from `(E₂E₄-E₆)^2 / Δ`), `φ₂'`
(`E₄(E₂E₄-E₆)/Δ`), `φ₄'` (`E₄²/Δ`) *and* the Poincaré `S`-transform
`φ₀_S_transform_mul_sq` (`StripBounds.lean:147-151`). Side B needs only `ψI`,
and the exponential growth bound for `ψI` is proved *once* in
`LaplaceB/Basic.lean:72-145` (73 lines).

The analogous work for A is duplicated/scattered:

- `exists_phi2'_phi4'_bound_exp` in `StripBounds.lean:46-144` (98 lines) —
  proves exponential bounds for `φ₂'` and `φ₄'` packed together.
- Near-origin bound for `φ₀''` used inside `aLaplaceIntegral_convergent`,
  `LaplaceA/Basic.lean:105-180` (~75 lines), with a hand-rolled domination
  combining `norm_φ₀''_le` from `I1Decay` and the S-transform.
- Strip/tail bounds using `norm_phi0S_mul_sq_le`, `StripBounds.lean:294-457`
  (~165 lines) — generic reusable helper, then applied specifically in
  `norm_Φ₂'_imag_axis_le` (`StripBounds.lean:460-568`, 108 lines),
  `norm_Φ₂'_strip_le` (`TailDeformation.lean:55-156`, 101 lines), and
  `norm_Φ₄'_strip_le` (`TailDeformation.lean:159-262`, 103 lines).

The three `norm_Φ_strip_le` variants are >80% syntactically identical (see
structural diff in §5 below). **Net savings potential here alone: ~200 lines.**

### 1c. Side A has a genuine mathematical obligation B lacks: the
`φ₀'' (-1/w) * w²` reformulation via `φ₀_S_transform`

In the tail-deformation for A, the integrand `Φ₂'(z)` at `z = x+it` cannot be
bounded directly because `Φ₂'(z) = φ₀''(-1/(z+1)) * (z+1)² * cexp(...)`. The
argument `-1/(z+1)` is not in the standard upper-half-plane form, so the proof
sets `w = z+1`, rewrites via the `S`-transform `φ₀(S•wH) = φ₀''(-1/wH)`, and
then uses the modular `S`-transform identity
`φ₀(S•w)*w² = φ₀(w)*w² - 12i/π * w * φ₂'(w) - 36/π² * φ₄'(w)`. This gives the
crucial factor of `w²` that allows the tail to be majorised by
`t² * exp(-π(u-2)t)`.

On side B, `ψI'(z) = ψT'(z) + ψS'(z)` and the `S`-transform is the identity
`ψT'(z) = ψI'(z+1)`, which is a *linear* shift — so no `w²` weight and no
polynomial-times-exponential integrand. B's tail is simply `C * exp(-π(u-2)t)`.

**This is genuine mathematical asymmetry**: about 250-300 lines of `w²`-bookkeeping
in A cannot be eliminated without a shared "integrand presented as
modular-form-times-exp-weight-and-polynomial-prefactor" abstraction. See §4
for how to capture it.

### Overview

| Category | A overhead | B overhead | Shareable? |
|---|---:|---:|:---|
| (1a) Integrand/weight abstraction | ~300 lines absent | encapsulated (190) | yes, migrate A to the pattern |
| (1a) Inline exponential-norm blocks | ~120 lines duplicated | concentrated (~15) | yes |
| (1b) Duplicated strip/tail bounds | ~200 lines across 3 variants | N/A | yes |
| (1c) `φ₀ S-transform + w²` bookkeeping | ~250 lines essential | N/A | no, but factorizable |
| Measurability / integrability plumbing | ~150 lines | ~80 lines | yes |
| Rectangle-deformation application | ~150 lines in TailDef | ~250 lines in LaplaceRep | yes (common driver) |

Total "pure overhead" in A that B avoids: **roughly 650-750 lines**. Genuine
mathematical difference: **roughly 250-350 lines**. The overall 2236 vs 1523 gap
(713 lines) matches that estimate well.


## 2. StripBounds vs TailDeformation architecture: where does B handle it?

Side A splits the contour work into three files (`FiniteDifference`, `StripBounds`,
`TailDeformation`) plus `LaplaceRepresentation` that assembles them. Side B
folds all of it into one 918-line `LaplaceRepresentation.lean`.

### The A-side split

`LaplaceA/StripBounds.lean` (786) handles:
- `exists_phi2'_phi4'_bound_exp` — modular-form exponential bounds
  (StripBounds.lean:46-144)
- `φ₀_S_transform_mul_sq` wrapper (StripBounds.lean:147-151)
- `norm_phi0S_mul_sq_le` — generic modular bound independent of argument
  (StripBounds.lean:294-457)
- Integrability `integrableOn_Φⱼ'_imag_axis` for `j ∈ {2,4,5,6}` on `Ioi 1`
  (StripBounds.lean:154-655)
- `I₁'_add_I₃'_add_I₅'_eq_imag_axis` — segment-integral lemma for the "non-tail"
  pieces (StripBounds.lean:661-784)

`LaplaceA/TailDeformation.lean` (710) handles:
- `norm_Φ₂'_strip_le`, `norm_Φ₄'_strip_le` — strip bounds with x ∈ [-1,0] / [0,1]
  (TailDeformation.lean:55-262)
- `tendsto_intervalIntegral_Φ₂/4_top` — top-edge decay for open-rect Cauchy
  (TailDeformation.lean:265-343)
- `Iⱼ'_eq_intervalIntegral_bottom` for `j ∈ {2,4}` — parametrization lemmas
  (TailDeformation.lean:345-405)
- `bottom_eq_I_smul_sub_of_rect_deform` — generic open-rect driver
  (TailDeformation.lean:407-446)
- `Iⱼ'_eq_deform_imag_axis` for `j ∈ {2,4,6}` — per-piece deformations
  (TailDeformation.lean:448-649)
- `I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail` — the combined tail identity
  (TailDeformation.lean:654-708)

### The B-side monolith

`LaplaceB/LaplaceRepresentation.lean` (918) handles *all* of:
- `bRadial_eq_laplace_psiI_main` — the final theorem (40-918 = 878 lines of proof)
- embedded: `setIntegral_Ioi0_eq_add_Ioc_Ioi` helper (lines 25-40)
- embedded: integrability of the three vertical-line integrals
  (`hintI`, `hintT_center`, `hintT_shift`, lines 95-232)
- embedded: `htendstoT` decay-at-infinity lemma (lines 234-310)
- embedded: two open-rectangle Cauchy applications (`hRectLeft`, `hRectRight`,
  lines 312-421)
- embedded: per-piece `J_i_top`/`J_i_set`/`J_i_ray` parametrisations (lines 422-598)
- embedded: `hITS`/`hCenter_split`/`hVI_split` linearity (lines 630-756)
- embedded: final algebraic assembly (lines 758-916)

### Recommendation: split B to mirror A, then fold together

A's split is **the right structure**. Having the `StripBounds`/`TailDeformation`
split makes the 786+710+141 file organization understandable; B's 918-line
monolith is an unmaintainable blob where the rectangle deformation and the final
algebra are interleaved.

**Action**: Split `LaplaceB/LaplaceRepresentation.lean` (918) into:
- `LaplaceB/StripBounds.lean` — integrability and decay estimates, ~200 lines
  (extracts lines 95-310, plus the rectangle-deformation applications)
- `LaplaceB/Parametrisations.lean` — the six `J_i_top`/`J_i_set`/`J_i_ray`
  pointwise identities, ~300 lines (extracts lines 422-756)
- `LaplaceB/LaplaceRepresentation.lean` — keeps only `bRadial_eq_laplace_psiI_main`,
  ~200 lines

**Savings (net from this reorganization alone)**: 0 lines. But it enables §4
because A and B can then share `Common/*` lemmas with matching call-site shapes.


## 3. Quantifying "distinct math" vs "shared boilerplate"

Going through each file and classifying each lemma:

### Genuinely A-specific math (non-shareable)

| Lemma | File:line | Lines | Why A-specific |
|---|---|---:|---|
| `φ₀_S_transform_mul_sq` | StripBounds:147 | 6 | Wraps a/SpecialValues theorem |
| `Φ_finite_difference_imag_axis` | FiniteDifference:59 | 57 | `φ₀` FD identity |
| `Φ₁'_shift_left`, `Φ₃'_shift_right` | FiniteDifference:25,31 | 11 | Shift identities for A |
| `norm_phi0S_mul_sq_le` | StripBounds:294 | 164 | Core A bound using S-transform |
| `integrableOn_Φ₆'_imag_axis` | StripBounds:154 | 96 | Uses `φ₀`-decay input |
| `aLaplaceIntegral_convergent` small-t branch | Basic:105-181 | 77 | Uses `I1Decay.norm_φ₀''_le` |
| Total A-only math | | **411** | |

### Genuinely B-specific math (non-shareable)

| Lemma | File:line | Lines | Why B-specific |
|---|---|---:|---|
| `ψI_apply_eq_factor`, `exists_ψI_bound_exp` | Basic:43,72 | 103 | ψI growth bound using H₂, H₃, H₄ |
| `hSlashS` and `ψS_bound` in small-t | Basic:154-178 | 25 | Uses ψS.resToImagAxis slash |
| `hITS` + `hCenter_split` | LaplaceRep:630,709 | 43 | Uses `ψI_eq_add_ψT_ψS` |
| `ψT'_*` shift identities (4 lemmas) | ContourIdentities:77-112 | 36 | ψT = ψI∘(·+1) via slash-T |
| `differentiableOn_ψT_ofComplex` | ContourIdentities:114 | 56 | Via H-functions |
| Total B-only math | | **263** | |

### Shared/duplicated infrastructure (highly refactorable)

| Pattern | A occurrences | B occurrences | Lines per copy |
|---|:---:|:---:|---:|
| Exp-norm on imag axis: `‖cexp(π*I*u*(x+tI))‖ = exp(-π*u*t)` | 4 | 3 | ~15 |
| `Real.exp(2πt)*Real.exp(-πut) = Real.exp(-(π(u-2))t)` | 5 | 3 | ~5 |
| `hExp'.const_mul` + `IntegrableOn` rewrite | 4 | 2 | ~7 |
| `(Ioc 0 1) ∪ (Ioi 1) = Ioi 0` + integrability-union | 4 | 3 | ~20 |
| `ae_restrict_of_forall_mem` + `MeasureTheory.Integrable.mono'` | 5 | 3 | ~15 |
| `UpperHalfPlane.isBoundedAtImInfty_iff → exists` | 5 (in A:46) | 0 | ~6 |
| `IntegrableOn.mono_set` for splitting | 12 | 6 | ~5 |
| `cexp (π*I*u*z)` evaluated on rays — rewriting to real exp | 4 | 1 (abstracted) | ~8 |
| Continuity of integrand via `ContMDiff`/`φ₀''_holo` | 4 | 2 | ~12 |
| Open-rectangle Cauchy application boilerplate | 2 | 2 | ~40 |

Conservatively: **~400 lines of pure copy-paste** are shareable, on top of
architectural simplification from §1.

### Summary numbers

- Pure A-specific math: ~410 lines
- Pure B-specific math: ~260 lines
- Shared framework (exp-norms, integrability plumbing, contour drivers): ~1200 lines
  *currently duplicated*, potentially compressible to ~400 lines (2-3x reduction)
- Assembly code (final theorems): ~150 lines each side
- **Theoretical floor**: ~410 (A math) + ~260 (B math) + ~400 (refactored common) +
  ~300 (assembly) + ~130 (ctor abstractions) ≈ **1500 lines total** vs
  **3759 currently** ⇒ ~2260 lines recoverable in the best case.

A realistic target respecting code quality (not over-golfing) is
**~1000-1200 lines recoverable**, matching the prompt's goal.


## 4. Concrete refactor proposal

### R1. Create `g/CohnElkies/LaplaceCommon/Weight.lean` (new, ~80 lines)

Pull the B-style contour-weight abstraction out of `LaplaceB/ContourIdentities.lean`
and generalize:

```
def contourWeight (u : ℝ) (z : ℂ) : ℂ := cexp (π * I * u * z)
lemma contourWeight_add, contourWeight_mul_I, contourWeight_one, contourWeight_neg_one
lemma norm_contourWeight  -- ‖contourWeight u z‖ = exp(-π u z.im)
```

Rename `bContourWeight → contourWeight` in B; instrument A to **use the same
weight** for `Φⱼ'`. The trig coefficient simplification
(`coeff = -4 sin²(πu/2)`) is already in `IntegralPieces.lean:30-53` (shared).

**Savings**: B saves ~30 lines (lemmas move out); A saves ~70 lines (4 hand-rolled
`hExpNorm` blocks in Basic/StripBounds/TailDeformation collapse to `norm_contourWeight`
applications). **Net: ~100 lines**. *Risk: low*; purely mechanical renaming plus
deleting redundant computations.

### R2. Create `g/CohnElkies/LaplaceCommon/RectDeformDriver.lean` (new, ~120 lines)

Extract the rectangle-deformation closer, which is nearly identical in A and B.
A's `bottom_eq_I_smul_sub_of_rect_deform` (TailDeformation.lean:407-446, 40 lines)
is already *almost* the right abstraction, but uses a single function argument.
Generalize:

```
lemma rect_deform_bottom_sub
    {f g : ℂ → ℂ} {x₁ x₂ : ℝ} {y₀ : ℝ}
    (hcontf : ContinuousOn f {z | y₀ ≤ z.im})
    (hdifff : DifferentiableOn ℂ f {z | y₀ < z.im})
    (hint_left, hint_right : IntegrableOn ...)
    (htop : Tendsto (fun m => ∫ x in x₁..x₂, f(x+mI)) atTop (𝓝 0)) :
  (∫ x in x₁..x₂, f(x + y₀*I)) = I • (left_ray - right_ray)
```

Then both `hRectLeft`/`hRectRight` in `LaplaceB/LaplaceRepresentation.lean:312-421`
(~110 lines of almost-identical twin rectangle applications) and A's
`I₂'/I₄'_eq_deform_imag_axis` (`TailDeformation.lean:448-532`, ~85 lines of
twin applications) reduce to ~10-line invocations of the driver.

**Savings**: A: ~80 lines. B: ~80 lines. **Net: ~160 lines**. *Risk: medium* —
requires careful handling of the `Set.uIcc`/`Set.min`/`Set.max` orientation
reversal (A uses both `x₁=−1,x₂=0` and `x₁=1,x₂=0` patterns; B uses
`x₁=0,x₂=1`). Making the API orientation-agnostic is the main design choice.

### R3. Create `g/CohnElkies/LaplaceCommon/Integrability.lean` (new, ~150 lines)

Pull out:
- `integrableOn_sq_mul_exp_neg` (currently `LaplaceA/Basic.lean:64-85`) — already
  generic; just move it.
- `IntegrableOn_of_exp_decay_on_Ioi` — generic "integrand ≤ C·exp(-a·t) on
  `Ioi A` with measurability ⇒ integrable" combinator. Called 3 times in A and
  2 times in B with ~25-line inline arguments each.
- `IntegrableOn_of_poly_exp_decay_on_Ioi` — same with `t²·exp(-a·t)`. Called 4
  times in A.
- `continuousOn_compose_imagAxis` — continuity of `t ↦ f(Complex.I * t)` on
  `Ioi 0` via upper-half-plane continuity of `f`. Repeated 5 times in B alone
  (e.g. `LaplaceB/Basic.lean:178-208` and 3 more places in `LaplaceRep`).
- `aestronglyMeasurable_imagAxis_Ioi` — dual for `AEStronglyMeasurable`.

**Savings**: A: ~120 lines. B: ~80 lines. **Net: ~200 lines**. *Risk: low*;
these are true library-quality generic lemmas. Will need careful naming to avoid
polluting the top-level namespace.

### R4. Abstract `LaplaceA/StripBounds.lean` `norm_Φⱼ'_{imag_axis/strip}_le`
(reduce A's 4 variants to 1 + 3 thin specializations)

Currently A has four functions structurally identical up to a parameter
`(x-shift, argument-of-S-transform)`:

- `norm_Φ₂'_imag_axis_le` (StripBounds:460-568, 108 lines; x=0)
- `norm_Φ₂'_strip_le` (TailDeformation:55-156, 101 lines; x ∈ [-1,0])
- `norm_Φ₄'_strip_le` (TailDeformation:159-262, 103 lines; x ∈ [0,1])
- Inline use inside `aLaplaceIntegral_convergent` large-t (Basic:182-468,
  ~285 lines ← this one is very tangled)

Introduce a single:

```
lemma norm_phi0_S_integrand_le (x t u : ℝ) (hx : |x| ≤ 1) (ht1 : 1 ≤ t)
    (hφ : …modular-form bound…) :
  ‖φ₀'' (-1 / (x + t*I + c)) * (x + t*I + c)² * cexp(π*I*u*(x+t*I))‖ ≤
    K * t² * exp(-π*(u-2)*t)
```

parameterized over the shift `c ∈ {-1, 0, 1}`, with the three `Φⱼ' u (...)`
definitions unfolded via small wrappers.

**Savings**: ~200 lines (collapse 3 copies + inline use to 1 definition + 3
×15-line specializations). *Risk: medium-high* — the existing inline use in
`aLaplaceIntegral_convergent` is especially large (~285 lines) and would need
to be mostly replaced by a call to this lemma + per-integrand-unfolding work
in Basic. It'd likely reduce `LaplaceA/Basic.lean` by 150+ lines alone, at
the cost of adding 50-80 to the common file.

### R5. Common `Iⱼ'_eq_intervalIntegral_bottom` / `Jⱼ'_eq_intervalIntegral_bottom`
parametrisation helper

A has two such lemmas (`TailDeformation:345-405`, 61 lines).
B has six (`LaplaceRep:428-598`, ~170 lines). They're all variants of
"take the definition `Iⱼ' u = ∫₀¹ I·Φⱼ'(zⱼ'(t))`, substitute
`zⱼ'(t) = aⱼ + bⱼ*t + cⱼ*I`, optionally reverse orientation, rewrite to set
integral". Abstract to a helper:

```
lemma eval_parametrised_integral
    {a b : ℂ} {Φ : ℝ → ℂ → ℂ} {z : ℝ → ℂ} {u : ℝ}
    (hz : ∀ t ∈ Icc 0 1, z t = a + b * (t : ℂ)) ... :
  ∫ t in (0:ℝ)..1, I * Φ u (z t) = I * (∫ t in (0:ℝ)..1, Φ u (a + b*(t:ℂ)))
```

plus `orient_reverse` wrapper. Each of the 8 call sites becomes a 2-line
invocation. **Savings**: ~100 lines across A and B. *Risk: low*.

### R6. Merge A's `FiniteDifference.lean` with
`LaplaceCommon/ShiftIdentities.lean`

A: `FiniteDifference.lean` has `Φ₁'_shift_left`, `Φ₃'_shift_right`
(11 lines) — pure algebraic shifts of the exponential weight
— and `Φ_finite_difference_imag_axis` (A-specific, keeps).

B: `ContourIdentities.lean` has `ψT'_{*}_add_I_mul` shifts (36 lines)
and `bContourWeight_add` (2 lines).

The shift identities for `Φⱼ'` on A's side and `ψT'` on B's side are both
of the form "translation of the integrand by ±1 factors out a
`bContourWeight u (±1) = cexp(±π u I)`". If the contour-weight
abstraction is shared (R1), the shift identities become:

- A side: `Φ_j'(z+shift) = bContourWeight u shift * Φ_j' z`
  (generic, ~5 lines)
- B side: ψT to ψI shift requires the slash-action identity (~15 lines;
  mathematically specific).

**Savings**: ~20 lines. *Risk: very low*. Mostly organizational.

### Summary of refactor plan

| Refactor | Lines saved | Risk | Order |
|---|---:|---|---|
| R1 Weight common | 100 | low | 1st |
| R2 Rect-deform driver | 160 | medium | 3rd |
| R3 Integrability common | 200 | low | 2nd |
| R4 Modular-bound unified | 200 | medium-high | 4th |
| R5 Parametrisation helper | 100 | low | 2nd |
| R6 Shift identities | 20 | very low | with R1 |
| Split B into 3 files (§2) | 0 | low | before R2/R4 |
| **Total** | **~780-880** | | |

To reach ~1000-1200, the split of `LaplaceB/LaplaceRepresentation.lean` into
3 files should be combined with a one-shot rewrite of the resulting `StripBounds.lean`
(both A and B versions) to use the unified lemmas — which, as a second-order
effect beyond line-by-line deletion, collapses several `have hcontIoi …` etc.
blocks because repeated simp-rewriting patterns become single lemma invocations.
Conservatively: **800 lines**, aspirationally: **1100 lines**, with
R1+R3+R5 being the no-regret path saving ~400 lines immediately with trivial risk.

### Risks

1. **Module visibility**: `LaplaceA/Basic.lean` has `public import ... DeltaBounds`
   etc.; moving lemmas requires checking the propagation of `@[expose]` and
   `public` annotations. Already two files (`IntegralReductions`, `LaplaceLemmas`)
   have been sanitized for this; pattern is understood.

2. **B downstream uses `ψT'`/`ψI'`/`ψS'` on non-imaginary arguments**
   (e.g. `x + 1*I` in `hRectLeft`); any shared abstraction must not over-assume
   the imaginary axis. R1's `contourWeight` is fine; R2 requires care.

3. **The `@[expose]` on `aLaplaceIntegrand`/`bLaplaceIntegrand`** means external
   callers of these names exist. The refactor must **not rename** these; it
   should only refactor the *proofs* of their properties.

4. **Phase 6's `analytic_continuation_of_gt2`** (70 lines in
   `AnotherIntegral/ContinuationGeneric.lean`) shows a shared wrapper already
   works for a genuinely harder 2-way duality between A and B. The pattern
   succeeded — but took 3 small commits totalling ~25 net lines of savings.
   The bigger wins proposed here need larger restructurings.


## 5. File-pair diffs: structural comparison

### Diff pair 1: `LaplaceA/Basic.lean:aLaplaceIntegral_convergent` vs `LaplaceB/Basic.lean:bLaplaceIntegral_convergent`

Both prove `IntegrableOn (fun t => <laplace-integrand> u t) (Set.Ioi (0 : ℝ))`
for `u > 2`. Both follow the pattern:

1. Split `Ioi 0 = Ioc 0 1 ∪ Ioi 1` (A:100-102, B:406-407)
2. Small-t branch by constant domination (A:103-180 = 78 lines, B:209-278 = 70 lines)
3. Large-t branch by exponential domination (A:182-480 = 299 lines, B:279-411 = 133 lines)
4. Combine via `IntegrableOn.union` (A:478-479, B:405-410)

The A large-t branch is **2.3× longer** than B's, mostly because:
- A must construct the `φ₀(S•w)·w²` bound inline (130 lines, R4 would cut to ~30)
- A must handle five different growth constants `B2, B4, B6, CΔ` for
  `E₂, E₄, E₆, Δ⁻¹` (~65 lines, B has just `CΔ` and `Cψ`)
- A must pick `A = max(1, AΔ, A2, A4, A6)` with four `le_trans` chains (~30 lines)

**The rest of the difference (~90 lines) is pure boilerplate** that R1+R3 eliminate.
A's small-t branch also has 8 more lines than B's for identical measurability
plumbing — again pure R3 territory.

### Diff pair 2: A's tail deformation vs B's rectangle-Cauchy application

A's tail-deformation: `TailDeformation.lean:448-708` (261 lines total)

- 3 `Iⱼ'_eq_deform_imag_axis` for `j ∈ {2,4,6}` (TailDef:448-649 = 202 lines)
- 1 combined `I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail` (TailDef:654-708 = 55 lines)

B's rectangle-Cauchy application: `LaplaceRep:310-421` (112 lines)

- 2 `hRectLeft`/`hRectRight` applications, ~55 lines each

Each A `Iⱼ'_eq_deform_imag_axis` is structurally the same as B's `hRectLeft`/
`hRectRight`, modulo (i) using `Φⱼ'` instead of `bContourIntegrandT`, (ii)
no bContourIntegrand-based `ψT'_{*}_add_I_mul` shifts (instead uses
`Φ₁'_shift_left`/`Φ₃'_shift_right`), (iii) no `htendstoT` (instead inlines
`tendsto_intervalIntegral_Φⱼ'_top`).

With R1 (shared weight) and R2 (shared rect-deform driver), each of A's 3 +
B's 2 = 5 invocations becomes ~15-line specializations instead of ~55. **Net
savings: 200 lines across A and B.**

### Diff pair 3: A's `exists_phi2'_phi4'_bound_exp` vs B's `exists_ψI_bound_exp`

A's proof (StripBounds:46-144, 99 lines) establishes exp bounds for
`φ₂', φ₄'`, which are `E₄(E₂E₄-E₆)/Δ` and `E₄²/Δ`. The argument:

1. Get `IsBoundedAtImInfty` for `E₂, E₄, E₆` (via
   `exists_bound_of_isBoundedAtImInfty` helper, 8 lines).
2. Get exponential bound for `Δ⁻¹` via `exists_inv_Delta_bound_exp`.
3. Take `max` of thresholds (15 lines of `le_max` chains).
4. Assemble both `‖φ₂'‖`, `‖φ₄'‖` bounds with `norm_mul_le`, `gcongr` (70 lines).

B's proof (Basic.lean:72-145, 74 lines) does exp bound for `ψI`, which is
`num/Δ` with `num` tending to 1 at `i∞`. Structure:

1. `Tendsto num atImInfty (𝓝 1)` computation (~40 lines via H₂, H₄).
2. Uniform `‖num z‖ ≤ 2` from eventual neighbourhood (~15 lines).
3. Combine with `Δ⁻¹` bound (~20 lines).

The *shape* is different (A has 3 input bounds and forms a max of thresholds;
B has one limit computation and takes ball neighborhood). But the `Δ⁻¹`
combination pattern (steps 3-4 in A, step 3 in B) is identical (~25 lines
each). A helper `combine_with_inv_Delta_bound (hf : ‖f z‖ ≤ Cf) (hΔ : ‖(Δz)⁻¹‖ ≤ CΔ·exp)
: ‖f z·(Δz)⁻¹‖ ≤ …` saves ~15 lines.

**This diff pair shows the hard limit on unification**: the outer *shape* of
the modular-form bound genuinely differs between A and B because of what
ingredients go into `ψI` vs `φⱼ'`. A can save within-A by unifying its
three `φ₂',φ₄',φ₀` bounds but the A-vs-B unification is shallow.


## Final takeaway for the user

- **Bulk target**: the combined LaplaceA/LaplaceB directory can credibly shrink
  from 3759 to **~2700-2900 lines** (saving 800-1100) without changing any
  mathematics, via R1+R2+R3+R5 (weight abstraction, rect-deform driver,
  integrability helpers, parametrisation helper).
- **The big win** is R2 (rectangle-deformation driver) and R4 (modular-bound
  unification) — each worth ~200 lines, but R4 is the riskiest.
- **Quick wins (days of work, trivial risk)**: R1 + R3 + R5 ≈ 400 lines, no
  downstream caller breakage.
- **Phase 6 ended too early**: only 3 small commits with ~25 net line savings.
  The major structural refactors were not attempted. The current branch
  (`gauss2-cleanup`) is a good moment to do them.
- **Architectural recommendation**: split `LaplaceB/LaplaceRepresentation.lean`
  (918) to mirror A's 3-file structure. This is a prerequisite for most
  R* refactors because without it, shared lemmas can't be called from both
  sides in the same "phase" of the argument.
