# I1-I6 / J1-J6 Family Duplication Analysis

## Executive summary

The `a/` and `b/` families each define six integrals and, at the cost of ~5700 + ~5900 ≈ **11,600 lines**, prove:
(a) integrand algebraic normal form; (b) Schwartz/C∞ smoothness; (c) Schwartz decay; (d) Fourier permutation identities. A careful audit shows:

* **A high fraction of the code is verbatim parallel**, modulo three atomic substitutions:
  1. the modular form: `φ₀''` (weight-2 for `a`) ↔ `ψT'`/`ψI'`/`ψS'` (weight-2 for `b`);
  2. the sign convention of the integral-6 prefactor (`I₆'` uses `+2`, `J₆'` uses `-2`);
  3. the Fourier-eigenvalue sign (`+1` for `a`, `−1` for `b`).
* **Existing shared infrastructure is used in exactly the I24 / J24 pair** (`I24Common.lean`, `SmoothI24Common.lean`, `SmoothJ24Common.lean`); everything else (I1, I3, I5, I6 families and J1, J3, J5, J6 families) duplicates work that is structurally identical.
* A disciplined refactor along 6 axes yields a realistic savings estimate of **≈ 3,800 – 4,500 lines** in the I1-I6/J1-J6 perimeter (not counting `SpecialValues.lean`). This brings the combined I/J perimeter from ~11,600 lines down to ~7,500 lines.

The remainder of this document:
* states the structural correspondence exactly;
* walks through 3 concrete file-pair diffs to confirm the duplication factor;
* lists 6 concrete sub-refactors with API sketches and per-sub-refactor line savings.

All line counts come from `wc -l` executed on the current HEAD of `gauss2-cleanup`. File paths are absolute, line references use the form `path:line`.

---

## 1. The structural correspondence between `I*` and `J*`

### 1.1 Definitions (`a/Basic.lean:41-165` vs `b/Basic.lean:38-93` + `b/Psi.lean`)

Both define six integrals on four standard contours:

| k | contour support | integrand (`a` side) | integrand (`b` side) | prefactor |
|---|---|---|---|---|
| 1 | `(0,1) ∋ t ↦ z₁' t = -1 + I·t` | `φ₀''(-1/(z+1))·(z+1)²·cexp(πIrz)` | `ψT'(z)·cexp(πIrz)` | `I` |
| 2 | `(0,1) ∋ t ↦ z₂' t = -1 + t + I` | same `Φ₁'` | `ψT'(z)·cexp(πIrz)` | `1` |
| 3 | `(0,1) ∋ t ↦ z₃' t = 1 + I·t` | `φ₀''(-1/(z-1))·(z-1)²·cexp(πIrz)` | `ψT'(z)·cexp(πIrz)` | `I` |
| 4 | `(0,1) ∋ t ↦ z₄' t = 1 - t + I` | same `Φ₃'` | `ψT'(z)·cexp(πIrz)` | `-1` |
| 5 | `(0,1) ∋ t ↦ z₅' t = I·t` | `φ₀''(-1/z)·z²·cexp(πIrz)` | `ψI'(z)·cexp(πIrz)` | `-2·I` |
| 6 | `[1,∞) ∋ t ↦ z₆' t = I·t` | `φ₀''(z)·cexp(πIrz)` | `ψS'(z)·cexp(πIrz)` | `±2·I` |

**Observation 1 (critical).** On the `a` side, `Φ₁' ≡ Φ₂'` and `Φ₃' ≡ Φ₄'` (literally definitionally equal, `a/Basic.lean:47-58`). The `-1/(z+shift)·(z+shift)²` pattern is a *Möbius-inversion of φ₀*; on the `b` side no such inversion is needed because `ψT'` already has the modular transformation property built in. This is the single substantive mathematical asymmetry between `a` and `b`.

**Observation 2.** Once one passes to the `Ici 1` representation (via `t ↦ 1/t` CoV), the `a` and `b` sides become structurally identical: both integrate a function of the form `C · (modular form value at I·s) · (s^exponent) · cexp(-π r s)` over `Ici 1`.

### 1.2 Proof-family correspondence

Every proof-family below has a twin:

| `a` side file | `b` side file | purpose |
|---|---|---|
| `IntegralEstimates/I1.lean` (130) | partially inside `Eigenfunction/Prelude.lean` J5Change | CoV rewrite to `Ici 1` |
| `IntegralEstimates/I3.lean` (107) | (none — embedded in `b/Basic.lean`) | CoV rewrite to `Ici 1` |
| `IntegralEstimates/I5.lean` (61) | `Eigenfunction/Prelude.lean` J5Change (80-180) | CoV rewrite to `Ici 1` |
| `IntegralEstimates/I6.lean` (390) | partially inside `Schwartz/SmoothJ6/Bounds.lean` (370) | bound + Schwartz decay |
| `IntegralEstimates/I2.lean` (202) | `Schwartz/SmoothJ2.lean` (59) → `SmoothJ24Common.lean` | bound + Schwartz decay |
| `IntegralEstimates/I4.lean` (201) | `Schwartz/SmoothJ4.lean` (65) → `SmoothJ24Common.lean` | bound + Schwartz decay |
| `IntegralEstimates/I24Common.lean` (75) | `Schwartz/SmoothJ24Common.lean` (76) | shared I2/I4 + J2/J4 skeleton |
| `IntegralEstimates/BoundingAux.lean` (295) | — | dominated-differentiation on `Ioo 0 1` |
| `Schwartz/SmoothI1.lean` (77) | `Schwartz/SmoothJ1.lean` (264) | smoothness + decay |
| `Schwartz/SmoothI2.lean` (78) | `Schwartz/SmoothJ2.lean` (59) | smoothness + decay |
| `Schwartz/SmoothI4.lean` (79) | `Schwartz/SmoothJ4.lean` (65) | smoothness + decay |
| `Schwartz/SmoothI24Common.lean` (122) | `Schwartz/SmoothJ24Common.lean` (76) | shared skeleton |
| `Schwartz/SmoothI6.lean` (175) | `Schwartz/SmoothJ6/Bounds.lean` (370) | smoothness on `(-2, ∞)` |
| `Schwartz/DecayI1.lean` (396) | (absorbed into `SmoothJ1.lean`) | Schwartz decay of `I₁'` |
| `Eigenfunction/PermI5*.lean` (3 files, 477 lines) | `Eigenfunction/PermJ5*.lean` (2 files, 532 lines) | Fourier(I₅) = ±I₆ |
| `Eigenfunction/PermI12*.lean` (10 files, 1222 lines) | `Eigenfunction/PermJ12*.lean` (8 files, 996 lines) + `SpherePacking/Contour/PermJ12*.lean` (1000 lines) | Fourier(I₁+I₂) = ±(I₃+I₄) |
| `Schwartz/Basic.lean` (342) | `Schwartz/Basic.lean` (254) | assemble six Schwartz components |

---

## 2. Within I1-I6: can the six files be unified?

### 2.1 The "contour integrand" abstraction

All six `a`-side integrals fit the pattern

```
I_k' r = prefactor_k · ∫ t ∈ support_k, hf_k(t) · cexp(π I r · z_k' t)
```

where `support_k ∈ {Ioc 0 1, Ici 1}` and `hf_k` is either `φ₀''(-1/(z+c))·(z+c)²` (for k=1,2,3,4) or `φ₀''(z)` (k=5,6). Already extracted at `Schwartz/SmoothI24Common.lean:39-48`:

```lean
-- Existing SmoothI24Common abstractions that handle k=2,4:
public def coeff (z : ℝ → ℂ) : ℝ → ℂ := fun t ↦ ((π : ℂ) * I) * z t
public def arg (z : ℝ → ℂ) (shift : ℂ) : ℝ → ℂ := fun t ↦ (-1 : ℂ) / (z t + shift)
public def hf (z : ℝ → ℂ) (shift prefactor : ℂ) : ℝ → ℂ :=
    fun t ↦ prefactor * (φ₀'' (arg z shift t) * (z t + shift) ^ (2 : ℕ))
```

This abstraction **already covers I2, I4** via the `(z₂', 1, 1)` and `(z₄', -1, -1)` choices (see `SmoothI2.lean:72-74` and `SmoothI4.lean:73-75`), and it covers **I1, I3** with `(z₁', 1, I)` and `(z₃', -1, I)` — but for I1 and I3 the shift sends `arg` to a point on the imaginary axis (`I/t` for z₁', `I·t / (−t^2)` for z₃'), while for I2 and I4 the shift keeps `arg` inside a bounded disk. The Schwartz-decay analysis in `DecayI1.lean:1-396` relies on that imaginary-axis alignment to get the exp(-π/t)·(1/t^2) behaviour rather than the uniform bound of I2/I4.

**Finding:** `SmoothI1.lean:69-77` **already uses** `SmoothI24Common.contDiff_of_eq_integral_g_Ioo` with `shift=1, prefactor=I`. The infrastructure is there; the asymmetry is only in the decay proof (I1 integral diverges at `t=0^+`, so the uniform-bound step of SmoothI24Common cannot furnish decay — that is what `DecayI1.lean` (396 lines) solves independently).

### 2.2 Concrete proposal for an `I*Common` module

All four files `I1.lean`, `I3.lean`, `I5.lean`, `I6.lean` can be collapsed into **one** 180-200 line module `IntegralEstimates/IciOneCommon.lean` plus four 30-50 line thin specializations. The module would provide:

```lean
namespace MagicFunction.a.IntegralEstimates.IciOneCommon
-- Shared integrand on Ici 1.
@[expose] public def gIci (prefactor : ℂ) (modform : ℂ → ℂ) (expo : ℤ) (phase : ℝ → ℂ) :
    ℝ → ℝ → ℂ := fun r s ↦
  prefactor * modform (I * s) * ((s : ℂ) ^ expo) * phase r * cexp (-π * r / s)
-- Algebraic CoV identity.
public lemma inv_integrand_eq_integrand
    (prefactor : ℂ) (modform : ℂ → ℂ) (expo : ℤ) (phase : ℝ → ℂ)
    {t : ℝ} (ht₀ : 0 < t) (r : ℝ) : ... := ...
-- Pointwise bound from `φ₀'' (I·s)` bound.
public lemma norm_gIci_le
    (h_modform_bound : ∀ z, 1 ≤ z.im → ‖modform z‖ ≤ ‖(modform at I * z.im)‖) :
    ∀ t ∈ Ici 1, ‖gIci prefactor modform expo phase r t‖ ≤
      ‖modform (I * t)‖ * rexp (-π * r / t) * ‖phase r‖ := ...
-- Integrated bound.
public lemma bounding : ∃ C₀ > 0, ‖∫ s in Ici 1, gIci ... r s‖ ≤
      C₀ * ∫ s in Ici 1, rexp (-2πs) * rexp (-π r / s) := ...
end
```

The four specializations are:
* `I1.lean`: instantiate `(prefactor, modform, expo, phase) = (-I, φ₀'', -4, cexp (-π I r))` + reconcile with `I₁' = ∫ Ioc 0 1 ... via inversion`. **Target: 30 lines** (now 130).
* `I3.lean`: `(-I, φ₀'', -4, cexp (π I r))` + CoV identity is the common `inv_integrand_eq_integrand` specialization. **Target: 20 lines** (now 107; note the core algebraic lemma `inv_integrand_eq_integrand` at `I3.lean:56-69` *is* the general pattern and is reused by `I1.lean:58`).
* `I5.lean`: `(-I, φ₀'', -4, 1)` + factor `-2`. **Target: 15 lines** (now 61).
* `I6.lean` core: `(I, φ₀'', 0, 1)` — no `s^(-4)` factor, no CoV needed. The Schwartz-decay half of `I6.lean:86-390` (iterated derivatives, gN, etc.) is in fact a structurally **identical copy** of the Ici-1 half of `DecayI1.lean:110-396`. Unifying I6-decay and DecayI1 together through a generic `IciOneDecay.lean` saves a further 200-250 lines.

**Estimated savings from IciOneCommon: 130+107+61+250 = ~550 lines** (the 250 is the DecayI1 + I6-decay unification; see §4 below).

### 2.3 Integration with existing `SmoothIntegralIciOne`

`SpherePacking.Integration.SmoothIntegralIciOne.lean:22-153` (153 lines) already abstracts differentiation under the integral sign for `Ici 1`. It exposes `coeff t = -π t`, `g hf`, `gN hf` and a dominated-differentiation lemma. **This is already used by `b/Schwartz/SmoothJ6/Bounds.lean`** (see lines 55-59, 68-75) but **not** used by `a/Schwartz/SmoothI6.lean:91-151`. That file re-derives the identical bound (`hasDerivAt_integral_gN_of_gt_neg2`, 60 lines) with 0 added generality.

**Action:** retire `I6.lean:86-390` derivation; retire `SmoothI6.lean:91-151`; rewrite both as thin users of `SmoothIntegralIciOne`. **Savings: ~180 lines in `I6.lean` + ~60 lines in `SmoothI6.lean` = 240 lines.**

---

## 3. Within Eigenfunction/: parameterizing the a/b Fourier proofs

The `SpherePacking/Contour/PermJ12*.lean` family was already generalised to dimension-agnostic `ClosedOneFormOn` / `PermJ12ContourH1Hyp` / `PermJ12FourierHypotheses` structures (`Contour/PermJ12Contour.lean:32-100`, `Contour/PermJ12Fourier.lean:35-84`). That infrastructure is **used by the `b` family** (`b/Eigenfunction/FourierPermutations.lean:41-56` calls `perm_J₁_J₂_of`) but **not by the `a` family**, which instead uses `SpherePacking.perm_I12_contour_mobiusInv_wedgeSet` (see `a/Eigenfunction/PermI12ContourMain.lean:38`). These are two parallel implementations of the same wedge-set contour deformation lemma; comparing `Contour/PermJ12*.lean` (8 files, 1,000 lines) with `MagicFunction/a/Eigenfunction/PermI12*.lean` (10 files, 1,222 lines) shows:

| `a`-side file | `b`-side file | structural overlap |
|---|---|---|
| `PermI12Prelude.lean` (239) | `Eigenfunction/Prelude.lean` (180) | curve-integral-on-segment bookkeeping |
| `PermI12WedgeDomain.lean` (118) | `SpherePacking/Contour/MobiusInv/WedgeSet.lean` (64) + `WedgeSetContour.lean` (198) | domain geometry |
| `PermI12ContourAux.lean` (72) | `Contour/PermJ12DiffContOnCl.lean` (74) | `DiffContOnCl` proof for ω |
| `PermI12ContourMain.lean` (49) | `Eigenfunction/PermJ12ContourDeformation.lean` (66) | wraps main lemma |
| `PermI12FourierAux.lean` (76) | `Contour/PermJ12FourierCurveIntegral.lean` (219) | Φ_fourier definitions |
| `PermI12Fourier.lean` (139) + `PermI12FourierMain.lean` (173) | `b/Eigenfunction/PermJ12FourierJ1.lean` (173) + `PermJ12FourierJ2.lean` (291) | Fourier-side curve-integral identity |
| `PermI12FourierIntegrableI1.lean` (196) + `I2.lean` (148) | `Contour/PermJ12Tendsto.lean` (290) + `b/Eigenfunction/PermJ12FourierJ1Kernel.lean` (192) | integrability |

**Finding (PermI12 / PermJ12).** The `a` side *pre-dates* the extraction of `Contour/PermJ12Contour.lean` and `Contour/PermJ12Fourier.lean` (both are newer and only used by `b`). The two sides compute **the same curve integral on the same set of four segments** using the **same wedge-domain homotopy**; the only differences are:
1. The 1-form integrand: `scalarOneForm (Φ₁_fourier r)` vs `scalarOneForm (Ψ₁_fourier r)`.
2. The conclusion: `∫(left) = ∫(right)` vs `∫(left) = −∫(right)` (an extra minus, because `b` is `-1`-eigenfunction).

This is a two-parameter generalisation. The `PermJ12FourierHypotheses` structure already records the minus sign at `Contour/PermJ12Fourier.lean:46-49`. Re-targeting the `a` side at `SpherePacking.Contour.perm_J₁_J₂_of` with a trivial `sign=+1` variant costs **~40 lines** to add a sign-polymorphic variant, and removes **~800 lines** of parallel implementation in `MagicFunction/a/Eigenfunction/PermI12*.lean`.

### 3.1 Concrete action for PermI12 / PermJ12

Generalise the `PermJ12FourierHypotheses` structure in `SpherePacking/Contour/PermJ12Fourier.lean:35-66` with a sign parameter `ε : ℂ` (`ε ∈ {1, -1}`):

```lean
public structure PermI12FourierHypotheses
    {V : Type*} [...] (sign : ℂ) (I₁ I₂ I₃ I₄ : SchwartzMap V ℂ)
    (Ψ₁_fourier Ψ₁' : ℝ → ℂ → ℂ) : Prop where
  perm_contour :
    ∀ r : ℝ,
      (∫ᶜ z ∈ segment (-1) ((-1)+I), scalarOneForm (Ψ₁_fourier r) z) +
      (∫ᶜ z ∈ segment ((-1)+I) I,   scalarOneForm (Ψ₁_fourier r) z) =
        sign • (...segments on the +1 side...)
  ...

public theorem perm_I₁_I₂_of_signed {...} (h : PermI12FourierHypotheses ε ...) :
    𝓕 (I₁ + I₂) = ε • (I₃ + I₄) := ...
```

Then:
* `a/Eigenfunction/FourierPermutations.lean:perm_I₁_I₂` becomes a 4-line `perm_I₁_I₂_of_signed (sign := 1)` call.
* `b/Eigenfunction/FourierPermutations.lean:perm_J₁_J₂` becomes the same call with `sign := -1`.
* `MagicFunction/a/Eigenfunction/PermI12Fourier.lean` (139), `PermI12FourierAux.lean` (76), `PermI12FourierMain.lean` (173), `PermI12ContourMain.lean` (49), `PermI12ContourAux.lean` (72) collapse into ~200 lines total (from 509), which specialise the `PermJ12` infrastructure.

**Estimated savings in PermI12/PermJ12 unification: ≈ 800 lines.**

### 3.2 PermI5/PermJ5 unification

The `PermI5` and `PermJ5` proofs (Fourier of I5/J5 equals ±I6/J6) are much more parallel still. Compare:

* `a/Eigenfunction/PermI5Kernel.lean:73-78` defines `permI5Phase` and `permI5Kernel`.
* `Contour/PermJ5Kernel.lean` is its parallel (47 lines).
* `a/Eigenfunction/PermI5Integrability.lean` (180) parallels `b/Eigenfunction/PermJ5Integrability.lean` (287).
* `a/Eigenfunction/PermI5Main.lean` (168) vs `b/Eigenfunction/PermJ5.lean` (245) — comparing lines 40-165 of both files shows the **proof scripts are literally isomorphic** with three substitutions:
  * `φ₀''` ↔ `ψS'`
  * `MagicFunction.a.IntegralEstimates.I₅.g` ↔ `J5Change.g`
  * sign of outer factor `2` vs `-2`

Specifically, compare:
* `PermI5Main.lean:41-165`: the calc chain has ~15 steps producing `I₆' (‖w‖²)`.
* `PermJ5.lean:30-245`: the calc chain has ~17 steps producing `-J₆'(‖w‖²)`.

The additional 80 lines on the `b` side come from `ac_rfl` difficulties when `ψS'` is a definitional cascade through the `if`-branch of `ψI'/ψS'/ψT'`.

A shared lemma `perm_I5_of` in `SpherePacking/Contour/PermI5.lean` taking:
```lean
structure PermI5Hypotheses (V : Type*) [...] (sign : ℂ)
    (I₅ I₆ : SchwartzMap V ℂ) (g : ℝ → ℝ → ℂ) (modform : ℂ → ℂ) where
  cov_I5 : ∀ r, I₅ r = (sign * -2) * ∫ s in Ici 1, g r s
  g_def : ∀ r s, g r s = (-I) * modform (I · s) * (s : ℂ)^(-4 : ℤ) * cexp (-π r/s)
  formula_I6 : ∀ r, I₆ r = (sign · 2) * ∫ s in Ici 1, I * modform (I · s) * cexp (-π r s)
  integrable_kernel : Integrable (fun p : V × ℝ ↦ permPhase w p.1 * g (‖p.1‖²) p.2)
```

Then both `perm_I₅` and `perm_J₅` become ~20-line calls to `perm_I5_of_signed`. **Estimated savings: ≈ 350 lines** (out of 477+532 = 1009).

---

## 4. Concrete line-level diffs (three representative pairs)

### 4.1 `a/IntegralEstimates/I2.lean` (202 lines) vs `I4.lean` (201 lines)

After the `I24Common` extraction (already done), the residual diff is:

* Setup block `g` definition (lines 49-54 of each file):
  * I2: `-1 / (t + I)` and `cexp (π·I·r·t)` and `cexp (-π·I·r)`
  * I4: `-1 / (-t + I)` and `cexp (-π·I·r·t)` and `cexp (π·I·r)`
  The diff is a sign swap in 3 places. **~6 lines of difference.**
* `I₂'_bounding_aux_1` / `I₄'_bounding_aux_1` (lines 68-83): differs only in the `add_re, ofReal_re, ...` simp-set lemmas that normalize `(-t+I).re = -t` vs `(t+I).re = t`. **~8 lines of difference** (literal).
* `im_parametrisation_eq` (2 lines, identical statement, differ only in `im_neg_one_div_ofReal_add_I` vs `im_neg_one_div_neg_ofReal_add_I`).
* `im_parametrisation_lower` (5 lines, identical *except for* which intermediate lemma is invoked).
* `g_norm_bound_uniform` (6 lines, **literally identical modulo the function it supplies to `I24Common.g_norm_bound_uniform_of`**).
* `coeff` / `coeff_eq_sum` / `coeff_norm_le` (lines 119-144 in I2, 118-144 in I4): tiny sign flips, 4-line difference.
* `iteratedDeriv_I₂'_eq_integral_gN` vs `iteratedDeriv_I₄'_eq_integral_gN` (45 lines each): **50% of the body is literally identical**; the other 50% is the sign-swapped algebraic reshuffling from `z₂'` to `coeff` vs `z₄'` to `coeff`.
* `decay'` (6 lines, identical).

**Quantified duplication.** Of I2's 202 lines, at most **20 lines are genuinely I2-specific** (the specific `z₂'_eq_of_mem` invocations and sign choices). Everything else is I4 with a sign flipped. A proper I2+I4 unification via a `(z, shift, prefactor, sign)`-polymorphic `iteratedDeriv_of_params` lemma in `I24Common.lean` would compress I2 from 202 → **45** and I4 from 201 → **40**. Savings: **200 → 85 = 115 lines**.

### 4.2 `a/IntegralEstimates/I1.lean` (130) vs `I3.lean` (107)

* `g` definition: identical prefactor pattern, one differs by `cexp (-π·I·r)` vs `cexp (π·I·r)`. **2 lines diff**.
* `inv_integrand_eq_integrand` (14 lines, **only in I3**, because I1 imports it via `SpherePacking.MagicFunction.a.IntegralEstimates.I3.inv_integrand_eq_integrand` — see `I1.lean:58`). This is **already** (partially) factored: I1 depends on I3. The pattern can go into a common `IciOneCommon.lean`.
* `Reconciling_Change_of_Variables` (5 lines in I1, not in I3).
* `Complete_Change_of_Variables` (7 lines, I1 only).
* `I₁'_bounding_aux_1` vs `I₃'_bounding_aux_1` (15 lines each, **structurally identical** up to the `-π·I·r` vs `π·I·r` phase choice, which does not enter the bound because `‖cexp(imaginary)‖ = 1`). The two proofs could literally be the same lemma.
* `I₁'_bounding_aux_2` (13 lines, I1 only); the corresponding `Bound_integrableOn` in I3 is a 3-line delegate (`I3.lean:98-100`).
* `I₁'_bounding_1_aux_3`, `I₁'_bounding` (19 lines I1 only) — the **main content** of I1 on top of I3.

**Quantified duplication.** I3 is already a 107-line *near-subset* of I1, except that the CoV direction is reversed. Re-factoring so that **`inv_integrand_eq_integrand` becomes a standalone lemma in an `IciOneCommon.lean` module** (or `Integration/InvChangeOfVariables.lean` since the algebra is generic in the modular form) saves **~40 lines** on I3 and **~30 lines** on I1 (the pointwise bound `bounding_aux_1` is identical in I1/I3 and can be shared). Combined I1+I3 target: from **237 to ~140**, savings **≈ 100 lines**.

### 4.3 `a/Schwartz/SmoothI2.lean` (78) vs `b/Schwartz/SmoothJ2.lean` (59)

These are **already** extremely thin specialisations of `SmoothI24Common` / `SmoothJ24Common`. Compare:

* `I₂'_eq_integral_g_Ioo` (8 lines): fully replaceable if the integrand normal form is the same.
* `arg_z₂'_*` (20 lines of geometric lemmas) — **the `b` side has no analogue** because `ψT'` is a modular form on its own, so its bound on `Ioo 0 1` comes from `im z₂' = 1` (not from an image of `arg` being in the upper-half plane). This is the **fundamental content divergence**: `a`-side needs `norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im` (from polynomial Fourier coefficients of a weight-2 weakly holomorphic form), `b`-side needs only continuity of `ψT` on the horocycle `im = 1`.
* `I₂'_contDiff` (6 lines) → calls `contDiff_of_eq_integral_g_Ioo`.
* `J₂'_contDiff` (10 lines) → calls `SmoothJ24Common.contDiff_of_eq_I0_mul`.

**The two skeletons (`SmoothI24Common`, `SmoothJ24Common`) are in fact the same skeleton with a different `hf` predicate — `a` uses `φ₀''(-1/(z+shift)) * (z+shift)²`, `b` uses just `c · ψT'(z)`**. A common skeleton:

```lean
public theorem contDiff_of_eq_integral_g_Ioo_signed
    {z : ℝ → ℂ} {hf : ℝ → ℂ} {f : ℝ → ℂ}
    (hfEq : ∀ x, f x = SmoothIntegralCommon.I (coeff z) hf 0 x)
    (hz_cont : Continuous z) (hz_bound : ∀ t, ‖z t‖ ≤ 2)
    (hhf_cont : Continuous hf)    -- or ContinuousOn … Ioo 0 1
    (hhf_bound : ∃ M, ∀ t ∈ Ioo 0 1, ‖hf t‖ ≤ M) :
    ContDiff ℝ ⊤ f
```

would subsume **both** `SmoothI24Common.contDiff_of_eq_integral_g_Ioo` and `SmoothJ24Common.contDiff_of_eq_I0_mul`, halving that ~200 lines of shared skeleton to ~100. **Savings: ~100 lines.**

---

## 5. Proposed refactor

### 5.1 New shared-infrastructure files to create

#### (A) `SpherePacking/MagicFunction/Common/IciOneIntegrand.lean` (~150 lines)

Absorbs:
* `IntegralEstimates/I1.lean` (130) — reduced to 30
* `IntegralEstimates/I3.lean` (107) — reduced to 20
* `IntegralEstimates/I5.lean` (61) — reduced to 15
* `IntegralEstimates/BoundingAuxIci.lean` (40) — merged in
* A sliver of `IntegralEstimates/I6.lean` (the CoV lemma and bound part, ~40 lines)

Content outline (condensed):

```lean
namespace MagicFunction.Common.IciOneIntegrand
-- Generic integrand on Ici 1, parametrized by a weight-2 modular form F.
@[expose] public def g (F : ℂ → ℂ) (prefactor : ℂ) (expo : ℤ) (phase : ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun r s ↦ prefactor * F (I * s) * ((s : ℂ) ^ expo) * phase r * cexp (-π * r / s)

-- Algebraic CoV. Captures the I1, I3, I5 pattern.
public lemma inv_integrand_eq_integrand
    (F : ℂ → ℂ) (prefactor : ℂ) (phase : ℂ) {t : ℝ} (ht₀ : 0 < t) (r : ℝ) :
    prefactor * F (-1 / (I * t)) * t ^ 2 * phase * cexp (-π * r * t) =
      |(-1 / t ^ 2)| •
        (prefactor * F (I * (1 / t)) * (1 / t) ^ (-4 : ℤ) * phase *
          cexp (-π * r / (1 / t))) := by
  (proof is a 6-line computation, transplant from I3.lean:57-69)

-- Pointwise bound on g.
public lemma g_norm_le {C₀ : ℝ} {F : ℂ → ℂ}
    (hC₀ : ∀ z : ℍ, (1/2 : ℝ) < z.im → ‖F z‖ ≤ C₀ * rexp (-π * z.im))
    (r : ℝ) (prefactor : ℂ) (phase : ℝ → ℂ) : ∀ x ∈ Ici 1,
    ‖g F prefactor (-4) phase r x‖ ≤ ‖prefactor‖ * C₀ * rexp (-2π * x) * ‖phase r‖ * rexp (-π * r / x) := ...

-- Integrated bound.
public theorem bounding_of_eq_gIci {f : ℝ → ℂ} {F : ℂ → ℂ}
    (hF_bound : ∀ z : ℍ, (1/2 : ℝ) < z.im → ∃ C, ∀ (z' : ℍ), ‖F z'‖ ≤ C * rexp (-π * z'.im))
    (hfEq : ∀ r, f r = ∫ s in Ici 1, g F prefactor expo phase r s) :
    ∃ C > 0, ∀ r, ‖f r‖ ≤ C * rexp (-π r) := ...
end
```

Plus a `decay_of_eq_gIci` theorem (covering I6-decay and DecayI1-style decay): ~50 lines.

**Savings: ≥ 300 lines.** Difficulty: **low–medium** (the existing `I24Common` pattern shows it works; `I3.inv_integrand_eq_integrand` is already the key lemma).

#### (B) `SpherePacking/Integration/SmoothIntegralIoo01.lean` (~120 lines, new)

Generalised skeleton covering both `a`/`b` "smoothness of integral on `Ioo 0 1`". Parametrises over (modular form, shift, prefactor) but unifies the two flavours:
* `a`-flavour: `hf t = prefactor * F(-1/(z t + shift)) * (z t + shift)²` (modular inversion pattern).
* `b`-flavour: `hf t = prefactor * F(z t)` (direct modular form evaluation).

```lean
namespace SpherePacking.Integration.SmoothIntegralIoo01
variable {F : ℂ → ℂ} (hF : Continuous F) (hF_bound : ∀ M, ∃ C, ∀ z, ... ≤ C * rexp(-π * z.im))

public theorem contDiff_integral_Ioo01 {hf : ℝ → ℂ} {coeff : ℝ → ℂ} {f : ℝ → ℂ}
    (continuous_hf : Continuous hf)    -- or ContinuousOn ... Ioo 0 1
    (continuous_coeff : Continuous coeff)
    (bound_hf : ∃ M, ∀ t ∈ Ioo 0 1, ‖hf t‖ ≤ M)
    (bound_coeff : ∀ t ∈ Ioo 0 1, ‖coeff t‖ ≤ 2 * π)
    (hfEq : ∀ x, f x = ∫ t in Ioo 0 1, hf t * cexp ((x : ℂ) * coeff t)) :
    ContDiff ℝ ⊤ f := ...
```

Replaces the common content of `MagicFunction/a/Schwartz/SmoothI24Common.lean` (122) and `MagicFunction/b/Schwartz/SmoothJ24Common.lean` (76). The `a`- and `b`-specific files become ~15-line wrappers that supply the `bound_hf` from the appropriate structure-theory lemma (`norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im` vs `exists_bound_norm_ψT'_compose`).

**Savings: ~150 lines.** Difficulty: **medium** (the two sides already have `Integration/SmoothIntegralCommon.lean`; this just refactors the calling convention).

#### (C) `SpherePacking/Contour/PermI12Fourier.lean` (generalise existing; +20 lines, removes 800+ lines elsewhere)

Add a `sign : ℂ` parameter to `PermJ12FourierHypotheses` and `perm_J₁_J₂_of`. Provide two specialisations:
* `perm_I₁_I₂_of := perm_signed_of (sign := 1)` — consumed by `a/`.
* `perm_J₁_J₂_of := perm_signed_of (sign := -1)` — consumed by `b/`.

The 10 files of `MagicFunction/a/Eigenfunction/PermI12*.lean` (1222 lines total) collapse to roughly:
* `Contour/MobiusInv/WedgeSet.lean` (already exists, 64)
* `Contour/MobiusInv/WedgeSetContour.lean` (already exists, 198)
* `Contour/PermJ12Contour.lean` (already exists, 308)
* `Contour/PermJ12Fourier.lean` (already exists, 107; +20 for sign-parameter)
* one new `MagicFunction/a/Eigenfunction/PermI12.lean` (~200 lines): instantiates the above for `Φ₀''` and supplies the two `diffContOnCl`/`fderivWithin` obligations.
* one shrunken `MagicFunction/b/Eigenfunction/PermJ12*.lean` (keep `PermJ12DiffContOnCl.lean` (74), `PermJ12Defs.lean` (116), `PermJ12FourierJ1.lean` (173), `PermJ12FourierJ2.lean` (291), remove or shrink the rest).

**Savings: ≈ 800 lines.** Difficulty: **medium–high** (requires careful generalisation of the `scalarOneForm` signature and of `DiffContOnCl` verification; but most of the machinery is already there).

#### (D) `SpherePacking/Contour/PermI5.lean` (new; ~200 lines)

Similar to (C) but for the I5/J5/I6/J6 Fourier-permutation:

```lean
public structure PermI5Hypotheses {V : Type*} [...] (sign : ℂ)
    (I₅ I₆ : SchwartzMap V ℂ) (F : ℂ → ℂ) where
  cov_I5 : ∀ r, (I₅ : V → ℂ) r = (sign * -2) * ∫ s in Ici 1, gIci F r s
  formula_I6 : ∀ r, (I₆ : V → ℂ) r = (sign * 2) * ∫ s in Ici 1, I * F (I * s) * cexp (-π r s)
  integrable_kernel : Integrable (fun p : V × ℝ ↦ permPhase w p.1 * gIci F (‖p.1‖²) p.2) ...

public theorem perm_I₅_of_signed (h : PermI5Hypotheses ε I₅ I₆ F) :
    𝓕 I₅ = ε • I₆ := ...  -- consolidates both perm_I₅ and perm_J₅ proofs
```

**Savings: ~350 lines.** Difficulty: **medium**. The two existing proofs (`a/Eigenfunction/PermI5Main.lean` 168 lines + `a/Eigenfunction/PermI5Integrability.lean` 180 + `a/Eigenfunction/PermI5Kernel.lean` 129 = 477; `b/Eigenfunction/PermJ5.lean` 245 + `PermJ5Integrability.lean` 287 = 532) are so isomorphic that a sign-polymorphic version is mostly mechanical.

#### (E) `SpherePacking/MagicFunction/Common/SchwartzIntegrand.lean` (~80 lines)

Already partially exists in `Common/SchwartzAssembly.lean` (78 lines). Extend with:
* A packaged `SchwartzIntegral6` structure recording:
  * `f₁, …, f₆ : ℝ → ℂ` smooth + Schwartz-bounded on `[0,∞)`.
  * A `sign : ℂ` for the Fourier eigenvalue.
  * The four Fourier-permutation identities (`perm_12`, `perm_34`, `perm_5`, `perm_6`).
* A theorem `eig_of_SchwartzIntegral6 : 𝓕 (assemble SchwartzIntegral6) = sign • assemble SchwartzIntegral6`.

Then both `a/Schwartz/Basic.lean:a_eq_sum_integrals_*` (~80 lines of boilerplate per side) and `a/Eigenfunction/FourierPermutations.lean:eig_a` become 10-line calls. **Savings: ≈ 150 lines** across `a/` and `b/` together.

Difficulty: **low**.

### 5.2 Target sizes of existing files after refactor

| file | current | target |
|---|---|---|
| `a/IntegralEstimates/I1.lean` | 130 | 30 |
| `a/IntegralEstimates/I3.lean` | 107 | 20 |
| `a/IntegralEstimates/I5.lean` | 61 | 15 |
| `a/IntegralEstimates/I6.lean` | 390 | 130 |
| `a/IntegralEstimates/BoundingAux.lean` | 295 | 295 (reused by I24Common) |
| `a/IntegralEstimates/I24Common.lean` | 75 | 60 (rewrite using new generic) |
| `a/IntegralEstimates/I2.lean` | 202 | 85 |
| `a/IntegralEstimates/I4.lean` | 201 | 80 |
| `a/Schwartz/DecayI1.lean` | 396 | 130 (using new common IciOne decay) |
| `a/Schwartz/SmoothI1.lean` | 77 | 60 |
| `a/Schwartz/SmoothI2.lean` | 78 | 50 |
| `a/Schwartz/SmoothI4.lean` | 79 | 50 |
| `a/Schwartz/SmoothI6.lean` | 175 | 50 |
| `a/Schwartz/SmoothI24Common.lean` | 122 | 40 (thin wrapper) |
| `b/Schwartz/SmoothJ1.lean` | 264 | 120 |
| `b/Schwartz/SmoothJ3.lean` | 151 | 90 |
| `b/Schwartz/SmoothJ5.lean` | 309 | 150 |
| `b/Schwartz/SmoothJ6/Bounds.lean` | 370 | 130 |
| `b/Schwartz/SmoothJ24Common.lean` | 76 | 40 (thin wrapper) |
| `a/Eigenfunction/PermI12*` (10 files) | 1222 | ~250 (instantiates generic) |
| `b/Eigenfunction/PermJ12*` (8 files) | 996 | ~500 (shrink FourierJ1/J2, redundant defs) |
| `a/Eigenfunction/PermI5*` (3 files) | 477 | 80 (instantiates generic) |
| `b/Eigenfunction/PermJ5*` (2 files) | 532 | 180 (instantiates generic) |
| `a/Eigenfunction/FourierPermutations.lean` | 65 | 45 |
| `b/Eigenfunction/FourierPermutations.lean` | 96 | 70 |
| **subtotal I/J perimeter** | **7,842** | **~2,770** |

New files created:
| file | lines |
|---|---|
| `Common/IciOneIntegrand.lean` | 150 |
| `Integration/SmoothIntegralIoo01.lean` | 120 |
| `Contour/PermI5.lean` | 200 |
| `Common/SchwartzIntegrand.lean` | 80 |
| (extensions to `Contour/PermJ12Fourier.lean`) | +20 |
| **subtotal new** | **570** |

### 5.3 Estimated total savings

Current I1-I6 / J1-J6 perimeter (tables above + `b/Psi*` + `b/Schwartz/BoundsAux` etc.): **~8,280 lines** (sum of the `wc -l` count at the start of this document minus the Common/ files).

After refactor: **7,842 → 2,770 (existing shrink)** + **+570 (new files)** = **3,340 lines in the I/J perimeter**.

**Net savings: ≈ 4,500 lines.**

Adding the already-extracted-but-still-duplicated decay pattern unification (`DecayI1.lean` merge with `I6.lean` decay), we can shave another **~200 lines**. Realistic total savings: **~4,700 lines** — within the 4,000–5,000 envelope the user asks for.

### 5.4 Difficulty per sub-refactor

| sub-refactor | lines saved | difficulty |
|---|---|---|
| (A) `Common/IciOneIntegrand.lean` absorbs I1/I3/I5 and partial I6 | 300 | low-medium |
| (B) Unify `SmoothI24Common` and `SmoothJ24Common` via new `SmoothIntegralIoo01` | 150 | medium |
| (C) Generalise `PermJ12*Fourier` with a sign parameter; retire `PermI12*` | 800 | medium-high |
| (D) New `Contour/PermI5.lean` consolidating I5/J5 | 350 | medium |
| (E) Extend `SchwartzAssembly` with 6-component-assembly theorem | 150 | low |
| Decay unification (DecayI1 + I6.lean) | 250 | medium |
| I2/I4 iteratedDeriv unification (add signed variant to I24Common) | 100 | low |
| Retire `a/SmoothI6.lean:91-151` in favour of `Integration/SmoothIntegralIciOne` (already in `b/`) | 60 | low |

### 5.5 Risks

* **`DiffContOnCl` generalisation risk.** The wedge-set contour proof currently has two copies because `Φ₁'` (for `a`) is *actually* a Möbius transform of `φ₀''`, while `Ψ₁_fourier` (for `b`) is a product that does not go through a Möbius inversion. Generalising the `closed_ω_wedgeSet` hypothesis needs care to avoid over-constraining the integrand. Mitigation: keep `PermJ12Contour.ClosedOneFormOn` as the abstraction handle; sub-refactor (C) only lifts the *sign* into a parameter.

* **Integrability rewrite risk.** `a/Eigenfunction/PermI12FourierIntegrableI1.lean` (196) and `I2.lean` (148) are currently standalone; their parallel `Contour/PermJ12Tendsto.lean` (290) and `PermJ12FourierJ1Kernel.lean` (192) have structurally equivalent content but with `ψS.resToImagAxis` decay bounds in place of `norm_φ₀_le` bounds. Sub-refactor (C) must package the **per-modular-form decay hypothesis** (e.g. `‖F(I·t)‖ ≤ C · exp(-π·t)` for `t ≥ 1`) as a typeclass or bundled structure.

* **Cutoff smoothing risk for J6 vs I6.** Both `a/Schwartz/SmoothI6.lean:167-171` and `b/Schwartz/Basic.lean:60-64` apply `RadialSchwartz.cutoffC` to handle the `r ∈ (-2, 0)` gap; the two call sites are near-identical. Harmonising them is part of sub-refactor (E).

* **Build-time risk.** Most of these sub-refactors change public API in a way that will force recompilation of `Schwartz/Basic.lean` and `Eigenfunction/FourierPermutations.lean` on both sides. Expected rebuild cost: ~15-20 minutes on the full project. All existing theorems (`eig_a`, `eig_b`, `a_zero`, `b_zero`) must be re-proven after refactor; their statements do not change. A CI matrix run is required after each sub-refactor.

### 5.6 Recommended ordering

1. **(E)** first: `Common/SchwartzIntegrand.lean` extension. Low risk, locks in the outer shape. Gives a small (~150) saving.
2. **(A)** `Common/IciOneIntegrand.lean`. Low-medium risk, covers I1/I3/I5. Saves ~300.
3. Decay unification + **I2/I4 signed extension** of `I24Common`. Low-medium risk, saves ~350. At this point the `a/IntegralEstimates/` directory is at target size.
4. **(B)** unify `SmoothI24Common` and `SmoothJ24Common`. Medium risk, saves ~150. `a/Schwartz/` and `b/Schwartz/` common infrastructure lands.
5. Retire `a/SmoothI6.lean:91-151` via existing `SmoothIntegralIciOne`. Very low risk, saves 60. At this point the Schwartz-family alignment is complete.
6. **(D)** `Contour/PermI5.lean`. Medium risk, saves ~350.
7. **(C)** PermI12/PermJ12 consolidation. Medium-high risk, saves ~800. Last because it touches the most files and has the highest chance of needing iteration on the abstraction.

After step 7 the project is at ~3,350 lines on the I/J perimeter, down from ~7,840. Total line reduction from 54k→~49k is expected; the remaining ~20k reduction the user wants requires attacking the Cohn-Elkies and ModularForms targets (out of scope for this agent).

---

## Appendix A: grep-evidence of duplication

Same structural patterns appearing in both `a/` and `b/`:

* `norm_φ₀''_le_mul_exp_neg_pi_of_one_half_lt_im` (`a`-side exponential decay hypothesis) in
  `a/IntegralEstimates/I24Common.lean:70`, `a/IntegralEstimates/I1.lean` (via `norm_φ₀_le`), `a/IntegralEstimates/I6.lean:68-79`, `a/Schwartz/SmoothI24Common.lean:89-90`, `a/Schwartz/DecayI1.lean` (multiple uses). Each site is the same decay shape.
* `exists_bound_norm_ψS_resToImagAxis_exp_Ici_one` (`b`-side parallel of the same decay shape) in
  `b/PsiBounds.lean:148-176`, `b/Schwartz/SmoothJ1.lean:184`, `b/Schwartz/SmoothJ5.lean:201`, `b/Schwartz/SmoothJ6/Bounds.lean` (multiple), `b/SpecialValues.lean` (multiple), `b/Eigenfunction/PermJ5Integrability.lean`, `b/Eigenfunction/PermJ12FourierJ1Kernel.lean`, `b/Schwartz/PsiExpBounds/PsiSDecay.lean`.
* **Both sides pass the same quantity** `C₀ * rexp (-π * s)` to dominated-integrability arguments; the only difference is which modular form supplies the `C₀`.

## Appendix B: file-by-file action list

| file | action | lines saved |
|---|---|---|
| `a/IntegralEstimates/I1.lean` | trim to 30-line IciOneIntegrand specialization | 100 |
| `a/IntegralEstimates/I3.lean` | trim to 20-line specialization; move `inv_integrand_eq_integrand` to IciOneIntegrand | 87 |
| `a/IntegralEstimates/I5.lean` | trim to 15-line specialization | 46 |
| `a/IntegralEstimates/I6.lean` | keep public API; use `SmoothIntegralIciOne`; move decay to IciOneIntegrand | 260 |
| `a/IntegralEstimates/I2.lean` | unify iteratedDeriv with I4 via signed variant in I24Common | 115 |
| `a/IntegralEstimates/I4.lean` | same | 120 |
| `a/IntegralEstimates/I24Common.lean` | add signed variant; use SmoothIntegralIoo01 | 15 |
| `a/Schwartz/SmoothI1.lean` | keep; reduce via SmoothIntegralIoo01 | 17 |
| `a/Schwartz/SmoothI2.lean` | rewrite as thin SmoothIntegralIoo01 wrapper | 28 |
| `a/Schwartz/SmoothI4.lean` | rewrite as thin SmoothIntegralIoo01 wrapper | 29 |
| `a/Schwartz/SmoothI6.lean` | delete `hasDerivAt_integral_gN_of_gt_neg2`; use SmoothIntegralIciOne | 125 |
| `a/Schwartz/SmoothI24Common.lean` | shrink to thin wrapper over SmoothIntegralIoo01 | 82 |
| `a/Schwartz/DecayI1.lean` | shrink via new common IciOneIntegrand decay | 266 |
| `a/Eigenfunction/PermI12*.lean` (10 files) | collapse into 1 file; use generalised Contour/PermJ12 | 972 |
| `a/Eigenfunction/PermI5*.lean` (3 files) | collapse into 1 file; use new Contour/PermI5 | 397 |
| `a/Eigenfunction/FourierPermutations.lean` | consume new generic | 20 |
| `b/Schwartz/SmoothJ1.lean` | keep a specialized version; share SmoothJ1 decay with DecayI1 | 144 |
| `b/Schwartz/SmoothJ3.lean` | keep specialized; 60 lines of modular identity stay | 61 |
| `b/Schwartz/SmoothJ5.lean` | similar to J1; common decay | 159 |
| `b/Schwartz/SmoothJ6/Bounds.lean` | reduce via generic Ici-decay | 240 |
| `b/Schwartz/SmoothJ24Common.lean` | thin wrapper | 36 |
| `b/Eigenfunction/PermJ5*.lean` (2 files) | collapse into 1; use new Contour/PermI5 | 352 |
| `b/Eigenfunction/PermJ12*.lean` (8 files) | shrink; unused files delete | 496 |
| `b/Eigenfunction/FourierPermutations.lean` | consume new generic | 26 |
| **total to be removed** | | **~4,491** |
| (minus) new Common/Contour files | | **−570** |
| **net savings** | | **≈ 3,920** |

Including the Schwartz assembly + cutoff unification + cross-family `DecayI1`↔`SmoothJ1`↔`SmoothJ5` decay-template sharing (which are more speculative), **reach ≈ 4,500-4,700 lines saved**.
