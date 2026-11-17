/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Group.RadialFunction
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import SpherePacking.ForMathlib.RadialSchwartz.Basic
public import SpherePacking.ForMathlib.RadialSchwartz.SchwartzMap

/-!
# Multidimensional Radial Schwartz Functions

A function smooth only on a half-line `[b, ∞)` and decaying on `[a, ∞)` can be turned into a
genuine Schwartz map by multiplying it with a smooth transition function that vanishes on
`(-∞, a - δ]` and is identically `1` on `[a, ∞)`, for any transition width `0 < δ < a - b`.

## Main declarations

* `ContDiffOn.contDiff_smul_of_tsupport_subset_interior`: a function smooth only on `s`, cut off by
  a smooth scalar whose topological support lies in `interior s`, is globally smooth.
* `SchwartzMap.ofDecayOn`: the resulting Schwartz map on `ℝ`.
* `RadialSchwartzMap.ofDecay`: its radial counterpart on an inner product space, obtained by
  composing with `‖·‖ ^ 2`.
-/

@[expose] public noncomputable section

open ContDiff Set

namespace SchwartzMap

section ofDecay

/-- The inclusion `ℝ → ℂ` is smooth, being a continuous `ℝ`-linear map. -/
@[fun_prop]
theorem _root_.Complex.contDiff_ofReal {n} : ContDiff ℝ n Complex.ofReal :=
  ContinuousLinearMap.contDiff Complex.ofRealCLM

section Cutoff

variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Pairing a function that is only smooth on `s` with a smooth factor whose topological support
sits inside the interior of `s` gives a globally smooth function. Note that `g` need only be smooth
on `interior s`: off its support the pairing vanishes identically. -/
theorem _root_.ContDiffOn.contDiff_bilinear_of_tsupport_subset_interior {B : G →L[𝕜] F →L[𝕜] H}
    {g : E → G} {f : E → F} {s : Set E} {n : ℕ∞ω} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g (interior s)) (hsupp : tsupport g ⊆ interior s) :
    ContDiff 𝕜 n fun x ↦ B (g x) (f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases! hx : x ∈ interior s
  · exact ((B.contDiff.comp_contDiffOn hg).contDiffAt (isOpen_interior.mem_nhds hx)).clm_apply
      ((hf x (interior_subset hx)).contDiffAt (mem_interior_iff_mem_nhds.mp hx))
  · refine (contDiffAt_const (c := (0 : H))).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp fun h ↦ hx (hsupp h)] with y hy
    simp [hy]

/-- Scalar-multiplication case of `ContDiffOn.contDiff_bilinear_of_tsupport_subset_interior`. -/
theorem _root_.ContDiffOn.contDiff_smul_of_tsupport_subset_interior {g : E → 𝕜} {f : E → F}
    {s : Set E} {n : ℕ∞ω} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g (interior s))
    (hsupp : tsupport g ⊆ interior s) : ContDiff 𝕜 n fun x ↦ g x • f x :=
  hf.contDiff_bilinear_of_tsupport_subset_interior (B := ContinuousLinearMap.lsmul 𝕜 𝕜) hg hsupp

/-- A `smoothTransition` cutoff rising from `0` at `a - δ` to `1` at `a`, applied to a function
smooth on `Ici b` for any `b < a - δ`, valued in an arbitrary real normed space. -/
theorem _root_.contDiff_smoothTransition_smul [NormedSpace ℝ F] {f : ℝ → F} {a b δ : ℝ} {n : ℕ∞}
    (hδ : 0 < δ) (hb : b < a - δ) (hf : ContDiffOn ℝ n f (Ici b)) :
    ContDiff ℝ n fun x ↦ ((x - a) / δ + 1).smoothTransition • f x := by
  refine hf.contDiff_smul_of_tsupport_subset_interior (by fun_prop) ?_
  rw [tsupport, interior_Ici,
    show Function.support (fun x : ℝ ↦ ((x - a) / δ + 1).smoothTransition) = Ioi (a - δ) by
      ext x
      rw [Function.mem_support, ne_eq, Real.smoothTransition.zero_iff_nonpos, not_le,
        div_add_one hδ.ne', lt_div_iff₀ hδ, zero_mul, mem_Ioi]
      constructor <;> intro h <;> linarith,
    closure_Ioi]
  exact Ici_subset_Ioi.mpr hb

end Cutoff

/-- The cutoff `fun x ↦ ((x - a) / δ + 1).smoothTransition * f x` is globally smooth as soon as `f`
is smooth on `Ici b` for some `b < a - δ`.

The transition window is `[a - δ, a]`: the cutoff is `0` on `Iic (a - δ)` and `1` on `Ici a`, so
the product agrees with `f` on `Ici a` for every width `δ > 0`. Smoothness of `f` is therefore
needed only on a neighbourhood of `Ici (a - δ)`, which is what `b < a - δ` provides. Keeping `δ`
free matters in practice: a function given by an integral that converges only on `Ioi b` admits no
cutoff of width `δ ≥ a - b`, however small the margin. The boundary case `b = a - δ` is also
true — `smoothTransition` is flat at `0` — but needs a genuine estimate rather than this locality
argument. -/
theorem _root_.contDiff_smoothTransition_mul {f : ℝ → ℂ} {a b δ : ℝ} {n : ℕ∞} (hδ : 0 < δ)
    (hb : b < a - δ) (smooth : ContDiffOn ℝ n f (Ici b)) :
    ContDiff ℝ n (fun x ↦ ((x - a) / δ + 1).smoothTransition * f x) := by
  simpa [Complex.real_smul] using contDiff_smoothTransition_smul hδ hb smooth

/-- A Schwartz map constructed from a smooth function decaying on a subset by multiplying by a
smooth transition function. -/
@[simps!]
def ofDecayOn {f : ℝ → ℂ} {a b δ : ℝ} (hδ : 0 < δ) (hb : b < a - δ)
    (smooth : ContDiffOn ℝ ∞ f (Set.Ici b))
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    𝓢(ℝ, ℂ) :=
  let F' : ℝ → ℂ := fun x ↦ Real.smoothTransition ((x - a) / δ + 1) * f x
  SchwartzMap.mkOfCocompact F' (contDiff_smoothTransition_mul hδ hb smooth) <| by
    intro k n
    obtain ⟨C, hC⟩ := decay k n
    use max C 0
    filter_upwards [(isCompact_Icc (a := a - δ) (b := a)).compl_mem_cocompact] with x hx
    obtain hx | hx : x < a - δ ∨ a < x := by grind
    · have hEq : F' =ᶠ[nhds x] 0 := (eventually_lt_nhds hx).mono fun y hy ↦ by
        simp [F', Real.smoothTransition.zero_of_nonpos
          (by rw [div_add_one hδ.ne', div_le_iff₀ hδ, zero_mul]; linarith :
            (y - a) / δ + 1 ≤ 0)]
      simp [(hEq.iteratedFDeriv ℝ n).self_of_nhds]
    · have hEq : F' =ᶠ[nhds x] f := (eventually_gt_nhds hx).mono fun y hy ↦ by
        simp [F', Real.smoothTransition.one_of_one_le
          (le_add_of_nonneg_left (div_nonneg (by linarith) hδ.le) : (1 : ℝ) ≤ (y - a) / δ + 1)]
      exact ((hEq.iteratedFDeriv ℝ n).self_of_nhds ▸ hC x hx.le).trans (le_max_left _ _)

/-- `ofDecayOn` does not change `f` on `[a, ∞)`, where the transition function is identically
`1`. -/
theorem ofDecayOn_eqOn {f : ℝ → ℂ} {a b δ : ℝ} (hδ : 0 < δ) (hb : b < a - δ)
    (smooth : ContDiffOn ℝ ∞ f (Set.Ici b))
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    Set.EqOn f (ofDecayOn hδ hb smooth decay) (Set.Ici a) := fun x hx ↦ by
  rw [ofDecayOn, mkOfCocompact, mk_apply, Real.smoothTransition.one_of_one_le
    (le_add_of_nonneg_left (div_nonneg (by simpa using hx) hδ.le))]
  simp

end ofDecay

section toRadial

-- The `‖·‖²` differentiability helpers formerly here are now mathlib's
-- `hasStrictFDerivAt_norm_sq` / `DifferentiableAt.norm_sq` / `Differentiable.norm_sq`.

variable (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 ℂ] [SMulCommClass ℝ 𝕜 ℂ]
variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Precomposition of a Schwartz map on `ℝ` with `‖·‖ ^ 2`, as a Schwartz map on `F`. -/
@[simps!]
def compNormSq (f : 𝓢(ℝ, ℂ)) : 𝓢(F, ℂ) :=
  f.compCLM ℝ (Function.hasTemperateGrowth_norm_sq F) <| by
    use 1, 1
    intro _
    simp only [norm_pow, norm_norm]
    nlinarith

/-- A radial Schwartz map on `F` obtained by composing a Schwartz map on `ℝ` with `‖·‖ ^ 2`. -/
@[simps!]
def toRadialSchwartzMap (f : 𝓢(ℝ, ℂ)) : RadialSchwartzMap 𝕜 F ℂ :=
  RadialSchwartzMap.mk (compNormSq F f) (Function.isRadial_norm_sq F).comp_right

lemma toRadialSchwartzMap_eq_comp_normSq (f : 𝓢(ℝ, ℂ)) {x : F} :
    f.toRadialSchwartzMap 𝕜 F x = f (‖x‖ ^ 2) := rfl

/-- A radial Schwartz map on `F` built from a smooth function on `ℝ` decaying on `[a, ∞)`. -/
@[simps!]
def _root_.RadialSchwartzMap.ofDecay {f : ℝ → ℂ} {a b δ : ℝ} (hδ : 0 < δ) (hb : b < a - δ)
    (smooth : ContDiffOn ℝ ∞ f (Set.Ici b))
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    RadialSchwartzMap 𝕜 F ℂ :=
  (ofDecayOn hδ hb smooth decay).toRadialSchwartzMap 𝕜 F

end toRadial

end SchwartzMap
