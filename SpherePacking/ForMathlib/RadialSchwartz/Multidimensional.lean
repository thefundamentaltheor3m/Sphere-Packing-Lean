/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Normed.Group.RadialFunction
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import SpherePacking.ForMathlib.RadialSchwartz.Basic
public import SpherePacking.ForMathlib.RadialSchwartz.SchwartzMap

/-!
# Multidimensional Radial Schwartz Functions
-/

@[expose] public noncomputable section

open SchwartzMap Function RCLike ContDiff Set

namespace SchwartzMap

section ofDecay

open Set

@[fun_prop]
theorem _root_.Complex.contDiff_ofReal {n} : ContDiff ℝ n Complex.ofReal :=
  ContinuousLinearMap.contDiff Complex.ofRealCLM

section Cutoff

variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Cutting a function that is only smooth on `s` by a smooth scalar whose topological support
sits inside the interior of `s` gives a globally smooth function. Note that `g` need only be
smooth on `interior s`: off its support the product vanishes identically. -/
theorem _root_.ContDiffOn.contDiff_smul_of_tsupport_subset_interior {g : E → 𝕜} {f : E → F}
    {s : Set E} {n : ℕ∞ω} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g (interior s))
    (hsupp : tsupport g ⊆ interior s) : ContDiff 𝕜 n fun x ↦ g x • f x := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases! hx : x ∈ interior s
  · exact (hg.contDiffAt (isOpen_interior.mem_nhds hx)).smul
      ((hf x (interior_subset hx)).contDiffAt (mem_interior_iff_mem_nhds.mp hx))
  · refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp fun h ↦ hx (hsupp h)] with y hy
    simp [hy]

/-- Bilinear form of `ContDiffOn.contDiff_smul_of_tsupport_subset_interior`: any continuous
bilinear pairing works, not just scalar multiplication. -/
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

/-- A `smoothTransition` cutoff at an arbitrary threshold `a`, applied to a function smooth on
`Ici b` for any `b < a`, valued in an arbitrary real normed space. -/
theorem _root_.contDiff_smoothTransition_smul [NormedSpace ℝ F] {f : ℝ → F} {a b : ℝ} {n : ℕ∞}
    (hab : b < a) (hf : ContDiffOn ℝ n f (Ici b)) :
    ContDiff ℝ n fun x ↦ (x - a).smoothTransition • f x := by
  refine hf.contDiff_smul_of_tsupport_subset_interior (by fun_prop) ?_
  rw [tsupport]
  refine (closure_mono (t := Ioi a) fun x hx ↦ ?_).trans ?_
  · simpa [Function.mem_support, Real.smoothTransition.zero_iff_nonpos, sub_nonpos] using hx
  · simpa [closure_Ioi, interior_Ici] using Ici_subset_Ioi.mpr hab

end Cutoff

/-- The cutoff `fun x ↦ (x - a + 1).smoothTransition * f x` is globally smooth as soon as `f` is
smooth on `Ici (a - ε)` for some `ε > 1`.

The threshold is chosen so that the cutoff is `1` on `Ici a` and `0` on `Iic (a - 1)`, so the
product agrees with `f` on `Ici a`; `f` must therefore be smooth on a neighbourhood of
`Ici (a - 1)`, which is exactly what `1 < ε` provides. The boundary case `ε = 1` is also true —
`smoothTransition` is flat at `0` — but needs a genuine estimate rather than this locality
argument. -/
theorem _root_.contDiff_smoothTransition_mul {f : ℝ → ℂ} {a ε : ℝ} {n : ℕ∞} (hε : 1 < ε)
    (smooth : ContDiffOn ℝ n f (Ici (a - ε))) :
    ContDiff ℝ n (fun x ↦ (x - a + 1).smoothTransition * f x) := by
  simpa [Complex.real_smul, sub_sub_eq_add_sub, sub_add_eq_add_sub] using
    contDiff_smoothTransition_smul (a := a - 1) (b := a - ε) (by linarith) smooth

/-- A Schwartz map constructed from a smooth function decaying on a subset by multiplying by a
smooth transition function. -/
@[simps!]
def ofDecayOn {f : ℝ → ℂ} {a ε : ℝ} (hε : 1 < ε)
    (smooth : ContDiffOn ℝ ∞ f (Set.Ici (a - ε)))
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    𝓢(ℝ, ℂ) :=
  let F' : ℝ → ℂ := fun x ↦ Real.smoothTransition (x - a + 1) * f x
  SchwartzMap.mkOfCocompact F' (contDiff_smoothTransition_mul hε smooth) <| by
    intro k n
    obtain ⟨C, hC⟩ := decay k n
    use max C 0
    rw [Filter.Eventually, Filter.mem_cocompact]
    use Set.Icc (a - 1) a, isCompact_Icc
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    simp only [Set.mem_ofPred_eq]
    obtain hx | hx := hx
    · have hEq : F' =ᶠ[nhds x] fun _ ↦ 0 := by
        filter_upwards [eventually_lt_nhds hx] with y hy
        simp only [F', Real.smoothTransition.zero_of_nonpos (by linarith : y - a + 1 ≤ 0),
          Complex.ofReal_zero, zero_mul]
      rw [(hEq.iteratedFDeriv ℝ n).self_of_nhds, iteratedFDeriv_fun_zero]
      simp
    · have hEq : F' =ᶠ[nhds x] f := by
        filter_upwards [eventually_gt_nhds hx] with y hy
        simp only [F', Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ y - a + 1),
          Complex.ofReal_one, one_mul]
      rw [(hEq.iteratedFDeriv ℝ n).self_of_nhds]
      exact (hC x hx.le).trans (le_max_left _ _)

theorem ofDecayOn_eqOn {f : ℝ → ℂ} {a ε : ℝ} (hε : 1 < ε)
    (smooth : ContDiffOn ℝ ∞ f (Set.Ici (a - ε)))
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    Set.EqOn f (ofDecayOn hε smooth decay) (Set.Ici a) := by
  grind [ofDecayOn, mkOfCocompact_toFun, Set.EqOn, Real.smoothTransition.eq_one_iff_one_le,
    Complex.ofReal_one, SchwartzMap.mkOfCocompact, mk_apply]

end ofDecay

section toRadial

-- The `‖·‖²` differentiability helpers formerly here are now mathlib's
-- `hasStrictFDerivAt_norm_sq` / `DifferentiableAt.norm_sq` / `Differentiable.norm_sq`.

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]

@[simps!]
def compNormSq (f : 𝓢(ℝ, ℂ)) : 𝓢(F, ℂ) :=
    f.compCLM ℝ (Function.hasTemperateGrowth_norm_sq F) <| by
  use 1, 1
  intro _
  simp only [norm_pow, norm_norm]
  nlinarith

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 ℂ] [SMulCommClass ℝ 𝕜 ℂ]

/-- A radial Schwartz map on `F` obtained by composing a Schwartz map on `ℝ` with `‖·‖ ^ 2`. -/
@[simps!]
def toRadialSchwartzMap (f : 𝓢(ℝ, ℂ)) : RadialSchwartzMap 𝕜 F ℂ :=
  RadialSchwartzMap.mk (compNormSq F f) (Function.isRadial_norm_sq F).comp_right

/-- A radial Schwartz map on `F` built from a smooth function on `ℝ` decaying on `[a, ∞)`. -/
@[simps!]
def _root_.RadialSchwartzMap.ofDecay {f : ℝ → ℂ} {a ε : ℝ} (hε : 1 < ε)
    (smooth : ContDiffOn ℝ ∞ f (Set.Ici (a - ε)))
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    RadialSchwartzMap 𝕜 F ℂ :=
  (ofDecayOn hε smooth decay).toRadialSchwartzMap F

end toRadial

end SchwartzMap
