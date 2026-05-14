module
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import SpherePacking.ForMathlib.BoundsOnIcc

/-!
# One-sided decay to a radial Schwartz function

This file defines the smooth cutoff `cutoff`/`cutoffC` for radial Schwartz constructions and
proves the bridge to global Schwartz on `ℝ`: if `f : ℝ → ℂ` is smooth and satisfies Schwartz-type
bounds for all iterated derivatives on `0 ≤ r`, then the radial function `x ↦ f (‖x‖ ^ 2)` is
Schwartz on any real inner product space `F`.

The construction multiplies `f` by a smooth cutoff on `ℝ` (to make it globally Schwartz), then
lifts it to `F` by composing with `‖x‖ ^ 2`.
-/

namespace RadialSchwartz

noncomputable section

open Complex Real

/-- Smooth cutoff: `cutoff r = 0` for `r ≤ -1/2`, `cutoff r = 1` for `0 ≤ r`. -/
@[expose] public def cutoff (r : ℝ) : ℝ := Real.smoothTransition (2 * r + 1)

@[simp] public lemma cutoff_eq_zero_of_le_neg_half {r : ℝ} (hr : r ≤ (-1 / 2 : ℝ)) :
    cutoff r = 0 := by
  simpa [cutoff] using Real.smoothTransition.zero_of_nonpos (x := 2 * r + 1) (by linarith)

@[simp] public lemma cutoff_eq_zero_of_le {r : ℝ} (hr : r ≤ -1) : cutoff r = 0 :=
  cutoff_eq_zero_of_le_neg_half (r := r) (by linarith [hr])

@[simp] public lemma cutoff_eq_one_of_nonneg {r : ℝ} (hr : 0 ≤ r) : cutoff r = 1 := by
  simpa [cutoff] using Real.smoothTransition.one_of_one_le (x := 2 * r + 1) (by linarith)

@[fun_prop]
public lemma cutoff_contDiff : ContDiff ℝ (⊤ : ℕ∞) cutoff := by
  simpa [cutoff] using
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

/-- Complex-valued version of `cutoff`. -/
@[expose] public def cutoffC (r : ℝ) : ℂ := (cutoff r : ℂ)

@[simp] public lemma cutoffC_eq_zero_of_le_neg_half {r : ℝ} (hr : r ≤ (-1 / 2 : ℝ)) :
    cutoffC r = 0 := by simp [cutoffC, cutoff_eq_zero_of_le_neg_half hr]

@[simp] public lemma cutoffC_eq_zero_of_le {r : ℝ} (hr : r ≤ -1) : cutoffC r = 0 := by
  simp [cutoffC, cutoff_eq_zero_of_le hr]

@[simp] public lemma cutoffC_eq_one_of_nonneg {r : ℝ} (hr : 0 ≤ r) : cutoffC r = 1 := by
  simp [cutoffC, cutoff_eq_one_of_nonneg hr]

@[fun_prop]
public lemma cutoffC_contDiff : ContDiff ℝ (⊤ : ℕ∞) cutoffC := by
  simpa [cutoffC] using ofRealCLM.contDiff.comp cutoff_contDiff

/-- If `f` is smooth on `(-1, ∞)` then `r ↦ cutoffC r * f r` is smooth on all of `ℝ`. -/
public lemma contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1 {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioi (-1 : ℝ))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun r ↦ cutoffC r * f r) := by
  rw [contDiff_iff_contDiffAt (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (f := fun r ↦ cutoffC r * f r)]
  intro x
  by_cases hx : x < (-1 / 2 : ℝ)
  · refine (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ ↦ (0 : ℂ)) x).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [cutoffC_eq_zero_of_le_neg_half (r := y) hy.le]
  · have hx' : (-1 : ℝ) < x := by linarith [le_of_not_gt hx]
    exact cutoffC_contDiff.contDiffAt.mul (hf.contDiffAt (isOpen_Ioi.mem_nhds hx'))

end

end RadialSchwartz

open SchwartzMap Function RCLike

/-- Lift a Schwartz function on `ℝ` to a Schwartz function on `F` by composing with `‖x‖ ^ 2`. -/
@[expose, simps!]
public noncomputable def schwartzMap_multidimensional_of_schwartzMap_real
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : 𝓢(ℝ, ℂ)) : 𝓢(F, ℂ) :=
  f.compCLM ℝ (Function.hasTemperateGrowth_norm_sq F) <| ⟨1, 1, fun _ => by
    simp only [norm_pow, norm_norm]; nlinarith⟩

namespace RadialSchwartz

noncomputable section

open scoped Topology
open Set SchwartzMap

/-- If `cutoffC * f` is smooth and `f` satisfies Schwartz decay bounds on `0 ≤ x`, then
`cutoffC * f` satisfies the global Schwartz decay bounds on `ℝ`. -/
public theorem cutoffC_mul_decay_of_nonneg_of_contDiff
    {f : ℝ → ℂ} (hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r ↦ cutoffC r * f r))
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x‖ ≤ C := by
  intro k n
  obtain ⟨Cpos, hCpos⟩ := hf_decay k n
  let g : ℝ → ℂ := fun r ↦ cutoffC r * f r
  have hn : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have hcont : Continuous fun x : ℝ ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖ := by
    simpa using (continuous_norm.pow k).mul
      (continuous_norm.comp (hg_smooth.continuous_iteratedFDeriv (m := n) hn))
  obtain ⟨Cmid, hCmid⟩ :=
    SpherePacking.ForMathlib.exists_upper_bound_on_Icc
      (g := fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖)
      (a := (-1 : ℝ)) (b := 0) (by norm_num) hcont.continuousOn
  refine ⟨max (max Cmid Cpos) 0, fun x => ?_⟩
  by_cases hx₁ : x < -1
  · simp [show iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x = 0 by
      simpa using (show (fun r ↦ cutoffC r * f r) =ᶠ[𝓝 x] fun _ ↦ (0 : ℂ) by
        filter_upwards [Iio_mem_nhds hx₁] with y hy
        simp [cutoffC_eq_zero_of_le hy.le]).iteratedFDeriv (𝕜 := ℝ) n |>.self_of_nhds]
  · by_cases hx₂ : x ≤ 0
    · exact (hCmid x ⟨le_of_not_gt hx₁, hx₂⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
    · have hxpos : 0 < x := lt_of_not_ge hx₂
      simpa [g, show iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x = iteratedFDeriv ℝ n f x by
        simpa using (show (fun r ↦ cutoffC r * f r) =ᶠ[𝓝 x] f by
          filter_upwards [Ioi_mem_nhds hxpos] with y hy
          simp [cutoffC_eq_one_of_nonneg hy.le]).iteratedFDeriv (𝕜 := ℝ) n |>.self_of_nhds] using
        (hCpos x hxpos.le).trans ((le_max_right Cmid Cpos).trans (le_max_left _ _))

/-- If `f` is smooth and satisfies one-sided Schwartz decay on `0 ≤ x`, then `cutoffC * f`
satisfies global Schwartz decay on `ℝ`. -/
public theorem cutoffC_mul_decay_of_nonneg
    {f : ℝ → ℂ} (hf_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x‖ ≤ C :=
  cutoffC_mul_decay_of_nonneg_of_contDiff (f := f) (cutoffC_contDiff.mul hf_smooth) hf_decay

namespace Bridge

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### The bridge to `𝓢(F,ℂ)` -/

/-- A cutoff-modified radial profile, used to build a Schwartz function on `ℝ`. -/
@[expose] public def fCut (f : ℝ → ℂ) (r : ℝ) : ℂ := cutoffC r * f r

/-- Package `fCut f` as an element of `𝓢(ℝ, ℂ)`. -/
@[expose] public def fCutSchwartz (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) : 𝓢(ℝ, ℂ) where
  toFun := fCut f
  smooth' := by simpa [fCut] using cutoffC_contDiff.mul hf
  decay' := by simpa [fCut] using cutoffC_mul_decay_of_nonneg (f := f) hf hf_decay

/-- On `0 ≤ r`, `fCut f` agrees with `f`. -/
public lemma fCut_apply_of_nonneg (f : ℝ → ℂ) {r : ℝ} (hr : 0 ≤ r) : fCut f r = f r := by
  simp [fCut, hr]

end Bridge

end

end RadialSchwartz
