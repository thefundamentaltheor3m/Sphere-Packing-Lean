module
public import SpherePacking.ForMathlib.RadialSchwartz.Cutoff
public import SpherePacking.ForMathlib.RadialSchwartz.Multidimensional
import SpherePacking.ForMathlib.BoundsOnIcc

/-!
# One-sided decay to a radial Schwartz function

If `f : ℝ → ℂ` is smooth and satisfies Schwartz-type bounds for all iterated derivatives on `0 ≤ r`,
then the radial function `x ↦ f (‖x‖ ^ 2)` is Schwartz on any real inner product space `F`.

The construction multiplies `f` by a smooth cutoff on `ℝ` (to make it globally Schwartz), then
lifts it to `F` by composing with `‖x‖ ^ 2`.
-/

namespace RadialSchwartz

noncomputable section

open scoped Topology
open Set SchwartzMap

private lemma iteratedFDeriv_cutoffC_mul_eq_zero_of_lt {f : ℝ → ℂ} {x : ℝ} (hx : x < -1) (n : ℕ) :
    iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x = 0 := by
  simpa using (show (fun r ↦ cutoffC r * f r) =ᶠ[𝓝 x] fun _ ↦ (0 : ℂ) by
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [cutoffC_eq_zero_of_le hy.le]).iteratedFDeriv (𝕜 := ℝ) n |>.self_of_nhds

private lemma iteratedFDeriv_cutoffC_mul_eq_of_pos {f : ℝ → ℂ} {x : ℝ} (hx : 0 < x) (n : ℕ) :
    iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x = iteratedFDeriv ℝ n f x := by
  simpa using (show (fun r ↦ cutoffC r * f r) =ᶠ[𝓝 x] f by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [cutoffC_eq_one_of_nonneg hy.le]).iteratedFDeriv (𝕜 := ℝ) n |>.self_of_nhds

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
  · simp [iteratedFDeriv_cutoffC_mul_eq_zero_of_lt (f := f) hx₁ n]
  · by_cases hx₂ : x ≤ 0
    · exact (hCmid x ⟨le_of_not_gt hx₁, hx₂⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
    · have hxpos : 0 < x := lt_of_not_ge hx₂
      simpa [g, iteratedFDeriv_cutoffC_mul_eq_of_pos (f := f) hxpos n] using
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

/-- If `f` is smooth then `fCut f` is smooth. -/
public lemma fCut_contDiff (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fCut f) := by simpa [fCut] using cutoffC_contDiff.mul hf

/-- If `f` has one-sided Schwartz decay, then `fCut f` has global Schwartz decay. -/
public lemma fCut_decay (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fCut f) x‖ ≤ C := by
  simpa [fCut] using cutoffC_mul_decay_of_nonneg (f := f) hf hf_decay

/-- Package `fCut f` as an element of `𝓢(ℝ, ℂ)`. -/
@[expose] public def fCutSchwartz (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) : 𝓢(ℝ, ℂ) where
  toFun := fCut f
  smooth' := fCut_contDiff f hf
  decay' := fCut_decay f hf hf_decay

/-- On `0 ≤ r`, `fCut f` agrees with `f`. -/
public lemma fCut_apply_of_nonneg (f : ℝ → ℂ) {r : ℝ} (hr : 0 ≤ r) : fCut f r = f r := by
  simp [fCut, hr]

/-- On `0 ≤ r`, `fCutSchwartz f` agrees with `f`. -/
@[simp] public lemma fCutSchwartz_apply_of_nonneg (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C)
    (r : ℝ) (hr : 0 ≤ r) : (fCutSchwartz f hf hf_decay : ℝ → ℂ) r = f r :=
  fCut_apply_of_nonneg f hr

end Bridge

end

end RadialSchwartz
