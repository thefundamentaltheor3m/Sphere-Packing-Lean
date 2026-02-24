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

lemma iteratedFDeriv_cutoffC_mul_eq_zero_of_lt {f : ℝ → ℂ} {x : ℝ} (hx : x < -1) (n : ℕ) :
    iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x = 0 := by
  have hEq : (fun r ↦ cutoffC r * f r) =ᶠ[𝓝 x] fun _ ↦ (0 : ℂ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [cutoffC_eq_zero_of_le (le_of_lt hy)]
  simpa using (hEq.iteratedFDeriv (𝕜 := ℝ) n).self_of_nhds

lemma iteratedFDeriv_cutoffC_mul_eq_of_pos {f : ℝ → ℂ} {x : ℝ} (hx : 0 < x) (n : ℕ) :
    iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x = iteratedFDeriv ℝ n f x := by
  have hEq : (fun r ↦ cutoffC r * f r) =ᶠ[𝓝 x] f := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [cutoffC_eq_one_of_nonneg (le_of_lt hy)]
  simpa using (hEq.iteratedFDeriv (𝕜 := ℝ) n).self_of_nhds

lemma exists_bound_on_Icc_of_continuous {g : ℝ → ℝ} (hg : Continuous g) :
    ∃ C, ∀ x ∈ Icc (-1 : ℝ) 0, g x ≤ C := by
  simpa using
    (SpherePacking.ForMathlib.Continuous.exists_upper_bound_on_Icc (g := g) hg (a := (-1 : ℝ))
      (b := 0) (by norm_num))

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
  have hg_smooth' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    simpa [g] using hg_smooth
  have hn : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have hcont_iter : Continuous fun x : ℝ ↦ iteratedFDeriv ℝ n g x :=
    hg_smooth'.continuous_iteratedFDeriv (m := n) hn
  have hcont : Continuous fun x : ℝ ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖ := by
    simpa using (continuous_norm.pow k).mul (continuous_norm.comp hcont_iter)
  obtain ⟨Cmid, hCmid⟩ :=
    exists_bound_on_Icc_of_continuous
      (g := fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖) hcont
  let C : ℝ := max (max Cmid Cpos) 0
  refine ⟨C, ?_⟩
  intro x
  have hC0 : 0 ≤ C := le_max_right _ _
  by_cases hx₁ : x < -1
  · have hzero : iteratedFDeriv ℝ n g x = 0 :=
      iteratedFDeriv_cutoffC_mul_eq_zero_of_lt (f := f) hx₁ n
    simp [C, g, hzero, hC0]
  · by_cases hx₂ : x ≤ 0
    · have hxIcc : x ∈ Icc (-1 : ℝ) 0 := by
        exact ⟨le_of_not_gt hx₁, hx₂⟩
      exact (hCmid x hxIcc).trans (le_trans (le_max_left _ _) (le_max_left _ _))
    · have hxpos : 0 < x := lt_of_not_ge hx₂
      have hx0 : 0 ≤ x := le_of_lt hxpos
      have hEq : iteratedFDeriv ℝ n g x = iteratedFDeriv ℝ n f x :=
        iteratedFDeriv_cutoffC_mul_eq_of_pos (f := f) hxpos n
      have hbd := hCpos x hx0
      have : Cpos ≤ C := le_trans (le_max_right Cmid Cpos) (le_max_left _ _)
      simpa [C, g, hEq] using hbd.trans this

/-- Convenience wrapper: if `f` is smooth and satisfies one-sided Schwartz decay on `0 ≤ x`,
then `cutoffC * f` satisfies global Schwartz decay on `ℝ`. -/
public theorem cutoffC_mul_decay_of_nonneg
    {f : ℝ → ℂ} (hf_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun r ↦ cutoffC r * f r) x‖ ≤ C := by
  have hg_smooth :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r ↦ cutoffC r * f r) := by
    simpa using cutoffC_contDiff.mul hf_smooth
  simpa using (cutoffC_mul_decay_of_nonneg_of_contDiff (f := f) (hg_smooth := hg_smooth) hf_decay)

namespace Bridge

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### The bridge to `𝓢(F,ℂ)` -/

/-- A cutoff-modified version of a radial profile, used to build a Schwartz function on `ℝ`. -/
@[expose] public def fCut (f : ℝ → ℂ) (r : ℝ) : ℂ := cutoffC r * f r

/-- If `f` is smooth then `fCut f` is smooth. -/
public lemma fCut_contDiff (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fCut f) :=
  by simpa [fCut] using cutoffC_contDiff.mul hf

/-- If `f` has one-sided Schwartz decay, then `fCut f` has global Schwartz decay. -/
public lemma fCut_decay (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fCut f) x‖ ≤ C := by
  simpa [fCut] using cutoffC_mul_decay_of_nonneg (f := f) hf hf_decay

/-- Package `fCut f` as an element of the Schwartz space `𝓢(ℝ, ℂ)`. -/
@[expose] public def fCutSchwartz (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) : 𝓢(ℝ, ℂ) where
  toFun := fCut f
  smooth' := fCut_contDiff f hf
  decay' := fCut_decay f hf hf_decay

/-- Build a Schwartz function `F → ℂ` from a smooth profile `f : ℝ → ℂ` that has Schwartz decay
for all derivatives on the half-line `0 ≤ r`, by composing with `‖x‖^2`. -/
@[expose] public noncomputable def schwartzMap_norm_sq_of_contDiff_decay_nonneg (f : ℝ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) : 𝓢(F, ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real F (fCutSchwartz f hf hf_decay)

/-- Evaluate `schwartzMap_norm_sq_of_contDiff_decay_nonneg` pointwise. -/
@[simp]
public theorem schwartzMap_norm_sq_of_contDiff_decay_nonneg_apply (f : ℝ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) (x : F) :
    schwartzMap_norm_sq_of_contDiff_decay_nonneg (F := F) f hf hf_decay x = f (‖x‖ ^ 2) := by
  simp only [schwartzMap_norm_sq_of_contDiff_decay_nonneg, fCutSchwartz,
    schwartzMap_multidimensional_of_schwartzMap_real_toFun]
  change fCut f (‖x‖ ^ 2) = f (‖x‖ ^ 2)
  simp [fCut]

/-- Variant that only assumes smoothness of the cutoff-modified profile. This is the right API
for profiles that are naturally only smooth on a neighborhood of `[0, ∞)`. -/
public noncomputable def schwartzMap_norm_sq_of_cutoffMul_contDiff_decay_nonneg (f : ℝ → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) (fun r ↦ cutoffC r * f r))
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) : 𝓢(F, ℂ) :=
  schwartzMap_multidimensional_of_schwartzMap_real F
    { toFun := fCut f
      smooth' := by simpa [fCut] using hg
      decay' := by
        simpa [fCut] using cutoffC_mul_decay_of_nonneg_of_contDiff (f := f) hg hf_decay }

/-- Evaluate `schwartzMap_norm_sq_of_cutoffMul_contDiff_decay_nonneg` pointwise. -/
@[simp]
public theorem schwartzMap_norm_sq_of_cutoffMul_contDiff_decay_nonneg_apply (f : ℝ → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) (fun r ↦ cutoffC r * f r))
    (hf_decay : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) (x : F) :
    schwartzMap_norm_sq_of_cutoffMul_contDiff_decay_nonneg (F := F) f hg hf_decay x =
      f (‖x‖ ^ 2) := by
  simp only [schwartzMap_norm_sq_of_cutoffMul_contDiff_decay_nonneg,
    schwartzMap_multidimensional_of_schwartzMap_real_toFun]
  change fCut f (‖x‖ ^ 2) = f (‖x‖ ^ 2)
  simp [fCut]

end Bridge

end

end RadialSchwartz
