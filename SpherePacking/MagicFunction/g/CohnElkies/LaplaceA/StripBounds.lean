module
public import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.Basic
import SpherePacking.MagicFunction.g.CohnElkies.LaplaceA.FiniteDifference
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
import SpherePacking.ModularForms.PhiTransformLemmas


/-!
# Strip bounds for the `a'` contour deformation

This file proves the strip estimates needed to deform the contour integrals defining the
"vertical-segment" pieces of `a'` to the imaginary axis.

Only decay along the top edge of the rectangle as `m → ∞` is required, so we avoid global uniform
hypotheses in `re z`.

## Main statements
* `MagicFunction.g.CohnElkies.IntegralReps.exists_phi2'_phi4'_bound_exp`
* `MagicFunction.g.CohnElkies.IntegralReps.integrableOn_Φ₂'_imag_axis`
* `MagicFunction.g.CohnElkies.IntegralReps.integrableOn_Φ₄'_imag_axis`
* `MagicFunction.g.CohnElkies.IntegralReps.I₁'_add_I₃'_add_I₅'_eq_imag_axis`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped UpperHalfPlane Topology intervalIntegral
open MeasureTheory Real Complex Filter
open MagicFunction.FourierEigenfunctions
open MagicFunction.a.ComplexIntegrands

local notation "c12π" => ‖(12 * (I : ℂ)) / (π : ℂ)‖
local notation "c36π2" => ‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖

/--
Turn an `IsBoundedAtImInfty` hypothesis into an explicit uniform bound with a positive constant.
-/
lemma exists_bound_of_isBoundedAtImInfty {f : ℍ → ℂ}
    (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖f z‖ ≤ C := by
  rcases (UpperHalfPlane.isBoundedAtImInfty_iff.mp hbdd) with ⟨C, A, hC⟩
  refine ⟨max 1 C, A, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z hz
  exact (hC z hz).trans (le_max_right _ _)

/-- Exponential growth bounds for `φ₂'` and `φ₄'` on vertical rays in the upper half-plane. -/
public lemma exists_phi2'_phi4'_bound_exp :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im →
      ‖φ₂' z‖ ≤ C * Real.exp (2 * π * z.im) ∧
        ‖φ₄' z‖ ≤ C * Real.exp (2 * π * z.im) := by
  -- Bounds for the Eisenstein series and for `Δ⁻¹` at `i∞`.
  rcases
      exists_bound_of_isBoundedAtImInfty (f := E₂) E₂_isBoundedAtImInfty with
    ⟨CE2, AE2, hCE2, hE2⟩
  have hbddE4 : UpperHalfPlane.IsBoundedAtImInfty (fun z : ℍ => E₄ z) := by
    simpa using (ModularFormClass.bdd_at_infty E₄)
  rcases exists_bound_of_isBoundedAtImInfty (f := fun z : ℍ => E₄ z) hbddE4 with
    ⟨CE4, AE4, hCE4, hE4⟩
  have hbddE6 : UpperHalfPlane.IsBoundedAtImInfty (fun z : ℍ => E₆ z) := by
    simpa using (ModularFormClass.bdd_at_infty E₆)
  rcases exists_bound_of_isBoundedAtImInfty (f := fun z : ℍ => E₆ z) hbddE6 with
    ⟨CE6, AE6, hCE6, hE6⟩
  rcases exists_inv_Delta_bound_exp with ⟨CΔ, AΔ, hCΔ, hΔ⟩
  let A : ℝ := max AΔ (max AE2 (max AE4 AE6))
  have hAΔ : AΔ ≤ A := le_max_left _ _
  have hAE2 : AE2 ≤ A := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hAE4 : AE4 ≤ A := by
    have h₁ : AE4 ≤ max AE4 AE6 := le_max_left _ _
    have h₂ : AE4 ≤ max AE2 (max AE4 AE6) := le_trans h₁ (le_max_right _ _)
    exact le_trans h₂ (le_max_right _ _)
  have hAE6 : AE6 ≤ A := by
    have h₁ : AE6 ≤ max AE4 AE6 := le_max_right _ _
    have h₂ : AE6 ≤ max AE2 (max AE4 AE6) := le_trans h₁ (le_max_right _ _)
    exact le_trans h₂ (le_max_right _ _)
  -- One constant dominating both bounds.
  let C : ℝ :=
    max 1 (max (CE4 ^ (2 : ℕ) * CΔ) (CE4 * (CE2 * CE4 + CE6) * CΔ))
  have hCpos : 0 < C := by
    have : (0 : ℝ) < 1 := by norm_num
    -- `C ≥ 1`.
    have h1 : (1 : ℝ) ≤ C := by
      dsimp [C]
      exact le_max_left _ _
    exact lt_of_lt_of_le this h1
  refine ⟨C, A, hCpos, ?_⟩
  intro z hzA
  have hzΔ : AΔ ≤ z.im := le_trans hAΔ hzA
  have hzE2 : AE2 ≤ z.im := le_trans hAE2 hzA
  have hzE4 : AE4 ≤ z.im := le_trans hAE4 hzA
  have hzE6 : AE6 ≤ z.im := le_trans hAE6 hzA
  have hE2z : ‖E₂ z‖ ≤ CE2 := hE2 z hzE2
  have hE4z : ‖E₄ z‖ ≤ CE4 := hE4 z hzE4
  have hE6z : ‖E₆ z‖ ≤ CE6 := hE6 z hzE6
  have hΔz : ‖(Δ z)⁻¹‖ ≤ CΔ * Real.exp (2 * π * z.im) := hΔ z hzΔ
  have hφ4 :
      ‖φ₄' z‖ ≤ C * Real.exp (2 * π * z.im) := by
    -- `φ₄' = (E₄^2) / Δ`.
    have hφ4' :
        ‖φ₄' z‖ ≤ (CE4 ^ (2 : ℕ) * CΔ) * Real.exp (2 * π * z.im) := by
      calc
        ‖φ₄' z‖
            = ‖(E₄ z) ^ (2 : ℕ) / (Δ z)‖ := by
                simp [φ₄', div_eq_mul_inv, pow_two, mul_assoc]
        _ = ‖(E₄ z) ^ (2 : ℕ) * (Δ z)⁻¹‖ := by simp [div_eq_mul_inv]
        _ ≤ ‖(E₄ z) ^ (2 : ℕ)‖ * ‖(Δ z)⁻¹‖ := by
              exact norm_mul_le ((E₄ z) ^ (2 : ℕ)) ((Δ z)⁻¹)
        _ = (‖E₄ z‖ ^ (2 : ℕ)) * ‖(Δ z)⁻¹‖ := by simp [norm_pow]
        _ ≤ (‖E₄ z‖ ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * z.im)) := by
              exact mul_le_mul_of_nonneg_left hΔz (pow_nonneg (norm_nonneg _) _)
        _ ≤ (CE4 ^ (2 : ℕ)) * (CΔ * Real.exp (2 * π * z.im)) := by
              gcongr
        _ = (CE4 ^ (2 : ℕ) * CΔ) * Real.exp (2 * π * z.im) := by ring
    have hCdom : CE4 ^ (2 : ℕ) * CΔ ≤ C := by
      dsimp [C]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    exact hφ4'.trans (mul_le_mul_of_nonneg_right hCdom (Real.exp_pos _).le)
  have hφ2 :
      ‖φ₂' z‖ ≤ C * Real.exp (2 * π * z.im) := by
    -- `φ₂' = E₄ * (E₂*E₄ - E₆) / Δ`.
    have hcore :
        ‖(E₂ z) * (E₄ z) - (E₆ z)‖ ≤ CE2 * CE4 + CE6 := by
      calc
        ‖(E₂ z) * (E₄ z) - (E₆ z)‖ ≤ ‖(E₂ z) * (E₄ z)‖ + ‖E₆ z‖ := by
            simpa using (norm_sub_le ((E₂ z) * (E₄ z)) (E₆ z))
        _ ≤ (‖E₂ z‖ * ‖E₄ z‖) + ‖E₆ z‖ := by
            gcongr
            simp
        _ ≤ (CE2 * CE4) + CE6 := by
            gcongr
    have hφ2' :
        ‖φ₂' z‖ ≤ (CE4 * (CE2 * CE4 + CE6) * CΔ) * Real.exp (2 * π * z.im) := by
      have hmul :
          ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z))‖ ≤ CE4 * (CE2 * CE4 + CE6) := by
        have hmul' :
            ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z))‖ ≤
              ‖E₄ z‖ * ‖(E₂ z) * (E₄ z) - (E₆ z)‖ := by
          exact norm_mul_le (E₄ z) ((E₂ z) * (E₄ z) - (E₆ z))
        have hmul'' :
            ‖E₄ z‖ * ‖(E₂ z) * (E₄ z) - (E₆ z)‖ ≤ CE4 * (CE2 * CE4 + CE6) := by
          have hnonneg : 0 ≤ ‖E₄ z‖ := norm_nonneg _
          gcongr
        exact hmul'.trans hmul''
      have hnonneg : 0 ≤ CE4 * (CE2 * CE4 + CE6) := by
        have : 0 ≤ CE2 * CE4 + CE6 := by nlinarith [hCE2.le, hCE4.le, hCE6.le]
        nlinarith [hCE4.le, this]
      calc
        ‖φ₂' z‖
            = ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) * (Δ z)⁻¹‖ := by
                simp [φ₂', div_eq_mul_inv, mul_assoc]
        _ ≤ ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z))‖ * ‖(Δ z)⁻¹‖ := by
              exact norm_mul_le ((E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z))) ((Δ z)⁻¹)
        _ ≤ (CE4 * (CE2 * CE4 + CE6)) * ‖(Δ z)⁻¹‖ := by
              exact mul_le_mul_of_nonneg_right hmul (norm_nonneg _)
        _ ≤ (CE4 * (CE2 * CE4 + CE6)) * (CΔ * Real.exp (2 * π * z.im)) := by
              exact mul_le_mul_of_nonneg_left hΔz hnonneg
        _ = (CE4 * (CE2 * CE4 + CE6) * CΔ) * Real.exp (2 * π * z.im) := by ring
    have hCdom : CE4 * (CE2 * CE4 + CE6) * CΔ ≤ C := by
      dsimp [C]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact hφ2'.trans (mul_le_mul_of_nonneg_right hCdom (Real.exp_pos _).le)
  refine ⟨hφ2, ?_⟩
  -- `φ₄'` bound from `hφ4`.
  exact hφ4

/-- A convenient form of `φ₀_S_transform`, clearing the denominators by multiplying by `z^2`. -/
public lemma φ₀_S_transform_mul_sq (w : ℍ) :
    φ₀ (ModularGroup.S • w) * ((w : ℂ) ^ (2 : ℕ)) =
        φ₀ w * ((w : ℂ) ^ (2 : ℕ)) - (12 * Complex.I) / π * (w : ℂ) * φ₂' w -
          (36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' w := by
  simpa using (_root_.φ₀_S_transform_mul_sq w)

/-- Integrability of `Φ₆'` on the imaginary axis tail `t > 1`. -/
lemma integrableOn_Φ₆'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₆' u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  -- Measurability by continuity on `t > 1`.
  have hcontΦ6 : ContinuousOn (Φ₆' u) {z : ℂ | 0 < z.im} :=
    (MagicFunction.a.ComplexIntegrands.Φ₆'_contDiffOn_ℂ (r := u)).continuousOn
  have hmul : ContinuousOn (fun t : ℝ => ((t : ℂ) * Complex.I : ℂ)) (Set.Ioi (1 : ℝ)) := by
    simpa using (by
      have : Continuous (fun t : ℝ => ((t : ℂ) * Complex.I : ℂ)) := by fun_prop
      exact this.continuousOn)
  have hmaps : Set.MapsTo (fun t : ℝ => ((t : ℂ) * Complex.I : ℂ)) (Set.Ioi (1 : ℝ))
      {z : ℂ | 0 < z.im} := by
    intro t ht
    have ht0 : 0 < t := lt_trans (by norm_num) ht
    simpa using ht0
  have hMeas :
      AEStronglyMeasurable (fun t : ℝ => Φ₆' u ((t : ℂ) * Complex.I))
        (volume.restrict (Set.Ioi (1 : ℝ))) := by
    exact (hcontΦ6.comp hmul hmaps).aestronglyMeasurable measurableSet_Ioi
  -- Domination by an integrable exponential.
  let b : ℝ := π * (u + 2)
  have hb : 0 < b := by
    have hπ : 0 < π := Real.pi_pos
    have : 0 < u + 2 := by linarith
    exact mul_pos hπ this
  have hExp :
      IntegrableOn (fun t : ℝ => C₀ * Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume := by
    have hExp' : IntegrableOn (fun t : ℝ => Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume :=
      exp_neg_integrableOn_Ioi 1 hb
    simpa [mul_assoc] using hExp'.const_mul C₀
  have hDom :
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi (1 : ℝ))),
        ‖Φ₆' u ((t : ℂ) * Complex.I)‖ ≤ C₀ * Real.exp (-b * t) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 <| .of_forall ?_
    intro t ht
    have ht0 : 0 < t := lt_trans (by norm_num) ht
    -- Work in `ℍ` with `z = i*t`.
    let zH : ℍ := ⟨(t : ℂ) * Complex.I, by simpa using ht0⟩
    have hz_im : zH.im = t := by simp [zH, UpperHalfPlane.im]
    have hz_half : (1 / 2 : ℝ) < zH.im := by
      have : (1 / 2 : ℝ) < t := lt_trans (by norm_num) ht
      simpa [hz_im] using this
    have hφ₀ : ‖φ₀ zH‖ ≤ C₀ * Real.exp (-2 * π * zH.im) := hC₀ zH hz_half
    have hφ₀'' : ‖φ₀'' (zH : ℂ)‖ ≤ C₀ * Real.exp (-2 * π * zH.im) := by
      simpa [φ₀''_coe_upperHalfPlane] using hφ₀
    set expTerm : ℂ :=
      cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I))
    have hExpNorm :
        ‖expTerm‖ = Real.exp (-π * u * t) := by
      -- The exponent is the real number `-(π*u*t)`.
      have hexp :
          expTerm = (Real.exp (-π * u * t) : ℂ) := by
        dsimp [expTerm]
        ring_nf
        simp [Complex.ofReal_exp]
      calc
        ‖expTerm‖ = ‖(Real.exp (-π * u * t) : ℂ)‖ := by
            simp [hexp]
        _ = Real.exp (-π * u * t) := by
              -- `‖(r : ℂ)‖ = ‖r‖` and `‖r‖ = r` for `r ≥ 0`.
              rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hExpLe : ‖expTerm‖ ≤ Real.exp (-π * u * t) := by
      simp [hExpNorm]
    have hF :
        ‖Φ₆' u ((t : ℂ) * Complex.I)‖ ≤
          (C₀ * Real.exp (-2 * π * t)) * Real.exp (-π * u * t) := by
      -- Unfold `Φ₆'` and apply the two bounds.
      have : ‖Φ₆' u ((t : ℂ) * Complex.I)‖ =
          ‖φ₀'' ((t : ℂ) * Complex.I) * expTerm‖ := by
        simp [MagicFunction.a.ComplexIntegrands.Φ₆', expTerm]
      rw [this]
      have hmul := norm_mul_le (φ₀'' ((t : ℂ) * Complex.I)) expTerm
      -- Replace `φ₀''` bound and the exponential norm.
      have hφ' : ‖φ₀'' ((t : ℂ) * Complex.I)‖ ≤ C₀ * Real.exp (-2 * π * t) := by
        simpa [hz_im, zH] using hφ₀''
      calc
        ‖φ₀'' ((t : ℂ) * Complex.I) * expTerm‖
            ≤ ‖φ₀'' ((t : ℂ) * Complex.I)‖ *
                ‖expTerm‖ := hmul
        _ ≤ (C₀ * Real.exp (-2 * π * t)) * Real.exp (-π * u * t) := by
              gcongr
    -- Combine the exponentials into `exp(-b*t)` (with `b = π*(u+2)`).
    have hcomb :
        (C₀ : ℝ) * Real.exp (-(2 * π * t)) * Real.exp (-(π * u * t)) =
          (C₀ : ℝ) * Real.exp (-b * t) := by
      have hsum : (-(2 * π * t)) + (-(π * u * t)) = (-b * t) := by
        dsimp [b]
        ring_nf
      calc
        (C₀ : ℝ) * Real.exp (-(2 * π * t)) * Real.exp (-(π * u * t))
            = (C₀ : ℝ) * (Real.exp (-(2 * π * t)) * Real.exp (-(π * u * t))) := by ring
        _ = (C₀ : ℝ) * Real.exp ((-(2 * π * t)) + (-(π * u * t))) := by simp [Real.exp_add]
        _ = (C₀ : ℝ) * Real.exp (-b * t) := by
              simp [hsum]
    have hF' :
        ‖Φ₆' u ((t : ℂ) * Complex.I)‖ ≤
          (C₀ : ℝ) * Real.exp (-(2 * π * t)) * Real.exp (-(π * u * t)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hF
    -- Rewrite the RHS using `hcomb`.
    exact hF'.trans_eq hcomb
  have hDomInt :
      Integrable (fun t : ℝ => (C₀ : ℝ) * Real.exp (-b * t))
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (by simpa [IntegrableOn] using hExp)
  have hInt :
      Integrable (fun t : ℝ => Φ₆' u ((t : ℂ) * Complex.I))
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
    MeasureTheory.Integrable.mono' (μ := volume.restrict (Set.Ioi (1 : ℝ))) hDomInt hMeas hDom
  simpa [IntegrableOn] using hInt

/-- Integrability of `Φ₅'` on the imaginary-axis tail `t > 1`, via `aLaplaceIntegrand`. -/
public lemma integrableOn_Φ₅'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
  have hLap : IntegrableOn (fun t : ℝ => aLaplaceIntegrand u t) (Set.Ioi (0 : ℝ)) volume :=
    aLaplaceIntegral_convergent (u := u) hu
  have hNeg : IntegrableOn (fun t : ℝ => -aLaplaceIntegrand u t) (Set.Ioi (1 : ℝ)) volume := by
    refine (hLap.mono_set ?_).neg
    intro t ht
    exact lt_trans (by norm_num : (0 : ℝ) < 1) ht
  refine hNeg.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := lt_trans (by norm_num) ht
  simpa using (Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand (u := u) (t := t)).symm

/-- Integrability of `Φ₂'` on the imaginary-axis bounded interval `(1,A]`. -/
lemma integrableOn_Φ₂'_imag_axis_Ioc (u A : ℝ) :
    IntegrableOn (fun t : ℝ => Φ₂' u ((t : ℂ) * I)) (Set.Ioc (1 : ℝ) A) volume := by
  have hcontΦ2 : ContinuousOn (Φ₂' u) {z : ℂ | 0 < z.im} :=
    (MagicFunction.a.ComplexIntegrands.Φ₁'_contDiffOn_ℂ (r := u)).continuousOn
  have hIcc : IntegrableOn (fun t : ℝ => Φ₂' u ((t : ℂ) * I)) (Set.Icc (1 : ℝ) A) volume := by
    have hmulIcc : ContinuousOn (fun t : ℝ => ((t : ℂ) * I : ℂ)) (Set.Icc (1 : ℝ) A) := by
      simpa using (by
        have : Continuous (fun t : ℝ => ((t : ℂ) * I : ℂ)) := by fun_prop
        exact this.continuousOn)
    have hmapsIcc :
        Set.MapsTo (fun t : ℝ => ((t : ℂ) * I : ℂ)) (Set.Icc (1 : ℝ) A) {z : ℂ | 0 < z.im} := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
      simpa using ht0
    exact (hcontΦ2.comp hmulIcc hmapsIcc).integrableOn_compact isCompact_Icc
  exact hIcc.mono_set Set.Ioc_subset_Icc_self

/-- Measurability of the imaginary-axis tail integrand `t ↦ Φ₂' u (tI)` on `t > A`. -/
lemma aestronglyMeasurable_Φ₂'_imag_axis_Ioi (u A : ℝ) (hA0 : 0 < A) :
    AEStronglyMeasurable (fun t : ℝ => Φ₂' u ((t : ℂ) * Complex.I))
      (volume.restrict (Set.Ioi A)) := by
  have hcontΦ2 : ContinuousOn (Φ₂' u) {z : ℂ | 0 < z.im} :=
    (MagicFunction.a.ComplexIntegrands.Φ₁'_contDiffOn_ℂ (r := u)).continuousOn
  refine (hcontΦ2.comp ?_ ?_).aestronglyMeasurable measurableSet_Ioi
  · simpa using (by
      have : Continuous (fun t : ℝ => ((t : ℂ) * Complex.I : ℂ)) := by fun_prop
      exact this.continuousOn)
  · intro t ht
    have ht0 : 0 < t := lt_trans hA0 ht
    simpa using ht0

/-- Modular-growth bound for `‖φ₀(S•w)‖‖w‖^2` depending only on `t = Im w`. -/
public lemma norm_phi0S_mul_sq_le {t : ℝ} (wH : ℍ) (hw_im : wH.im = t)
    {Cφ Aφ C₀ : ℝ}
    (hC₀_pos : 0 < C₀)
    (hC₀ :
      ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd :
      ∀ z : ℍ, Aφ ≤ z.im →
        ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
          ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
  (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t) (hw_norm : ‖(wH : ℂ)‖ ≤ 2 * t) :
    ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
  have hwpos : 0 < t := by
    have hwpos' : 0 < wH.im := wH.im_pos
    simpa [hw_im] using hwpos'
  have ht_nonneg : 0 ≤ t := le_of_lt hwpos
  have hwH_im : wH.im = t := hw_im
  have hφ2 : ‖φ₂' wH‖ ≤ Cφ * Real.exp (2 * π * t) := by
    have : Aφ ≤ wH.im := by simpa [hwH_im] using htAφ
    simpa [hwH_im] using (hφbd wH this).1
  have hφ4 : ‖φ₄' wH‖ ≤ Cφ * Real.exp (2 * π * t) := by
    have : Aφ ≤ wH.im := by simpa [hwH_im] using htAφ
    simpa [hwH_im] using (hφbd wH this).2
  have hφ0 : ‖φ₀ wH‖ ≤ C₀ := by
    have hhalf : (1 / 2 : ℝ) < wH.im := by
      have : (1 / 2 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht1
      simpa [hwH_im] using this
    have hφ0' := hC₀ wH hhalf
    have hexp : Real.exp (-2 * π * wH.im) ≤ 1 := by
      have : (-2 * π * wH.im) ≤ 0 := by
        have : 0 ≤ wH.im := le_of_lt wH.im_pos
        nlinarith [Real.pi_pos, this]
      simpa using (Real.exp_le_one_iff.2 this)
    have : C₀ * Real.exp (-2 * π * wH.im) ≤ C₀ :=
      mul_le_of_le_one_right hC₀_pos.le hexp
    exact hφ0'.trans this
  have hw2 : ‖(wH : ℂ) ^ (2 : ℕ)‖ ≤ (2 * t) ^ (2 : ℕ) := by
    simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hw_norm (2 : ℕ)
  have htri :
      ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
        ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ +
          ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖ +
            ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖ := by
    have hS := φ₀_S_transform_mul_sq (w := wH)
    have : φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ)) =
        φ₀ wH * ((wH : ℂ) ^ (2 : ℕ)) -
          (12 * Complex.I) / π * (wH : ℂ) * φ₂' wH -
            (36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH := by
      simpa using hS
    calc
        ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ =
            ‖(φ₀ wH * ((wH : ℂ) ^ (2 : ℕ)) -
                  (12 * Complex.I) / π * (wH : ℂ) * φ₂' wH) -
                (36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖ := by
              exact congrArg (fun z : ℂ => ‖z‖) this
      _ ≤ ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ)) -
                (12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖ +
            ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖ := by
            exact norm_sub_le _ _
        _ ≤ (‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ +
                  ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖) +
              ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖ := by
              have hab :
                  ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ)) -
                        (12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖ ≤
                    ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ +
                      ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖ :=
                norm_sub_le _ _
              have hab' :=
                add_le_add_left hab (‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖)
              simpa [add_assoc, add_comm, add_left_comm] using hab'
      _ = ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ +
            ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖ +
              ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖ := by ring
  have hexp_ge : (1 : ℝ) ≤ Real.exp (2 * π * t) := by
    have h2pi : 0 ≤ (2 : ℝ) * π := mul_nonneg (by norm_num) Real.pi_pos.le
    have : 0 ≤ (2 : ℝ) * π * t := mul_nonneg h2pi ht_nonneg
    have : 0 ≤ 2 * π * t := by simpa [mul_assoc] using this
    simpa using (Real.one_le_exp_iff.2 this)
  have hA :
      ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
        (4 * C₀) * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
    calc
      ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
          ‖φ₀ wH‖ * ‖(wH : ℂ) ^ (2 : ℕ)‖ := by
        exact norm_mul_le (φ₀ wH) ((wH : ℂ) ^ (2 : ℕ))
      _ ≤ C₀ * (2 * t) ^ (2 : ℕ) := by
        exact mul_le_mul hφ0 hw2 (norm_nonneg _) hC₀_pos.le
      _ = (4 * C₀) * (t ^ (2 : ℕ)) := by ring
      _ ≤ (4 * C₀) * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
        have ht2_nonneg : 0 ≤ t ^ (2 : ℕ) := pow_nonneg ht_nonneg _
        have ht2_le : t ^ (2 : ℕ) ≤ t ^ (2 : ℕ) * Real.exp (2 * π * t) := by
          have := mul_le_mul_of_nonneg_left hexp_ge ht2_nonneg
          simpa [one_mul, mul_assoc] using this
        have hC0' : 0 ≤ 4 * C₀ := mul_nonneg (by norm_num) hC₀_pos.le
        exact mul_le_mul_of_nonneg_left ht2_le hC0'
  have hB :
      ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖ ≤
        (2 * c12π * Cφ) * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
    have ht_le : t ≤ t ^ (2 : ℕ) := by
      have : (0 : ℝ) ≤ t := le_trans (by norm_num) ht1
      have ht := mul_le_mul_of_nonneg_left ht1 this
      simpa [pow_two, mul_assoc] using ht
    have hY_nonneg : 0 ≤ Cφ * Real.exp (2 * π * t) := le_trans (norm_nonneg _) hφ2
    calc
      ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖ ≤
          (c12π * ‖(wH : ℂ)‖) * ‖φ₂' wH‖ := by
        -- Two applications of `‖ab‖ ≤ ‖a‖‖b‖`.
        have h1 :
            ‖((12 * Complex.I) / (π : ℂ) * (wH : ℂ)) * φ₂' wH‖ ≤
              ‖(12 * Complex.I) / (π : ℂ) * (wH : ℂ)‖ * ‖φ₂' wH‖ := by
          exact norm_mul_le (((12 * Complex.I) / (π : ℂ)) * (wH : ℂ)) (φ₂' wH)
        have h2 :
            ‖(12 * Complex.I) / (π : ℂ) * (wH : ℂ)‖ ≤
              c12π * ‖(wH : ℂ)‖ := by
          exact norm_mul_le ((12 * Complex.I) / (π : ℂ)) (wH : ℂ)
        have h2' :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg (φ₂' wH))
        -- Normalize associativity.
        have hmul : ‖(12 * Complex.I) / (π : ℂ) * (wH : ℂ)‖ * ‖φ₂' wH‖ ≤
            (c12π * ‖(wH : ℂ)‖) * ‖φ₂' wH‖ := by
          exact h2'
        -- Chain the bounds.
        exact le_trans h1 hmul
      _ ≤ (c12π * (2 * t)) * (Cφ * Real.exp (2 * π * t)) := by
        -- First use `‖φ₂'‖ ≤ Cφ*exp`, then `‖w‖ ≤ 2t`.
        have hφ :
            (c12π * ‖(wH : ℂ)‖) * ‖φ₂' wH‖ ≤
              (c12π * ‖(wH : ℂ)‖) * (Cφ * Real.exp (2 * π * t)) := by
          have hcoeff_nonneg : 0 ≤ c12π * ‖(wH : ℂ)‖ :=
            mul_nonneg (norm_nonneg _) (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left hφ2 hcoeff_nonneg
        have hw' :
            c12π * ‖(wH : ℂ)‖ ≤ c12π * (2 * t) :=
          mul_le_mul_of_nonneg_left hw_norm (norm_nonneg _)
        have hw'' :=
          mul_le_mul_of_nonneg_right hw' hY_nonneg
        have hw''' :
            (c12π * ‖(wH : ℂ)‖) * (Cφ * Real.exp (2 * π * t)) ≤
              (c12π * (2 * t)) * (Cφ * Real.exp (2 * π * t)) := by
          simpa [mul_assoc] using hw''
        exact le_trans hφ hw'''
      _ ≤ (2 * c12π * Cφ) * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
        -- Use `t ≤ t^2` (since `t ≥ 1`) and `0 ≤ Cφ*exp`.
        have htY :
            t * (Cφ * Real.exp (2 * π * t)) ≤
              t ^ (2 : ℕ) * (Cφ * Real.exp (2 * π * t)) := by
          have := mul_le_mul_of_nonneg_right ht_le hY_nonneg
          simpa [pow_two, mul_assoc] using this
        have hpiabs_pos : 0 < |(π : ℝ)| := by
          simpa [abs_of_pos Real.pi_pos] using Real.pi_pos
        have h12pi_nonneg : 0 ≤ (12 : ℝ) / |(π : ℝ)| :=
          div_nonneg (by norm_num) hpiabs_pos.le
        have hcoeff_nonneg : 0 ≤ (2 : ℝ) * ((12 : ℝ) / |(π : ℝ)|) :=
          mul_nonneg (by norm_num) h12pi_nonneg
        have hmain := mul_le_mul_of_nonneg_left htY hcoeff_nonneg
        -- Rewrite both sides to isolate `t*(Cφ*exp)` and apply `htY`.
        simpa [mul_assoc, mul_left_comm, mul_comm, pow_two] using hmain
  have hC :
      ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖ ≤
        c36π2 * Cφ * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
    have hY_nonneg : 0 ≤ Cφ * Real.exp (2 * π * t) := le_trans (norm_nonneg _) hφ4
    have ht2 : (1 : ℝ) ≤ t ^ (2 : ℕ) := one_le_pow₀ (show (1 : ℝ) ≤ t from ht1)
    calc
      ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖ ≤
          c36π2 * ‖φ₄' wH‖ := by
        exact norm_mul_le ((36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) (φ₄' wH)
      _ ≤ c36π2 * (Cφ * Real.exp (2 * π * t)) := by
        -- Multiply the bound `‖φ₄'‖ ≤ Cφ*exp`.
        have hmul :=
          mul_le_mul_of_nonneg_left hφ4
            (a := c36π2) (norm_nonneg _)
        simpa [mul_assoc] using hmul
      _ ≤ c36π2 * Cφ * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
        -- Use `1 ≤ t^2` and `0 ≤ Cφ*exp`.
        have hY :
            Cφ * Real.exp (2 * π * t) ≤ t ^ (2 : ℕ) * (Cφ * Real.exp (2 * π * t)) := by
          have := mul_le_mul_of_nonneg_right ht2 hY_nonneg
          simpa [one_mul, mul_assoc] using this
        have hn_nonneg : 0 ≤ c36π2 := norm_nonneg _
        have hn := mul_le_mul_of_nonneg_left hY hn_nonneg
        -- Normalize the product layout.
        have hrew :
            c36π2 * (t ^ (2 : ℕ) * (Cφ * Real.exp (2 * π * t))) =
              c36π2 * Cφ * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
          ring
        exact le_trans hn (le_of_eq hrew)
  have hsum :
      (4 * C₀) + (2 * c12π * Cφ) + (c36π2 * Cφ) ≤
        (4 * C₀ + (2 * c12π + c36π2) * Cφ) := by
    ring_nf
    nlinarith
  have htot := (le_trans htri (add_le_add (add_le_add hA hB) hC))
  -- Factor out `t^2 * exp(2πt)` and compare coefficients.
  let X : ℝ := t ^ (2 : ℕ) * Real.exp (2 * π * t)
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg (pow_nonneg ht_nonneg _) (Real.exp_pos _).le
  let K : ℝ :=
    4 * C₀ +
      (2 * c12π + c36π2) * Cφ
  have hcoeff_mul :
      ((4 * C₀) + (2 * c12π * Cφ) + (c36π2 * Cφ)) * X ≤ K * X := by
    simpa [K, mul_assoc, add_assoc, add_comm, add_left_comm] using
      (mul_le_mul_of_nonneg_right hsum hX_nonneg)
  have hsum_bound :
      (4 * C₀) * X + (2 * ‖(12 * (Complex.I : ℂ)) / (π : ℂ)‖ * Cφ) * X +
            (‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖ * Cφ) * X ≤
        K * X := by
    calc
      (4 * C₀) * X + (2 * ‖(12 * (Complex.I : ℂ)) / (π : ℂ)‖ * Cφ) * X +
            (‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖ * Cφ) * X =
          ((4 * C₀) + (2 * ‖(12 * (Complex.I : ℂ)) / (π : ℂ)‖ * Cφ) +
                (‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖ * Cφ)) * X := by ring
      _ ≤ K * X := hcoeff_mul
  -- Rewrite `htot` in terms of `X` and finish.
  have htot' :
      ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
        (4 * C₀) * X + (2 * ‖(12 * (Complex.I : ℂ)) / (π : ℂ)‖ * Cφ) * X +
            (‖(36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))‖ * Cφ) * X := by
    simpa [X, mul_assoc, add_assoc, add_comm, add_left_comm] using htot
  exact le_trans htot' (by simpa [X, K] using hsum_bound)

/-- Pointwise bound for `‖Φ₂' u (tI)‖` on the tail `t ≥ 1`. -/
lemma norm_Φ₂'_imag_axis_le {u t : ℝ} {Cφ Aφ C₀ : ℝ}
    (hC₀_pos : 0 < C₀)
    (hC₀ :
      ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd :
      ∀ z : ℍ, Aφ ≤ z.im →
        ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
          ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (ht1 : (1 : ℝ) ≤ t) (htAφ : Aφ ≤ t) :
    ‖Φ₂' u ((t : ℂ) * I)‖ ≤
      (4 * C₀ + (2 * c12π + c36π2) * Cφ) *
        (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
  let a : ℝ := π * (u - 2)
  let K : ℝ :=
    4 * C₀ +
      (2 * c12π + c36π2) * Cφ
  -- Set `w = tI + 1` and work in `ℍ`.
  let w : ℂ := (t : ℂ) * I + 1
  have hwpos : 0 < w.im := by simpa [w] using ht0
  let wH : ℍ := ⟨w, hwpos⟩
  have hwH_im : wH.im = t := by simp [wH, w, UpperHalfPlane.im]
  -- Bound `‖w‖` by `2*t` (since `t ≥ 1`).
  have hw_norm_w : ‖w‖ ≤ 2 * t := by
    have h1 : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
    have hIt : ‖(t : ℂ) * Complex.I‖ = t := by
      calc
        ‖(t : ℂ) * Complex.I‖ = ‖(t : ℂ)‖ * ‖(Complex.I : ℂ)‖ := by
            simp
        _ = ‖t‖ := by simp [Complex.norm_real]
        _ = t := by simp [Real.norm_of_nonneg (le_of_lt ht0)]
    have h0 : ‖w‖ ≤ ‖(t : ℂ) * Complex.I‖ + ‖(1 : ℂ)‖ := by
      simpa [w] using (norm_add_le ((t : ℂ) * Complex.I) (1 : ℂ))
    have htri : ‖w‖ ≤ t + 1 := by
      calc
        ‖w‖ ≤ ‖(t : ℂ) * Complex.I‖ + ‖(1 : ℂ)‖ := h0
        _ = t + 1 := by
          rw [hIt, h1]
    have : t + 1 ≤ 2 * t := by linarith
    exact le_trans htri this
  have hw_norm : ‖(wH : ℂ)‖ ≤ 2 * t := by simpa [wH] using hw_norm_w
  have hmod :
      ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
        K * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
    simpa [K] using
      (norm_phi0S_mul_sq_le (t := t) wH hwH_im (Cφ := Cφ) (Aφ := Aφ) (C₀ := C₀)
        hC₀_pos hC₀ hφbd ht1 htAφ hw_norm)
  -- Exponential factor on the imaginary axis.
  have hExpNorm :
      ‖cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I))‖ =
        Real.exp (-π * u * t) := by
    have hexp :
        cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
          (Real.exp (-π * u * t) : ℂ) := by
      ring_nf
      simp [Complex.ofReal_exp]
    calc
      ‖cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I))‖ =
          ‖(Real.exp (-π * u * t) : ℂ)‖ := by
            simp [hexp]
      _ = Real.exp (-π * u * t) := by
            rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hExpRew :
      Real.exp (2 * π * t) * Real.exp (-π * u * t) = Real.exp (-a * t) := by
    simpa [a, mul_assoc, mul_left_comm, mul_comm] using
      (MagicFunction.g.CohnElkies.IntegralReps.exp_two_pi_mul_mul_exp_neg_pi_mul (u := u) (t := t))
  have hΦ :
      ‖Φ₂' u ((t : ℂ) * I)‖ ≤ K * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
    have hdef :
        Φ₂' u ((t : ℂ) * I) =
          (φ₀'' ((-1 : ℂ) / (((t : ℂ) * I) + 1)) * (((t : ℂ) * I + 1) ^ (2 : ℕ))) *
            cexp ((π : ℂ) * I * (u : ℂ) * ((t : ℂ) * I)) := by
      simp [MagicFunction.a.ComplexIntegrands.Φ₂', MagicFunction.a.ComplexIntegrands.Φ₁',
        mul_assoc]
    have hw' : (wH : ℂ) = ((t : ℂ) * I + 1) := by
      simp [wH, w]
    have hphi0S :
        φ₀'' ((-1 : ℂ) / (((t : ℂ) * I) + 1)) * (((t : ℂ) * I + 1) ^ (2 : ℕ)) =
          φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ)) := by
      have hwS : φ₀ (ModularGroup.S • wH) = φ₀'' ((ModularGroup.S • wH : ℍ) : ℂ) := by
        simp
      have harg : ((ModularGroup.S • wH : ℍ) : ℂ) = (-1 : ℂ) / (wH : ℂ) := by
        simpa using (ModularGroup.coe_S_smul (z := wH))
      -- Rewrite everything to the common form `φ₀'' (-1 / wH) * (wH^2)`.
      rw [hw'.symm]
      rw [hwS]
      rw [harg]
    calc
      ‖Φ₂' u ((t : ℂ) * I)‖ =
          ‖(φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))) *
                cexp ((π : ℂ) * I * (u : ℂ) * ((t : ℂ) * I))‖ := by
            simp [hdef, hphi0S, mul_assoc]
      _ ≤ ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ *
            ‖cexp ((π : ℂ) * I * (u : ℂ) * ((t : ℂ) * I))‖ := by
            exact norm_mul_le _ _
      _ =
          ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ *
            Real.exp (-π * u * t) := by
            simp [hExpNorm]
      _ ≤ (K * (t ^ (2 : ℕ) * Real.exp (2 * π * t))) * Real.exp (-π * u * t) := by
            exact mul_le_mul_of_nonneg_right hmod (Real.exp_pos _).le
      _ = K * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
            calc
              (K * (t ^ (2 : ℕ) * Real.exp (2 * π * t))) * Real.exp (-π * u * t) =
                  K * (t ^ (2 : ℕ) * (Real.exp (2 * π * t) * Real.exp (-π * u * t))) := by
                    ring
              _ = K * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
                    simpa using congrArg (fun x => K * (t ^ (2 : ℕ) * x)) hExpRew
  simpa [K, a, mul_assoc] using hΦ

/-- Integrability of `Φ₂'` on the imaginary-axis tail `(A,∞)` using modular bounds. -/
lemma integrableOn_Φ₂'_imag_axis_Ioi {u : ℝ} (hu : 2 < u) {Cφ Aφ C₀ A : ℝ}
    (hC₀_pos : 0 < C₀)
    (hC₀ :
      ∀ z : ℍ, (1 / 2 : ℝ) < z.im → ‖φ₀ z‖ ≤ C₀ * Real.exp (-2 * π * z.im))
    (hφbd :
      ∀ z : ℍ, Aφ ≤ z.im →
        ‖φ₂' z‖ ≤ Cφ * Real.exp (2 * π * z.im) ∧
          ‖φ₄' z‖ ≤ Cφ * Real.exp (2 * π * z.im))
    (hA1 : (1 : ℝ) ≤ A) (hAA : Aφ ≤ A) :
    IntegrableOn (fun t : ℝ => Φ₂' u ((t : ℂ) * I)) (Set.Ioi A) volume := by
  have hMeas :
      AEStronglyMeasurable (fun t : ℝ => Φ₂' u ((t : ℂ) * I))
        (volume.restrict (Set.Ioi A)) :=
    aestronglyMeasurable_Φ₂'_imag_axis_Ioi u A (lt_of_lt_of_le (by norm_num) hA1)
  let a : ℝ := π * (u - 2)
  have ha : 0 < a := by
    have hπ : 0 < π := Real.pi_pos
    exact mul_pos hπ (sub_pos.mpr hu)
  let K : ℝ :=
    4 * C₀ + (2 * c12π + c36π2) * Cφ
  have hdomReal :
      Integrable (fun t : ℝ => K * (t ^ (2 : ℕ) * Real.exp (-a * t)))
        (volume.restrict (Set.Ioi A)) := by
    simpa [IntegrableOn, mul_assoc] using (integrableOn_sq_mul_exp_neg A a ha).const_mul K
  have hdom :
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioi A)),
        ‖Φ₂' u ((t : ℂ) * I)‖ ≤ K * (t ^ (2 : ℕ) * Real.exp (-a * t)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 <| .of_forall ?_
    intro t ht
    have ht1 : 1 ≤ t := le_trans hA1 (le_of_lt ht)
    have htAφ : Aφ ≤ t := le_trans hAA (le_of_lt ht)
    simpa [K, a] using
      (norm_Φ₂'_imag_axis_le (u := u) (t := t) (Cφ := Cφ) (Aφ := Aφ) (C₀ := C₀)
        hC₀_pos hC₀ hφbd ht1 htAφ)
  -- `IntegrableOn` is definitional: reduce to `Integrable` on a restricted measure.
  change Integrable (fun t : ℝ => Φ₂' u ((t : ℂ) * Complex.I)) (volume.restrict (Set.Ioi A))
  exact MeasureTheory.Integrable.mono' (μ := volume.restrict (Set.Ioi A)) hdomReal hMeas hdom

/-- Integrability of `Φ₂'` on the imaginary-axis tail `t > 1`. -/
public lemma integrableOn_Φ₂'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₂' u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
  rcases exists_phi2'_phi4'_bound_exp with ⟨Cφ, Aφ, hCφ, hφbd⟩
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  let A : ℝ := max 1 Aφ
  have hA1 : (1 : ℝ) ≤ A := le_max_left _ _
  have hAA : Aφ ≤ A := le_max_right _ _
  have hmid :
      IntegrableOn (fun t : ℝ => Φ₂' u ((t : ℂ) * Complex.I)) (Set.Ioc (1 : ℝ) A) volume :=
    integrableOn_Φ₂'_imag_axis_Ioc u A
  have hbig :
      IntegrableOn (fun t : ℝ => Φ₂' u ((t : ℂ) * Complex.I)) (Set.Ioi A) volume :=
    integrableOn_Φ₂'_imag_axis_Ioi (u := u) hu (Cφ := Cφ) (Aφ := Aφ) (C₀ := C₀) (A := A)
      hC₀_pos hC₀ hφbd hA1 hAA
  have hsplit : Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) A ∪ Set.Ioi A :=
    (Set.Ioc_union_Ioi_eq_Ioi (a := (1 : ℝ)) (b := A) hA1).symm
  simpa [hsplit] using hmid.union hbig

/--
Integrability of `Φ₄'` on the imaginary-axis tail `t > 1`, via the finite-difference identity.
-/
public lemma integrableOn_Φ₄'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₄' u ((t : ℂ) * I)) (Set.Ioi (1 : ℝ)) volume := by
  -- Use `Φ₂' - 2 Φ₅' + Φ₄' = 2 Φ₆'` on the imaginary axis and solve for `Φ₄'`.
  have h6 :
      IntegrableOn
        (fun t : ℝ => (2 : ℂ) * Φ₆' u ((t : ℂ) * I)) (Set.Ioi (1 : ℝ)) volume :=
    by
    simpa [mul_assoc] using (integrableOn_Φ₆'_imag_axis (u := u) hu).const_mul (2 : ℂ)
  have h2 : IntegrableOn (fun t : ℝ => Φ₂' u ((t : ℂ) * I)) (Set.Ioi (1 : ℝ)) volume :=
    integrableOn_Φ₂'_imag_axis (u := u) hu
  have h5 :
      IntegrableOn
        (fun t : ℝ => (2 : ℂ) * Φ₅' u ((t : ℂ) * I)) (Set.Ioi (1 : ℝ)) volume :=
    by
    simpa [mul_assoc] using (integrableOn_Φ₅'_imag_axis (u := u) hu).const_mul (2 : ℂ)
  have hcomb :
      IntegrableOn
        (fun t : ℝ =>
          (2 : ℂ) * Φ₆' u ((t : ℂ) * I) - Φ₂' u ((t : ℂ) * I) +
            (2 : ℂ) * Φ₅' u ((t : ℂ) * I))
        (Set.Ioi (1 : ℝ)) volume := by
    exact (h6.sub h2).add h5
  refine hcomb.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1) ht
  have hfd := Φ_finite_difference_imag_axis (u := u) (t := t) ht0
  -- Rearrange `Φ₂' - 2 Φ₅' + Φ₄' = 2 Φ₆'` to solve for `Φ₄'`.
  have h :=
    congrArg
      (fun z : ℂ => z - (Φ₂' u ((t : ℂ) * I) - 2 * Φ₅' u ((t : ℂ) * I))) hfd
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc] using h.symm

/--
Rewrite the vertical-segment part `I₁' + I₃' + I₅'` as the imaginary-axis segment integral of
`Φ₅'`.
-/
public lemma I₁'_add_I₃'_add_I₅'_eq_imag_axis (u : ℝ) :
    MagicFunction.a.RealIntegrals.I₁' u + MagicFunction.a.RealIntegrals.I₃' u +
        MagicFunction.a.RealIntegrals.I₅' u =
      (I : ℂ) *
        ((Complex.exp (((π * u : ℝ) : ℂ) * I) +
              Complex.exp (-(((π * u : ℝ) : ℂ) * I)) - (2 : ℂ)) *
            (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I))) := by
  -- Common abbreviation for the imaginary-axis segment integral.
  let V0 : ℂ := ∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I)
  have hV0 : V0 = ∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I) := rfl
  have hI1 :
      MagicFunction.a.RealIntegrals.I₁' u =
        (I : ℂ) * Complex.exp (-(((π * u : ℝ) : ℂ) * I)) * V0 := by
    -- Unfold `I₁'` and rewrite the parametrisation `z₁' t = -1 + i t`.
    have hparam :
        (∫ t in (0 : ℝ)..1,
              (I : ℂ) * Φ₁' u (MagicFunction.Parametrisations.z₁' t)) =
            ∫ t in (0 : ℝ)..1,
              (I : ℂ) * Φ₁' u ((-1 : ℂ) + (t : ℂ) * I) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have h01 : (0 : ℝ) ≤ 1 := by norm_num
      have hmem : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le h01] using ht
      simp [MagicFunction.Parametrisations.z₁'_eq_of_mem hmem, mul_comm, add_comm]
    -- Apply the shift identity and pull the constants out of the integral.
    have hshift :
        (∫ t in (0 : ℝ)..1, (I : ℂ) * Φ₁' u ((-1 : ℂ) + (t : ℂ) * I)) =
          (I : ℂ) * Complex.exp (-(((π * u : ℝ) : ℂ) * I)) *
            (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I)) := by
      calc
        (∫ t in (0 : ℝ)..1, (I : ℂ) * Φ₁' u ((-1 : ℂ) + (t : ℂ) * I)) =
            ∫ t in (0 : ℝ)..1,
              (I : ℂ) *
                (Complex.exp (-(((π * u : ℝ) : ℂ) * I)) * Φ₅' u ((t : ℂ) * I)) := by
              refine intervalIntegral.integral_congr ?_
              intro t ht
              simp [Φ₁'_shift_left (u := u) (t := t), mul_assoc]
        _ = (I : ℂ) * Complex.exp (-(((π * u : ℝ) : ℂ) * I)) *
              (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I)) := by
              simp [mul_assoc]
    -- Finish by unfolding `I₁'`/`Φ₁` and rewriting `V0`.
    simpa
        [MagicFunction.a.RealIntegrals.I₁', MagicFunction.a.RealIntegrands.Φ₁, hV0, mul_assoc]
      using hparam.trans hshift
  have hI3 :
      MagicFunction.a.RealIntegrals.I₃' u =
        (I : ℂ) * Complex.exp (((π * u : ℝ) : ℂ) * I) * V0 := by
    have hparam :
        (∫ t in (0 : ℝ)..1,
              (I : ℂ) * Φ₃' u (MagicFunction.Parametrisations.z₃' t)) =
            ∫ t in (0 : ℝ)..1,
              (I : ℂ) * Φ₃' u ((1 : ℂ) + (t : ℂ) * I) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have h01 : (0 : ℝ) ≤ 1 := by norm_num
      have hmem : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le h01] using ht
      simp [MagicFunction.Parametrisations.z₃'_eq_of_mem hmem, mul_comm, add_comm]
    have hshift :
        (∫ t in (0 : ℝ)..1, (I : ℂ) * Φ₃' u ((1 : ℂ) + (t : ℂ) * I)) =
          (I : ℂ) * Complex.exp (((π * u : ℝ) : ℂ) * I) *
            (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I)) := by
      calc
        (∫ t in (0 : ℝ)..1, (I : ℂ) * Φ₃' u ((1 : ℂ) + (t : ℂ) * I)) =
            ∫ t in (0 : ℝ)..1,
              (I : ℂ) *
                (Complex.exp (((π * u : ℝ) : ℂ) * I) * Φ₅' u ((t : ℂ) * I)) := by
              refine intervalIntegral.integral_congr ?_
              intro t ht
              simp [Φ₃'_shift_right (u := u) (t := t), mul_assoc]
        _ = (I : ℂ) * Complex.exp (((π * u : ℝ) : ℂ) * I) *
              (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I)) := by
              simp [mul_assoc]
    simpa
        [MagicFunction.a.RealIntegrals.I₃', MagicFunction.a.RealIntegrands.Φ₃, hV0, mul_assoc]
      using hparam.trans hshift
  have hI5 : MagicFunction.a.RealIntegrals.I₅' u = (-2 : ℂ) * (I : ℂ) * V0 := by
    have hparam :
        (∫ t in (0 : ℝ)..1,
              (I : ℂ) * Φ₅' u (MagicFunction.Parametrisations.z₅' t)) =
            ∫ t in (0 : ℝ)..1, (I : ℂ) * Φ₅' u ((t : ℂ) * I) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have h01 : (0 : ℝ) ≤ 1 := by norm_num
      have hmem : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le h01] using ht
      simp [MagicFunction.Parametrisations.z₅'_eq_of_mem hmem, mul_comm]
    have hI :
        (∫ t in (0 : ℝ)..1, (I : ℂ) * Φ₅' u ((t : ℂ) * I)) =
          (I : ℂ) * (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I)) := by
      simp
    -- Unfold `I₅'`/`Φ₅` and rewrite `V0`.
    have h' :
        MagicFunction.a.RealIntegrals.I₅' u =
          (-2 : ℂ) *
            (∫ t in (0 : ℝ)..1, (I : ℂ) * Φ₅' u ((t : ℂ) * I)) := by
      simpa [MagicFunction.a.RealIntegrals.I₅', MagicFunction.a.RealIntegrands.Φ₅] using
        congrArg (fun z : ℂ => (-2 : ℂ) * z) hparam
    -- Pull out the remaining constant `I`, then rewrite the integral as `V0`.
    have hI' :
        (-2 : ℂ) *
            (∫ t in (0 : ℝ)..1, (I : ℂ) * Φ₅' u ((t : ℂ) * I)) =
          (-2 : ℂ) *
            ((I : ℂ) * (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I))) :=
      congrArg (fun z : ℂ => (-2 : ℂ) * z) hI
    have h'' :
        MagicFunction.a.RealIntegrals.I₅' u =
          (-2 : ℂ) * ((I : ℂ) * (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I))) :=
      h'.trans hI'
    calc
      MagicFunction.a.RealIntegrals.I₅' u =
          (-2 : ℂ) * ((I : ℂ) * (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * I))) := h''
      _ = (-2 : ℂ) * ((I : ℂ) * V0) := by
            simp [hV0]
      _ = (-2 : ℂ) * (I : ℂ) * V0 := by ring
  -- Assemble the three identities.
  have :
      MagicFunction.a.RealIntegrals.I₁' u + MagicFunction.a.RealIntegrals.I₃' u +
          MagicFunction.a.RealIntegrals.I₅' u =
        (I : ℂ) *
          ((Complex.exp (((π * u : ℝ) : ℂ) * I) +
                Complex.exp (-(((π * u : ℝ) : ℂ) * I)) - (2 : ℂ)) * V0) := by
    -- `ring` is fine here: only associative/commutative rearrangements.
    rw [hI1, hI3, hI5]
    ring
  simpa [hV0, mul_assoc] using this

end MagicFunction.g.CohnElkies.IntegralReps
