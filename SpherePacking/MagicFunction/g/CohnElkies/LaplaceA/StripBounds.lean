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
  rcases exists_bound_of_isBoundedAtImInfty (f := E₂) E₂_isBoundedAtImInfty with
    ⟨CE2, AE2, _, hE2⟩
  rcases exists_bound_of_isBoundedAtImInfty (f := fun z : ℍ => E₄ z)
      (by simpa using (ModularFormClass.bdd_at_infty E₄)) with ⟨CE4, AE4, _, hE4⟩
  rcases exists_bound_of_isBoundedAtImInfty (f := fun z : ℍ => E₆ z)
      (by simpa using (ModularFormClass.bdd_at_infty E₆)) with ⟨CE6, AE6, _, hE6⟩
  rcases exists_inv_Delta_bound_exp with ⟨CΔ, AΔ, hCΔ, hΔ⟩
  refine ⟨max 1 (max (CE4 ^ 2 * CΔ) (CE4 * (CE2 * CE4 + CE6) * CΔ)),
    max AΔ (max AE2 (max AE4 AE6)), by positivity, ?_⟩
  intro z hzA
  have hzΔ : AΔ ≤ z.im := (le_max_left _ _).trans hzA
  have hzE2 : AE2 ≤ z.im := ((le_max_left _ _).trans (le_max_right _ _)).trans hzA
  have hzE4 : AE4 ≤ z.im :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hzA
  have hzE6 : AE6 ≤ z.im :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hzA
  have hΔz : ‖(Δ z)⁻¹‖ ≤ CΔ * Real.exp (2 * π * z.im) := hΔ z hzΔ
  have hexp_pos : 0 ≤ Real.exp (2 * π * z.im) := (Real.exp_pos _).le
  refine ⟨?_, ?_⟩
  · -- `φ₂' = E₄ * (E₂*E₄ - E₆) / Δ`.
    have hcore : ‖(E₂ z) * (E₄ z) - (E₆ z)‖ ≤ CE2 * CE4 + CE6 := by
      calc ‖(E₂ z) * (E₄ z) - (E₆ z)‖
          ≤ ‖E₂ z‖ * ‖E₄ z‖ + ‖E₆ z‖ := by
            simpa [norm_mul] using norm_sub_le ((E₂ z) * (E₄ z)) (E₆ z)
        _ ≤ CE2 * CE4 + CE6 := by gcongr <;> [exact hE2 z hzE2; exact hE4 z hzE4; exact hE6 z hzE6]
    have hmul : ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z))‖ ≤ CE4 * (CE2 * CE4 + CE6) :=
      norm_mul_le_of_le (hE4 z hzE4) hcore
    have hφ2' : ‖φ₂' z‖ ≤ (CE4 * (CE2 * CE4 + CE6) * CΔ) * Real.exp (2 * π * z.im) := by
      calc ‖φ₂' z‖
          = ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z)) * (Δ z)⁻¹‖ := by
            simp [φ₂', div_eq_mul_inv, mul_assoc]
        _ ≤ ‖(E₄ z) * ((E₂ z) * (E₄ z) - (E₆ z))‖ * ‖(Δ z)⁻¹‖ := norm_mul_le _ _
        _ ≤ (CE4 * (CE2 * CE4 + CE6)) * (CΔ * Real.exp (2 * π * z.im)) :=
            mul_le_mul hmul hΔz (norm_nonneg _) (by positivity)
        _ = _ := by ring
    exact hφ2'.trans <| mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) hexp_pos
  · -- `φ₄' = (E₄^2) / Δ`.
    have hE4z : ‖E₄ z‖ ≤ CE4 := hE4 z hzE4
    have hφ4' : ‖φ₄' z‖ ≤ (CE4 ^ 2 * CΔ) * Real.exp (2 * π * z.im) := by
      calc ‖φ₄' z‖
          = ‖E₄ z‖ ^ 2 * ‖(Δ z)⁻¹‖ := by
            simp [φ₄', div_eq_mul_inv, pow_two]
        _ ≤ CE4 ^ 2 * (CΔ * Real.exp (2 * π * z.im)) := by
            gcongr
        _ = _ := by ring
    exact hφ4'.trans <| mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) hexp_pos

/-- A convenient form of `φ₀_S_transform`, clearing the denominators by multiplying by `z^2`. -/
public lemma φ₀_S_transform_mul_sq (w : ℍ) :
    φ₀ (ModularGroup.S • w) * ((w : ℂ) ^ (2 : ℕ)) =
        φ₀ w * ((w : ℂ) ^ (2 : ℕ)) - (12 * Complex.I) / π * (w : ℂ) * φ₂' w -
          (36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' w := by
  simpa using (_root_.φ₀_S_transform_mul_sq w)

/-- Integrability of `Φ₆'` on the imaginary axis tail `t > 1`. -/
lemma integrableOn_Φ₆'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₆' u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := MagicFunction.PolyFourierCoeffBound.norm_φ₀_le
  have hcontΦ6 : ContinuousOn (Φ₆' u) {z : ℂ | 0 < z.im} :=
    (MagicFunction.a.ComplexIntegrands.Φ₆'_contDiffOn_ℂ (r := u)).continuousOn
  have hmaps : Set.MapsTo (fun t : ℝ => ((t : ℂ) * Complex.I : ℂ)) (Set.Ioi (1 : ℝ))
      {z : ℂ | 0 < z.im} := fun t ht => by simpa using lt_trans (by norm_num : (0:ℝ) < 1) ht
  have hMeas : AEStronglyMeasurable (fun t : ℝ => Φ₆' u ((t : ℂ) * Complex.I))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (hcontΦ6.comp (by fun_prop) hmaps).aestronglyMeasurable measurableSet_Ioi
  set b : ℝ := π * (u + 2) with hb_def
  have hb : 0 < b := mul_pos Real.pi_pos (by linarith)
  have hExp : IntegrableOn (fun t : ℝ => C₀ * Real.exp (-b * t)) (Set.Ioi (1 : ℝ)) volume := by
    simpa [mul_assoc] using (exp_neg_integrableOn_Ioi 1 hb).const_mul C₀
  refine MeasureTheory.Integrable.mono'
    (by simpa [IntegrableOn] using hExp) hMeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 <| .of_forall fun t ht => ?_
  have ht0 : 0 < t := lt_trans (by norm_num) ht
  let zH : ℍ := ⟨(t : ℂ) * Complex.I, by simpa using ht0⟩
  have hz_im : zH.im = t := by simp [zH, UpperHalfPlane.im]
  have hφ₀'' : ‖φ₀'' (zH : ℂ)‖ ≤ C₀ * Real.exp (-2 * π * t) := by
    have := hC₀ zH (by simpa [hz_im] using lt_trans (by norm_num : (1/2:ℝ) < 1) ht)
    simpa [φ₀''_coe_upperHalfPlane, hz_im] using this
  have hExpEq : cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
      (Real.exp (-π * u * t) : ℂ) := by ring_nf; simp [Complex.ofReal_exp]
  have hExpLe : ‖cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I))‖ ≤
      Real.exp (-π * u * t) := by
    rw [hExpEq, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hF : ‖Φ₆' u ((t : ℂ) * Complex.I)‖ ≤
      (C₀ * Real.exp (-2 * π * t)) * Real.exp (-π * u * t) := by
    have : Φ₆' u ((t : ℂ) * Complex.I) = φ₀'' ((t : ℂ) * Complex.I) *
        cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) := by
      simp [MagicFunction.a.ComplexIntegrands.Φ₆']
    rw [this]
    exact norm_mul_le_of_le (by simpa [zH] using hφ₀'') hExpLe
  refine hF.trans ?_
  rw [mul_assoc, ← Real.exp_add]
  have : -2 * π * t + -π * u * t = -(b * t) := by dsimp [b]; ring
  rw [this]

/-- Integrability of `Φ₅'` on the imaginary-axis tail `t > 1`, via `aLaplaceIntegrand`. -/
public lemma integrableOn_Φ₅'_imag_axis {u : ℝ} (hu : 2 < u) :
    IntegrableOn (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
  have hNeg : IntegrableOn (fun t : ℝ => -aLaplaceIntegrand u t) (Set.Ioi (1 : ℝ)) volume :=
    ((aLaplaceIntegral_convergent (u := u) hu).mono_set
      fun _ ht => lt_trans (by norm_num : (0:ℝ) < 1) ht).neg
  refine hNeg.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simpa using (Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand (u := u) (t := t)).symm

/-- Integrability of `Φ₂'` on the imaginary-axis bounded interval `(1,A]`. -/
lemma integrableOn_Φ₂'_imag_axis_Ioc (u A : ℝ) :
    IntegrableOn (fun t : ℝ => Φ₂' u ((t : ℂ) * I)) (Set.Ioc (1 : ℝ) A) volume := by
  have hcontΦ2 : ContinuousOn (Φ₂' u) {z : ℂ | 0 < z.im} :=
    (MagicFunction.a.ComplexIntegrands.Φ₁'_contDiffOn_ℂ (r := u)).continuousOn
  have hmapsIcc : Set.MapsTo (fun t : ℝ => ((t : ℂ) * I : ℂ)) (Set.Icc (1 : ℝ) A)
      {z : ℂ | 0 < z.im} :=
    fun t ht => by simpa using lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) ht.1
  exact ((hcontΦ2.comp (by fun_prop) hmapsIcc).integrableOn_compact
    isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

/-- Measurability of the imaginary-axis tail integrand `t ↦ Φ₂' u (tI)` on `t > A`. -/
lemma aestronglyMeasurable_Φ₂'_imag_axis_Ioi (u A : ℝ) (hA0 : 0 < A) :
    AEStronglyMeasurable (fun t : ℝ => Φ₂' u ((t : ℂ) * Complex.I))
      (volume.restrict (Set.Ioi A)) :=
  ((MagicFunction.a.ComplexIntegrands.Φ₁'_contDiffOn_ℂ (r := u)).continuousOn.comp
    (by fun_prop) fun t ht => by simpa using lt_trans hA0 ht).aestronglyMeasurable
    measurableSet_Ioi

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
  have ht_nonneg : 0 ≤ t := by linarith
  have hAw : Aφ ≤ wH.im := by simpa [hw_im] using htAφ
  have hφ2 : ‖φ₂' wH‖ ≤ Cφ * Real.exp (2 * π * t) := by
    simpa [hw_im] using (hφbd wH hAw).1
  have hφ4 : ‖φ₄' wH‖ ≤ Cφ * Real.exp (2 * π * t) := by
    simpa [hw_im] using (hφbd wH hAw).2
  have hφ0 : ‖φ₀ wH‖ ≤ C₀ := by
    have hhalf : (1 / 2 : ℝ) < wH.im := by
      rw [hw_im]; linarith
    have hexp : Real.exp (-2 * π * wH.im) ≤ 1 := Real.exp_le_one_iff.2 <| by
      nlinarith [Real.pi_pos, wH.im_pos]
    exact (hC₀ wH hhalf).trans (mul_le_of_le_one_right hC₀_pos.le hexp)
  have hw2 : ‖(wH : ℂ) ^ (2 : ℕ)‖ ≤ (2 * t) ^ (2 : ℕ) := by
    simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hw_norm 2
  have hexp_nonneg : 0 ≤ Real.exp (2 * π * t) := (Real.exp_pos _).le
  have hexp_ge : (1 : ℝ) ≤ Real.exp (2 * π * t) :=
    Real.one_le_exp_iff.2 <| by positivity
  have hY_nonneg : 0 ≤ Cφ * Real.exp (2 * π * t) := (norm_nonneg _).trans hφ2
  have hCφ_nonneg : 0 ≤ Cφ :=
    le_of_mul_le_mul_right (by simpa using hY_nonneg) (Real.exp_pos _)
  have ht_le : t ≤ t ^ 2 := by nlinarith
  have ht2 : (1 : ℝ) ≤ t ^ 2 := one_le_pow₀ ht1
  have ht2_nonneg : 0 ≤ t ^ 2 := by positivity
  -- Triangle inequality.
  have hS : φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ)) =
      φ₀ wH * ((wH : ℂ) ^ (2 : ℕ)) -
        (12 * Complex.I) / π * (wH : ℂ) * φ₂' wH -
          (36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH := by
    simpa using φ₀_S_transform_mul_sq (w := wH)
  have htri : ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
      ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ +
        ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖ +
          ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖ := by
    rw [hS]
    refine (norm_sub_le _ _).trans ?_
    gcongr
    exact norm_sub_le _ _
  -- Bound each of the three summands by `Kᵢ * (t^2 * exp(2πt))`.
  have hA : ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
      (4 * C₀) * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
    calc ‖φ₀ wH * ((wH : ℂ) ^ (2 : ℕ))‖
        ≤ C₀ * (2 * t) ^ 2 :=
          (norm_mul_le _ _).trans (mul_le_mul hφ0 hw2 (norm_nonneg _) hC₀_pos.le)
      _ = (4 * C₀) * t ^ 2 := by ring
      _ ≤ (4 * C₀) * (t ^ 2 * Real.exp (2 * π * t)) := by
          have : 0 ≤ 4 * C₀ := by positivity
          gcongr
          nlinarith [ht2_nonneg]
  have hB : ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖ ≤
      (2 * c12π * Cφ) * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
    have h2coeff : 0 ≤ 2 * c12π * Cφ := by positivity
    calc ‖(12 * Complex.I) / π * (wH : ℂ) * φ₂' wH‖
        ≤ (c12π * ‖(wH : ℂ)‖) * ‖φ₂' wH‖ := norm_mul₃_le
      _ ≤ (c12π * (2 * t)) * (Cφ * Real.exp (2 * π * t)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw_norm (norm_nonneg _))
            hφ2 (norm_nonneg _) (by positivity)
      _ = (2 * c12π * Cφ) * (t * Real.exp (2 * π * t)) := by ring
      _ ≤ (2 * c12π * Cφ) * (t ^ 2 * Real.exp (2 * π * t)) := by
          gcongr
  have hC : ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖ ≤
      c36π2 * Cφ * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) := by
    have hccoeff : 0 ≤ c36π2 * Cφ := by positivity
    calc ‖(36 : ℂ) / (π ^ (2 : ℕ)) * φ₄' wH‖
        ≤ c36π2 * ‖φ₄' wH‖ := norm_mul_le _ _
      _ ≤ c36π2 * (Cφ * Real.exp (2 * π * t)) :=
          mul_le_mul_of_nonneg_left hφ4 (norm_nonneg _)
      _ = c36π2 * Cφ * (1 * Real.exp (2 * π * t)) := by ring
      _ ≤ c36π2 * Cφ * (t ^ 2 * Real.exp (2 * π * t)) := by gcongr
  linarith [htri, hA, hB, hC]

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
  set K : ℝ := 4 * C₀ + (2 * c12π + c36π2) * Cφ
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
  -- Set `w = tI + 1` and work in `ℍ`.
  let wH : ℍ := ⟨(t : ℂ) * I + 1, by simpa using ht0⟩
  have hwH_im : wH.im = t := by simp [wH, UpperHalfPlane.im]
  have hwH_coe : (wH : ℂ) = (t : ℂ) * I + 1 := rfl
  -- Bound `‖w‖` by `2*t` (since `t ≥ 1`).
  have hw_norm : ‖(wH : ℂ)‖ ≤ 2 * t := by
    have hIt : ‖(t : ℂ) * Complex.I‖ = t := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg ht0.le]
    calc ‖(wH : ℂ)‖ = ‖(t : ℂ) * I + 1‖ := by rw [hwH_coe]
      _ ≤ ‖(t : ℂ) * I‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = t + 1 := by rw [hIt]; simp
      _ ≤ 2 * t := by linarith
  have hmod : ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ ≤
      K * (t ^ (2 : ℕ) * Real.exp (2 * π * t)) :=
    norm_phi0S_mul_sq_le wH hwH_im hC₀_pos hC₀ hφbd ht1 htAφ hw_norm
  -- `Φ₂' u (tI) = (φ₀(S•w) * w^2) * exp(…)` on the imaginary axis.
  have hdef : Φ₂' u ((t : ℂ) * I) =
      (φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))) *
        cexp ((π : ℂ) * I * (u : ℂ) * ((t : ℂ) * I)) := by
    have hwS : φ₀ (ModularGroup.S • wH) = φ₀'' ((ModularGroup.S • wH : ℍ) : ℂ) := by simp
    have harg : ((ModularGroup.S • wH : ℍ) : ℂ) = (-1 : ℂ) / (wH : ℂ) := by
      simpa using ModularGroup.coe_S_smul (z := wH)
    have hphi0S : φ₀'' ((-1 : ℂ) / (((t : ℂ) * I) + 1)) * (((t : ℂ) * I + 1) ^ (2 : ℕ)) =
        φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ)) := by
      rw [show ((t : ℂ) * I + 1) = (wH : ℂ) from rfl, hwS, harg]
    rw [show Φ₂' u ((t : ℂ) * I) =
      (φ₀'' ((-1 : ℂ) / (((t : ℂ) * I) + 1)) * (((t : ℂ) * I + 1) ^ (2 : ℕ))) *
        cexp ((π : ℂ) * I * (u : ℂ) * ((t : ℂ) * I)) from by
      simp [MagicFunction.a.ComplexIntegrands.Φ₂', MagicFunction.a.ComplexIntegrands.Φ₁',
        mul_assoc], hphi0S]
  have hExpNorm : ‖cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I))‖ =
      Real.exp (-π * u * t) := by
    have hexp : cexp ((π : ℂ) * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I)) =
        (Real.exp (-π * u * t) : ℂ) := by ring_nf; simp [Complex.ofReal_exp]
    rw [hexp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hExpRew : Real.exp (2 * π * t) * Real.exp (-π * u * t) =
      Real.exp (-(π * (u - 2)) * t) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      MagicFunction.g.CohnElkies.exp_two_pi_mul_mul_exp_neg_pi_mul (u := u) (t := t)
  calc ‖Φ₂' u ((t : ℂ) * I)‖
      = ‖φ₀ (ModularGroup.S • wH) * ((wH : ℂ) ^ (2 : ℕ))‖ * Real.exp (-π * u * t) := by
        rw [hdef, norm_mul, hExpNorm]
    _ ≤ (K * (t ^ (2 : ℕ) * Real.exp (2 * π * t))) * Real.exp (-π * u * t) :=
        mul_le_mul_of_nonneg_right hmod (Real.exp_pos _).le
    _ = K * (t ^ (2 : ℕ) * Real.exp (-(π * (u - 2)) * t)) := by
        rw [show (K * (t ^ 2 * Real.exp (2 * π * t))) * Real.exp (-π * u * t) =
          K * (t ^ 2 * (Real.exp (2 * π * t) * Real.exp (-π * u * t))) from by ring, hExpRew]

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
    exact norm_Φ₂'_imag_axis_le hC₀_pos hC₀ hφbd ht1 htAφ
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
  grind only

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
